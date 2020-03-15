#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
import warnings

from six import iteritems

import pysmt.walkers
from pysmt.walkers.generic import handles
import pysmt.operators as op
from pysmt.exceptions import PysmtTypeError


class Substituter(pysmt.walkers.IdentityDagWalker):
    """Performs substitution of a set of terms within a formula.

    Let f be a formula ans subs be a map from formula to formula.
    Substitution returns a formula f' in which all occurrences of the
    keys of the map have been replaced by their value.

    There are a few considerations to take into account:
      - In which order to apply the substitution
      - How to deal with quantified subformulas

    The order in which we apply the substitutions gives raise to two
    different approaches: Most General Substitution and Most Specific
    Substitution. Lets consider the example:

      f = (a & b)
      subs = {a -> c, (c & b) -> d, (a & b) -> c}

    With the Most General Substitution (MGS) we obtain:
      f' = c
    with the Most Specific Substitution (MSS) we obtain:
      f' = d

    The default behavior before version 0.5 was MSS. However, this
    leads to unexpected results when dealing with literals, i.e.,
    substitutions in which both x and Not(x) appear, do not work as
    expected.  In case of doubt, it is recommended to issue two
    separate calls to the substitution procedure.
    """
    def __init__(self, env):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=env, invalidate_memoization=True)
        self.manager = self.env.formula_manager
        if self.__class__ == Substituter:
            raise NotImplementedError(
                "Cannot instantiate abstract Substituter class directly. "
                "Use MSSubstituter or MGSubstituter instead.")

    def _get_key(self, formula, **kwargs):
        return formula

    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""

        # Deal with quantifiers
        if formula.is_quantifier():
            # 1. We create a new substitution in which we remove the
            #    bound variables from the substitution map
            substitutions = kwargs["substitutions"]
            ssubstitutions = kwargs["ssubstitutions"]
            simplemode = kwargs["simplemode"]
            new_subs = {}
            if simplemode:
                new_subs = substitutions
            else:
                for k,v in iteritems(substitutions):
                    # If at least one bound variable is in the cone of k,
                    # we do not consider this substitution in the body of
                    # the quantifier.
                    if all(m not in formula.quantifier_vars()
                           for m in k.get_free_variables()):
                        new_subs[k] = v

            # 2. We apply the substitution on the quantifier body with
            #    the new 'reduced' map
            sub = self.__class__(self.env)
            res_formula = sub.substitute_helper(formula.arg(0), new_subs, ssubstitutions, simplemode)

            # 3. We invoke the relevant function (walk_exists or
            #    walk_forall) to compute the substitution
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=[res_formula], **kwargs)

            # 4. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            pysmt.walkers.IdentityDagWalker._push_with_children_to_stack(self,
                                                                         formula,
                                                                         **kwargs)

    def simple_substitute(self, formula, subs, ssubs=None):
        return self.substitute_helper(formula, subs, ssubs, simple=True)
        
    def substitute(self, formula, subs, ssubs=None):
        return self.substitute_helper(formula, subs, ssubs, simple=False)
        
    def substitute_helper(self, formula, subs, ssubs=None, simple=False):
        """Replaces any subformula in formula with the definition in subs."""

        # Check that formula is a term
        if not formula.is_term():
            raise PysmtTypeError("substitute() can only be used on terms.")

        for (i, k) in enumerate(subs):
            v = subs[k]
#             # Check that substitutions are terms
#             if not k.is_term():
#                 raise PysmtTypeError(
#                     "Only terms should be provided as substitutions." +
#                     " Non-term '%s' found." % k)
#             if not v.is_term():
#                 raise PysmtTypeError(
#                     "Only terms should be provided as substitutions." +
#                     " Non-term '%s' found." % v)
            # Check that substitutions belong to the current formula manager
            if k not in self.manager:
                raise PysmtTypeError(
                    "Key %d does not belong to the Formula Manager." % i)
            if v not in self.manager:
                raise PysmtTypeError(
                    "Value %d does not belong to the Formula Manager." % i)

        res = self.walk(formula, substitutions=subs, ssubstitutions=ssubs, simplemode=simple)
        return res


class MGSubstituter(Substituter):
    """Performs Most Generic Substitution.

    This is the default behavior since version 0.5
    """
    def __init__(self, env):
        Substituter.__init__(self, env=env)

    @handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_identity_or_replace(self, formula, args, **kwargs):
        """
        If the formula appears in the substitution, return the substitution.
        Otherwise, rebuild the formula by calling the IdentityWalker.
        """
        substitutions = kwargs['substitutions']
        if formula in substitutions:
            res = substitutions[formula]
        else:
            res = Substituter.super(self, formula, args=args, **kwargs)
        return res

    def walk_forall(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        if formula in substitutions:
            res = substitutions[formula]
        else:
            qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
            res = self.mgr.ForAll(qvars, args[0])
        return res

    def walk_exists(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        if formula in substitutions:
            res = substitutions[formula]
        else:
            qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
            res = self.mgr.Exists(qvars, args[0])
        return res


# EOC MGSubstituter


class MSSubstituter(Substituter):
    """Performs Most Specific Substitution.

    This was the default beahvior before version 0.5
    """

    def __init__(self, env):
        Substituter.__init__(self, env=env)

    def substitute(self, formula, subs):
        return Substituter.substitute(self, formula, subs)

    def _substitute(self, formula, substitutions):
        """Returns the substitution for formula, if one is defined, otherwise
        returns the formula unchanged.

        This is an helper function, to simplify the implementation of
        the walk_* functions.
        """
        return substitutions.get(formula, formula)

    @handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_replace(self, formula, args, **kwargs):
        new_f =  Substituter.super(self, formula, args=args, **kwargs)
        return self._substitute(new_f, kwargs['substitutions'])

    def walk_forall(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        new_f = self.mgr.ForAll(qvars, args[0])
        return self._substitute(new_f, substitutions)

    def walk_exists(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        new_f = self.mgr.Exists(qvars, args[0])
        return self._substitute(new_f, substitutions)

# EOC MSSSubstituter

class FFiniteSubstituter(pysmt.walkers.IdentityDagWalker):
    """Performs Finite Substitution.

    """
    def __init__(self, env):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=env, invalidate_memoization=False)
        self.manager = self.env.formula_manager
        self.fcache = dict()
        self.memoization.clear()

    def freset(self):
        print("len(fcache) = %d" % len(self.fcache))
        print("len(memoization) = %d" % len(self.memoization))
        self.fcache = dict()
        self.memoization.clear()

    def set_ssubs(self, ssubs):
        self.ssubstitutions = ssubs

    def get_fkey(self, formula):
        return formula

    def fsubstitute(self, formula):
        """Replaces any subformula in formula with the definition in subs."""
        # Check that formula is a term
        if not formula.is_term():
            raise PysmtTypeError("substitute() can only be used on terms.")

        res = self.walk(formula, substitutions=dict())

        key = self.get_fkey(formula)
        self.memoization[key] = res
        return res
    
    @handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_identity_or_replace(self, formula, args, **kwargs):
        """
        If the formula appears in the substitution, return the substitution.
        Otherwise, rebuild the formula by calling the IdentityWalker.
        """
        res = pysmt.walkers.IdentityDagWalker.super(self, formula, args=args, **kwargs)
        return res

    def finitize_slow(self, ipayload, ivars):
        key = (ipayload, ivars)
        if key in self.fcache:
            return self.fcache[key]
        
        q = [ipayload]
        qvars = []
        qvar2val = dict()
        subs = {}
        for v in ivars:
            vt = v.symbol_type()
            if vt in self.ssubstitutions:
                vals = self.ssubstitutions[vt]
                qvar2val[v] = [vals, 0]
                subs[v] = vals[0]
            else:
                qvars.append(v)
        
        s = [subs]
        for v, rhs in qvar2val.iteritems():
#             print("v: %s" % (v))
            vals = rhs[0]
            sN = []
#             print("s: %s" % (s))
            while len(s) > 0:
                curr = s.pop()
#                 print("curr: %s" % (curr))
                for val in vals:
                    new_subs = curr.copy()
                    new_subs[v] = val
#                     print("subs: %s" % (new_subs))
                    sN.append(new_subs)
            sN.reverse()
            s = sN
#             for v in s:
#                 print("-- %s" % v)
        
        s.reverse()
        q = []
        for curr in s:
            currval = ipayload.substitute(curr)
            q.append(currval)
#             print("-- %s" % currval)
        
        rhs = [q, qvars]
        self.fcache[key] = rhs
        return rhs

    def finitize(self, ipayload, ivars):
        key = (ipayload, ivars)
        if key in self.fcache:
            return self.fcache[key]
        
        q = [ipayload]
        qvars = []
        for v in ivars:
#             print("v: %s" % (v))
            vt = v.symbol_type()
            if vt in self.ssubstitutions:
                vals = self.ssubstitutions[vt]
    #             print("vt: %s -> %s" % (vt, vals))
                qN = []
    #             print("q: %s" % (q))
                while len(q) > 0:
                    curr = q.pop()
    #                 print("curr: %s" % (curr))
                    for val in vals:
                        new_subs = {}
                        new_subs[v] = val
    #                     print("subs: %s" % (new_subs))
#                         sub = self.__class__(self.env)
#                         sub.memoization = {}
                        currval = curr.substitute(new_subs)
    #                     print("currval: %s" % (currval))
                        qN.append(currval)
                q = qN
    #         for v in q:
    #             print("-- %s" % v)
            else:
                qvars.append(v)
        
        rhs = [q, qvars]
        self.fcache[key] = rhs
        return rhs

    def mk_finite(self, formula, args):
#         print("f: %s" % formula)
        ipayload = args[0]
        ivars = formula.quantifier_vars()
        f = self.finitize(ipayload, ivars)
        return f[0], f[1]
    
    def walk_forall(self, formula, args, **kwargs):
        fpayload, fvars = self.mk_finite(formula, args)
        res = self.mgr.And(fpayload)
        if len(fvars) != 0:
            res = self.mgr.ForAll(fvars, res)
#         print("res: %s" % res)
        return res

    def walk_exists(self, formula, args, **kwargs):
        fpayload, fvars = self.mk_finite(formula, args)
        res = self.mgr.Or(fpayload)
        if len(fvars) != 0:
            res = self.mgr.Exists(fvars, res)
#         print("res: %s" % res)
        return res

    def _get_key(self, formula, **kwargs):
        return formula

# EOC FiniteSubstituter

class FiniteSubstituter(pysmt.walkers.IdentityDagWalker):
    """Performs Finite Substitution.

    """
    def __init__(self, env):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=env, invalidate_memoization=False)
        self.manager = self.env.formula_manager
        self.memoization.clear()

    def freset(self):
#         print("len(memoization) = %d" % len(self.memoization))
        self.memoization.clear()

    def set_ssubs(self, ssubs, idx, has_inf_sort):
        self.ssubstitutions = ssubs
        self.has_inf_sort = has_inf_sort
        self.esuffix = ":e" + str(idx)

    def get_fkey(self, formula):
        return formula

    def fsubstitute(self, formula):
        """Replaces any subformula in formula with the definition in subs."""
        # Check that formula is a term
        if formula.is_symbol():
            res = self.fsymbol(formula)
        else:
            if not formula.is_term():
                raise PysmtTypeError("substitute() can only be used on terms.")

            res = self.walk(formula, substitutions=dict())

        key = self.get_fkey(formula)
        self.memoization[key] = res
        return res
    
    @handles(set(op.ALL_TYPES) - op.SYMBOLS)
    def walk_identity_or_replace(self, formula, args, **kwargs):
        """
        If the formula appears in the substitution, return the substitution.
        Otherwise, rebuild the formula by calling the IdentityWalker.
        """
        res = pysmt.walkers.IdentityDagWalker.super(self, formula, args=args, **kwargs)
        return res

    def walk_symbol(self, formula, args, **kwargs):
#         print("in: %s of type %s" % (formula, formula.symbol_type()))
        key = formula.symbol_type()
        rett = key
        if key.is_function_type():
            rett = key.return_type
        if rett in self.ssubstitutions:
            rett = self.ssubstitutions[rett]
        
        isFunc = False
        if key.is_function_type():
            argst = []
            for arg in args:
                argt = arg.get_type()
                argst.append(argt)
            rett = self.mgr.env.type_manager.FunctionType(rett, argst)
            isFunc = True
            
        res = self.mgr.Symbol(self.fsymbol_name(formula.symbol_name(), isFunc),
                               rett)
#         print("out: %s of type %s" % (res, res.symbol_type()))
        return res

    def fsymbol_name(self, name, isFunc):
        if self.has_inf_sort:
            prefix = name.rstrip('1234567890')
            if prefix.endswith(":e"):
                return prefix[:-2]
            elif not isFunc and prefix.endswith(":i"):
                return name
            else:
                if prefix.endswith(":"):
                    suffix = name[len(prefix):]
                    prefix = prefix[:-1].rstrip('1234567890')
                    if prefix.endswith(":e"):
                        prefix_new = prefix[:-2] + ":i"
                        name_new = prefix_new + ":" + suffix
                        return name_new
                elif not isFunc and prefix.endswith(":i"):
                    return name
            return name + ":i"
        else:
            if name.endswith(":i"):
                return name[:-2] + self.esuffix
            else:
                prefix = name.rstrip('1234567890')
                if prefix.endswith(":i:"):
                    suffix = name[len(prefix):]
                    prefix_new = prefix[:-3] + self.esuffix
                    name_new = prefix_new + ":" + suffix
                    return name_new
                elif not isFunc and prefix.endswith(":i"):
                    return name
        return name + self.esuffix

    def fsymbol(self, formula):
#         print("in: %s of type %s" % (formula, formula.symbol_type()))
        key = formula.symbol_type()
        rett = key
        if key.is_function_type():
            rett = key.return_type
        if rett in self.ssubstitutions:
            rett = self.ssubstitutions[rett]
        
        isFunc = False
        if key.is_function_type():
            fparams = []
            for p in key.param_types:
                fp = p
                if fp in self.ssubstitutions:
                    fp = self.ssubstitutions[fp]
                fparams.append(fp)
            rett = self.mgr.env.type_manager.FunctionType(rett, fparams)
            isFunc = True

        res = self.mgr.Symbol(self.fsymbol_name(formula.symbol_name(), isFunc),
                               rett)
#         print("out: %s of type %s" % (res, res.symbol_type()))
        return res

    def _get_key(self, formula, **kwargs):
        return formula

# EOC FiniteSubstituter



