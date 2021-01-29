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
import pysmt.logics

from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.utils import all_assignments
from pysmt.exceptions import InternalSolverError

import pysmt.walkers
from pysmt.walkers.generic import handles
import pysmt.operators as op
import itertools

class QuantifierEliminator(object):

    def __init__(self):
        self._destroyed = False

    def eliminate_quantifiers(self, formula):
        """
        Returns a quantifier-free equivalent formula of the given
        formula

        If explicit_vars is specified, an explicit enumeration of all
        the possible models for such variables is computed and
        quantifier elimination is performed on each disjunct
        separately.
        """
        raise NotImplementedError

    def __enter__(self):
        """ Manage entering a Context (i.e., with statement) """
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """ Manage exiting from Context (i.e., with statement)

        The default behaviour is to explicitely destroy the qelim to free
        the associated resources.
        """
        self.exit()

    def exit(self):
        """Destroys the solver and closes associated resources."""
        if not self._destroyed:
            self._exit()
            self._destroyed = True

    def _exit(self):
        """Destroys the solver and closes associated resources."""
        raise NotImplementedError


# class ScalarQuantifierEliminator(QuantifierEliminator, IdentityDagWalker):
#     """Quantifier Elimination over scalar domain."""
#     # We have the following categories for this walker.
#     #
#     # - Constants
#     # - Symbols
#     # - Quantifiers
#     # - Anything else
#     #
# 
#     LOGICS = [pysmt.logics.UF]
# 
#     def __init__(self, environment, logic=None):
#         IdentityDagWalker.__init__(self, env=environment)
#         QuantifierEliminator.__init__(self)
#         self.logic = logic
#         self.mgr = self.env.formula_manager
# 
#     def eliminate_quantifiers(self, formula):
#         res = self.walk(formula)
#         return res[0]
# 
#     @handles(set(op.ALL_TYPES) - op.QUANTIFIERS - op.SYMBOLS - op.CONSTANTS - frozenset([op.FUNCTION]))
#     def walk_op(self, formula, args, **kwargs):
#         res = []
# #         print("formula: %s" % formula)
# #         print("args: %s" % args)
# #         for set_ in itertools.product(*args):
# #             new_args = [set_[idx] for idx in range(len(args))]
# #             print("new_args: %s" % new_args)
#         for set_ in itertools.product(*args):
#             new_args = [set_[idx] for idx in range(len(args))]
#             inst = pysmt.walkers.IdentityDagWalker.super(self, formula, args=new_args, **kwargs)
#             res.append(inst)
# #             print("inst: %s" % inst)
#         return res
# 
#     @handles(op.CONSTANTS)
#     def walk_constant(self, formula, **kwargs):
#         return [formula]
# 
#     def walk_symbol(self, formula, args, **kwargs):
#         ft = formula.symbol_type()
#         res = []
#         if ft.is_enum_type():
#             for d in ft.domain:
#                 res.append(self.mgr.Enum(d, ft))
#         else:
#             res.append(formula)
#         return res
# 
#     def walk_function(self, formula, args, **kwargs):
#         name = formula.function_name()
#         res = []
# #         print("formula: %s" % formula)
# #         for set_ in itertools.product(*args):
# #             new_args = [set_[idx] for idx in range(len(args))]
# #             print("new_args: %s" % new_args)
#         for set_ in itertools.product(*args):
#             new_args = [set_[idx] for idx in range(len(args))]
#             inst = self.mgr.Function(name, new_args)
#             res.append(inst)
# #             print("inst: %s" % inst)
#         return res
#     
#     def walk_forall(self, formula, args, **kwargs):
#         print("QE: %s" % formula)
#         for inst in args[0]:
#             print("--- %s" % inst)
#         res = [self.mgr.And(args[0])]
#         return res
# 
#     def walk_exists(self, formula, args, **kwargs):
#         print("QE: %s" % formula)
#         for inst in args[0]:
#             print("--- %s" % inst)
#         res = [self.mgr.Or(args[0])]
#         return res
# 
#     def _exit(self):
#         pass
# 
# # EOC ShannonQuantifierEliminator


class ScalarShannonQuantifierEliminator(QuantifierEliminator, IdentityDagWalker):
    """Quantifier Elimination over scalar domain using Shannon Expansion."""

    LOGICS = [pysmt.logics.UF]

    def __init__(self, environment, logic=None):
        IdentityDagWalker.__init__(self, env=environment)
        QuantifierEliminator.__init__(self)
        self.logic = logic
        self.mgr = self.env.formula_manager
        self.enum_domain = {}
        self.instances_cache = {}

    def eliminate_quantifiers(self, formula):
        return self.walk(formula)

    def _assert_var_scalar(self, v):
        if not v.symbol_type().is_enum_type():
            raise InternalSolverError(
                "Scalar Shannon Quantifier Elimination only supports "\
                "quantification over Enum variables: "\
                "(%s is %s)" % (v, v.symbol_type()))

    def _scalar_domain(self, v):
        if v in self.enum_domain:
            return self.enum_domain[v]

        self._assert_var_scalar(v)
        vt = v.symbol_type()
        econsts = [self.mgr.Enum(d, vt) for d in vt.domain]
        self.enum_domain[v] = econsts
        return econsts

    def _scalar_instances(self, variables):
        vstr = str(variables)
        if vstr in self.instances_cache:
            return self.instances_cache[vstr]

        enums = []
        for v in variables:
            enums.append(self._scalar_domain(v))
            
        instances = []
        for set_ in itertools.product(*enums):
            d = dict((v, set_[idx]) for idx, v in enumerate(variables))
            instances.append(d)
#         instances = list(itertools.product(*enums))

        self.instances_cache[vstr] = instances
        return instances

    def _all_scalar_assignments(self, variables_orig):
        """Generates all possible assignments for a set of variables."""
        variables = set(variables_orig)
        for d in self._scalar_instances(variables):
            yield d
#             yield dict((v, d[idx]) for idx, v in enumerate(variables))

    def _expand(self, formula, args):
        """Returns the list of elements from the Shannon expansion."""
        qvarsEnum = set()
        qvarsRem = set()
        for v in formula.quantifier_vars():
            if v.symbol_type().is_enum_type():
               qvarsEnum.add(v)
            else:
                qvarsRem.add(v)
                 
        res = []
        f = args[0]
        for subs in self._all_scalar_assignments(qvarsEnum):
            res.append(f.variable_substitute(subs))
        return qvarsRem, res

    def walk_forall(self, formula, args, **kwargs):
        qvarsRem, instances = self._expand(formula, args)
        res = self.mgr.And(instances)
        if len(qvarsRem) != 0:
            res = self.mgr.ForAll(qvarsRem, res)
        return res

    def walk_exists(self, formula, args, **kwargs):
        qvarsRem, instances = self._expand(formula, args)
        res = self.mgr.Or(instances)
        if len(qvarsRem) != 0:
            res = self.mgr.Exists(qvarsRem, res)
        return res

    def _exit(self):
        pass

# EOC ShannonQuantifierEliminator


class ShannonQuantifierEliminator(QuantifierEliminator, IdentityDagWalker):
    """Quantifier Elimination using Shannon Expansion."""

    LOGICS = [pysmt.logics.BOOL]

    def __init__(self, environment, logic=None):
        IdentityDagWalker.__init__(self, env=environment)
        QuantifierEliminator.__init__(self)
        self.logic = logic

    def eliminate_quantifiers(self, formula):
        return self.walk(formula)

    def _assert_vars_boolean(self, var_set):
        for v in var_set:
            if not v.symbol_type().is_bool_type():
                raise InternalSolverError(
                    "Shannon Quantifier Elimination only supports "\
                    "quantification over Boolean variables: "\
                    "(%s is %s)" % (v, v.symbol_type()))

    def _expand(self, formula, args):
        """Returns the list of elements from the Shannon expansion."""
        qvars = formula.quantifier_vars()
        self._assert_vars_boolean(qvars)
        res = []
        f = args[0]
        for subs in all_assignments(qvars, self.env):
            res.append(f.substitute(subs))
        return res

    def walk_forall(self, formula, args, **kwargs):
        return self.mgr.And(self._expand(formula, args))

    def walk_exists(self, formula, args, **kwargs):
        return self.mgr.Or(self._expand(formula, args))

    def _exit(self):
        pass

# EOC ShannonQuantifierEliminator

class SelfSubstitutionQuantifierEliminator(QuantifierEliminator, IdentityDagWalker):
    """Boolean Quantifier Elimination based on Self-Substitution.

    Described in :
     "BDD-Based Boolean Functional Synthesis",
     Dror Fried, Lucas M. Tabajara, and Moshe Y. Vardi,
     CAV 2016
    """
    LOGICS = [pysmt.logics.BOOL]

    def __init__(self, environment, logic=None):
        IdentityDagWalker.__init__(self, env=environment)
        QuantifierEliminator.__init__(self)
        self.logic = logic

    def eliminate_quantifiers(self, formula):
        return self.walk(formula)

    def self_substitute(self, formula, qvars, token):
        for v in qvars[::-1]:
            inner_sub = formula.substitute({v: token})
            formula = formula.substitute({v: inner_sub})
        return formula

    def walk_forall(self, formula, args, **kwargs):
        """Forall y . f(x, y) =>  f(x, f(x, 0))"""
        qvars = formula.quantifier_vars()
        f = args[0]
        token = self.env.formula_manager.FALSE()
        qf_f = self.self_substitute(f, qvars, token)
        return qf_f

    def walk_exists(self, formula, args, **kwargs):
        """Exists y . f(x, y) =>  f(x, f(x, 1))"""
        qvars = formula.quantifier_vars()
        f = args[0]
        token = self.env.formula_manager.TRUE()
        qf_f = self.self_substitute(f, qvars, token)
        return qf_f

    def _exit(self):
        pass
