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
from __future__ import absolute_import

from pysmt.exceptions import SolverAPINotFound
from z3.z3core import Z3_inc_ref

try:
    import z3
except ImportError:
    raise SolverAPINotFound

# Keep array models expressed as values instead of Lambdas
# (see https://github.com/Z3Prover/z3/issues/1769)
z3.set_param('model_compress', False)

from six.moves import xrange


import pysmt.typing as types
import pysmt.operators as op
from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter, SolverOptions)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.qelim import QuantifierEliminator

from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              ConvertExpressionError,
                              UndefinedSymbolError, PysmtValueError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.logics import LRA, LIA, QF_UFLRA, PYSMT_LOGICS
from pysmt.oracles import get_logic
from pysmt.constants import Fraction, Numeral, is_pysmt_integer, to_python_integer


# patch z3api
z3.is_ite = lambda x: z3.is_app_of(x, z3.Z3_OP_ITE)
z3.is_function = lambda x: z3.is_app_of(x, z3.Z3_OP_UNINTERPRETED)
z3.is_array_store = lambda x: z3.is_app_of(x, z3.Z3_OP_STORE)
z3.get_payload = lambda node,i : z3.Z3_get_decl_int_parameter(node.ctx.ref(),
                                                              node.decl().ast, i)

class AstRefKey:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n.hash()
    def __eq__(self, other):
        return self.n.eq(other.n)

def askey(n):
    assert isinstance(n, z3.AstRef)
    return AstRefKey(n)



class Z3Model(Model):

    def __init__(self, environment, z3_model):
        Model.__init__(self, environment)
        self.z3_model = z3_model
        self.converter = Z3Converter(environment, z3_model.ctx)

    def print_model(self):    
        print(self.z3_model.sexpr())

    def get_diagram_sorts(self):
#         print(self.z3_model)
#         print(self.z3_model.sexpr())
#         print(self.z3_model.decls())
#         for s in self.z3_model.sorts():
#             print("%s -> %s" % (s, self.z3_model.get_universe(s)))
#         for d in self.z3_model.decls():
#             print("%s -> %s" % (d, self.z3_model.get_interp(d)))
        
        sorts = dict()
        for s in self.z3_model.sorts():
            universe = self.z3_model.get_universe(s)
            pysort = self.converter._z3_to_type(s)
            
            for v in universe:
                pyv = self.converter.back(v)
#                 print("%s of type %s\n" % (pyv, pyv.symbol_type()))
                if not(pysort in sorts):
                    sorts[pysort] = list()
                sorts[pysort].append(pyv)
                self.converter.z3MemoizeUniverse(pyv, v)
        return sorts

    def get_diagram_funcs(self):
        consts = dict()
        funcs = dict()
        for d in self.z3_model.decls():
            print("func: %s" % d)
            if d.arity() == 0:
                pyconst = self.converter._back_single_decl(d)
#                 print("%s of type %s\n" % (pyconst, pyconst.symbol_type()))
                
                if pyconst.symbol_type().is_int_type():
                    pyvalue = self.get_value(pyconst)
                else:
                    value = self.z3_model.get_interp(d)
                    pyvalue = self.converter.back(value)
                consts[pyconst] = [pyvalue]
                print("%s <- %s" % (pyconst, pyvalue))
            else:
                pyfun = self.converter._back_single_decl(d)
                value = self.z3_model.get_interp(d)
                print("%s <- %s" % (pyfun, value))
                
                arity = value.arity()
                num_entries = value.num_entries()
                print(arity)
                print(num_entries)
                for i in range(num_entries):
                    value_i = value.entry(i)
                    print("%d: %s" % (i, value_i))
                value_else = value.else_value()
                print("else: %s" % value_else)                
        return consts, funcs

    def get_value(self, formula, model_completion=True):
        titem = self.converter.convert(formula)
        z3_res = self.z3_model.eval(titem, model_completion=model_completion)
        return self.converter.back(z3_res, model=self.z3_model)

    def iterator_over(self, language):
        for x in language:
            yield x, self.get_value(x, model_completion=True)

    def __iter__(self):
        """Overloading of iterator from Model.  We iterate only on the
        variables defined in the assignment.
        """
        for d in self.z3_model.decls():
            if d.arity() == 0:
                try:
                    pysmt_d = self.converter.back(d())
                    yield pysmt_d, self.get_value(pysmt_d)
                except UndefinedSymbolError:
                    # avoids problems with symbols generated by z3
                    pass

    def __contains__(self, x):
        """Returns whether the model contains a value for 'x'."""
        return x in (v for v, _ in self)

# EOC Z3Model


class Z3Options(SolverOptions):

    @staticmethod
    def _set_option(z3solver, name, value):
        try:
            z3solver.set(name, value)
        except z3.Z3Exception:
            raise PysmtValueError("Error setting the option '%s=%s'" \
                                  % (name, value))
        except z3.z3types.Z3Exception:
            raise PysmtValueError("Error setting the option '%s=%s'" \
                                  % (name, value))

    def __call__(self, solver):
        self._set_option(solver.z3, 'model', self.generate_models)
        if self.unsat_cores_mode is not None:
            self._set_option(solver.z3, 'unsat_core', True)
        if self.random_seed is not None:
            self._set_option(solver.z3, 'random_seed', self.random_seed)
        for k,v in self.solver_options.items():
            try:
                self._set_option(solver.z3, str(k), v)
            except z3.Z3Exception:
                raise PysmtValueError("Error setting the option '%s=%s'" % (k,v))
            except z3.z3types.Z3Exception:
                raise PysmtValueError("Error setting the option '%s=%s'" % (k,v))
# EOC Z3Options


class Z3Solver(IncrementalTrackingSolver, UnsatCoreSolver,
               SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = PYSMT_LOGICS - set(x for x in PYSMT_LOGICS if x.theory.strings)
    OptionsClass = Z3Options

    def __init__(self, environment, logic, **options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           **options)
        try:
            self.z3 = z3.SolverFor(str(logic))
        except z3.Z3Exception:
            self.z3 = z3.Solver()
        except z3.z3types.Z3Exception:
            self.z3 = z3.Solver()
        self.options(self)
        self.declarations = set()
        self.converter = Z3Converter(environment, z3_ctx=self.z3.ctx)
        self.mgr = environment.formula_manager

        self._name_cnt = 0
        return

    @clear_pending_pop
    def _reset_assertions(self):
        self.z3.reset()
        self.options(self)

    @clear_pending_pop
    def declare_variable(self, var):
        raise NotImplementedError

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)

        if (named is not None) and (self.options.unsat_cores_mode is not None):
            # TODO: IF unsat_cores_mode is all, then we add this fresh variable.
            # Otherwise, we should track this only if it is named.
            key = self.mgr.FreshSymbol(template="_assertion_%d")
            tkey = self.converter.convert(key)
            self.z3.assert_and_track(term, tkey)
            return (key, named, formula)
        else:
            self.z3.add(term)
            return formula

    def get_model(self):
        return Z3Model(self.environment, self.z3.model())

    @clear_pending_pop
    def _solve(self, assumptions=None):
        if assumptions is not None:
            bool_ass = []
            other_ass = []
            for x in assumptions:
                if x.is_literal():
                    bool_ass.append(self.converter.convert(x))
                else:
                    other_ass.append(x)

            if len(other_ass) > 0:
                self.push()
                self.add_assertion(self.mgr.And(other_ass))
                self.pending_pop = True
            res = self.z3.check(*bool_ass)
        else:
            res = self.z3.check()

        sres = str(res)
        assert sres in ['unknown', 'sat', 'unsat']
        if sres == 'unknown':
            raise SolverReturnedUnknownResultError
        return (sres == 'sat')

    def get_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        set of formulae"""
        return self.get_named_unsat_core().values()

    def _named_assertions_map(self):
        if self.options.unsat_cores_mode is not None:
            return dict((t[0], (t[1],t[2])) for t in self.named_assertions)
        return None

    def get_named_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        dict of names to formulae"""
        if self.options.unsat_cores_mode is None:
            raise SolverNotConfiguredForUnsatCoresError

        if self.last_result is not False:
            raise SolverStatusError("The last call to solve() was not" \
                                    " unsatisfiable")

        if self.last_command != "solve":
            raise SolverStatusError("The solver status has been modified by a" \
                                    " '%s' command after the last call to" \
                                    " solve()" % self.last_command)

        assumptions = self.z3.unsat_core()
        pysmt_assumptions = set(self.converter.back(t) for t in assumptions)

        res = {}
        n_ass_map = self._named_assertions_map()
        cnt = 0
        for key in pysmt_assumptions:
            if key in n_ass_map:
                (name, formula) = n_ass_map[key]
                if name is None:
                    name = "_a_%d" % cnt
                    cnt += 1
                res[name] = formula
        return res

    @clear_pending_pop
    def all_sat(self, important, callback):
        raise NotImplementedError

    @clear_pending_pop
    def _push(self, levels=1):
        for _ in xrange(levels):
            self.z3.push()

    @clear_pending_pop
    def _pop(self, levels=1):
        for _ in xrange(levels):
            self.z3.pop()

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print("%s = %s" % (var.symbol_name(), self.get_value(var)))

    def get_value(self, item):
#         self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        z3_res = self.z3.model().eval(titem, model_completion=True)
        res = self.converter.back(z3_res, self.z3.model())
        if not res.is_constant():
            return res.simplify()
        return res

    def _exit(self):
        del self.converter
        del self.z3


BOOLREF_SET = op.BOOL_OPERATORS | op.RELATIONS
ARITHREF_SET = op.IRA_OPERATORS
BITVECREF_SET = op.BV_OPERATORS


class Z3Converter(Converter, DagWalker):

    def __init__(self, environment, z3_ctx):
        DagWalker.__init__(self, environment)
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type
        self._back_memoization = {}
        self.ctx = z3_ctx

        # Back Conversion
        self._back_fun = {
            z3.Z3_OP_AND: lambda args, expr: self.mgr.And(args),
            z3.Z3_OP_OR: lambda args, expr: self.mgr.Or(args),
            z3.Z3_OP_MUL: lambda args, expr: self.mgr.Times(args),
            z3.Z3_OP_ADD: lambda args, expr: self.mgr.Plus(args),
            z3.Z3_OP_DIV: lambda args, expr: self.mgr.Div(args[0], args[1]),
            z3.Z3_OP_IFF: lambda args, expr: self.mgr.Iff(args[0], args[1]),
            z3.Z3_OP_XOR: lambda args, expr:  self.mgr.Xor(args[0], args[1]),
            z3.Z3_OP_FALSE: lambda args, expr: self.mgr.FALSE(),
            z3.Z3_OP_TRUE: lambda args, expr: self.mgr.TRUE(),
            z3.Z3_OP_GT: lambda args, expr: self.mgr.GT(args[0], args[1]),
            z3.Z3_OP_GE: lambda args, expr: self.mgr.GE(args[0], args[1]),
            z3.Z3_OP_LT: lambda args, expr: self.mgr.LT(args[0], args[1]),
            z3.Z3_OP_LE: lambda args, expr: self.mgr.LE(args[0], args[1]),
            z3.Z3_OP_SUB: lambda args, expr: self.mgr.Minus(args[0], args[1]),
            z3.Z3_OP_NOT: lambda args, expr: self.mgr.Not(args[0]),
            z3.Z3_OP_IMPLIES: lambda args, expr: self.mgr.Implies(args[0], args[1]),
            z3.Z3_OP_ITE: lambda args, expr: self.mgr.Ite(args[0], args[1], args[2]),
            z3.Z3_OP_TO_REAL: lambda args, expr: self.mgr.ToReal(args[0]),
            z3.Z3_OP_BAND : lambda args, expr: self.mgr.BVAnd(args[0], args[1]),
            z3.Z3_OP_BOR : lambda args, expr: self.mgr.BVOr(args[0], args[1]),
            z3.Z3_OP_BXOR : lambda args, expr: self.mgr.BVXor(args[0], args[1]),
            z3.Z3_OP_BNOT : lambda args, expr: self.mgr.BVNot(args[0]),
            z3.Z3_OP_BNEG : lambda args, expr: self.mgr.BVNeg(args[0]),
            z3.Z3_OP_CONCAT : lambda args, expr: self.mgr.BVConcat(args[0], args[1]),
            z3.Z3_OP_ULT : lambda args, expr: self.mgr.BVULT(args[0], args[1]),
            z3.Z3_OP_ULEQ : lambda args, expr: self.mgr.BVULE(args[0], args[1]),
            z3.Z3_OP_SLT : lambda args, expr: self.mgr.BVSLT(args[0], args[1]),
            z3.Z3_OP_SLEQ : lambda args, expr: self.mgr.BVSLE(args[0], args[1]),
            z3.Z3_OP_UGT : lambda args, expr: self.mgr.BVUGT(args[0], args[1]),
            z3.Z3_OP_UGEQ : lambda args, expr: self.mgr.BVUGE(args[0], args[1]),
            z3.Z3_OP_SGT : lambda args, expr: self.mgr.BVSGT(args[0], args[1]),
            z3.Z3_OP_SGEQ : lambda args, expr: self.mgr.BVSGE(args[0], args[1]),
            z3.Z3_OP_BADD : lambda args, expr: self.mgr.BVAdd(args[0], args[1]),
            z3.Z3_OP_BMUL : lambda args, expr: self.mgr.BVMul(args[0], args[1]),
            z3.Z3_OP_BUDIV : lambda args, expr: self.mgr.BVUDiv(args[0], args[1]),
            z3.Z3_OP_BSDIV : lambda args, expr: self.mgr.BVSDiv(args[0], args[1]),
            z3.Z3_OP_BUREM : lambda args, expr: self.mgr.BVURem(args[0], args[1]),
            z3.Z3_OP_BSREM : lambda args, expr: self.mgr.BVSRem(args[0], args[1]),
            z3.Z3_OP_BSHL : lambda args, expr: self.mgr.BVLShl(args[0], args[1]),
            z3.Z3_OP_BLSHR : lambda args, expr: self.mgr.BVLShr(args[0], args[1]),
            z3.Z3_OP_BASHR : lambda args, expr: self.mgr.BVAShr(args[0], args[1]),
            z3.Z3_OP_BSUB : lambda args, expr: self.mgr.BVSub(args[0], args[1]),
            z3.Z3_OP_EXT_ROTATE_LEFT : lambda args, expr: self.mgr.BVRol(args[0], args[1].bv_unsigned_value()),
            z3.Z3_OP_EXT_ROTATE_RIGHT: lambda args, expr: self.mgr.BVRor(args[0], args[1].bv_unsigned_value()),
            z3.Z3_OP_BV2INT: lambda args, expr: self.mgr.BVToNatural(args[0]),
            z3.Z3_OP_POWER : lambda args, expr: self.mgr.Pow(args[0], args[1]),
            z3.Z3_OP_SELECT : lambda args, expr: self.mgr.Select(args[0], args[1]),
            z3.Z3_OP_STORE : lambda args, expr: self.mgr.Store(args[0], args[1], args[2]),
            # Actually use both args, expr
            z3.Z3_OP_SIGN_EXT: lambda args, expr: self.mgr.BVSExt(args[0], z3.get_payload(expr, 0)),
            z3.Z3_OP_ZERO_EXT: lambda args, expr: self.mgr.BVZExt(args[0], z3.get_payload(expr, 0)),
            z3.Z3_OP_ROTATE_LEFT: lambda args, expr: self.mgr.BVRol(args[0], z3.get_payload(expr, 0)),
            z3.Z3_OP_ROTATE_RIGHT: lambda args, expr: self.mgr.BVRor(args[0], z3.get_payload(expr, 0)),
            z3.Z3_OP_EXTRACT: lambda args, expr: self.mgr.BVExtract(args[0],
                                                              z3.get_payload(expr, 1),
                                                              z3.get_payload(expr, 0)),
            # Complex Back Translation
            z3.Z3_OP_EQ : self._back_z3_eq,
            z3.Z3_OP_UMINUS : self._back_z3_uminus,
            z3.Z3_OP_CONST_ARRAY : self._back_z3_const_array,
        }
        # Unique reference to Sorts
        self.z3RealSort = z3.RealSort(self.ctx)
        self.z3BoolSort = z3.BoolSort(self.ctx)
        self.z3IntSort  = z3.IntSort(self.ctx)
        self._z3ArraySorts = {}
        self._z3BitVecSorts = {}
        self._z3Sorts = {}
        # Unique reference to Function Declaration
        self._z3_func_decl_cache = {}
        return

    def z3MemoizeUniverse(self, key, value):
        self.memoization[key] = value.as_ast()
        
    def z3BitVecSort(self, width):
        """Return the z3 BitVecSort for the given width."""
        try:
            bvsort = self._z3BitVecSorts[width]
        except KeyError:
            bvsort = z3.BitVecSort(width, self.ctx)
            self._z3BitVecSorts[width] = bvsort
        return bvsort

    def z3ArraySort(self, key, value):
        """Return the z3 ArraySort for the given key value."""
        try:
            return self._z3ArraySorts[(askey(key),
                                      askey(value))]
        except KeyError:
            sort = z3.ArraySort(key, value)
            self._z3ArraySorts[(askey(key),
                               askey(value))] = sort
        return sort

    def z3Sort(self, name):
        """Return the z3 Sort for the given name."""
        name = str(name)
        try:
            return self._z3Sorts[name]
        except KeyError:
            sort = z3.DeclareSort(name, self.ctx)
            self._z3Sorts[name] = sort
        return sort

    def get_z3_ref(self, formula):
        if formula.node_type in op.QUANTIFIERS:
            return z3.QuantifierRef
        elif formula.node_type() in BOOLREF_SET:
            return z3.BoolRef
        elif formula.node_type() in ARITHREF_SET:
            return z3.ArithRef
        elif formula.node_type() in BITVECREF_SET:
            return z3.BitVecRef
        elif formula.is_symbol() or formula.is_function_application():
            if formula.is_function_application():
                type_ = formula.function_name().symbol_type()
                type_ = type_.return_type
            else:
                type_ = formula.symbol_type()

            if type_.is_bool_type():
                return z3.BoolRef
            elif type_.is_real_type() or type_.is_int_type():
                return z3.ArithRef
            elif type_.is_array_type():
                return z3.ArrayRef
            elif type_.is_bv_type():
                return z3.BitVecRef
            elif type_.is_function_type():
                return z3.FuncDeclRef
            else:
                return z3.AstRef
#                 raise NotImplementedError(formula)
        elif formula.node_type() in op.ARRAY_OPERATORS:
            return z3.ArrayRef
        elif formula.is_ite():
            child = formula.arg(1)
            return self.get_z3_ref(child)
        else:
            assert formula.is_constant(), formula
            type_ = formula.constant_type()
            if type_.is_bool_type():
                return z3.BoolRef
            elif type_.is_real_type() or type_.is_int_type():
                return z3.ArithRef
            elif type_.is_array_type():
                return z3.ArrayRef
            elif type_.is_bv_type():
                return z3.BitVecRef
            else:
                raise NotImplementedError(formula)

    @catch_conversion_error
    def convert(self, formula):
        z3term = self.walk(formula)
        ref_class = self.get_z3_ref(formula)
        return ref_class(z3term, self.ctx)

    def back(self, expr, model=None):
        """Convert a Z3 expression back into a pySMT expression.

        This is done using the Z3 API. For very big expressions, it is
        sometimes faster to go through the SMT-LIB format. In those
        cases, consider using the method back_via_smtlib.
        """
        stack = [expr]
        while len(stack) > 0:
            current = stack.pop()
            key = (askey(current), model)
            if key not in self._back_memoization:
                self._back_memoization[key] = None
                stack.append(current)
                for c in current.children():
                    stack.append(c)
            elif self._back_memoization[key] is None:
                args = [self._back_memoization[(askey(c), model)]
                        for c in current.children()]
                res = self._back_single_term(current, args, model)
                self._back_memoization[key] = res
            else:
                # we already visited the node, nothing else to do
                pass
        return self._back_memoization[(askey(expr), model)]

    def _back_single_decl(self, decl, args=[]):
        try:
            fsymbol = self.mgr.get_symbol(decl.name())
            return fsymbol
        except UndefinedSymbolError:
            print("decl: %s not found" % decl)
            return self.back(decl(args))
        

    def _back_single_term(self, expr, args, model=None):
        assert z3.is_expr(expr)

        if z3.is_quantifier(expr):
            raise NotImplementedError(
                "Quantified back conversion is currently not supported")

        assert not len(args) > 2 or \
            (z3.is_and(expr) or z3.is_or(expr) or
             z3.is_add(expr) or z3.is_mul(expr) or
             (len(args) == 3 and (z3.is_ite(expr) or z3.is_array_store(expr)))),\
            "Unexpected n-ary term: %s" % expr

        res = None
        try:
            decl = z3.Z3_get_app_decl(expr.ctx_ref(), expr.as_ast())
            kind = z3.Z3_get_decl_kind(expr.ctx.ref(), decl)
            # Try to get the back-conversion function for the given Kind
            fun = self._back_fun[kind]
            return fun(args, expr)
        except KeyError as ex:
            pass

        if z3.is_const(expr):
            # Const or Symbol
            if z3.is_rational_value(expr):
                n = expr.numerator_as_long()
                d = expr.denominator_as_long()
                f = Fraction(n, d)
                return self.mgr.Real(f)
            elif z3.is_int_value(expr):
                n = expr.as_long()
                return self.mgr.Int(n)
            elif z3.is_bv_value(expr):
                n = expr.as_long()
                w = expr.size()
                return self.mgr.BV(n, w)
            elif z3.is_as_array(expr):
                if model is None:
                    raise NotImplementedError("As-array expressions cannot be" \
                                              " handled as they are not " \
                                              "self-contained")
                else:
                    interp_decl = z3.get_as_array_func(expr)
                    interp = model[interp_decl]
                    default = self.back(interp.else_value(), model=model)
                    assign = {}
                    for i in xrange(interp.num_entries()):
                        e = interp.entry(i)
                        assert e.num_args() == 1
                        idx = self.back(e.arg_value(0), model=model)
                        val = self.back(e.value(), model=model)
                        assign[idx] = val
                    arr_type = self._z3_to_type(expr.sort())
                    return self.mgr.Array(arr_type.index_type, default, assign)
            elif z3.is_algebraic_value(expr):
                # Algebraic value
                return self.mgr._Algebraic(Numeral(expr))
            else:
                # it must be a symbol
                try:
                    return self.mgr.get_symbol(str(expr))
                except UndefinedSymbolError:
#                     import warnings
                    symb_type = self._z3_to_type(expr.sort())
                    return self.mgr.Symbol(str(expr), symb_type)
#                     warnings.warn("Defining new symbol: %s" % str(expr))
#                     return self.mgr.FreshSymbol(symb_type,
#                                                 template="__z3_%d")
        elif z3.is_function(expr):
            # This needs to be after we try to convert regular Symbols
            fsymbol = self.mgr.get_symbol(expr.decl().name())
            return self.mgr.Function(fsymbol, args)

        # If we reach this point, we did not manage to translate the expression
        raise ConvertExpressionError(message=("Unsupported expression: %s" %
                                              (str(expr))),
                                     expression=expr)

    def _back_z3_eq(self, args, expr):
        if self._get_type(args[0]).is_bool_type():
            return self.mgr.Iff(args[0], args[1])
        return self.mgr.Equals(args[0], args[1])

    def _back_z3_uminus(self, args, expr):
        tp = self._get_type(args[0])
        if tp.is_real_type():
            minus_one = self.mgr.Real(-1)
        else:
            assert tp.is_int_type()
            minus_one = self.mgr.Int(-1)
        return self.mgr.Times(args[0], minus_one)

    def _back_z3_const_array(self, args, expr):
        arr_ty = self._z3_to_type(expr.sort())
        return self.mgr.Array(arr_ty.index_type, args[0])

    def back_via_smtlib(self, expr):
        """Back convert a Z3 Expression by translation to SMT-LIB."""
        from six import StringIO
        from pysmt.smtlib.parser import SmtLibZ3Parser
        parser = SmtLibZ3Parser(self.env)

        z3.Z3_set_ast_print_mode(expr.ctx.ref(), z3.Z3_PRINT_SMTLIB2_COMPLIANT)
        s = z3.Z3_benchmark_to_smtlib_string(expr.ctx.ref(),
                                             None, None,
                                             None, None,
                                             0, None,
                                             expr.ast)
        stream_in = StringIO(s)
        r = parser.get_script(stream_in).get_last_formula(self.mgr)
        key = (askey(expr), None)
        self._back_memoization[key] = r
        return r

    # Fwd Conversion
    def _to_ast_array(self, args):
        """Convert a list of arguments into an z3.AST vector."""
        sz = len(args)
        _args = (z3.Ast * sz)()
        for i, arg in enumerate(args):
            _args[i] = arg
        return _args, sz

    def walk_not(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_not(self.ctx.ref(), args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_symbol(self, formula, **kwargs):
        symbol_type = formula.symbol_type()
        if symbol_type.is_function_type():
            res = self._z3_func_decl(formula)
        else:
            sname = formula.symbol_name()
            z3_sname = z3.Z3_mk_string_symbol(self.ctx.ref(), sname)
            if symbol_type.is_bool_type():
                sort_ast = self.z3BoolSort.ast
            elif symbol_type.is_real_type():
                sort_ast = self.z3RealSort.ast
            elif symbol_type.is_int_type():
                sort_ast = self.z3IntSort.ast
            elif symbol_type.is_array_type():
                sort_ast = self._type_to_z3(symbol_type).ast
            elif symbol_type.is_string_type():
                raise ConvertExpressionError(message=("Unsupported string symbol: %s" %
                                                      str(formula)),
                                             expression=formula)
            elif symbol_type.is_custom_type():
                sort_ast = self._type_to_z3(symbol_type).ast
            else:
                sort_ast = self._type_to_z3(symbol_type).ast
            # Create const with given sort
            res = z3.Z3_mk_const(self.ctx.ref(), z3_sname, sort_ast)
            z3.Z3_inc_ref(self.ctx.ref(), res)
        return res

    def walk_ite(self, formula, args, **kwargs):
        i = args[0]
        ni = self.walk_not(None, (i,))
        t = args[1]
        e = args[2]

        if self._get_type(formula).is_bool_type():
            # Rewrite as (!i \/ t) & (i \/ e)
            _args, sz = self._to_ast_array((ni, t))
            or1 = z3.Z3_mk_or(self.ctx.ref(), sz, _args)
            z3.Z3_inc_ref(self.ctx.ref(), or1)
            _args, sz = self._to_ast_array((i, e))
            or2 = z3.Z3_mk_or(self.ctx.ref(), sz, _args)
            z3.Z3_inc_ref(self.ctx.ref(), or2)
            _args, sz = self._to_ast_array((or1, or2))
            z3term = z3.Z3_mk_and(self.ctx.ref(), sz, _args)
            z3.Z3_inc_ref(self.ctx.ref(), z3term)
            z3.Z3_dec_ref(self.ctx.ref(), or1)
            z3.Z3_dec_ref(self.ctx.ref(), or2)
            return z3term
        z3term = z3.Z3_mk_ite(self.ctx.ref(), i, t, e)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        z3term = z3.Z3_mk_numeral(self.ctx.ref(),
                                  rep,
                                  self.z3RealSort.ast)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_int_constant(self, formula, **kwargs):
        assert is_pysmt_integer(formula.constant_value())
        const = str(formula.constant_value())
        z3term = z3.Z3_mk_numeral(self.ctx.ref(),
                                  const,
                                  self.z3IntSort.ast)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bool_constant(self, formula, **kwargs):
        _t = z3.BoolVal(formula.constant_value(), ctx=self.ctx)
        z3term = _t.as_ast()
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_quantifier(self, formula, args, **kwargs):
        qvars = formula.quantifier_vars()
        qvars, qvars_sz = self._to_ast_array([self.walk_symbol(x)\
                                              for x in qvars])
        empty_str = z3.Z3_mk_string_symbol(self.ctx.ref(), "")
        z3term = z3.Z3_mk_quantifier_const_ex(self.ctx.ref(),
                                              formula.is_forall(),
                                              1, empty_str, empty_str,
                                              qvars_sz, qvars,
                                              0, None, 0, None,
                                              args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_toreal(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_int2real(self.ctx.ref(), args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def _z3_func_decl(self, func_name):
        """Create a Z3 Function Declaration for the given function."""
        try:
            return self._z3_func_decl_cache[func_name]
        except KeyError:
            tp = func_name.symbol_type()
            arity = len(tp.param_types)
            z3dom = (z3.Sort * arity)()
            for i, t in enumerate(tp.param_types):
                z3dom[i] = self._type_to_z3(t).ast
            z3ret = self._type_to_z3(tp.return_type).ast
            z3name = z3.Z3_mk_string_symbol(self.ctx.ref(),
                                            func_name.symbol_name())
            z3func = z3.Z3_mk_func_decl(self.ctx.ref(), z3name,
                                        arity, z3dom, z3ret)
            self._z3_func_decl_cache[func_name] = z3func
            return z3func

    def walk_function(self, formula, args, **kwargs):
        z3func = self._z3_func_decl(formula.function_name())
        _args, sz = self._to_ast_array(args)
        z3term = z3.Z3_mk_app(self.ctx.ref(), z3func, sz, _args)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_constant(self, formula, **kwargs):
        value = formula.constant_value()
        z3term = z3.Z3_mk_numeral(self.ctx.ref(),
                                  str(value),
                                  self.z3BitVecSort(formula.bv_width()).ast)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_extract(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_extract(self.ctx.ref(),
                                  formula.bv_extract_end(),
                                  formula.bv_extract_start(),
                                  args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_not(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_bvnot(self.ctx.ref(), args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_neg(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_bvneg(self.ctx.ref(), args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_rol(self, formula, args, **kwargs):
        bvsort = self.z3BitVecSort(formula.bv_width())
        step = z3.Z3_mk_numeral(self.ctx.ref(),
                                str(formula.bv_rotation_step()),
                                bvsort.ast)
        z3term = z3.Z3_mk_ext_rotate_left(self.ctx.ref(),
                                          args[0], step)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_ror(self, formula, args, **kwargs):
        bvsort = self.z3BitVecSort(formula.bv_width())
        step = z3.Z3_mk_numeral(self.ctx.ref(),
                                str(formula.bv_rotation_step()),
                                bvsort.ast)
        z3term = z3.Z3_mk_ext_rotate_right(self.ctx.ref(),
                                          args[0], step)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_zext(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_zero_ext(self.ctx.ref(),
                                   formula.bv_extend_step(), args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_sext (self, formula, args, **kwargs):
        z3term = z3.Z3_mk_sign_ext(self.ctx.ref(),
                                   formula.bv_extend_step(), args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_bv_comp(self, formula, args, **kwargs):
        cond = z3.Z3_mk_eq(self.ctx.ref(), args[0], args[1])
        z3.Z3_inc_ref(self.ctx.ref(), cond)
        then_ = z3.Z3_mk_numeral(self.ctx.ref(), "1", self.z3BitVecSort(1).ast)
        z3.Z3_inc_ref(self.ctx.ref(), then_)
        else_ = z3.Z3_mk_numeral(self.ctx.ref(), "0", self.z3BitVecSort(1).ast)
        z3.Z3_inc_ref(self.ctx.ref(), else_)
        z3term = z3.Z3_mk_ite(self.ctx.ref(), cond, then_, else_)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        # De-Ref since this is handled internally by Z3
        z3.Z3_dec_ref(self.ctx.ref(), cond)
        z3.Z3_dec_ref(self.ctx.ref(), then_)
        z3.Z3_dec_ref(self.ctx.ref(), else_)
        return z3term

    def walk_bv_tonatural(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_bv2int(self.ctx.ref(), args[0], False)
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_array_select(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_select(self.ctx.ref(), args[0], args[1])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_array_store(self, formula, args, **kwargs):
        z3term = z3.Z3_mk_store(self.ctx.ref(), args[0], args[1], args[2])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def walk_array_value(self, formula, args, **kwargs):
        idx_type = formula.array_value_index_type()
        arraysort = self._type_to_z3(idx_type).ast
        z3term = z3.Z3_mk_const_array(self.ctx.ref(), arraysort, args[0])
        z3.Z3_inc_ref(self.ctx.ref(), z3term)

        for i in xrange(1, len(args), 2):
            c = args[i]
            z3term = self.walk_array_store(None, (z3term, c, args[i+1]))
            z3.Z3_inc_ref(self.ctx.ref(), z3term)
        return z3term

    def _z3_to_type(self, sort):
        if sort.kind() == z3.Z3_BOOL_SORT:
            return types.BOOL
        elif sort.kind() == z3.Z3_INT_SORT:
            return types.INT
        elif sort.kind() == z3.Z3_REAL_SORT:
            return types.REAL
        elif sort.kind() == z3.Z3_ARRAY_SORT:
            return types.ArrayType(self._z3_to_type(sort.domain()),
                                   self._z3_to_type(sort.range()))
        elif sort.kind() == z3.Z3_BV_SORT:
            return types.BVType(sort.size())
        elif sort.kind() == z3.Z3_UNINTERPRETED_SORT:
            return types.Type(str(sort))
        else:
            raise NotImplementedError("Unsupported sort in conversion: %s" % sort)

    def make_walk_nary(func):
        def walk_nary(self, formula, args, **kwargs):
            _args, sz = self._to_ast_array(args)
            z3term = func(self.ctx.ref(), sz, _args)
            z3.Z3_inc_ref(self.ctx.ref(), z3term)
            return z3term
        return walk_nary

    def make_walk_binary(func):
        def walk_binary(self, formula, args, **kwargs):
            z3term = func(self.ctx.ref(), args[0], args[1])
            z3.Z3_inc_ref(self.ctx.ref(), z3term)
            return z3term
        return walk_binary

    walk_and     = make_walk_nary(z3.Z3_mk_and)
    walk_or      = make_walk_nary(z3.Z3_mk_or)
    walk_plus    = make_walk_nary(z3.Z3_mk_add)
    walk_times   = make_walk_nary(z3.Z3_mk_mul)
    walk_minus   = make_walk_nary(z3.Z3_mk_sub)
    walk_implies = make_walk_binary(z3.Z3_mk_implies)
    walk_le      = make_walk_binary(z3.Z3_mk_le)
    walk_lt      = make_walk_binary(z3.Z3_mk_lt)
    walk_equals  = make_walk_binary(z3.Z3_mk_eq)
    walk_iff     = make_walk_binary(z3.Z3_mk_eq)
    walk_pow     = make_walk_binary(z3.Z3_mk_power)
    walk_div     = make_walk_binary(z3.Z3_mk_div)
    walk_bv_ult  = make_walk_binary(z3.Z3_mk_bvult)
    walk_bv_ule  = make_walk_binary(z3.Z3_mk_bvule)
    walk_bv_slt  = make_walk_binary(z3.Z3_mk_bvslt)
    walk_bv_sle  = make_walk_binary(z3.Z3_mk_bvsle)
    walk_bv_concat = make_walk_binary(z3.Z3_mk_concat)
    walk_bv_or   = make_walk_binary(z3.Z3_mk_bvor)
    walk_bv_and  = make_walk_binary(z3.Z3_mk_bvand)
    walk_bv_xor  = make_walk_binary(z3.Z3_mk_bvxor)
    walk_bv_add  = make_walk_binary(z3.Z3_mk_bvadd)
    walk_bv_sub  = make_walk_binary(z3.Z3_mk_bvsub)
    walk_bv_mul  = make_walk_binary(z3.Z3_mk_bvmul)
    walk_bv_udiv = make_walk_binary(z3.Z3_mk_bvudiv)
    walk_bv_urem = make_walk_binary(z3.Z3_mk_bvurem)
    walk_bv_lshl = make_walk_binary(z3.Z3_mk_bvshl)
    walk_bv_lshr = make_walk_binary(z3.Z3_mk_bvlshr)
    walk_bv_sdiv = make_walk_binary(z3.Z3_mk_bvsdiv)
    walk_bv_srem = make_walk_binary(z3.Z3_mk_bvsrem)
    walk_bv_ashr = make_walk_binary(z3.Z3_mk_bvashr)
    walk_exists = walk_quantifier
    walk_forall = walk_quantifier

    def _type_to_z3(self, tp):
        """Convert a pySMT type into the corresponding Z3 sort."""
        if tp.is_bool_type():
            return self.z3BoolSort
        elif tp.is_real_type():
            return self.z3RealSort
        elif tp.is_int_type():
            return self.z3IntSort
        elif tp.is_array_type():
            key_sort = self._type_to_z3(tp.index_type)
            val_sort = self._type_to_z3(tp.elem_type)
            return self.z3ArraySort(key_sort, val_sort)
        elif tp.is_bv_type():
            return self.z3BitVecSort(tp.width)
        else:
            assert tp.is_custom_type(), "Unsupported type '%s'" % tp
            return self.z3Sort(tp)
        raise NotImplementedError("Unsupported type in conversion: %s" % tp)

    def __del__(self):
        # Cleaning-up Z3Converter requires dec-ref'ing the terms in the cache
        if self.ctx.ref():
            # Check that there is still a context object
            # This might not be the case if we are using the global context
            # and the interpreter is shutting down
            for t in self.memoization.values():
                z3.Z3_dec_ref(self.ctx.ref(), t)

# EOC Z3Converter

class Z3QuantifierEliminator(QuantifierEliminator):

    LOGICS = [LIA, LRA]

    def __init__(self, environment, logic=None):
        QuantifierEliminator.__init__(self)
        self.environment = environment
        self.logic = logic
        self.converter = Z3Converter(environment, z3.main_ctx())

    def eliminate_quantifiers(self, formula):
        logic = get_logic(formula, self.environment)
        if not logic <= LRA and not logic <= LIA:
            raise PysmtValueError("Z3 quantifier elimination only "\
                                  "supports LRA or LIA without combination."\
                                  "(detected logic is: %s)" % str(logic))

        simplifier = z3.Tactic('simplify')
        eliminator = z3.Tactic('qe')

        f = self.converter.convert(formula)
        s = simplifier(f, elim_and=True,
                       pull_cheap_ite=True,
                       ite_extra_rules=True).as_expr()
        res = eliminator(f).as_expr()

        pysmt_res = None
        try:
            pysmt_res = self.converter.back(res)
        except ConvertExpressionError:
            if logic <= LRA:
                raise
            raise ConvertExpressionError(message=("Unable to represent" \
                "expression %s in pySMT: the quantifier elimination for " \
                "LIA is incomplete as it requires the modulus. You can " \
                "find the Z3 expression representing the quantifier " \
                "elimination as the attribute 'expression' of this " \
                "exception object" % str(res)),
                                          expression=res)

        return pysmt_res

    def _exit(self):
        pass
