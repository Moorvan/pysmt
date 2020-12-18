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
import atexit
from warnings import warn

from six.moves import xrange

from pysmt.exceptions import (SolverAPINotFound,
                              SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              ConvertExpressionError,
                              UndefinedSymbolError, PysmtValueError)

try:
    import yices_api as yicespy
except ImportError:
    raise SolverAPINotFound

from ctypes import ( c_int, c_int32, c_uint32, c_int64, c_uint64, c_double )

from pysmt.solvers.eager import EagerModel
from pysmt.solvers.solver import (Solver, IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter, SolverOptions)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin

from pysmt.walkers import DagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.exceptions import (InternalSolverError, NonLinearError,
                              PysmtValueError, PysmtTypeError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.constants import Fraction, is_pysmt_integer

import pysmt.logics
from pysmt.shortcuts import QuantifierEliminator

# Initialization
def init():
    if not getattr(init, 'initialized', False):
        yicespy.yices_init()
    init.initialized = True

def reset_yices():
    yicespy.yices_reset()

init()

@atexit.register
def cleanup():
    yicespy.yices_exit()

# Yices constants
STATUS_UNKNOWN = 2
STATUS_SAT = 3
STATUS_UNSAT = 4

CTX_INVALID_PARAMETER_VALUE = 502


def yices_logic(pysmt_logic):
    """Return a Yices String representing the given pySMT logic."""
    ylogic = str(pysmt_logic)
    if ylogic == "QF_BOOL":
        ylogic = "NONE"
    return ylogic

class YicesModel(Model):

    def __init__(self, environment, yices_model, converter, qf):
        Model.__init__(self, environment)
        self.yices_model = yices_model
        self.converter = converter
        self.qf = qf
        self.mgr = environment.formula_manager

    def print_model(self):    
        status = yicespy.yices_print_model_fd(1, self.yices_model)
        self._check_error(status)

    def get_diagram_sorts(self):
        raise NotImplementedError

    def get_diagram_funcs(self):
        raise NotImplementedError

    def get_term(self, formula):
        return self.converter.get_term(formula, self.qf)
        
    def get_value(self, item, model_completion=True):
#         self._assert_no_function_type(item)
        titem = self.get_term(item)
        ty = self.environment.stc.get_type(item)
        if ty.is_bool_type():
            res = c_int32()
            status = yicespy.yices_get_bool_value(self.yices_model, titem, res)
            if (status != 0):
                res = yicespy.yices_formula_true_in_model(self.yices_model, titem)
                if res == -1:
                    return self.mgr.Bool(bool(0))
            self._check_error(status)
            return self.mgr.Bool(bool(res.value))
        elif ty.is_int_type():
            res = c_int32()
            status = yicespy.yices_get_int64_value(self.yices_model, titem, res)
            self._check_error(status)
            return self.mgr.Int(res.value)
        elif ty.is_real_type():
            num = c_int32()
            den = c_int32()
            status = yicespy.yices_get_rational64_value(self.yices_model, titem, num, den)
            self._check_error(status)
            return self.mgr.Real(Fraction(num.value, den.value))
        elif ty.is_bv_type():
            res = yicespy.make_empty_int32_array(ty.width)
            status = yicespy.yices_get_bv_value(self.yices_model, titem, res)
            self._check_error(status)
            str_val = "".join(str(x.value) for x in reversed(res))
            return self.mgr.BV("#b" + str_val)
        elif ty.is_enum_type():
            res = c_int32()
            status = yicespy.yices_get_scalar_value(self.yices_model, titem, res)
            if (status != 0):
                return self.mgr.Enum(ty._domain[0], ty)
            self._check_error(status)
            assert(res.value >= 0)
            assert(res.value < len(ty._domain))
            return self.mgr.Enum(ty._domain[res.value], ty)
        else:
            status, yices_res = yicespy.yices_get_value_as_term(self.yices_model, titem)
            self._check_error(status)
            return self.converter.back(yices_res, model=self.yices_model)

    def _check_error(self, res):
        if res != 0:
            err = yicespy.yices_error_string()
            raise InternalSolverError("Yices returned an error: " + err)

    def iterator_over(self, language):
        for x in language:
            yield x, self.get_value(x, model_completion=True)

    def __iter__(self):
        """Overloading of iterator from Model.  We iterate only on the
        variables defined in the assignment.
        """
        term_v = yicespy.term_vector_t()
        yicespy.yices_init_term_vector(term_v)
        #todo here
        status = yicespy.yices_model_collect_defined_terms(self.yices_model, term_v)
        self._check_error(status)
        for d in term_v:
            try:
                pysmt_d = self.converter.back(d())
                yield pysmt_d, self.get_value(pysmt_d)
            except UndefinedSymbolError:
                # avoids problems with symbols generated by z3
                pass
        yicespy.yices_delete_term_vector(term_v)

    def __contains__(self, x):
        """Returns whether the model contains a value for 'x'."""
        return x in (v for v, _ in self)

# EOC Z3Model

class YicesOptions(SolverOptions):
    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        # TODO: Yices Supports UnsatCore extraction
        # but we did not wrapped it yet.
#         if self.unsat_cores_mode is not None:
#             raise PysmtValueError("'unsat_cores_mode' option not supported.")

    @staticmethod
    def _set_option(cfg, name, value):
        rv = yicespy.yices_set_config(cfg, name, value)
        if rv != 0:
            # This might be a parameter to be set later (see set_params)
            # We raise the exception only if the parameter exists but the value
            # provided to the parameter is invalid.
            err = yicespy.yices_error_code()
            if err == CTX_INVALID_PARAMETER_VALUE:
                raise PysmtValueError("Error setting the option "
                                      "'%s=%s'" % (name,value))

    def __call__(self, solver):
        if self.generate_models:
            # Yices always generates models
            pass
        if self.incremental:
            self._set_option(solver.yices_config, "mode", "push-pop")
        else:
            self._set_option(solver.yices_config, "mode", "one-shot")

        if self.random_seed is not None:
            self._set_option(solver.yices_config,
                             "random-seed", str(self.random_seed))

        for k,v in self.solver_options.items():
            self._set_option(solver.yices_config, str(k), str(v))

    def set_params(self, solver):
        """Set Search Parameters.

        Yices makes a distinction between configuratin and search
        parameters.  The first are fixed for the lifetime of a
        context, while the latter can be different for every call to
        check_context.

        A list of available parameters is available at:
        http://yices.csl.sri.com/doc/parameters.html
        """
        params = yicespy.yices_new_param_record()
        yicespy.yices_default_params_for_context(solver.yices, params)
        for k,v in self.solver_options.items():
            rv = yicespy.yices_set_param(params, k, v)
            if rv != 0:
                raise PysmtValueError("Error setting the option '%s=%s'" % (k,v))
        solver.yices_params = params

# EOC YicesOptions

class YicesSolver(IncrementalTrackingSolver, UnsatCoreSolver, 
                  SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = pysmt.logics.PYSMT_QF_LOGICS -\
             pysmt.logics.ARRAYS_LOGICS -\
             set(l for l in pysmt.logics.PYSMT_QF_LOGICS
                 if not l.theory.linear or l.theory.strings)
    OptionsClass = YicesOptions

    def __init__(self, environment, logic, **options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           **options)

        self.declarations = set()
        self.yices_config = yicespy.yices_new_config()
        if yicespy.yices_default_config_for_logic(self.yices_config,
                                                  yices_logic(logic)) != 0:
            warn("Error setting config for logic %s" % logic)
        self.options(self)
        self.yices = yicespy.yices_new_context(self.yices_config)
        self.options.set_params(self)
        yicespy.yices_free_config(self.yices_config)
        self.converter = YicesConverter(environment)
        self.mgr = environment.formula_manager
        self.model = None
        self.failed_pushes = 0
        
        self.yices_assumptions = []
        self.unsat_core = None
        self.qf = False
        return

    def enable_qf(self):
        self.qf = True

    def get_term(self, formula):
        return self.converter.get_term(formula, self.qf)

    @clear_pending_pop
    def _reset_assertions(self):
        yicespy.yices_reset_context(self.yices)
        self.yices_assumptions = []

    @clear_pending_pop
    def _reset_named_assertions(self):
        self.yices_assumptions = []

    @clear_pending_pop
    def declare_variable(self, var):
        raise NotImplementedError

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.get_term(formula)

        if (named is not None) and (self.options.unsat_cores_mode is not None):
            # TODO: IF unsat_cores_mode is all, then we add this fresh variable.
            # Otherwise, we should track this only if it is named.
            key = self.mgr.FreshSymbol(template="_assertion_%d")
            tkey = self.get_term(key)
            key2term = yicespy.yices_implies(tkey, term)
            self.yices_assumptions.append(tkey)
            code = yicespy.yices_assert_formula(self.yices, key2term)
            if code != 0:
                msg = yicespy.yices_error_string()
                if code == -1 and "non-linear arithmetic" in msg:
                    raise NonLinearError(formula)
                raise InternalSolverError("Yices returned non-zero code upon assert"\
                                          ": %s (code: %s)" % \
                                          (msg, code))
            return (key, named, formula)
        else:
            code = yicespy.yices_assert_formula(self.yices, term)
            if code != 0:
                msg = yicespy.yices_error_string()
                if code == -1 and "non-linear arithmetic" in msg:
                    raise NonLinearError(formula)
                raise InternalSolverError("Yices returned non-zero code upon assert"\
                                          ": %s (code: %s)" % \
                                          (msg, code))
            return formula

    def get_model(self):
        return YicesModel(self.environment, self.model, self.converter, self.qf)

    def set_timeout(self, timeout):
        pass
            
    @clear_pending_pop
    def _solve(self, assumptions=None):
        count = 0
        if assumptions is not None:
            bool_ass = []
            other_ass = []
            assert(len(self.yices_assumptions) == 0)
            for x in assumptions:
                if x.is_literal():
                    self.yices_assumptions.append(self.get_term(x))
                    count += 1
                else:
                    other_ass.append(x)

            if len(other_ass) > 0:
                self.push()
                self.add_assertion(self.mgr.And(other_ass))
                self.pending_pop = True
        
        if len(self.yices_assumptions) == 0:
            out = yicespy.yices_check_context(self.yices, self.yices_params)
        else:
            out = yicespy.yices_check_context_with_assumptions(self.yices, self.yices_params, 
                                                               len(self.yices_assumptions), 
                                                               yicespy.make_term_array(self.yices_assumptions))
            
        if self.model is not None:
            yicespy.yices_free_model(self.model)
            self.model = None
        
        if count != 0:
            for i in range(count):
               self.yices_assumptions.pop()
            
        sres = 'unknown'
        assert out in [STATUS_SAT, STATUS_UNSAT, STATUS_UNKNOWN]
        if out == STATUS_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        elif out == STATUS_SAT:
            sres = 'sat'
            self.model = yicespy.yices_get_model(self.yices, 1)
        else:
            sres = 'unsat'
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
        
        assumptions = yicespy.term_vector_t()
        yicespy.yices_init_term_vector(assumptions)
        code = yicespy.yices_get_unsat_core(self.yices, assumptions)
        if code != 0:
            msg = yicespy.yices_error_string()
            raise InternalSolverError("Yices returned non-zero code upon unsat core extraction"\
                                      ": %s (code: %s)" % \
                                      (msg, code))
#         for i in range(assumptions.size):
#             d = assumptions.data[i]
#             print(yicespy.yices_term_to_string(d, 200, 10, 0))
        pysmt_assumptions = set(self.converter.back(assumptions.data[i]) for i in range(assumptions.size))
        yicespy.yices_delete_term_vector(assumptions)

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
            c = yicespy.yices_push(self.yices)
            if c != 0:
                # 4 is STATUS_UNSAT
                if yicespy.yices_context_status(self.yices) == 4:
                    # Yices fails to push if the context is in UNSAT state
                    # (It makes no sense to conjoin formulae to False)
                    # PySMT allows this and we support it by counting the
                    # spurious push calls
                    self.failed_pushes += 1
                else:
                    raise InternalSolverError("Error in push: %s" % \
                                              yicespy.yices_error_string())

    @clear_pending_pop
    def _pop(self, levels=1):
        for _ in xrange(levels):
            if self.failed_pushes > 0:
                self.failed_pushes -= 1
            else:
                c = yicespy.yices_pop(self.yices)
                if c != 0:
                    raise InternalSolverError("Error in pop: %s" % \
                                              yicespy.yices_error_string())

    def _exit(self):
        yicespy.yices_free_context(self.yices)
        yicespy.yices_free_param_record(self.yices_params)

# EOC YicesSolver


class YicesConverter(Converter, DagWalker):

    def __init__(self, environment):
        DagWalker.__init__(self, environment)
        self.backconversion = {}
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type

#         self.qelim = QuantifierEliminator(name="z3")
        self.qelim = QuantifierEliminator(name="scalarshannon")
        self.cache_qf = {}

        # Maps a Symbol into the corresponding internal yices instance
        self.symbol_to_decl = {}
        # Maps an internal yices instance into the corresponding symbol
        self.decl_to_symbol = {}
        self._yicesSort = {}
        self._yicesEnumSort = {}
        self._yicesEnumConsts = {}
        self._yices2pysmt = {}
    
    def quantifier_free(self, formula):
        if formula in self.cache_qf:
            return self.cache_qf[formula]
        formulaqf = self.qelim.eliminate_quantifiers(formula)
#         formulaqf = self.qelim.eliminate_quantifiers(formula).simplify()
        res = self.convert(formulaqf)
        self._yices2pysmt[res] = formula
        self.cache_qf[formula] = res
#         print("q : %s" % term.serialize())
#         print("qf: %s" % res.serialize())
#         assert(0)
        return res

    def get_term(self, formula, qf):
        if qf:
            return self.quantifier_free(formula)
        else:
            return self.convert(formula)

    @catch_conversion_error
    def convert(self, formula):
        res = self.walk(formula)
        self._yices2pysmt[res] = formula
        return res

    def back(self, expr, model=None):
        """Convert a Yices expression back into a pySMT expression.
        """
        if expr in self._yices2pysmt:
            return self._yices2pysmt[expr]
        raise NotImplementedError

    def _check_term_result(self, res):
        if res == -1:
            err = yicespy.yices_error_string()
            raise InternalSolverError("Yices returned an error: " + err)

    def walk_and(self, formula, args, **kwargs):
        res = yicespy.yices_and(len(args), yicespy.make_term_array(args))
        self._check_term_result(res)
        return res

    def walk_or(self, formula, args, **kwargs):
        res = yicespy.yices_or(len(args), yicespy.make_term_array(args))
        self._check_term_result(res)
        return res

    def walk_not(self, formula, args, **kwargs):
        res = yicespy.yices_not(args[0])
        self._check_term_result(res)
        return res

    def walk_symbol(self, formula, **kwargs):
        symbol_type = formula.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = yicespy.yices_new_uninterpreted_term(var_type)
        yicespy.yices_set_term_name(term, formula.symbol_name())
        self._check_term_result(term)
        return term

    def _bound_symbol(self, var):
        symbol_type = var.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = yicespy.yices_new_variable(var_type)
        yicespy.yices_set_term_name(term, var.symbol_name())
        return term

    def walk_iff(self, formula, args, **kwargs):
        res = yicespy.yices_iff(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_implies(self, formula, args, **kwargs):
        res = yicespy.yices_implies(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_le(self, formula, args, **kwargs):
        res = yicespy.yices_arith_leq_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_lt(self, formula, args, **kwargs):
        res = yicespy.yices_arith_lt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_ite(self, formula, args, **kwargs):
        i, t, e = args
        res = yicespy.yices_ite(i, t, e)
        self._check_term_result(res)
        return res

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        res = yicespy.yices_parse_rational(rep)
        self._check_term_result(res)
        return res

    def walk_int_constant(self, formula, **kwargs):
        assert is_pysmt_integer(formula.constant_value())
        rep = str(formula.constant_value())
        res = yicespy.yices_parse_rational(rep)
        self._check_term_result(res)
        return res

    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return yicespy.yices_true()
        else:
            return yicespy.yices_false()

    def walk_exists(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        res = yicespy.yices_exists(len(var_list), yicespy.make_term_array(var_list), bound_formula)
        self._check_term_result(res)
        return res

    def walk_forall(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        res = yicespy.yices_forall(len(var_list), yicespy.make_term_array(var_list), bound_formula)
        self._check_term_result(res)
        return res

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        new_vars = [self._bound_symbol(x) for x in variables]
        old_vars = [self.walk_symbol(x) for x in variables]
        new_formula = yicespy.yices_subst_term(len(variables), yicespy.make_term_array(new_vars),
                                                yicespy.make_term_array(old_vars), formula)
        return (new_formula, new_vars)


    def walk_plus(self, formula, args, **kwargs):
        res = yicespy.yices_sum(len(args), yicespy.make_term_array(args))
        self._check_term_result(res)
        return res

    def walk_minus(self, formula, args, **kwargs):
        res = yicespy.yices_sub(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_equals(self, formula, args, **kwargs):
        tp = self._get_type(formula.arg(0))
        res = None
        if tp.is_bv_type():
            res = yicespy.yices_bveq_atom(args[0], args[1])
        elif tp.is_int_type() or tp.is_real_type():
            res = yicespy.yices_arith_eq_atom(args[0], args[1])
        else:
            assert tp.is_custom_type() or tp.is_enum_type()
            res = yicespy.yices_eq(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_times(self, formula, args, **kwargs):
        res = args[0]
        for x in args[1:]:
            res = yicespy.yices_mul(res, x)
            self._check_term_result(res)
        return res

    def walk_toreal(self, formula, args, **kwargs):
        return args[0]

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        if name not in self.symbol_to_decl:
            self.declare_variable(name)
        decl = self.symbol_to_decl[name]
        res = yicespy.yices_application(decl, len(args), yicespy.make_term_array(args))
        self._check_term_result(res)
        return res


    def walk_bv_constant(self, formula, **kwargs):
        width = formula.bv_width()
        res = None
        value = formula.constant_value()
        if value <= ((2**63) - 1):
            # we can use the numerical representation
            # Note: yicespy uses *signed* longs in the API, so the maximal
            # representable number is 2^63 - 1
            res = yicespy.yices_bvconst_uint64(width, value)
        else:
            # we must resort to strings to communicate the result to yices
            res = yicespy.yices_parse_bvbin(formula.bv_bin_str())
        self._check_term_result(res)
        return res

    def walk_enum_constant(self, formula, **kwargs):
        sname = str(formula.constant_value())
        tp = formula.constant_type()
        sort_ast = self._type_to_yices(tp)
        assert(sname in self._yicesEnumConsts)
        res = self._yicesEnumConsts[sname]
        return res

    def walk_bv_ult(self, formula, args, **kwargs):
        res = yicespy.yices_bvlt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_ule(self, formula, args, **kwargs):
        res = yicespy.yices_bvle_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_concat(self, formula, args, **kwargs):
        res = yicespy.yices_bvconcat2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_extract(self, formula, args, **kwargs):
        res = yicespy.yices_bvextract(args[0],
                                       formula.bv_extract_start(),
                                       formula.bv_extract_end())
        self._check_term_result(res)
        return res

    def walk_bv_or(self, formula, args, **kwargs):
        res = yicespy.yices_bvor2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_not(self, formula, args, **kwargs):
        res = yicespy.yices_bvnot(args[0])
        self._check_term_result(res)
        return res

    def walk_bv_and(self, formula, args, **kwargs):
        res = yicespy.yices_bvand2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_xor(self, formula, args, **kwargs):
        res = yicespy.yices_bvxor2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_add(self, formula, args, **kwargs):
        res = yicespy.yices_bvadd(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_sub(self, formula, args, **kwargs):
        res = yicespy.yices_bvsub(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_neg(self, formula, args, **kwargs):
        res = yicespy.yices_bvneg(args[0])
        self._check_term_result(res)
        return res

    def walk_bv_mul(self, formula, args, **kwargs):
        res = yicespy.yices_bvmul(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_udiv(self, formula, args, **kwargs):
        res = yicespy.yices_bvdiv(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_urem(self, formula, args, **kwargs):
        res = yicespy.yices_bvrem(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_lshl(self, formula, args, **kwargs):
        res = yicespy.yices_bvshl(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_lshr(self, formula, args, **kwargs):
        res = yicespy.yices_bvlshr(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_rol(self, formula, args, **kwargs):
        res = yicespy.yices_rotate_left(args[0], formula.bv_rotation_step())
        self._check_term_result(res)
        return res

    def walk_bv_ror(self, formula, args, **kwargs):
        res = yicespy.yices_rotate_right(args[0], formula.bv_rotation_step())
        self._check_term_result(res)
        return res

    def walk_bv_zext(self, formula, args, **kwargs):
        res = yicespy.yices_zero_extend(args[0], formula.bv_extend_step())
        self._check_term_result(res)
        return res

    def walk_bv_sext (self, formula, args, **kwargs):
        res = yicespy.yices_sign_extend(args[0], formula.bv_extend_step())
        self._check_term_result(res)
        return res

    def walk_bv_slt(self, formula, args, **kwargs):
        res = yicespy.yices_bvslt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_sle (self, formula, args, **kwargs):
        res = yicespy.yices_bvsle_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_comp (self, formula, args, **kwargs):
        a,b = args
        eq = yicespy.yices_bveq_atom(a, b)
        self._check_term_result(eq)
        one = yicespy.yices_bvconst_int32(1, 1)
        zero = yicespy.yices_bvconst_int32(1, 0)
        res = yicespy.yices_ite(eq, one, zero)
        self._check_term_result(res)
        return res

    def walk_bv_sdiv (self, formula, args, **kwargs):
        res = yicespy.yices_bvsdiv(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_srem (self, formula, args, **kwargs):
        res = yicespy.yices_bvsrem(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_ashr (self, formula, args, **kwargs):
        res = yicespy.yices_bvashr(args[0], args[1])
        self._check_term_result(res)
        return res

    def yicesSort(self, name):
        """Return the yices Sort for the given name."""
        name = str(name)
        try:
            return self._yicesSort[name]
        except KeyError:
            sort = yicespy.yices_new_uninterpreted_type()
            self._yicesSort[name] = sort
        return sort

    def yicesEnumSort(self, name, value):
        """Return the yices EnumSort for the given name."""
        key = str(name)
        try:
            return self._yicesEnumSort[key][0]
        except KeyError:
            sort = yicespy.yices_new_scalar_type(len(value))
            sortvalues = []
            for i in range(len(value)):
                lhs = str(value[i])
                rhs = yicespy.yices_constant(sort, i)
                yicespy.yices_set_term_name(rhs, lhs)
                sortvalues.append(rhs)
                self._yicesEnumConsts[lhs] = rhs
            self._yicesEnumSort[key] = (sort, sortvalues)
        return sort

    def _type_to_yices(self, tp):
        if tp.is_bool_type():
            return yicespy.yices_bool_type()
        elif tp.is_real_type():
            return yicespy.yices_real_type()
        elif tp.is_int_type():
            return yicespy.yices_int_type()
        elif tp.is_function_type():
            stps = [self._type_to_yices(x) for x in tp.param_types]
            rtp = self._type_to_yices(tp.return_type)
            #arr = (yicespy.type_t * len(stps))(*stps)
            return yicespy.yices_function_type(len(stps),
                                              yicespy.make_type_array(stps),
                                              rtp)
        elif tp.is_bv_type():
            return yicespy.yices_bv_type(tp.width)
        elif tp.is_enum_type():
            return self.yicesEnumSort(tp.name, tp.domain)
        elif tp.is_custom_type():
            return self.yicesSort(str(tp))
        else:
            raise NotImplementedError(tp)

    def declare_variable(self, var):
        if not var.is_symbol():
            raise PysmtTypeError("Trying to declare as a variable something "
                                 "that is not a symbol: %s" % var)
        if var.symbol_name() not in self.symbol_to_decl:
            tp = self._type_to_yices(var.symbol_type())
            decl = yicespy.yices_new_uninterpreted_term(tp)
            yicespy.yices_set_term_name(decl, var.symbol_name())
            self.symbol_to_decl[var] = decl
            self.decl_to_symbol[decl] = var
