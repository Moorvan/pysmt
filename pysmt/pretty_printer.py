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
from six.moves import cStringIO

import pysmt.operators as op
from pysmt.walkers import TreeWalker
from pysmt.walkers.generic import handles
from pysmt.utils import quote
from pysmt.constants import is_pysmt_fraction, is_pysmt_integer

from pysmt.printers import HRPrinter
from pysmt.shortcuts import ForAll, Exists, Not, And, Or, Implies

class PrettyPrinter(HRPrinter):
    """Better serialization allowing special printing of subformula.

    The formula is serialized according to the format defined in the
    HRPrinter. However, everytime a formula that is present in
    'subs' is found, this is replaced.

    E.g., subs  = {And(a,b): "ab"}

    Everytime that the subformula And(a,b) is found, "ab" will be
    printed instead of "a & b". This makes it possible to rename big
    subformulae, and provide better human-readable representation.
    """

    def __init__(self, stream, subs=None):
        HRPrinter.__init__(self, stream)
        if subs is None:
            self.subs = {}
        else:
            self.subs = subs

    def printer(self, f, threshold=None):
        self.walk(f, threshold=threshold)

    @handles(set(op.ALL_TYPES) - set([op.NOT, op.OR, op.BOOL_CONSTANT]))
    def smart_walk_default(self, formula):
        if formula in self.subs:
            # Smarties contains a string.
            # In the future, we could allow for arbitrary function calls
            self.write(self.subs[formula])
        else:
            return HRPrinter.super(self, formula)

    @handles(set([op.NOT]))
    def smart_walk_not(self, formula):
        if formula in self.subs:
            # Smarties contains a string.
            # In the future, we could allow for arbitrary function calls
            self.write(self.subs[formula])
        else:
            arg = formula.arg(0)
            if arg.is_iff():
                arg = self.get_iff(arg)
                
            if arg.is_exists():
                argn = ForAll(arg.quantifier_vars(), Not(arg.arg(0)))
                return self.walk(argn)
            elif arg.is_forall():
                argn = Exists(arg.quantifier_vars(), Not(arg.arg(0)))
                return self.walk(argn)
            elif arg.is_and():
                args = [Not(a) for a in arg.args()]
                argn = Or(args)
                return self.walk(argn)
            elif arg.is_or():
                args = [Not(a) for a in arg.args()]
                argn = And(args)
                return self.walk(argn)
            elif arg.is_not():
                return self.walk(arg.arg(0))
            else:
                if (arg.is_not()):
                    assert(0)
                return HRPrinter.super(self, formula)
    
    @handles(set([op.OR]))
    def smart_walk_or(self, formula):
        if formula in self.subs:
            # Smarties contains a string.
            # In the future, we could allow for arbitrary function calls
            self.write(self.subs[formula])
        else:
            args = formula.args()
            arg_ant = []
            arg_con = []
            for a in args:
                if a.is_not():
                    arg_ant.append(a.arg(0))
                else:
                    arg_con.append(a)
            if len(arg_ant) != 0 and len(arg_con) != 0:
                argn = Implies(And(arg_ant), Or(arg_con))
                return self.walk(argn)
            elif len(arg_ant) != 0:
                for i in range(1, len(arg_ant)):
                    arg_con.append(Not(arg_ant[i]))
                argn = Implies(arg_ant[0], Or(arg_con))
                return self.walk(argn)
            else:
                return HRPrinter.super(self, formula)
    
    @handles(set([op.BOOL_CONSTANT]))
    def smart_walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("true")
        else:
            self.write("false")

# EOC SmartPrinter

def pretty_serialize(formula, subs=None, threshold=None):
    """Creates and calls a SmartPrinter to perform smart serialization."""
    buf = cStringIO()
    p = PrettyPrinter(buf, subs=subs)
    p.printer(formula, threshold=threshold)
    res = buf.getvalue()
    buf.close()
    return res
