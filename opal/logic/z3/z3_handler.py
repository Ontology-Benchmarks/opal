from opal.logic.base.base_literal import Literal
from z3 import Function, BoolSort, RealSort, Not, DeclareSort, RealVal, Const
import typing

# define type for individuals
Ind = DeclareSort('Ind')

# define a register for functions, with temporal functions predefined
SIGNATURE_REGISTER = {'hasRecordedTime' : Function('hasRecordedTime', Ind, RealSort()),
    'begin_of' : Function('begin_of', Ind, RealSort()),
    'end_of' : Function('end_of', Ind, RealSort()),}

IND_REGISTER = {}
    