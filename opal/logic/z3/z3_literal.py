from opal.logic.base.base_literal import Literal
from z3 import Function, StringVal, BoolSort, RealSort, Not, DeclareSort, RealVal, Const
import typing

# define type for individuals
Ind = DeclareSort('Ind')

# define a register for functions, with temporal functions predefined
SIGNATURE_REGISTER = {'hasRecordedTime' : Function('hasRecordedTime', Ind, RealSort()),
    'begin_of' : Function('begin_of', Ind, RealSort()),
    'end_of' : Function('end_of', Ind, RealSort()),}

IND_REGISTER = {}
    

class Z3Literal(Literal):
    """A concrete subclass of Literal that uses Z3 expressions."""
    
    def __init__(self, predicate: str, terms: typing.Iterable = None, positive: bool = True):
        super().__init__(predicate, terms, positive)
        self._z3_expr = self._build_z3_expr()
    
    def _build_z3_expr(self):
        """Builds the Z3 expression for this literal."""
        # check if the predicate is registered in the signature
        if self.predicate in SIGNATURE_REGISTER:
            func = SIGNATURE_REGISTER[self.predicate]
        else:
            # If not registered, create a new function
            func = Function(self.predicate, *([Ind] * len(self.terms)), BoolSort())
            SIGNATURE_REGISTER[self.predicate] = func
        
         # Get expected argument sorts from the function signature
        arity = func.arity()
        domain_sorts = [func.domain(i) for i in range(arity)]
        return_sort = func.range()
        
        # check if the return sort is BoolSort (meaning it's a predicate)
        is_predicate = return_sort == BoolSort()
        expected_term_count = arity + (0 if is_predicate else 1)  # +1 if it's a predicate, otherwise just arity
        

        if expected_term_count != len(self.terms):
            raise ValueError(f"Arity mismatch: predicate '{self.predicate}' expects {expected_term_count} terms, got {len(self.terms)}.")

        z3_args = []
        for term, expected_sort in zip(self.terms, domain_sorts):
            if expected_sort == Ind:
                # Use a registered constant for individuals
                if term not in IND_REGISTER:
                    IND_REGISTER[term] = Const(term, Ind)
                z3_args.append(IND_REGISTER[term])
            elif expected_sort == RealSort(): 
                # Convert term to real value (expecting numeric)
                z3_args.append(RealVal(term))
            else:
                raise TypeError(f"Unsupported sort {sort} for term '{term}'")
                
        # Create the expression based on whether it's a predicate or not
        if is_predicate:
            expr = func(*z3_args)
        else:
            target_terms = z3_args
            target_val = self.terms[-1]
            expr = func(*target_terms) == target_val
        
        # If the literal is negative, negate the expression
        if not self.positive:
            expr = Not(expr)
        
        return expr
    
    @property
    def z3_expr(self):
        """Returns the Z3 expression corresponding to this literal."""
        return self._z3_expr
    
    def __str__(self) -> str:
        return str(self.z3_expr)