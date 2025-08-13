from opal.logic.base.base_literal import Literal
from z3 import Function, StringVal, BoolSort, RealSort, Not, DeclareSort, RealVal, Const
import typing
from opal.logic.z3.z3_handler import REFERENCE_TAXONOMY_ENV


class Z3Literal(Literal):
    """A concrete subclass of Literal that uses Z3 expressions."""
    
    def __init__(self, predicate: str, terms: typing.Iterable = None, positive: bool = True, env: dict = None):
        super().__init__(predicate, terms, positive)
        self._env = env if env is not None else {}
        self._z3_expr = self._build_z3_expr(self._env)

    def _build_z3_expr(self, env=None):
        """Builds the Z3 expression for this literal."""
        
        # Retrieve the signature and individual registers from the passed environment/context
        ctx = env['ctx']
        sig_ctx = env['functions']
        ind_ctx = env['constants']
        ind_type = env['sorts']['Ind']

        # check if the predicate is registered in the signature
        if self.predicate in sig_ctx:
            func = sig_ctx[self.predicate]
        else:
            # If not registered, create a new function
            func = Function(self.predicate, *([ind_type] * len(self.terms)), BoolSort(ctx))
            sig_ctx[self.predicate] = func
        
         # Get expected argument sorts from the function signature
        arity = func.arity()
        domain_sorts = [func.domain(i) for i in range(arity)]
        return_sort = func.range()
        
        # check if the return sort is BoolSort (meaning it's a predicate)
        is_predicate = return_sort == BoolSort(ctx)
        expected_term_count = arity + (0 if is_predicate else 1)  # +1 if it's a predicate, otherwise just arity
        

        if expected_term_count != len(self.terms):
            raise ValueError(f"Arity mismatch: predicate '{self.predicate}' expects {expected_term_count} terms, got {len(self.terms)}.")

        z3_args = []
        for term, expected_sort in zip(self.terms, domain_sorts):
            if expected_sort == ind_type:
                # Use a registered constant for individuals
                if term not in ind_ctx:
                    ind_ctx[term] = Const(term, ind_type)
                z3_args.append(ind_ctx[term])
            elif expected_sort == RealSort(ctx): 
                # Convert term to real value (expecting numeric)
                z3_args.append(RealVal(term, ctx))
            else:
                raise TypeError(f"Unsupported sort {expected_sort} for term '{term}'")
                
        # Create the expression based on whether it's a predicate or not
        if is_predicate:
            expr = func(*z3_args)
        else:
            target_terms = z3_args
            target_val = self.terms[-1]
            # If target_val is numeric, make sure it's in ctx too
            if expected_sort == RealSort(ctx):
                target_val = RealVal(target_val, ctx)
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