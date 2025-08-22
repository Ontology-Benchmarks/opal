from opal.logic.base.base_reasoner import Reasoner
from opal.logic.z3.z3_ontology import Z3Ontology
from opal.logic.z3.z3_literal import Z3Literal
from z3 import Solver, parse_smt2_string

class Z3Reasoner(Reasoner):
    """
    Reasoner implementation using Z3.
    """
    def __init__(self):
        super().__init__()
        self.assertions = []

    def load_ontology(self, ontology : Z3Ontology):
        """
        Load the ontology into the Z3 environment.
        
        Args:
            ontology (Z3Ontology object)
            """
            
        # firstly establish environment to get ctx, sorts, decls
            
        # check if ontology has axioms, then load them
        if hasattr(ontology, "axioms"):
            for axiom in ontology.axioms:
                self.assertions.append(axiom)

        # check if ontology has ground facts, then load them
        if hasattr(ontology, "literals"):
            for literal in ontology.literals:
                self.facts.append(literal)


    def load_facts(self, facts):
        for fact in facts:
            if isinstance(fact, Z3Literal):
                self.facts.append(fact)
            else:
                raise TypeError("Expected Z3Literal instances in facts.")

    def query(self, query):
        
        # initalize the solver and load assertions and facts
        

        # firstly do a check
        solver = self.check()

        # add the query to the solver
        solver.assert_and_track(query['expr'], query['name'])

        
        return solver


    def check(self):
        pass
        # check if there are any facts loaded, and use the existing ctx if so.
        if self.facts:
            ctx = self.facts[0].ctx

        # init the solver
        solver = Solver(ctx=ctx)
        solver.set(unsat_core=True)
        solver.set(completion=True)

        # add assertions
        for assertion in self.assertions:
            expr = parse_smt2_string(assertion['expr'], ctx=ctx)
            solver.assert_and_track(expr, assertion['name'])

        # add facts
        for fact in self.facts:
            name, expr = next(iter(fact.items()))
            solver.assert_and_track(expr, name)

        return solver