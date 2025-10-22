from opal.logic.base.base_ontology import Ontology
from opal.logic.z3.z3_literal import Z3Literal
from opal.logic.z3.z3_handler import parse_smt2_declarations, REFERENCE_TAXONOMY_ENV
from z3 import Function, BoolSort, RealSort, Not, DeclareSort, RealVal, Const, ForAll, Exists, And, Or, Implies
from z3 import parse_smt2_string, Z3Exception
import re
import sexpdata

class Z3Ontology(Ontology):
    """
    A concrete subclass of Ontology that uses Z3 for logical reasoning.
    
    This class is intended to be used with Z3 expressions and provides methods
    for managing axioms, individuals, and the signature of the ontology.
    """

    def __init__(self, name=None):
        """
        Initializes a new instance of the Z3Ontology class.
        """
        super().__init__(name=name)
        # initialize the environment according to the reference taxonomy
        self._env = REFERENCE_TAXONOMY_ENV
        self._axioms = []
        self._literals = []
        

    @classmethod
    def from_smt2(cls, ontology_str, mapping=None, name=None):
        """
        Loads the ontology from a SMT-LIB representation.

        Args:
            ontology_str (str): The SMT-LIB text representation of the ontology, or a path to the SMT-LIB file.
            
            mapping (str): The SMT-LIB text representation of the mapping (from the language of the reference taxonomy into the language of the ontology),
            or a path to the SMT-LIB file.

        Returns:
            self: The current instance of the ontology.
        """
        ontology = cls(name=name)
        ontology.load_from_smt2(ontology_str, mapping=mapping, name=name)
        return ontology


    def load_from_smt2(self, ontology_str, mapping=None, name=None):

        """
        Loads axioms, declarations, and literals from an SMT-LIB representation into the existing ontology.
        """
        # Check if the input is a file path or a string
        if ontology_str.endswith('.smt2'):
            with open(ontology_str, 'r') as f:
                ontology_str = f.read()
                
        if mapping and mapping.endswith('.smt2'):
            with open(mapping, 'r') as f:
                mapping = f.read()
                
        # Parse the SMT-LIB string to extract all named assertions
        ont_axioms, ont_ground, ont_str_other = self._load_assertions_from_smtlib(ontology_str)
        if mapping:
          map_axioms, map_ground, map_str_other = self._load_assertions_from_smtlib(mapping)
        else:
          map_axioms, map_ground, map_str_other = [], [], ""
        
        # Parse the remaining SMT-LIB string to extract additional non-assertion statements (declarations, signature, etc.)
        remaining_str = ont_str_other + map_str_other
        
        # update the extracted environment to the ontology
        env = parse_smt2_declarations(remaining_str, env = self._env)
        self._env = env
        
        # Add the parsed assertions to the ontology
        self._add_axioms(ont_axioms, prefix=f"{name}_ont")
        self._add_literals(ont_ground, prefix=f"{name}_ont")

        # Add the mapping assertions to the ontology
        self._add_axioms(map_axioms, prefix=f"{name}_map")
        self._add_literals(map_ground, prefix=f"{name}_map")

    @staticmethod
    def load_new_smt2_ontology(imported_ontology, new_ontology_str, mapping=None, name=None):
      """
      Loads additional smt2 ontology and mapping 'on top of' the existing Z3Ontology, effectively importing the existing ontology as a dependency for the new one.

      Args:
          ontology_str (str): The SMT-LIB text representation of the new ontology, or a path to the SMT-LIB file.
          
          mapping (str): The SMT-LIB text representation of the new mapping (from the language of the reference taxonomy into the language of the ontology),

          name (str): The name of the new ontology.

      Returns:
          Z3Ontology: A new instance of Z3Ontology with the loaded ontology and mapping ('on top of' the existing Z3Ontology).
      """
      # get axioms, literals, and env from the imported ontology
      imported_axioms = imported_ontology.axioms
      imported_literals = imported_ontology.literals
      imported_env = imported_ontology._env
      
      # create a new ontology and load the new ontology and mapping into it
      new_ontology = Z3Ontology(name=name)
      for axiom in imported_axioms:
          new_ontology.add_axiom(axiom)
      for literal in imported_literals:
          new_ontology.add_literal(literal)
      new_ontology._env = imported_env
      
      # load the new ontology and mappings
      new_ontology.load_from_smt2(new_ontology_str, mapping=mapping, name=new_ontology.name)
      
      return new_ontology

    @staticmethod
    def _load_assertions_from_smtlib(smtlib_str):
        named_assertions, remaining_str = Z3Ontology.extract_named_assertions(smtlib_str)

        axiom_assertions = [a for a in named_assertions if 'forall' in a['formula'] or 'exists' in a['formula']]
        ground_assertions = [a for a in named_assertions if a not in axiom_assertions]

        return axiom_assertions, ground_assertions, remaining_str

    def _add_axioms(self, assertions, prefix):
        for i, assertion in enumerate(assertions):
            name = f"{prefix}_t_{i}_{assertion['name']}"
            print(f"Adding axiom: {name}")
            self.add_axiom({
                'name': name,
                'description': assertion['description'],
                'expr': assertion['formula']
            })

    @staticmethod
    def parse_ground_assertion(smtlib_str):
      expr = sexpdata.loads(smtlib_str)

      # expr looks like: ['assert', ['!', ['transition', 'T_start'], ':named', 'transition_start', ':description', '...']]
      if expr[0].value() != "assert":
          raise ValueError("Not an assertion")

      inner = expr[1]  # match on the (! ...)
      if inner[0].value() != "!":
          raise ValueError("Assertion not annotated")

      formula = inner[1]   # inner part of ground formula (transition T_start)
      
      positive = True

      # Check if the assertion is negated
      if isinstance(formula, list) and formula[0].value() == "not":
          positive = False
          formula = formula[1]  # unwrap inner formula
        
      predicate = formula[0].value()
      terms = [t.value() if isinstance(t, sexpdata.Symbol) else t for t in formula[1:]]

      # get annotations
      name = None
      description = None
      for i in range(2, len(inner), 2):
          key = inner[i].value()
          val = inner[i+1]
          if key == ":named":
              name = val.value() if isinstance(val, sexpdata.Symbol) else val
          elif key == ":description":
              description = val

      return {
          "predicate": predicate,
          "terms": terms,
          "name": name,
          "description": description,
          "positive": positive
      }

    def _add_literals(self, assertions, prefix):
      
        for i, assertion in enumerate(assertions):
            parsed_assertion = self.parse_ground_assertion(assertion['formula'])
            name = parsed_assertion['name']
            name = f"{prefix}_a_{i}_{name}"
            terms = parsed_assertion['terms']
            predicate = parsed_assertion['predicate']
            positive = parsed_assertion['positive']

            self.add_literal({name : Z3Literal(predicate, terms, positive, env=self._env)})

    @staticmethod
    def extract_named_assertions(smtlib_str):
      parsed = sexpdata.loads(f"({smtlib_str})")  # wrap in () to parse multiple top-level forms

      assertions = []
      remaining = []

      for expr in parsed:
          if isinstance(expr, list) and expr and expr[0].value() == "assert":
              inner = expr[1]  # (! ... )
              if isinstance(inner, list) and inner[0].value() == "!":
                  formula = inner[1]
                  attrs = inner[2:]

                  name = None
                  description = None
                  for i in range(0, len(attrs), 2):
                      key = attrs[i].value()
                      val = attrs[i+1]
                      if key == ":named":
                          name = val.value()
                      elif key == ":description":
                          description = val

                  assertions.append({
                      "name": name,
                      "description": description,
                      "formula": sexpdata.dumps(expr)  # dump back to string
                  })
              else:
                  remaining.append(sexpdata.dumps(expr))
          else:
              remaining.append(sexpdata.dumps(expr))

      return assertions, "\n".join(remaining)
    
    def _is_temporal_variable(self, var_name):
        """
        Determines if a variable name represents a temporal variable.
        
        Args:
            var_name (str): The variable name to check
            
        Returns:
            bool: True if the variable represents time, False otherwise
        """
        # Check for common temporal variable patterns
        temporal_patterns = [
            r'^t$',           # just 't'
            r'^t\d+$',        # t1, t2, t3, etc.
        ]
        
        for pattern in temporal_patterns:
            if re.match(pattern, var_name, re.IGNORECASE):
                return True
        
        return False
        
    def add_axiom(self, axiom):
        """
        Adds an axiom to the ontology.
        Args:
            axiom (dictionary): The axiom to add
        """
        # make sure axiom is not duplicated
        axiom_expr = axiom['expr']
        current_axiom_exprs = [a['expr'] for a in self._axioms]
        if axiom_expr not in current_axiom_exprs:
          self._axioms.append(axiom)
          

    def add_literal(self, literal):
        """
        Adds a literal to the ontology.
        Args:
            literal (dictionary): The literal to add
        """
        # make sure literal is not duplicated
        if literal not in self._literals:
          self._literals.append(literal)
    
    @property
    def axioms(self):
        """
        Returns the axioms of the ontology.
        
        Returns:
            An iterable containing the axioms of the ontology.
        """
        return self._axioms

    @property
    def literals(self):
        """
        Returns the literals of the ontology.

        Returns:
            An iterable containing the literals of the ontology.
        """
        return self._literals
      
    @property
    def env(self):
        """
        Returns the environment of the ontology.

        Returns:
            The environment of the ontology.
        """
        return self._env

REF_ONTOLOGY_Z3 = Z3Ontology.from_smt2('../../opal/logic/z3/ontologies/ref/reference_taxonomy.smt2', name="Reference Taxonomy")
PSL_CORE_Z3 = Z3Ontology.load_new_smt2_ontology(REF_ONTOLOGY_Z3, '../../opal/logic/z3/ontologies/PSL/PSL_core.smt2', mapping='../../opal/logic/z3/ontologies/PSL/PSL_core_mapping.smt2', name="PSL Core Ontology")
PSL_OCCTREE_Z3 = Z3Ontology.load_new_smt2_ontology(PSL_CORE_Z3, '../../opal/logic/z3/ontologies/PSL/PSL_occtree.smt2', name="PSL Occtree Ontology")
PSL_SUBACTIVITY_Z3 = Z3Ontology.load_new_smt2_ontology(PSL_CORE_Z3, '../../opal/logic/z3/ontologies/PSL/PSL_subactivity.smt2', name="PSL Subactivity Ontology")
PSL_subactivity_occtree = Z3Ontology.load_new_smt2_ontology(PSL_OCCTREE_Z3, '../../opal/logic/z3/ontologies/PSL/PSL_subactivity.smt2', name="PSL Subactivity Ontology with Occtree")
#PSL_ATOMIC_Z3 = Z3Ontology.load_new_smt2_ontology(PSL_subactivity_occtree, '../../opal/logic/z3/ontologies/PSL/PSL_atomic.smt2', name="PSL Atomic Ontology")
PSL_COMPLEX_Z3 = Z3Ontology.load_new_smt2_ontology(PSL_subactivity_occtree, '../../opal/logic/z3/ontologies/PSL/PSL_complex.smt2', name="PSL Complex Ontology")