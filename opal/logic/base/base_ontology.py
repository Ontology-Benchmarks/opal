
class Ontology:
    """
    Base class for ontology representation.
    This class is intended to be extended by specific ontology implementations.
    It provides a common interface and basic functionality for handling ontologies.
    """

    def __init__(self, name=None):
        """
        Initializes a new instance of the Ontology class.
        This constructor is intended to be called by subclasses to set up the ontology.
        """
        # Initialize axioms, individuals, and signature as empty lists or dictionaries
        self._axioms = []
        self._individuals = {}
        self._signature = {}
        self._imports = []
        self.name = name or f"Ontology_{id(self)}"
    
    def from_txt(self, text):
        """
        Loads the ontology from a text representation.
        
        Args:
            text (str): The text representation of the ontology.
        
        Returns:
            self: The current instance of the ontology.
        """
        raise NotImplementedError("This method should be implemented by subclasses.")

    def add_axiom(self, axiom):
        """
        Adds an axiom to the ontology.
        
        Args:
            axiom: The axiom to be added to the ontology.
        """
        raise NotImplementedError("This method should be implemented by subclasses.")
    
    def import_ontology(self, other_ontology):
        """
        Imports another ontology into this ontology.
        
        Args:
            ontology (Ontology): The ontology to be imported.
        """
        if other_ontology not in self._imports:
            self._imports.append(other_ontology)
        # Leave additional merging logic to subclasses if needed.

    
    
    #  PROPERTIES  #####################################################################################################
    
    @property
    def axioms(self):
        """
        Returns the axioms of the ontology.
        
        Returns:
            An iterable containing the axioms of the ontology.
        """
        raise NotImplementedError("This method should be implemented by subclasses.")
    
    @property
    def individuals(self):
        """
        Returns the individuals of the ontology.
        
        Returns:
            An iterable containing the individuals of the ontology.
        """
        raise NotImplementedError("This method should be implemented by subclasses.")
    
    @property
    def signature(self):
        """
        Returns the signature of the ontology.
        
        Returns:
            An iterable containing the signature of the ontology.
        """
        raise NotImplementedError("This method should be implemented by subclasses.")