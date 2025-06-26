
class Ontology:
    """
    Base class for ontology representation.
    This class is intended to be extended by specific ontology implementations.
    It provides a common interface and basic functionality for handling ontologies.
    """

    def __init__(self):
        """
        Initializes a new instance of the Ontology class.
        This constructor is intended to be called by subclasses to set up the ontology.
        """
        # Initialize any necessary attributes or structures here
        pass

    def add_axiom(self, axiom):
        """
        Adds an axiom to the ontology.
        
        Args:
            axiom: The axiom to be added to the ontology.
        """
        raise NotImplementedError("This method should be implemented by subclasses.")
    
    
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