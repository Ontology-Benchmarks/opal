# Ontology-driven Process Analysis engine (OPAL)

OPAL is a library designed to enable ontology-driven process mining. Ontology-driven process mining is meant to formalize process knowledge applied throughout the process mining lifecycle to enable transparency and replicability. This is accomplished through *process meaning patterns*, first-order logic ontology patterns that correspond to common verification and inference steps in the process mining lifecycle. This repository contains an implementation of the process meaning pattern framework implemented in python and supporting exporting of process knowledge to various formats including OWL/RDF, First order logic via CLIF or Prover9 syntax, and prolog/datalog. 

OPAL is actively maintaned and developed by [Riley Moher](https://riley-momo.github.io/) of the semantic technologies laboratory (stl) at the University of Toronto.

Example Usage
------------

The examples repository contains notebooks and example data that illustrate usage scenarios of the library. As the library is further expanded and developed, more examples will be added.


Installation
------------

OPAL can be installed on any python version >= 3.9.X by simply using pip to install this library from the github repository:

```
pip install git+https://github.com/Ontology-Benchmarks/opal
```

Release Notes
------------

Release notes are tracked in the CHANGELOG.md file of this repository.


Contact
------------
Please feel free to reach out with comments, questions, and feedback to riley.moher@mail.utoronto.ca
