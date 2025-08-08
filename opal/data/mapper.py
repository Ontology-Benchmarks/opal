from opal.data.event_data import EventData
from opal.logic.z3.z3_literal import Z3Literal
from opal.logic.z3.z3_handler import REFERENCE_TAXONOMY_ENV

import pandas as pd
import numpy as np

import yatter
from ruamel.yaml import YAML
import kglab
import rdflib

import re
from string import Template
import tempfile
from itertools import combinations
import dateutil.parser
from tqdm import tqdm

# Define the mapping template for YARRML, with optional columns for resources and transitions
def generate_yarrml_mapping(include_resources: bool, include_transitions: bool):
    resource_block = ""
    event_resource_line = ""
    transition_block = ""
    event_transition_line = ""
    
    if include_resources:
        resource_block = """
            resources:
                sources:
                - ['$log_path~$log_format']
                s: ex:$$($resourceID)
                po:
                - [a, on:Resource]"""
        
        event_resource_line = "- [on:hasResource, ex:$$($resourceID)]"
    if include_transitions:
        transition_block = """
            transitions:
                sources:
                - ['$log_path~$log_format']
                s: ex:$$($transition)
                po:
                - [a, on:Transition]"""
        
        event_transition_line = "- [on:hasTransition, ex:$$($transition)]"
        

    template_str = f"""
        prefixes:
            ex: $ex_prefix
            on: $on_prefix

        mappings:
            events:
                sources:
                - ['$log_path~$log_format']
                s: ex:$$($eventID)
                po:
                - [a, on:Event]
                - [on:hasCase, ex:$$($caseID)]
                - [on:hasActivity, ex:$$($activityID)]
                {event_resource_line}
                {event_transition_line}
                - [on:hasRecordedTime, $$($timestamp), xsd:dateTimeStamp]
                
            {resource_block}
            
            {transition_block}

            cases:
                sources:
                - ['$log_path~$log_format']
                s: ex:$$($caseID)
                po:
                - [a, on:Case]
                - [on:hasProcess, ex:$$(processID)]

            activities:
                sources:
                - ['$log_path~$log_format']
                s: ex:$$($activityID)
                po:
                - [a, on:Activity]
    """

    return Template(template_str)


class LogMapper:
    def __init__(self, 
                 data: EventData, 
                 output_encoding : str, 
                 prefixes : dict = {'ex':'http://www.example.com/', 'on': 'https://stl.mie.utoronto.ca/ontologies/spm/'}):
        self.data = data
        self.output_encoding = output_encoding
        self.prefixes = prefixes
        self.mappings = self.build_mappings()
        
        
    def build_mapping(self, log_path: str):
        """
        Modifies YARRML mapping according to expected columns in the log
        """
        # check if the log contains resources and transitions (optional columns)
        include_resources = 'resourceID' in self.data.data.columns
        include_transitions = 'transition' in self.data.data.columns
        
        mapping_template = generate_yarrml_mapping(include_resources, include_transitions)
        
        # create a mapping string from the template
        mapping_string = mapping_template.substitute(
            log_path=log_path,
            log_format='csv',
            ex_prefix=self.prefixes['ex'],
            on_prefix=self.prefixes['on'],
            eventID='eventID',
            caseID='caseID',
            activityID='activityID',
            resourceID='resourceID',
            timestamp='timestamp',
            transition='transition',
        )
        yaml = YAML(typ='safe', pure=True)
        yarrrml_content = yaml.load(mapping_string)
        rml_mapping = yatter.translate(yarrrml_content)
        # write rml mapping to temporary file
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.ttl') as f:
            f.write(rml_mapping)
            rml_path = f.name
        
        return rml_mapping, rml_path
    
    
    def build_mappings(self):
        """
        Builds the mappings for the log data
        """
        mappings = np.empty(len(self.data.metadata['log_paths']), dtype=object)
        print("Building mappings for logs...")
        for i in tqdm(range(len(self.data.metadata['log_paths']))):
            current_log_path = self.data.metadata['log_paths'][i]
            mapping = self.build_mapping(current_log_path)
            mappings[i] = mapping
        print("Mappings built.")
        
        return mappings
    
    def generate_knowledge_graphs(self):
        """
        Generates knowledge graphs for each mapping
        """
        
        kgs = []
        for _, mapping_path in self.mappings:
            kg = self.generate_knowledge_graph(mapping_path)
            kgs.append(kg)
            print(f"Knowledge graph {len(kgs)}/{len(self.mappings)} generated.")
        self.kgs = kgs
        return kgs
    
    
    def generate_knowledge_graph(self, mapping_path):
        """
        Generates a knowledge graph from the log and mapping
        """
        # init knowledge graph
        print("Generating knowledge graph...")
        kg = kglab.KnowledgeGraph(name=mapping_path.replace('.rml', ''), namespaces=self.prefixes)
        process_name = self.data.metadata['process_name']
        # generate config
        config_string = f"""
        [{process_name}]
        mappings={mapping_path}
        """
        # write config to temporary file
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.ini') as f:
            f.write(config_string)
            kg_config_path = f.name
        # generate the knowledge graph from the config
        kg.materialize(kg_config_path)
        
        print("Knowledge graph generated.")
        
        return kg
    
    def save_ground_data(self, output_path: str):
        # if kg does not yet exist, first generate it
        if not hasattr(self, 'ground_data'):
            self.get_mapped_data()
        output_format = self.output_encoding.get_metadata()['format'].lower()
        # save to path if specified    
        output_file = output_path + f'{self.process_name}_ground_data.{output_format}'
        
        with open(output_file, 'w') as f:
            for literal in self.ground_data:
                f.write(f'{literal}\n')
           
        print("Ground data saved.")
        
        return None
    
    def get_mapped_data(self):
        
        encoding = self.output_encoding
        
        if encoding == 'RDF':
            ground_data = self.kg
            
        elif encoding == 'FOL':
            ground_data = self.generate_fol()
            
        elif encoding == 'datalog':
            ground_data = self.generate_datalog()
        
        elif encoding == 'z3':
            ground_data = self.generate_z3()
            
        
        return ground_data
    
    
    def generate_fol(self):
        """
        Generates a First Order Logic representation of the log
        """
        print("Generating First Order Logic representation...")
        
        if not hasattr(self, 'kg'):
            self.generate_knowledge_graph()
        
        # initialize an empty array for ground facts
        ground_facts = np.array([])    
        
        # helper functions definitions for converting RDF to FOL    
        def query_and_apply(query, func):
            df = self.kg.query_as_df(sparql=query)
            vals = df.apply(func, axis=1).values
            if vals.size > 0:
                ground_facts = np.concatenate((ground_facts, vals), axis=0)

        # define helper functions to strip URIs
        strip_ex_prefix  = lambda x: re.sub(r".*/|>$", '', x)
        strip_on_prefix = lambda x: re.sub(r".*:", '', x)
        # define helper functions for converting RDF literals to FOL
        unary_pred = lambda s,o : f'{strip_on_prefix(o)}({strip_ex_prefix(s)})'
        binary_pred = lambda s,p,o : f'{strip_on_prefix(p)}({strip_ex_prefix(s)}, {strip_ex_prefix(o)})'
        
        # helper function for converting timepoints from data property to FOL
        def convert_timepoints(kg):
            tp_query = "SELECT ?s ?t WHERE {?s ns1:hasRecordedTime ?t}"
            df = kg.query_as_df(sparql=tp_query)
            unique_timestamps = df['t'].unique()
            # create timestamp mapping
            timestamp_mapping = {timestamp: f'ts_{i}' for i, timestamp in enumerate(sorted(unique_timestamps))}
            # apply mapping
            df['new_t'] = df['t'].map(timestamp_mapping)
            # create ordering relations over timestamps
            unique_mapped_timestamps = sorted(df['new_t'].unique())
            timestamp_pairs = [(unique_mapped_timestamps[i], unique_mapped_timestamps[i+1]) for i in range(len(unique_mapped_timestamps) - 1)]
            before_relations = [f'before({t1},{t2})' for t1, t2 in timestamp_pairs]
            timestamp_preds = [f'timepoint({t})' for t in unique_mapped_timestamps]
            event_timings = df.apply(lambda x: 'hasRecordedTime({}, {})'.format(re.sub(r".*/|>$", '', x["s"]), x["new_t"]), axis=1).values
            # add to Abox
            ground_facts = np.concatenate((ground_facts, timestamp_preds, event_timings, before_relations), axis=0)
        
        
        # Convert simple unary rdf:type predicates
        type_query = "SELECT ?s ?o WHERE {?s a ?o}"
        type_f = lambda x: unary_pred(x['s'], x['o'])
        query_and_apply(type_query, type_f)
        
        # convert binary relations other than time and rdf:type
        relation_query = "SELECT ?s ?p ?o WHERE {?s ?p ?o . FILTER (?p != rdf:type && ?p != ns1:hasRecordedTime)}"
        relation_f = lambda x: binary_pred(x['s'], x['p'], x['o'])
        query_and_apply(relation_query, relation_f)
        
        # convert timepoints
        convert_timepoints(self.kg)
        
        return ground_facts
        
    
    def generate_datalog(self):
        
        # datalog facts are just a syntactic difference from FOL literals
        fol_facts = self.generate_FOL()
        
        # start with copy of FOL literals
        dl_facts = np.array([f'{str(x)}.' for x in fol_facts])
        # replace camel case with underscores
        dl_facts = np.array([re.sub(r'(?<!^)(?=[A-Z])(?=.*\()', '_', x) for x in dl_facts])
        # make sure predicates are lowercase
        dl_facts = np.array([x.lower() for x in dl_facts])
        # eliminate special characters
        dl_facts = np.array([re.sub(r'[<>\-%!#$^&*]', '', x) for x in dl_facts])
        
        return dl_facts

    def generate_z3(self):
        """
        Generates a Z3 representation of the log
        """
        # define helper function to strip URIs
        strip_uri = lambda x: re.sub(r".*/", '', x)
        
        # define a helper function to parse triples into Z3Literal objects
        def parse_triple(triple) -> Z3Literal:
            s, p, o = triple
            # parse subject with ex prefix
            s = strip_uri(str(s))
            
            # special case of type statements:
            if str(p) == 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type':
                predicate = strip_uri(str(o))
                s = strip_uri(str(s))
                terms = [s]
            else:
                predicate = strip_uri(str(p))
                if isinstance(o, rdflib.Literal) and o.datatype == rdflib.XSD.dateTimeStamp:
                    # convert datetime to timestamp
                    o = dateutil.parser.isoparse(str(o)).timestamp()
                else:
                    o = strip_uri(str(o))
                terms = [s,o]
                 
            return Z3Literal(predicate=predicate, terms=terms, env=REFERENCE_TAXONOMY_ENV)
        
        # define helper to transform one kg into an array of Z3Literal objects
        def kg_to_z3_literals(kg):
            # initialize an empty array for Z3 facts with length = number of triples in the graph
            z3_facts = np.empty(len(kg.rdf_graph()), dtype=Z3Literal)
            # get the RDF graph from the knowledge graph
            graph = kg.rdf_graph()

            # map the triples in the graph to Z3Literal objects
            for i,triple in enumerate(graph.triples((None, None, None))):
                # parse the triple to get predicate and terms
                z3_literal = parse_triple(triple)
                # add the Z3Literal to the array of Z3 facts
                z3_facts[i] = z3_literal
            return z3_facts
        
        # initialize an empty array for Z3 literals
        z3_facts_result = np.empty(0, dtype=Z3Literal)
        
        # first perform rdf mappings if necessary
        if not hasattr(self, 'kgs'):
            self.generate_knowledge_graphs()
        
        # iterate over all knowledge graphs and convert them to Z3 literals
        for i,kg in enumerate(self.kgs):
            z3_facts_result = np.concatenate((z3_facts_result, kg_to_z3_literals(kg)), axis=0)
            print(f"Z3 literal set generated ({i+1}/{len(self.kgs)})")
            
        return z3_facts_result

