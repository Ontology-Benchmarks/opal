import pandas as pd
import numpy as np
import pm4py
import tempfile
from opal.data.event_data import EventData

class LogProcessor:
    def __init__(self, log_path:str, 
                 col_dict:dict = {'caseID': 'case:concept:name', 'activityID': 'concept:name', 'timestamp': 'time:timestamp', 'resourceID': 'org:resource', 'eventID' : None, 'transition': 'lifecycle:transition'}, 
                 process_name:str = 'P1',
                 batch_size:int = 0):
        self.log_path = log_path
        self.col_dict = col_dict
        self.process_name = process_name
        self.batch_size = batch_size
        
        
    def load_log(self, downsample_rate:float = 1.0) -> EventData:
        """
        Return a dataframe from a given XES log filepath or CSV 
        and creates a temporary csv file with additional columns needed for consistent processing.
        Optionally downsample data for large datasets (necessary for large logs to be used with first order logic reasoning at this stage)
        """
        log_path = self.log_path
        col_dict = self.col_dict
        batches = 0
        if any(log_path.lower().endswith(ext) for ext in ['.xes', '.xes.gz']): # if log is in XES format
            log = pm4py.read_xes(log_path)
            df = pm4py.convert_to_dataframe(log)
        elif log_path.lower().endswith('.csv'): # if log is in CSV format
            df = pd.read_csv(log_path)
        else: # if log is in an unsupported format
            return None

        # add a process instance column to the dataframe
        df['processID'] = self.process_name
        
        # if no unique identifier for events, create one
        if col_dict['eventID'] is None: 
            df['eventID'] = df.index
            
        # rename columns based on the provided column dictionary
        rename_dict = {v: k for k, v in col_dict.items() if v is not None}
        df.rename(columns=rename_dict, inplace=True)
        
        # create unique prefixes for IDs to disambiguate them
        df['eventID'] = df['eventID'].apply((lambda x: f'E_{str(x)}'))
        df['caseID'] = df['caseID'].apply((lambda x: f'C_{str(x)}'))
        df['activityID'] = df['activityID'].apply((lambda x: f'A_{str(x)}'))
        df['resourceID'] = df['resourceID'].apply((lambda x: f'R_{str(x)}'))
        # ensure timestamp is in datetime format
        df['timestamp'] = pd.to_datetime(df['timestamp'], errors='coerce')
        
        # ensure downsample_rate is between 0 and 1
        downsample_rate = max(0, min(1, downsample_rate))  
        # downsample data if necessary
        if downsample_rate < 1:
            # sample by caseIDs
            unique_cases = df['caseID'].unique()
            sampled_cases = np.random.choice(unique_cases, int(downsample_rate * len(unique_cases)), replace=False)
            df = df[df['caseID'].isin(sampled_cases)]
        
        # check if there is a defined batch size
        if self.batch_size > 0:
            # batching: batch the log by the number of cases defined through batch size
            # if batch size is larger than the number of cases, use all cases
            if self.batch_size >= len(df['caseID'].unique()):
                df['batch'] = 0
            else:
                df['batch'] = (df.groupby('caseID').ngroup() // self.batch_size) + 1
                batches = df['batch'].nunique()
                
        # save the dataframe to temporary CSV files - one for each batch if batching is enabled
        log_paths = []
        if batches > 0:
            for batch_num in range(1, batches + 1):
                batch_df = df[df['batch'] == batch_num].drop(columns=['batch'])
                temp_file = tempfile.NamedTemporaryFile(delete=False, suffix='.csv')
                batch_df.to_csv(temp_file.name, index=False)
                log_paths.append(temp_file.name)
        else:
            temp_file = tempfile.NamedTemporaryFile(delete=False, suffix='.csv')
            df.to_csv(temp_file.name, index=False)
            log_paths.append(temp_file.name)
            
        return EventData(data=df, metadata={'log_paths': log_paths, 'process_name': self.process_name, 'batches' : batches})
    


    def __repr__(self):
        return f"LogProcessor(log_path={self.log_path}, process_name={self.process_name})"