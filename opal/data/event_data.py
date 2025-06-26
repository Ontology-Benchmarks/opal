import pandas as pd
import numpy as np
import pm4py
import tempfile


class EventData:
    def __init__(self, data: pd.DataFrame = None,
                 metadata: dict = None,):
        self.data = data if data is not None else pd.DataFrame()
        self.metadata = metadata if metadata is not None else {}

    def __repr__(self):
        return f"EventData with {len(self.data)} events and metadata: {self.metadata}"
    