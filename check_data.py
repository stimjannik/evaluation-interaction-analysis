import os
import sys
import numpy as np
import pandas as pd
import math
from dataclasses import dataclass

@dataclass
class Config:
    root_dir_name: str
    algorithms: list

    def __init__(self, argv):
        if len(argv) > 1:
            self.root_dir_name = argv[1]
        else:
            self.root_dir_name = 'results/'

        self.algorithms = [random,single,incremental]


def main(argv):
    config = Config(argv)

    set_graphics_options(config)
    df_data = prepare_data(config)

    investigateProblem(df_data.copy(), config)


def set_graphics_options(config):
    pd.set_option('display.max_columns', None)
    pd.set_option('display.max_rows', None)
    pd.set_option('display.max_colwidth', None)


def prepare_data(config):
    df_parts = []

    # removing the new line characters
    with open(config.root_dir_name + '/.current') as f:
        lines = [line.rstrip() for line in f]
        cur_dir = lines[0]
        print(cur_dir)

        data_dirs = [f.path for f in os.scandir(config.root_dir_name + '/' + cur_dir) if f.is_dir() and os.path.basename(os.path.normpath(f.path)).startswith('data-')]
        for data_dir in data_dirs:
            print(data_dir)
            df = pd.read_csv(data_dir + "/runData.csv", sep = ';')
            df_algo = pd.read_csv(data_dir + "/algorithms.csv", sep = ';')
            df_models = pd.read_csv(data_dir + "/models.csv", sep = ';')
            key = ['AlgorithmID']
            df = df.join(df_algo.set_index(key), on=key, rsuffix="_algo")
            key = ['ModelID']
            df = df.join(df_models.set_index(key), on=key, rsuffix="_model")
            df_parts.append(df)

    df_data = pd.concat(df_parts)

    # Columns
    df_data = df_data.rename(columns={"Name": "Algorithm", "Name_model": "ModelName", "ConfigurationVerificationCount": "Configurations"}, errors="raise")
    print('data count: ' + str(len(df_data)))

    # Filter
    df_data = df_data[df_data['InteractionSize'] > 0]
    df_data = df_data[df_data['T'] > 0]

    df_data = df_data.replace({'Algorithm': 'NaiveRandom'}, random)
    df_data = df_data.replace({'Algorithm': 'Single'}, single)
    df_data = df_data.replace({'Algorithm': 'IterativeNaiveRandom'}, 'IncRandom')
    df_data = df_data.replace({'Algorithm': 'IterativeSingle'}, 'IncSingle')
    df_data = df_data.replace({'Algorithm': 'ForwardBackwardOld'}, oldIncremental)
    df_data = df_data.replace({'Algorithm': 'ForwardBackward'}, incremental)

    df_data['Type'] = \
        df_data['FoundMergedUpdatedIsSubsetFaultyUpdated'] + \
        df_data['FaultyUpdatedIsSubsetFoundMergedUpdated']

    df_data = df_data.replace({'Type': 'NN'}, 'NoResult')
    df_data = df_data.replace({'Type': 'FF'}, 'Different')
    df_data = df_data.replace({'Type': 'TF'}, 'Subset')
    df_data = df_data.replace({'Type': 'FT'}, 'Superset')
    df_data = df_data.replace({'Type': 'TT'}, 'Equal')

    df_data['Time'] = df_data['Time'] / 1000.0

    return df_data


def investigateProblem(df_error, config):
    df_error = df_error[df_error['Type'] != 'Equal']
    df_error = df_error[df_error['T'] == df_error['InteractionSize']]
    df_error = df_error[df_error['Algorithm'].isin([incremental])]
    df_error = df_error[['Algorithm','ModelName', 'ModelIteration', 'InteractionSize', 'T', 'MissedLiteralsCount', 'IncorrectlyFoundLiteralsCount','InteractionsUpdated', 'FoundInteractionsMerged']]
    print(df_error)


if __name__ == "__main__":
    random = 'Random'
    single = 'iident'
    incremental = 'Inciident'
    oldIncremental = 'OldIncremental'
    main(sys.argv)
