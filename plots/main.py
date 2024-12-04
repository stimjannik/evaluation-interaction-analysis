import os
import sys
from dataclasses import dataclass

from plotnine import *
import numpy as np
import pandas as pd
import matplotlib
from scipy.stats import ttest_rel


@dataclass
class Config:
    root_dir_name: str
    out_dir_name: str
    save_results: bool
    show_results: bool
    colors: list
    pdf_width: int
    pdf_height: int
    color_t1: str
    color_t2: str
    color_t3: str
    color_t4: str
    color_t5: str
    axis_title_x: int
    axis_title_y: int
    strip_text_x: int
    text: int
    size_x: int
    size_y: int

    def __init__(self, argv):
        if len(argv) > 1:
            self.root_dir_name = argv[1]
        else:
            self.root_dir_name = 'data'
            if os.path.exists('results/.current'):
                with open('results/.current') as f:
                    data_dir_name = f.readline()
                    self.root_dir_name = 'results/' + data_dir_name

        self.out_dir_name = self.root_dir_name + '/plots/'

        self.show_results = False
        self.save_results = True
        self.pdf_width = 400
        self.pdf_height = 200
        self.color_t1 = '#D95F02'
        self.color_t2 = '#0072B2'
        self.color_t3 = '#009E73'
        self.color_t4 = '#009E73'
        self.color_t5 = '#009E73'
        self.axis_title_x = 12
        self.axis_title_y = 12
        self.strip_text_x = 10
        self.text = 10
        self.size_x = 150
        self.size_y = 150


def set_graphics_options():
    pd.set_option('display.max_columns', None)
    pd.set_option('display.max_rows', None)
    pd.set_option('display.max_colwidth', None)

    font = {'size': 34}
    matplotlib.rc('font', **font)


def readCSVs(file_name, dtype_spec, subfolder):
    data_files = []
    for dirpath, _, filenames in os.walk(config.root_dir_name + "/data/" + subfolder):
        if file_name in filenames:
            data_files.append(os.path.join(dirpath, file_name))

    print(data_files)
    data_frames = [pd.read_csv(file, dtype=dtype_spec, sep=',') for file in data_files]
    combined_data_frame = pd.concat(data_frames, ignore_index=True)
    combined_data_frame = combined_data_frame.drop_duplicates()
    return combined_data_frame


def prepare_data():
    dtype_models = {
        'ModelID': 'int16',
        'ModelName': 'str',
        'VariableCount': 'int32',
        'ClauseCount': 'int32',
    }

    dtype_interactions = {
        'ModelID': 'int16',
        'ModelIt': 'int16',
        'Source': 'str',
        'InteractionCount': 'int8',
        'InteractionSize': 'int8',
        'InteractionID': 'str',
    }

    dtype_algorithms = {
        'AlgorithmID': 'int16',
        'AlgorithmName': 'str',
        'T': 'int8',
    }

    dtype_data = {
        'ModelID': 'int16',
        'InteractionID': 'str',
        'AlgorithmID': 'int16',
        'AlgorithmIt': 'int16',
        'T': 'int8',
        'fpNoise': 'int8',
        'fnNoise': 'int8',
        'NInteractionsFound': 'int8',
        'FoundContainsFaulty': 'str',
        'FaultyContainsFound': 'str',
        'NFoundLiterals': 'int16',
        'NSameLiterals': 'int16',
        'NNonFoundLiterals': 'int16',
        'NWrongLiteralsFound': 'int16',
        'NVerifications': 'int16',
        'TimeMS': 'int32',
        'Timeout': 'bool',
        'Error': 'bool',
    }

    if not os.path.exists(config.out_dir_name + 'complete.pkl'):
        print('Reading and joining original tables')

        subdirectories = sorted([d for d in os.listdir(config.root_dir_name + "/data/") if
                                 os.path.isdir(os.path.join(config.root_dir_name + "/data/", d))])

        models = readCSVs("model.csv", dtype_models, subdirectories[0])
        interactions_1 = readCSVs("interactions_gen.csv", dtype_interactions, subdirectories[1])
        # interactions_2 = readCSVs("interactions_gen.csv", dtype_interactions, subdirectories[2])
        # interactions_3 = readCSVs("interactions_gen.csv", dtype_interactions, subdirectories[3])
        # interactions_4 = readCSVs("interactions_gen.csv", dtype_interactions, subdirectories[4])
        algorithms = readCSVs("algorithms.csv", dtype_algorithms, subdirectories[2])
        results = readCSVs("data.csv", dtype_data, subdirectories[2])

        results[['FoundContainsFaulty', 'FaultyContainsFound', 'FoundAll', 'FoundFirst', 'FoundSecond']] = results[
            ['FoundContainsFaulty', 'FaultyContainsFound', 'FoundAll', 'FoundFirst', 'FoundSecond']].replace({
            'F': False,
            'T': True,
            'N': pd.NA
        })

        results.reset_index(drop=True, inplace=True)
        models.reset_index(drop=True, inplace=True)

        big_data = results.merge(models, on="ModelID", suffixes=('', '_models'), how="left")

        big_data['Interaction_Model_Key'] = big_data['InteractionID'].astype(str) + '_' + big_data['ModelID'].astype(
            str)

        interactions_1['Interaction_Model_Key'] = interactions_1['InteractionID'].astype(str) + '_' + interactions_1[
            'ModelID'].astype(str)

        big_data = big_data.merge(
            interactions_1,
            on='Interaction_Model_Key',
            suffixes=('', '_interaction'),
            how='left'
        )

        # interactions_2['Interaction_Model_Key'] = interactions_2['InteractionID'].astype(str) + '_' + interactions_2[
        #     'ModelID'].astype(str)
        #
        # big_data = big_data.merge(
        #     interactions_2,
        #     on='Interaction_Model_Key',
        #     suffixes=('', '_interaction'),
        #     how='left'
        # )
        #
        # interactions_3['Interaction_Model_Key'] = interactions_3['InteractionID'].astype(str) + '_' + interactions_3[
        #     'ModelID'].astype(str)
        #
        # big_data = big_data.merge(
        #     interactions_3,
        #     on='Interaction_Model_Key',
        #     suffixes=('', '_interaction'),
        #     how='left'
        # )

        # interactions_4['Interaction_Model_Key'] = interactions_4['InteractionID'].astype(str) + '_' + interactions_4[
        #     'ModelID'].astype(str)
        #
        # big_data = big_data.merge(
        #     interactions_4,
        #     on='Interaction_Model_Key',
        #     suffixes=('', '_interaction'),
        #     how='left'
        # )



        big_data.drop(columns=['Interaction_Model_Key'], inplace=True)

        algorithms.set_index('AlgorithmID', inplace=True)  # Set AlgorithmID as index for the algorithms DataFrame
        big_data = big_data.join(algorithms[['AlgorithmName']], on='AlgorithmID',
                                 rsuffix="_algorithm")

        big_data["Success"] = big_data["FoundFirst"] | big_data["FoundSecond"] | big_data["FoundAll"]

        big_data_no_errors = big_data[(big_data['Error'] == False) &
                                      (big_data['Timeout'] == False)]
        create_out_dir()
        big_data.to_pickle(config.out_dir_name + 'complete.pkl', compression='gzip')

    print('Reading complete table')
    data = pd.read_pickle(config.out_dir_name + 'complete.pkl', compression='gzip')

    return data


def get_metric(row):
    metric = (('CF ' if row['Core'] == True else '') + ('DF ' if row['Dead'] == True else '') + (
        'AF ' if row['Abstract'] == 'abstrakt' else '') + ('ConF ' if row['Abstract'] == 'concrete' else '') + (
                  'AFS ' if row['Atomic'] == 'features' else '') + ('ALS ' if row['Atomic'] == 'literals' else '') + (
                  'PCI ' if row['PC'] == True else '') + ('EFI ' if row['Equal'] == True else '')).strip().replace(' ',
                                                                                                                   '-')
    return 'default' if not metric else metric


def calc_coverage(row):
    return (row['CoveredInteractions'] / row['CoveredInteractions_complete_metric']) if row[
                                                                                            'CoveredInteractions_complete_metric'] != 0 else 0


def add_times(row):
    time = row['CoverageTime'] + ((row['CoreTime'] if row['Core'] == True or row['Dead'] == True else 0) + (
        row['AtomicTime'] if row['Atomic'] != 'none' else 0))
    return time


def top(series):
    return series.iloc[0]


def create_out_dir():
    if not os.path.exists(config.out_dir_name):
        try:
            os.mkdir(config.out_dir_name)
        except OSError:
            print("Failed to create output directory %s" % output_path)
            os.exit(-1)


def create_plot(name, p, ratio, width=400, height=200):
    create_out_dir()

    if config.show_results:
        p.show()

    if config.save_results:
        file_name = config.out_dir_name + name + '.pdf'
        print('Writing ' + file_name)
        p.save(file_name, verbose=False, width=width, height=height, units='mm', dpi=300)


def create_csv(df, name):
    create_out_dir()

    if config.show_results:
        print(df)

    if config.save_results:
        df.to_csv(config.out_dir_name + name + '.csv', index=False, sep=';')


def create_table(df, name):
    create_out_dir()

    table = df.style.format(decimal='.', thousands=',', precision=2, escape="latex").to_latex(multicol_align='c')

    if config.show_results:
        print(table)

    if config.save_results:
        with open(config.out_dir_name + name + '.tex', 'w') as f:
            print(table, file=f)


def plot_system_statistics():
    create_plot('system_statistics', (
            ggplot(systems, aes('VariableCount', 'ClauseCount'))
            + geom_point()
            + xlab("Number of Features")
            + ylab("Number of Clauses in CNF")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
    ), 1)


def plot_system_core():
    create_plot('system_statistics', (
            ggplot(systems, aes('VariableCount', 'ClauseCount'))
            + geom_point()
            + xlab("Number of Features")
            + ylab("Number of Clauses in CNF")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
    ), 1)


def plot_coverage_per_system():
    df_plot = data.groupby(['SystemName', 'T', 'SystemIteration', 'ShuffleIteration', 'MetricID'], observed=True)[
        'Coverage'].median().reset_index()

    create_plot('coverage_per_system', (
            ggplot(df_plot, aes('SystemName', 'Coverage', color='factor(T)'))
            + geom_point()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + v)))
            + xlab("Feature Model")
            + ylab("Interaction Reduction")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + guides(color=False)
    ), 1)


def plot_coverage_per_metric():
    df_plot = data.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True)[
        'Coverage'].median().reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(
        ['default', 'CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS', 'CF-DF-AF-ALS-PCI'])]

    create_plot('coverage_per_metric', (
            ggplot(df_plot, aes('Metric', 'Coverage', color='factor(T)'))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + v)))
            + xlab("Metric")
            + ylab("Coverage")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_y_continuous(breaks=[0.5, 0.6, 0.8, 1.0], labels=['50%', '60%', '80%', '100%'], limits=(0.5, 1.0))
            + scale_color_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + guides(color=False)
    ), 1)


def plot_relative_coverage_per_metric():
    df_plot = data.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True)[
        'CoverageDiff'].median().reset_index()
    df_plot = df_plot[
        df_plot['Metric'].isin(['CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS', 'CF-DF-AF-ALS-PCI'])]

    annotation_df = pd.DataFrame({
        'T': [3]
    })

    create_plot('paper/relative_coverage_per_metric', (
            ggplot(df_plot, aes('Metric', 'CoverageDiff', color='factor(T)'))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + v)))
            + xlab("Metric")
            + ylab("Coverage Difference")
            + scale_y_continuous(labels=lambda l: ["%d%%" % (v * 100) for v in l])
            + theme(
        axis_title_x=element_text(size=16),
        axis_title_y=element_text(size=16),
        strip_text_x=element_text(size=14),
        text=element_text(size=14),
    )
            + geom_label(
        data=annotation_df,
        x=3,
        y=0.11,
        label='only 37 out of 48 models scaled for t=3',
        fill='white',
        color='black',
        size=11,
    )
            + scale_color_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + guides(color=False)
    ), 1)


def plot_interaction_reduction_per_metric():
    df_plot = data[data['Size'] == data['PartialSampleSize']]
    df_plot = df_plot.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True)[
        'InteractionReduction'].median().reset_index()
    df_plot = df_plot[
        df_plot['Metric'].isin(['CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS', 'CF-DF-AF-ALS-PCI'])]

    create_plot('interaction_reduction_per_metric', (
            ggplot(df_plot, aes('Metric', 'InteractionReduction', color='factor(T)'))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + v)))
            + xlab("Metric")
            + ylab("Interaction Ratio")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + guides(color=False)
    ), 1)


def plot_interaction_reduction_per_metric_t2():
    df_plot = data[(data['Size'] == data['PartialSampleSize']) & (data['T'] == 2)]
    df_plot = df_plot.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True)[
        'InteractionReduction'].median().reset_index()
    df_plot = df_plot[
        df_plot['Metric'].isin(['CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS', 'CF-DF-AF-ALS-PCI'])]

    create_plot('paper/interaction_reduction_per_metric_t2', (
            ggplot(df_plot, aes('Metric', 'InteractionReduction', color='factor(T)'))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + xlab("Metric")
            + ylab("Percentage of Interactions")
            + scale_y_continuous(breaks=[0.0, 0.25, 0.5, 0.75, 1.0], labels=['0%', '25%', '50%', '75%', '100%'],
                                 limits=[0.0, 1.0])
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=[config.color_t2])
            + guides(color=False)
    ), 1, config.size_x, (config.size_y - 50))


def plot_interaction_reduction_per_system():
    df_plot = data[data['Size'] == data['PartialSampleSize']]
    df_plot = df_plot.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True).agg({
        'VariableCount': top,
        'InteractionReduction': 'median'}).reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(['CF-DF-AF-ALS-PCI', 'CF-DF'])]
    df_plot = df_plot.dropna()
    df_plot['Metric'] = df_plot['Metric'].cat.remove_unused_categories()

    create_plot('interaction_reduction_per_system', (
            ggplot(df_plot, aes('VariableCount', 'InteractionReduction', color='Metric', shape='Metric'))
            + geom_point()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + v)))
            + scale_shape_manual(values=('o', '+', '^'))
            + xlab("Number of Features")
            + ylab("Interaction Ratio")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=['#83aff0', '#090088'])
            + guides(color=False)
    ), 1)


def custom_format(x, pos):
    return f'10^{int(x)}'


def plot_interactions_per_system():
    df_plot = data[data['Size'] == data['PartialSampleSize']]
    df_plot = df_plot.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True).agg({
        'VariableCount': top,
        'CoveredInteractions': 'median'}).reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(['CF-DF-AF-ALS-PCI', 'default'])]
    df_plot = df_plot.dropna()
    df_plot['Metric'] = df_plot['Metric'].cat.remove_unused_categories()
    df_plot['T'] = pd.Categorical(df_plot['T'])

    create_plot('paper/interactions_per_system', (
            ggplot(df_plot, aes('VariableCount', 'CoveredInteractions', color='factor(T)', shape='Metric'))
            + geom_point(size=4)
            + theme(axis_text_x=element_text(rotation=30, hjust=1),
                    legend_position=(0.1, 0.9),
                    legend_box_margin=5)
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
        legend_background=element_rect(color='black')
    )
            + labs(color='t')
            + scale_colour_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + scale_shape_manual(values=['o', '+', '^'])
            + scale_x_log10(labels=lambda x: [f'10^{int(np.log10(y))}' for y in x])
            + scale_y_log10(labels=lambda x: [f'10^{int(np.log10(y))}' for y in x],
                            breaks=[10 ** i for i in [1, 2, 3, 6, 9]])
            + xlab("Number of Features")
            + ylab("Number of Considered Interactions")
    ), 1, config.size_x, config.size_y)


def plot_variable_reduction_per_metric():
    df_plot = data[data['Size'] == data['PartialSampleSize']]
    df_plot = df_plot.groupby(['SystemID', 'Metric'], observed=True).agg({
        'VariableCount': top,
        'FilteredVariableCount': top}).reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(['CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS'])]

    df_plot['VariableReduction'] = df_plot['FilteredVariableCount'] / df_plot['VariableCount']

    create_plot('feature_reduction_per_metric', (
            ggplot(df_plot, aes('Metric', 'VariableReduction'))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + xlab("Metric")
            + ylab("Feature Ratio")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
    ), 1)


def plot_metric_time_per_metric():
    df_plot = data[data['Size'] == data['PartialSampleSize']]
    df_plot = df_plot.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True)[
        'MetricTime'].median().reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(
        ['default', 'CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS', 'CF-DF-AF-ALS-PCI'])]

    create_plot('metric_time_per_metric', (
            ggplot(df_plot, aes('Metric', 'MetricTime', color='factor(T)'))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + v)))
            + scale_y_log10()
            + xlab("Metric")
            + ylab("Computation Time (s)")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + guides(color=False)
    ), 1)


def plot_metric_time_per_metric_t2():
    df_plot = data[(data['Size'] == data['PartialSampleSize']) & (data["T"] == 2)]
    df_plot = df_plot.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True)[
        'MetricTime'].median().reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(
        ['default', 'CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS', 'CF-DF-AF-ALS-PCI'])]

    create_plot('paper/metric_time_per_metric_t2', (
            ggplot(df_plot, aes('Metric', 'MetricTime', color="factor(T)"))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + scale_y_log10()
            + xlab("Metric")
            + ylab("Computation Time (s)")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=[config.color_t2])
            + guides(color=False)
    ), 1, config.size_x, (config.size_y - 50))


def plot_metric_time_per_system():
    df_plot = data[data['Size'] == data['PartialSampleSize']]
    df_plot = df_plot[df_plot['Metric'].isin(['CF-DF-AF-ALS-PCI', 'default'])]
    df_plot['Metric'] = df_plot['Metric'].cat.remove_unused_categories()
    df_plot['T'] = pd.Categorical(df_plot['T'])

    df_plot = df_plot.dropna()

    df_plot = df_plot.groupby(['SystemID', 'T', 'Metric'], observed=True).agg({
        'VariableCount': top,
        'MetricTime': 'median'}).reset_index()

    create_plot('paper/metric_time_per_system', (
            ggplot(df_plot, aes('VariableCount', 'MetricTime', color='T', shape='Metric'))
            + geom_point(size=4)
            + theme(axis_text_x=element_text(rotation=30, hjust=1),
                    legend_position=(0.1, 0.9),
                    legend_box_margin=5)
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
        legend_background=element_rect(color='black')
    )
            + labs(color='t')
            + scale_colour_manual(values=(config.color_t1, config.color_t2, config.color_t3))
            + scale_shape_manual(values=('o', '+', '^'))
            + scale_x_log10(labels=lambda x: [f'10^{int(np.log10(y))}' for y in x])
            + scale_y_log10(breaks=[0.00001, 0.1, 1, 10, 100],
                            limits=[0.00001, 200.0],
                            labels=lambda x: [f'10^{int(np.log10(y))}' for y in x])
            + xlab("Number of Features")
            + ylab("Computation Time (s)")
    ), 1, config.size_x, config.size_y)


def plot_coverage_time_per_metric():
    df_plot = data[data['Size'] == data['PartialSampleSize']]
    df_plot = df_plot.groupby(['SystemID', 'T', 'SystemIteration', 'ShuffleIteration', 'Metric'], observed=True)[
        'CoverageTime'].median().reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(
        ['default', 'CF-DF', 'AF', 'ALS', 'CF-DF-ALS', 'PCI', 'CF-DF-AF-ALS', 'CF-DF-AF-ALS-PCI'])]

    create_plot('coverage_time_per_metric', (
            ggplot(df_plot, aes('Metric', 'CoverageTime', color='factor(T)'))
            + geom_boxplot()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + v)))
            + scale_y_log10()
            + xlab("Metric")
            + ylab("Computation Time (s)")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + guides(color=False)
    ), 1)


def plot_coverage_time_per_system():
    df_plot = data[data['Size'] == data['PartialSampleSize']]

    df_median = df_plot.groupby(['VariableCount', 'T'], observed=True)['CoverageTime'].median().reset_index()

    create_plot('coverage_time_per_number_of_features', (
            ggplot(df_median, aes('VariableCount', 'CoverageTime', color="factor(T)"))
            + geom_point(size=3)
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_grid(cols='T', labeller=labeller(cols=(lambda v: 't = ' + str(v))))
            + scale_y_log10()
            + xlab("Number of Features")
            + ylab("Computation Time (s)")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
    )
            + scale_color_manual(values=[config.color_t1, config.color_t2, config.color_t3])
            + guides(color=False)
    ), 1)


def plot_coverage_per_partial_sample_size():
    df_plot = data[data['T'] == 2]

    df_plot = df_plot.groupby(['SystemName', 'Metric', 'PartialSampleSize'], observed=True).agg({
        'Coverage': 'median',
        'RelaltivePartialSize': 'median'
    }).reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(['default', 'CF-DF-AF-ALS-PCI'])]
    df_plot = df_plot.dropna()
    df_plot['Metric'] = df_plot['Metric'].cat.remove_unused_categories()

    df_test = df_plot.pivot(index=['SystemName', 'PartialSampleSize'], columns='Metric',
                            values='Coverage').reset_index()
    df_test = df_test[['SystemName', 'PartialSampleSize', 'default', 'CF-DF-AF-ALS-PCI']]

    df_plot['p'] = 1.0
    system_names = df_test['SystemName'].unique()
    for system_name in system_names:
        df_test_filter = df_test[df_test['SystemName'] == system_name]
        stat, p = ttest_rel(df_test_filter['default'], df_test_filter['CF-DF-AF-ALS-PCI'])
        df_plot.loc[df_plot['SystemName'] == system_name, 'p'] = p
    df_plot = df_plot[df_plot['p'] < 0.05]

    create_plot('coverage_per_partial_sample_size', (
            ggplot(df_plot, aes('RelaltivePartialSize', 'Coverage', color='Metric'))
            + geom_line()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_wrap('SystemName')
            + scale_colour_manual(values=('#83aff0', '#090088', 'green'))
            + xlab("Relative Partial Sample Size")
            + ylab("Pair-wise Coverage")
            + scale_y_continuous(breaks=[0.2, 0.4, 0.6, 0.8, 1.0], labels=['20%', '40%', '60%', '80%', '100%'],
                                 limits=[0.2, 1.0])
            + scale_x_continuous(breaks=[0.0, 0.2, 0.4, 0.6, 0.8, 1.0],
                                 labels=['0%', '20%', '40%', '60%', '80%', '100%'])
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
        legend_position=(1, 0),
        legend_box_margin=5,
        legend_margin=5,
        legend_background=element_rect(fill='white', size=0.5, color='black')
    )
    ), 1, 600, 300)


def plot_coverage_per_partial_sample_size_t2():
    df_plot = data[(data['T'] == 2) & ((data['SystemName'] == "axTLS") | (data['SystemName'] == "am31_sim"))]

    df_plot = df_plot.groupby(['SystemName', 'Metric', 'PartialSampleSize'], observed=True).agg({
        'Coverage': 'median',
        'RelaltivePartialSize': 'median'
    }).reset_index()

    df_plot = df_plot[df_plot['Metric'].isin(['default', 'CF-DF-AF-ALS-PCI'])]
    df_plot = df_plot.dropna()
    df_plot['Metric'] = df_plot['Metric'].cat.remove_unused_categories()

    df_test = df_plot.pivot(index=['SystemName', 'PartialSampleSize'], columns='Metric',
                            values='Coverage').reset_index()
    df_test = df_test[['SystemName', 'PartialSampleSize', 'default', 'CF-DF-AF-ALS-PCI']]

    df_plot['p'] = 1.0
    system_names = df_test['SystemName'].unique()
    for system_name in system_names:
        df_test_filter = df_test[df_test['SystemName'] == system_name]
        stat, p = ttest_rel(df_test_filter['default'], df_test_filter['CF-DF-AF-ALS-PCI'])
        df_plot.loc[df_plot['SystemName'] == system_name, 'p'] = p
    df_plot = df_plot[df_plot['p'] < 0.05]

    custom_labels = {
        'axTLS': 'axTLS (number of features: 96)',
        'am31_sim': 'am31_sim (number of features: 1178)'
    }

    create_plot('paper/coverage_per_partial_sample_size_t2', (
            ggplot(df_plot, aes('RelaltivePartialSize', 'Coverage', color='Metric'))
            + geom_line()
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_wrap('SystemName', ncol=1, labeller=labeller(SystemName=lambda s: custom_labels[s]))
            + scale_colour_manual(values=('#83aff0', '#090088', 'green'))
            + xlab("Relative Partial Sample Size")
            + ylab("Pair-wise Coverage")
            + scale_y_continuous(breaks=[0.2, 0.4, 0.6, 0.8, 1.0], labels=['20%', '40%', '60%', '80%', '100%'],
                                 limits=[0.2, 1.0])
            + scale_x_continuous(breaks=[0.0, 0.2, 0.4, 0.6, 0.8, 1.0],
                                 labels=['0%', '20%', '40%', '60%', '80%', '100%'])
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        strip_text_x=element_text(size=config.strip_text_x),
        text=element_text(size=config.text),
        legend_position=(0.975, 0.025),
        legend_box_margin=5,
        legend_margin=5,
        legend_background=element_rect(fill='white', size=0.5, color='black')
    )
    ), 1, config.size_x, config.size_y)


def plot_found_per_method():
    df_plot = data[data["T"] == 5]
    df_plot['Success'] = df_plot['Success'].astype('category')
    df_plot = df_plot.groupby(['AlgorithmName', 'Success', 'T'], observed=False).size().reset_index(name='Count')
    df_plot['Percentage'] = df_plot.groupby(['AlgorithmName', 'T'], observed=False)['Count'].transform(
        lambda x: x / x.sum() * 100)

    plot = (
            ggplot(df_plot, aes('AlgorithmName', 'Percentage', fill='Success'))
            + ggtitle("Percentage of Success by Algorithm (T=5)")
            + geom_bar(stat='identity', position='dodge')
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + xlab("Algorithm")
            + ylab("Percentage")
            + theme(
        axis_title_x=element_text(size=config.axis_title_x),
        axis_title_y=element_text(size=config.axis_title_y),
        text=element_text(size=config.text),
    )
            + scale_fill_manual(values=[config.color_t1, config.color_t2],
                                name='Success',
                                labels=['Fail', 'Success'])
            + guides(fill=guide_legend(title='Success'))
            + facet_wrap('~ T')
    )

    create_plot('found_per_method', plot, 1)


def plot_found_per_method_i2():
    df_plot = data[data["T"] == 5]
    df_plot['Success'] = df_plot['Success'].astype('category')
    df_plot = df_plot.groupby(['AlgorithmName', 'Success', 'T', 'InteractionCount'], observed=False).size().reset_index(name='Count')
    df_plot['Percentage'] = df_plot.groupby(['AlgorithmName', 'T'], observed=False)['Count'].transform(
        lambda x: x / x.sum() * 100
    )

    plot = (
        ggplot(df_plot, aes('AlgorithmName', 'Percentage', fill='Success'))
        + ggtitle("Percentage of Success by Algorithm (T=5)")
        + geom_bar(stat='identity', position='dodge')
        + theme(axis_text_x=element_text(rotation=30, hjust=1))
        + xlab("Algorithm")
        + ylab("Percentage")
        + theme(
            axis_title_x=element_text(size=config.axis_title_x),
            axis_title_y=element_text(size=config.axis_title_y),
            text=element_text(size=config.text),
        )
        + scale_fill_manual(values=[config.color_t1, config.color_t2],
                            name='Success',
                            labels=['Fail', 'Success'])
        + guides(fill=guide_legend(title='Success'))
        + facet_wrap('~ InteractionCount')
    )

    create_plot('found_per_method_i2', plot, 1)


def plot_verifications_vs_inciident():
    # Filter for successful runs and exclude 'random' algorithm
    data_filtered = data[(data['Success'] == True) & (data['AlgorithmName'] != 'random')]

    # Identify "inciident" entries for each T, InteractionID, and ModelID
    inciident_data = data_filtered[data_filtered['AlgorithmName'] == 'inciident']
    comparison_data = data_filtered[data_filtered['AlgorithmName'] != 'inciident']

    # Merge data to calculate difference from "inciident"
    df_merged = comparison_data.merge(
        inciident_data[['ModelID', 'InteractionID', 'T', 'NVerifications']],
        on=['ModelID', 'InteractionID', 'T'],
        suffixes=('', '_inciident')
    )

    # Calculate difference in "NVerifications" relative to "inciident"
    df_merged['VerificationDifference'] = df_merged['NVerifications'] - df_merged['NVerifications_inciident']

    # Calculate mean difference for each algorithm and T
    mean_values = (
        df_merged.groupby(['AlgorithmName', 'T'])['VerificationDifference']
        .mean()
        .reset_index(name='MeanDifference')
    )

    # Plot: boxplot of verification differences per algorithm with facets by T, with means as annotations
    plot = (
            ggplot(df_merged, aes(x='AlgorithmName', y='VerificationDifference'))
            + geom_boxplot()
            + geom_text(
        data=mean_values,
        mapping=aes(x='AlgorithmName', y=0, label='MeanDifference'),
        color='blue',
        size=8,
        va='bottom'
    )
            + xlab("Algorithm")
            + ylab("Difference in NVerifications vs inciident")
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_wrap('~ T')
    )

    create_plot('verifications_comparison_inciident', plot, 1)

def plot_time_vs_inciident():
    # Filter for successful runs and exclude 'random' algorithm
    data_filtered = data[(data['TimeMS'] == True) & (data['AlgorithmName'] != 'random')]

    # Identify "inciident" entries for each T, InteractionID, and ModelID
    inciident_data = data_filtered[data_filtered['AlgorithmName'] == 'inciident']
    comparison_data = data_filtered[data_filtered['AlgorithmName'] != 'inciident']

    # Merge data to calculate difference from "inciident"
    df_merged = comparison_data.merge(
        inciident_data[['ModelID', 'InteractionID', 'T', 'TimeMS']],
        on=['ModelID', 'InteractionID', 'T'],
        suffixes=('', '_inciident')
    )

    # Calculate difference in "NVerifications" relative to "inciident"
    df_merged['TimeDifference'] = df_merged['TimeMS'] - df_merged['TimeMS_inciident']

    # Calculate mean difference for each algorithm and T
    mean_values = (
        df_merged.groupby(['AlgorithmName', 'T'])['TimeDifference']
        .mean()
        .reset_index(name='MeanDifference')
    )

    # Plot: boxplot of verification differences per algorithm with facets by T, with means as annotations
    plot = (
            ggplot(df_merged, aes(x='AlgorithmName', y='TimeDifference'))
            + geom_boxplot()
            + geom_text(
        data=mean_values,
        mapping=aes(x='AlgorithmName', y=0, label='MeanDifference'),
        color='blue',
        size=8,
        va='bottom'
    )
            + xlab("Algorithm")
            + ylab("Difference in TimeMS vs inciident")
            + theme(axis_text_x=element_text(rotation=30, hjust=1))
            + facet_wrap('~ T')
    )

    create_plot('time_comparison_inciident', plot, 1)


if __name__ == "__main__":
    config = Config(sys.argv)
    set_graphics_options()

    dfs = prepare_data()

    data = dfs

    print('Ploting')
    plot_found_per_method()
    plot_found_per_method_i2()
    plot_verifications_vs_inciident()
    # plot_system_statistics()
    # plot_coverage_per_system()
    # plot_coverage_per_metric()
    # plot_relative_coverage_per_metric()
    # plot_interactions_per_system()
    # plot_interaction_reduction_per_metric()
    # plot_interaction_reduction_per_metric_t2()
    # plot_interaction_reduction_per_system()
    # plot_variable_reduction_per_metric()
    # plot_coverage_per_partial_sample_size()
    # plot_coverage_per_partial_sample_size_t2()
    # plot_metric_time_per_metric()
    # plot_metric_time_per_metric_t2()
    # plot_metric_time_per_system()
    # plot_coverage_time_per_metric()
    # plot_coverage_time_per_system()
    print('Finished')
