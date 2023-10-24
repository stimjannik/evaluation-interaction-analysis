#! /bin/bash
config_dir='config_minimal'

java -jar build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar --config ${config_dir}/general.properties,${config_dir}/prepare.properties 
java -jar build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar --config ${config_dir}/general.properties,${config_dir}/interactions_01.properties 
java -jar build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar --config ${config_dir}/general.properties,${config_dir}/interactions_02.properties
#java -jar build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar --config ${config_dir}/general.properties,${config_dir}/interactions_03.properties
java -jar build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar --config ${config_dir}/general.properties,${config_dir}/interactions_04.properties
java -jar build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar --config ${config_dir}/general.properties,${config_dir}/run.properties 
