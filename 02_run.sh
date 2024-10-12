#!/bin/bash

# Settings
config_dir='config_default'

args="--config_dir ${config_dir} --config"

# Run evaluation
./gradlew run --args="${args} clean" || exit 1
./gradlew run --args="${args} prepare" || exit 1
./gradlew run --args="${args} interactions_01" || exit 1
./gradlew run --args="${args} run --log-info MESSAGE,INFO --log-error WARNING,ERROR" || exit 1