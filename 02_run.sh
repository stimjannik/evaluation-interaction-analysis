#!/bin/bash

# Settings
config_dir='config'

args="--config_dir ${config_dir} --config"

# Run evaluation
./gradlew run --args="${args} clean" || exit 1
./gradlew run --args="${args} prepare" || exit 1
./gradlew run --args="${args} interactions_01" || exit 1
./gradlew run --args="${args} interactions_02" || exit 1
./gradlew run --args="${args} interactions_03" || exit 1
./gradlew run --args="${args} interactions_04" || exit 1
./gradlew run --args="${args} run" || exit 1