# Evaluation for "Incremental Identification of T-Wise Feature Interactions" (Inciident)

## Structure
This project is part of [FeatJAR](https://github.com/FeatureIDE/FeatJAR).
**Please clone FeatJAR first, following the *README.md* on Github, and then clone this repository into the FeatJAR directory.**

### Build
Execute the follwing gradle task:
```
./gradlew build
```

The resulting Jar can be found in `build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar` and can be called directly.

### Run
The evaluation is run in multiple phases. To run a phase execute the follwing gradle task:
```
./gradlew run --args="--config_dir config_default --config <phase_name>"
```

The following phases exist and should be run in order for the complete evaluation:

- clean
- prepare
- interactions_01
- interactions_02
- interactions_03
- interactions_04
- run

A new directory `results` will be created, containing all generated files.


