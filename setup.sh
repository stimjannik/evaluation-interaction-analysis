#! /bin/bash
unzip config_default.zip
unzip models.zip -d resources/models/
./gradlew assemble
