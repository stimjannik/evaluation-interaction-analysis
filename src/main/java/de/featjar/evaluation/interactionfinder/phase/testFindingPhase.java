package de.featjar.evaluation.interactionfinder.phase;

import de.featjar.analysis.sat4j.computation.RandomConfigurationUpdater;
import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Cache;
import de.featjar.base.io.IO;
import de.featjar.base.log.Log;
import de.featjar.evaluation.interactionfinder.ConfigurationOracle;
import de.featjar.evaluation.interactionfinder.InteractionFinderRunner;
import de.featjar.formula.assignment.ABooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanClauseList;
import de.featjar.formula.computation.interactionfinder.*;
import de.featjar.formula.io.csv.BooleanAssignmentGroupsCSVFormat;
import de.featjar.formula.io.dimacs.BooleanAssignmentGroupsDimacsFormat;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

public class testFindingPhase {

    public static void main(String[] args) {
        String[] arg = {
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/2024-11-27_13-50-15/gen/FameDB/cnf.dimacs",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/2024-11-27_13-50-15/gen/FameDB/core.dimacs",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/2024-11-27_13-50-15/gen/FameDB/samples/sol_gs1.csv",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/2024-11-27_13-50-15/gen/FameDB/interactions/int_g0_gs1.dimacs",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/2024-11-27_13-50-15/temp/result.txt",
                "inciident",
                "2",
                "11",
                "0",
                "0",
                "500000000"
        };
        try {
            InteractionFinderRunner.main(arg);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
