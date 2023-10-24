/*
 * Copyright (C) 2023 FeatJAR-Development-Team
 *
 * This file is part of FeatJAR-evaluation-interaction-analysis.
 *
 * evaluation-interaction-analysis is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3.0 of the License,
 * or (at your option) any later version.
 *
 * evaluation-interaction-analysis is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with evaluation-interaction-analysis. If not, see <https://www.gnu.org/licenses/>.
 *
 * See <https://github.com/FeatJAR> for further information.
 */
package de.featjar.evaluation.interactionfinder.phase;

import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Computations;
import de.featjar.base.data.Result;
import de.featjar.base.io.IO;
import de.featjar.base.io.csv.CSVFile;
import de.featjar.evaluation.EvaluationPhase;
import de.featjar.evaluation.Evaluator;
import de.featjar.evaluation.interactionfinder.InteractionFinderEvaluator;
import de.featjar.evaluation.interactionfinder.InteractionFinderRunner;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentSpace;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.sat4j.ComputeCoreDeadVariablesSAT4J;
import de.featjar.formula.io.csv.BooleanAssignmentSpaceCSVFormat;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * @author Sebastian Krieter
 */
public class FindingPhase implements EvaluationPhase<InteractionFinderEvaluator> {

    private List<BooleanSolution> faultyInteractionsUpdated;
    private List<ABooleanAssignment> foundInteractions;
    private ABooleanAssignment foundInteractionsMerged;
    private ABooleanAssignment foundInteractionsMergedAndUpdated;
    private long elapsedTimeInMS;
    private int verificationCounter;

    private CSVFile dataCSV, algorithmCSV;
    private BooleanClauseList cnf;
    private VariableMap variables;

    private int t, modelID, algorithmID, algorithmIteration;
    private double fpNoise, fnNoise;
    private String modelName, algorithmName, interactionID;

    private static final Pattern compile = Pattern.compile("int_([a-z]+\\d+)_([a-z]+\\d+)[.]csv");

    public void optionLoop(InteractionFinderEvaluator evaluator, int lastChanged) {
        switch (lastChanged) {
            case 0:
                modelName = evaluator.cast(0);
                modelID = evaluator.systemNames.indexOf(modelName);
                Result<BooleanAssignmentSpace> load = IO.load(
                        evaluator.outputPath.resolve(modelName).resolve("cnf.csv"),
                        new BooleanAssignmentSpaceCSVFormat());
                if (load.isEmpty()) {
                    FeatJAR.log().problems(load.getProblems());
                } else {
                    BooleanAssignmentSpace space = load.get();
                    variables = space.getVariableMap();
                    cnf = new BooleanClauseList(space.getGroups().get(0), variables.getVariableCount());
                }
            case 1:
                fpNoise = evaluator.cast(1);
            case 2:
                fnNoise = evaluator.cast(2);
                algorithmID = 0;
            case 3:
                algorithmName = evaluator.cast(3);
            case 4:
                t = evaluator.cast(4);
                evaluator.writeCSV(algorithmCSV, w -> {
                    w.add(algorithmID);
                    w.add(evaluator.<String>cast(0));
                    w.add(evaluator.<String>cast(1));
                });
                algorithmID++;
            case 5:
                algorithmIteration = evaluator.cast(5);

                Path resolve = evaluator.outputPath.resolve(modelName);
                List<Path> interactionFiles;
                try {
                    interactionFiles = Files.list(resolve.resolve("interactions"))
                            .filter(Files::isRegularFile)
                            .collect(Collectors.toList());
                } catch (IOException e) {
                    FeatJAR.log().error(e);
                    return;
                }
                for (Path interactionFile : interactionFiles) {
                    Matcher matcher =
                            compile.matcher(interactionFile.getFileName().toString());
                    matcher.matches();
                    interactionID = matcher.group(1);
                    String solSuffix = matcher.group(2);
                    String samplePathString = resolve.resolve("samples")
                            .resolve("sol_" + solSuffix + ".csv")
                            .toString();
                    String modelPathString = resolve.resolve("cnf.csv").toString();
                    String outputPath = evaluator.tempPath.resolve("result.txt").toString();

                    BooleanAssignmentSpace interaction = IO.load(interactionFile, new BooleanAssignmentSpaceCSVFormat())
                            .orElseThrow();
                    faultyInteractionsUpdated = interaction.toSolutionList(1).getAll();

                    extracted(evaluator, interactionFile, samplePathString, modelPathString, outputPath);
                    if (foundInteractions != null) {
                        foundInteractionsMerged = BooleanAssignment.merge(foundInteractions);
                        foundInteractionsMergedAndUpdated = Computations.of(cnf)
                                .map(ComputeCoreDeadVariablesSAT4J::new)
                                .set(ComputeCoreDeadVariablesSAT4J.ASSUMED_ASSIGNMENT, foundInteractionsMerged)
                                .compute();
                    } else {
                        foundInteractions = Collections.emptyList();
                        foundInteractionsMerged = new BooleanAssignment();
                        foundInteractionsMergedAndUpdated = new BooleanAssignment();
                    }

                    try {
                        IO.save(
                                new BooleanAssignmentSpace(
                                        variables,
                                        List.of(
                                                foundInteractions,
                                                List.of(foundInteractionsMerged, foundInteractionsMergedAndUpdated))),
                                evaluator
                                        .outputPath
                                        .resolve(modelName)
                                        .resolve("found")
                                        .resolve(String.format(
                                                "int_found_%s_%d_%d_%s.csv",
                                                algorithmName, t, algorithmIteration, interactionID)),
                                new BooleanAssignmentSpaceCSVFormat());
                        evaluator.writeCSV(dataCSV, this::writeRunData);
                    } catch (IOException e) {
                        FeatJAR.log().error(e);
                    }
                }
            default:
        }
    }

    private void extracted(
            InteractionFinderEvaluator evaluator,
            Path interactionFile,
            String samplePathString,
            String modelPathString,
            String outputPath) {
        Process process;
        try {
            process = new ProcessBuilder(
                            "java", //
                            "-Xmx" + evaluator.getOption(InteractionFinderEvaluator.memoryOption) + "g", //
                            "-da", //
                            "-cp", //
                            "build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar", //
                            "de.featjar.evaluation.interactionfinder.InteractionFinderRunner", //
                            modelPathString, // + core
                            samplePathString, //
                            interactionFile.toString(), //
                            outputPath, //
                            algorithmName,
                            String.valueOf(t), //
                            String.valueOf(evaluator.getOption(Evaluator.randomSeed) + algorithmIteration), // +???
                            String.valueOf(fpNoise), //
                            String.valueOf(fnNoise)) //
                    .start();

            BufferedReader prcErr = new BufferedReader(new InputStreamReader(process.getErrorStream()));

            final Path output = Path.of(outputPath);
            int exitCode = process.waitFor();
            if (exitCode == 0 && Files.exists(output)) {
                String[] results = Files.lines(output).toArray(String[]::new);
                elapsedTimeInMS = Long.parseLong(results[0]);
                verificationCounter = Integer.parseInt(results[1]);

                if ("null".equals(results[2])) {
                    foundInteractions = null;
                } else {
                    foundInteractions = new ArrayList<>(results.length - 2);
                    for (int i = 2; i < results.length; i++) {
                        foundInteractions.add(InteractionFinderRunner.parseLiteralList(results[i]));
                    }
                }
            } else {
                elapsedTimeInMS = -1;
                verificationCounter = -1;
                foundInteractions = null;
            }
            if (prcErr.ready()) {
                String split = prcErr.lines().reduce("", (s1, s2) -> s1 + s2 + "\n");
                FeatJAR.log().error(split);
            }
            try {
                prcErr.close();
            } catch (IOException e) {
                FeatJAR.log().error(e);
            }
            process.destroyForcibly();
            process.waitFor();
        } catch (Exception e) {
            FeatJAR.log().error(e);
        }
    }

    private void extracted2(
            InteractionFinderEvaluator evaluator,
            Path interactionFile,
            String samplePathString,
            String modelPathString,
            String outputPath) {

        try {
            InteractionFinderRunner.main(new String[] {
                modelPathString, // + core
                samplePathString, //
                interactionFile.toString(), //
                outputPath, //
                algorithmName,
                String.valueOf(t), //
                String.valueOf(evaluator.getOption(Evaluator.randomSeed) + algorithmIteration), // +???
                String.valueOf(fpNoise), //
                String.valueOf(fnNoise)
            });

            String[] results = Files.lines(Path.of(outputPath)).toArray(String[]::new);
            elapsedTimeInMS = Long.parseLong(results[0]);
            verificationCounter = Integer.parseInt(results[1]);

            if ("null".equals(results[2])) {
                foundInteractions = null;
            } else {
                foundInteractions = new ArrayList<>(results.length - 2);
                for (int i = 2; i < results.length; i++) {
                    foundInteractions.add(InteractionFinderRunner.parseLiteralList(results[i]));
                }
            }
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    protected void writeRunData(CSVFile dataCSVWriter) {
        dataCSVWriter.add(modelID);
        dataCSVWriter.add(interactionID);
        dataCSVWriter.add(algorithmID);
        dataCSVWriter.add(algorithmIteration);

        dataCSVWriter.add(t);
        dataCSVWriter.add(fpNoise);
        dataCSVWriter.add(fnNoise);
        dataCSVWriter.add(foundInteractions != null ? foundInteractions.size() : -1);
        dataCSVWriter.add(
                foundInteractions != null
                        ? foundInteractionsMergedAndUpdated.containsAll(faultyInteractionsUpdated.get(0)) ? "T" : "F"
                        : "N");
        dataCSVWriter.add(
                foundInteractions != null
                        ? faultyInteractionsUpdated.get(0).containsAll(foundInteractionsMergedAndUpdated) ? "T" : "F"
                        : "N");
        dataCSVWriter.add(foundInteractions != null ? foundInteractionsMergedAndUpdated.countNonZero() : -1);
        dataCSVWriter.add(
                foundInteractions != null
                        ? faultyInteractionsUpdated
                                .get(0)
                                .retainAll(foundInteractionsMergedAndUpdated)
                                .countNonZero()
                        : -1);
        dataCSVWriter.add(
                foundInteractions != null
                        ? faultyInteractionsUpdated
                                .get(0)
                                .removeAll(foundInteractionsMergedAndUpdated)
                                .countNonZero()
                        : -1);
        dataCSVWriter.add(
                foundInteractions != null
                        ? foundInteractionsMergedAndUpdated
                                .removeAll(faultyInteractionsUpdated.get(0))
                                .countNonZero()
                        : -1);
        dataCSVWriter.add(verificationCounter);
        dataCSVWriter.add(elapsedTimeInMS);
    }

    @Override
    public void run(InteractionFinderEvaluator evaluator) {
        try {
            dataCSV = new CSVFile(evaluator.csvPath.resolve("data.csv"));
            dataCSV.setHeaderFields("ModelID", "InteractionID", "AlgorithmID", "AlgorithmIt", "Data");
            dataCSV.flush();
            algorithmCSV = new CSVFile(evaluator.csvPath.resolve("algorithms.csv"));
            algorithmCSV.setHeaderFields("AlgorithmID", "AlgorithmName", "T");
            algorithmCSV.flush();
            evaluator.optionLoop(
                    this,
                    InteractionFinderEvaluator.systemsOption,
                    InteractionFinderEvaluator.fpNoiseOption,
                    InteractionFinderEvaluator.fnNoiseOption,
                    InteractionFinderEvaluator.algorithmsOption,
                    InteractionFinderEvaluator.tOption,
                    InteractionFinderEvaluator.algorithmIterationsOption);
        } catch (IOException e) {
            FeatJAR.log().error(e);
        }
    }
}
