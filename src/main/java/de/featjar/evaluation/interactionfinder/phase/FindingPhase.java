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
import de.featjar.base.cli.ListOption;
import de.featjar.base.cli.Option;
import de.featjar.base.data.Result;
import de.featjar.base.io.IO;
import de.featjar.base.io.csv.CSVFile;
import de.featjar.evaluation.Evaluator;
import de.featjar.evaluation.ProgressTracker;
import de.featjar.evaluation.interactionfinder.InteractionFinderRunner;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentSpace;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.io.dimacs.BooleanAssignmentSpaceDimacsFormat;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Sebastian Krieter
 */
public class FindingPhase extends Evaluator {

    public static final Option<Integer> memoryOption = new Option<>("memory", Option.IntegerParser, 8);
    public static final ListOption<Integer> tOption = new ListOption<>("t", Option.IntegerParser);
    public static final ListOption<Double> fpNoiseOption = new ListOption<>("fpNoise", Option.DoubleParser);
    public static final ListOption<Double> fnNoiseOption = new ListOption<>("fnNoise", Option.DoubleParser);
    public static final ListOption<String> algorithmsOption = new ListOption<>("algorithm", Option.StringParser);
    public static final Option<Boolean> runjarOption = new Option<>("jar", Option.BooleanParser, false);

    private static final Pattern compile = Pattern.compile("uint_([a-z]+\\d+)_([a-z]+\\d+)[.]dimacs");

    private static class ProcessResult {
        List<ABooleanAssignment> foundInteractions;
        ABooleanAssignment foundInteractionsMerged;
        ABooleanAssignment foundInteractionsMergedAndUpdated;
        long elapsedTimeInMS;
        int verificationCounter;
        boolean timeoutOccured, errorOccured;

        ProcessResult() {
            elapsedTimeInMS = -1;
            verificationCounter = -1;
            timeoutOccured = false;
            errorOccured = false;
            foundInteractions = Collections.emptyList();
            foundInteractionsMerged = new BooleanAssignment();
            foundInteractionsMergedAndUpdated = new BooleanAssignment();
        }

        ProcessResult(
                List<ABooleanAssignment> foundInteractions,
                ABooleanAssignment foundInteractionsMerged,
                ABooleanAssignment foundInteractionsMergedAndUpdated,
                long elapsedTimeInMS,
                int verificationCounter,
                boolean timeoutOccured,
                boolean errorOccured) {
            this.foundInteractions = foundInteractions;
            this.foundInteractionsMerged = foundInteractionsMerged;
            this.foundInteractionsMergedAndUpdated = foundInteractionsMergedAndUpdated;
            this.elapsedTimeInMS = elapsedTimeInMS;
            this.verificationCounter = verificationCounter;
            this.timeoutOccured = timeoutOccured;
            this.errorOccured = errorOccured;
        }
    }

    private List<BooleanClause> faultyInteractionsUpdated;
    private ProcessResult result;

    private CSVFile dataCSV, algorithmCSV;
    private VariableMap variables;

    private int t, modelID, algorithmID, algorithmIteration;
    private double fpNoise, fnNoise;
    private String modelName, algorithmName, interactionID;

    @Override
    public List<Option<?>> getOptions() {
        ArrayList<Option<?>> options = new ArrayList<>(super.getOptions());
        options.add(memoryOption);
        options.add(tOption);
        options.add(fpNoiseOption);
        options.add(fnNoiseOption);
        options.add(algorithmsOption);
        options.add(runjarOption);
        return options;
    }

    @Override
    public void runEvaluation() {
        try {
            dataCSV = new CSVFile(csvPath.resolve("data.csv"));
            dataCSV.setHeaderFields(
                    "ModelID",
                    "InteractionID",
                    "AlgorithmID",
                    "AlgorithmIt",
                    "T",
                    "fpNoise",
                    "fnNoise",
                    "NInteractionsFound",
                    "FoundContainsFaulty",
                    "FaultyContainsFound",
                    "NFoundLiterals",
                    "NSameLiterals",
                    "NNonFoundLiterals",
                    "NWrongLiteralsFound",
                    "NVerifications",
                    "TimeMS",
                    "Timeout",
                    "Error");

            algorithmCSV = new CSVFile(csvPath.resolve("algorithms.csv"));
            algorithmCSV.setHeaderFields("AlgorithmID", "AlgorithmName", "T");
            algorithmCSV.flush();

            optionCombiner.init(
                    systemsOption, fpNoiseOption, fnNoiseOption, algorithmsOption, tOption, algorithmIterationsOption);
            optionCombiner.loopOverOptions(this::optionLoop);
        } catch (IOException e) {
            FeatJAR.log().error(e);
        }
    }

    public void optionLoop(int lastChanged) {
        switch (lastChanged) {
            case 0:
                modelName = optionCombiner.getValue(0);
                modelID = systemNames.indexOf(modelName);
                Result<BooleanAssignmentSpace> load = IO.load(
                        genPath.resolve(modelName).resolve("cnf.dimacs"), new BooleanAssignmentSpaceDimacsFormat());
                if (load.isEmpty()) {
                    FeatJAR.log().problems(load.getProblems());
                } else {
                    BooleanAssignmentSpace space = load.get();
                    variables = space.getVariableMap();
                }
            case 1:
                fpNoise = optionCombiner.getValue(1);
            case 2:
                fnNoise = optionCombiner.getValue(2);
                if (algorithmID > 0) {
                    algorithmCSV = null;
                }
                algorithmID = 0;
            case 3:
                algorithmName = optionCombiner.getValue(3);
            case 4:
                t = optionCombiner.getValue(4);
                algorithmID++;
                if (algorithmCSV != null) {
                    writeCSV(algorithmCSV, w -> {
                        w.add(algorithmID);
                        w.add(algorithmName);
                        w.add(t);
                    });
                }
            case 5:
                algorithmIteration = optionCombiner.getValue(5);
                processInteractions();
            default:
        }
    }

    private void processInteractions() {
        Path outPath = genPath.resolve(modelName);
        List<Path> interactionFiles;
        try {
            Path interactionDir = outPath.resolve("interactions");
            if (!Files.exists(interactionDir)) {
                FeatJAR.log().debug("No interactions found for %s", modelName);
                return;
            }
            interactionFiles =
                    Files.list(interactionDir).filter(Files::isRegularFile).collect(Collectors.toList());
        } catch (IOException e) {
            FeatJAR.log().error(e);
            return;
        }
        ProgressTracker progress = new ProgressTracker(interactionFiles.size());
        for (Path interactionFile : interactionFiles) {
            FeatJAR.log().progress(progress::nextAndPrint);
            Matcher matcher = compile.matcher(interactionFile.getFileName().toString());
            if (matcher.matches()) {
                interactionID = matcher.group(1);
                String solSuffix = matcher.group(2);
                String samplePathString = outPath.resolve("samples")
                        .resolve("sol_" + solSuffix + ".csv")
                        .toString();
                String modelPathString = outPath.resolve("cnf.dimacs").toString();
                String corePathString = outPath.resolve("core.dimacs").toString();
                String outputPath = tempPath.resolve("result.txt").toString();

                BooleanAssignmentSpace interaction = IO.load(interactionFile, new BooleanAssignmentSpaceDimacsFormat())
                        .orElseThrow();
                faultyInteractionsUpdated = interaction.toClauseList(0).getAll();

                ProcessResult result =
                        startProcess(interactionFile, samplePathString, modelPathString, corePathString, outputPath);

                try {
                    IO.save(
                            new BooleanAssignmentSpace(variables, List.of(result.foundInteractions)),
                            genPath.resolve(modelName)
                                    .resolve("found")
                                    .resolve(String.format(
                                            "int_found_%s_%d_%d_%s.dimacs",
                                            algorithmName, t, algorithmIteration, interactionID)),
                            new BooleanAssignmentSpaceDimacsFormat());
                    IO.save(
                            new BooleanAssignmentSpace(
                                    variables,
                                    List.of(List.of(
                                            result.foundInteractionsMerged, result.foundInteractionsMergedAndUpdated))),
                            genPath.resolve(modelName)
                                    .resolve("found")
                                    .resolve(String.format(
                                            "uint_found_%s_%d_%d_%s.dimacs",
                                            algorithmName, t, algorithmIteration, interactionID)),
                            new BooleanAssignmentSpaceDimacsFormat());
                    writeCSV(dataCSV, this::writeRunData);
                } catch (IOException e) {
                    FeatJAR.log().error(e);
                }
            }
        }
        FeatJAR.log().progress(progress::printStatus);
    }

    private ProcessResult startProcess(
            Path interactionFile,
            String samplePathString,
            String modelPathString,
            String corePathString,
            String outputPath) {
        final Path output = Path.of(outputPath);
        Result<Long> timeout = optionParser.get(Evaluator.timeout);

        ArrayList<String> args = new ArrayList<>(Arrays.asList(
                modelPathString, // + core
                corePathString, // + core
                samplePathString, //
                interactionFile
                        .resolveSibling(interactionFile.getFileName().toString().substring(1))
                        .toString(), //
                outputPath, //
                algorithmName,
                String.valueOf(t), //
                String.valueOf(getOption(Evaluator.randomSeed) + algorithmIteration), // +???
                String.valueOf(fpNoise), //
                String.valueOf(fnNoise),
                String.valueOf(TimeUnit.SECONDS.toMillis(timeout.get()))));

        FeatJAR.log()
                .debug(() -> String.format(
                        "%d | %.3f | %.3f | %.3f", //
                        Thread.activeCount(), //
                        (Runtime.getRuntime().freeMemory() / 1000_000) / 1000.0, //
                        (Runtime.getRuntime().totalMemory() / 1000_000) / 1000.0, //
                        (Runtime.getRuntime().maxMemory() / 1000_000) / 1000.0));

        if (getOption(runjarOption)) {
            runProcess(output, args);
        } else {
            runInPlace(output, args);
        }
        return result = readResults(output);
    }

    private void runInPlace(final Path output, List<String> args) {
        try {
            InteractionFinderRunner.main(args.toArray(new String[0]));
        } catch (IOException e) {
            FeatJAR.log().error(e);
        }
    }

    private void runProcess(final Path output, List<String> args) {
        Process process = null;
        BufferedReader prcErr = null;
        try {
            ArrayList<String> jvmArgs = new ArrayList<>(Arrays.asList(
                    "java", //
                    "-Xmx" + getOption(memoryOption) + "g", //
                    "-da", //
                    "-cp", //
                    "build/libs/evaluation-interaction-analysis-0.1.0-SNAPSHOT-all.jar", //
                    "de.featjar.evaluation.interactionfinder.InteractionFinderRunner"));
            jvmArgs.addAll(args);
            process = new ProcessBuilder(jvmArgs).start();
            prcErr = new BufferedReader(new InputStreamReader(process.getErrorStream()));
            process.waitFor();
        } catch (Exception e) {
            FeatJAR.log().error(e);
        } finally {
            try {
                if (prcErr != null) {
                    if (prcErr.ready()) {
                        FeatJAR.log().error(prcErr.lines().reduce("", (s1, s2) -> s1 + s2 + "\n"));
                    }
                    prcErr.close();
                }
            } catch (IOException e) {
                FeatJAR.log().error(e);
            }
            if (process != null) {
                process.destroy();
                try {
                    process.waitFor(2, TimeUnit.SECONDS);
                } catch (InterruptedException e) {
                    FeatJAR.log().error(e);
                }
                process.destroyForcibly();
            }
        }
    }

    private ProcessResult readResults(final Path output) {
        if (Files.exists(output)) {
            long parsedElapsedTimeInMS;
            int parsedVerificationCounter;
            boolean parsedTimeout;
            boolean parsedError;
            List<ABooleanAssignment> parsedInteractions;
            ABooleanAssignment parsedInteractionsMerged;
            ABooleanAssignment parsedInteractionsMergedAndUpdated;
            try (Stream<String> lines = Files.lines(output)) {
                String[] results = lines.toArray(String[]::new);
                parsedElapsedTimeInMS = Long.parseLong(results[0]);
                parsedVerificationCounter = Integer.parseInt(results[1]);
                parsedTimeout = Boolean.parseBoolean(results[2]);
                parsedError = Boolean.parseBoolean(results[3]);
                parsedInteractionsMerged = InteractionFinderRunner.parseLiteralList(results[4]);
                parsedInteractionsMergedAndUpdated = InteractionFinderRunner.parseLiteralList(results[5]);
                if ("null".equals(results[6])) {
                    parsedInteractions = Collections.emptyList();
                } else {
                    parsedInteractions = new ArrayList<>(results.length - 6);
                    for (int i = 6; i < results.length; i++) {
                        parsedInteractions.add(InteractionFinderRunner.parseLiteralList(results[i]));
                    }
                }
                return new ProcessResult(
                        parsedInteractions,
                        parsedInteractionsMerged,
                        parsedInteractionsMergedAndUpdated,
                        parsedElapsedTimeInMS,
                        parsedVerificationCounter,
                        parsedTimeout,
                        parsedError);
            } catch (Exception e) {
                FeatJAR.log().error(e);
            }
        }
        return new ProcessResult();
    }

    protected void writeRunData(CSVFile dataCSVWriter) {
        dataCSVWriter.add(modelID);
        dataCSVWriter.add(interactionID);
        dataCSVWriter.add(algorithmID);
        dataCSVWriter.add(algorithmIteration);

        dataCSVWriter.add(t);
        dataCSVWriter.add(fpNoise);
        dataCSVWriter.add(fnNoise);
        dataCSVWriter.add(result.foundInteractions.size());
        dataCSVWriter.add(
                result.foundInteractions.isEmpty()
                        ? "N"
                        : result.foundInteractionsMergedAndUpdated.containsAll(faultyInteractionsUpdated.get(0))
                                ? "T"
                                : "F");
        dataCSVWriter.add(
                result.foundInteractions.isEmpty()
                        ? "N"
                        : faultyInteractionsUpdated.get(0).containsAll(result.foundInteractionsMergedAndUpdated)
                                ? "T"
                                : "F");
        dataCSVWriter.add(
                result.foundInteractions.isEmpty() ? 0 : result.foundInteractionsMergedAndUpdated.countNonZero());
        dataCSVWriter.add(
                result.foundInteractions.isEmpty()
                        ? -1
                        : faultyInteractionsUpdated
                                .get(0)
                                .retainAll(result.foundInteractionsMergedAndUpdated)
                                .countNonZero());
        dataCSVWriter.add(
                result.foundInteractions.isEmpty()
                        ? -1
                        : faultyInteractionsUpdated
                                .get(0)
                                .removeAll(result.foundInteractionsMergedAndUpdated)
                                .countNonZero());
        dataCSVWriter.add(
                result.foundInteractions.isEmpty()
                        ? -1
                        : result.foundInteractionsMergedAndUpdated
                                .removeAll(faultyInteractionsUpdated.get(0))
                                .countNonZero());
        dataCSVWriter.add(result.verificationCounter);
        dataCSVWriter.add(result.elapsedTimeInMS);
        dataCSVWriter.add(result.timeoutOccured);
        dataCSVWriter.add(result.errorOccured);
    }
}
