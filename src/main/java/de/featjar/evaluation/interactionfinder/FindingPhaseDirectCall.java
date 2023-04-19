/*
 * Copyright (C) 2023 Sebastian Krieter
 *
 * This file is part of evaluation-interaction-analysis.
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
 * See <> for further information.
 */
package de.featjar.evaluation.interactionfinder;

import de.featjar.analysis.mig.solver.MIG;
import de.featjar.analysis.mig.solver.MIGProvider;
import de.featjar.analysis.mig.solver.Vertex;
import de.featjar.analysis.sat4j.FastRandomConfigurationGenerator;
import de.featjar.analysis.sat4j.RandomConfigurationGenerator;
import de.featjar.analysis.sat4j.RandomConfigurationUpdater;
import de.featjar.clauses.CNF;
import de.featjar.clauses.CNFProvider;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.SolutionList;
import de.featjar.clauses.solutions.analysis.InteractionFinder;
import de.featjar.clauses.solutions.analysis.InteractionFinder.Statistic;
import de.featjar.clauses.solutions.analysis.InteractionFinderWrapper;
import de.featjar.clauses.solutions.analysis.finder.InteractionFinderCombinationForwardBackward;
import de.featjar.clauses.solutions.analysis.finder.NaiveRandomInteractionFinder;
import de.featjar.clauses.solutions.analysis.finder.SingleInteractionFinder;
import de.featjar.clauses.solutions.io.PartialListFormat;
import de.featjar.evaluation.EvaluationPhase;
import de.featjar.evaluation.Evaluator;
import de.featjar.evaluation.util.ModelReader;
import de.featjar.formula.ModelRepresentation;
import de.featjar.formula.io.FormulaFormatManager;
import de.featjar.formula.structure.Formula;
import de.featjar.util.io.csv.CSVWriter;
import de.featjar.util.logging.Logger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Sebastian Krieter
 */
public class FindingPhaseDirectCall implements EvaluationPhase {

    private final PartialListFormat sampleFormat = new PartialListFormat();

    private List<InteractionFinder> algorithmList;
    private List<String> algorithmNameList;

    private CSVWriter runDataWriter, iterationDataWriter, modelWriter, algorithmWriter;
    private int algorithmIndex, algorithmIteration;
    private ModelRepresentation model;

    private List<LiteralList> faultyConfigs;
    private List<LiteralList> faultyInteractions, faultyInteractionsUpdated;

    private InteractionFinderEvaluator interactionFinderEvaluator;

    private int t;
    private int interactionSize;
    private int interactionCount;
    private int configCreationLimit;
    private int configVerificationLimit;
    private double fpNoise;
    private double fnNoise;
    private int runID;

    private List<LiteralList> foundInteractions;
    private LiteralList foundInteractionsMerged;
    private LiteralList foundInteractionsMergedAndUpdated;
    private Statistic lastStatistic;
    private Statistic statistic;
    private long elapsedTimeInMS;

    @Override
    public void run(Evaluator evaluator) {
        Logger.setPrintStackTrace(true);
        interactionFinderEvaluator = (InteractionFinderEvaluator) evaluator;

        modelWriter = evaluator.addCSVWriter("models.csv", "ModelID", "Name", "#Variables", "#Clauses");
        algorithmWriter = evaluator.addCSVWriter("algorithms.csv", "AlgorithmID", "Name");
        runDataWriter = evaluator.addCSVWriter(
                "runData.csv",
                "ModelID",
                "ModelIteration",
                "AlgorithmID",
                "AlgorithmIteration",
                "RunID",
                "T",
                "InteractionSize",
                // "InteractionCount",
                "Interactions",
                "InteractionsUpdated",
                // "FPNoise",
                // "FNNoise",
                // "ConfigurationVerificationLimit",
                // "ConfigurationCreationLimit",
                // "FoundInteractions",
                // "FoundInteractionsUpdated",
                "FoundInteractionCount",
                "FoundInteractionsMerged",
                "FoundMergedUpdatedIsSubsetFaultyUpdated",
                "FaultyUpdatedIsSubsetFoundMergedUpdated",
                "FoundMergedIsSubsetFaulty",
                "FaultyIsSubsetFoundMerged",
                "FaultyIsSubsetFound",
                "FoundIsSubsetFaulty",
                "FoundLiteralsCount",
                "CorrectlyFoundLiteralsCount",
                "MissedLiteralsCount",
                "IncorrectlyFoundLiteralsCount",
                "ConfigurationVerificationCount",
                "Time");
        iterationDataWriter = evaluator.addCSVWriter(
                "iterationData.csv",
                "RunID",
                "RunT",
                "RunIteration",
                "InteractionRemaining",
                "RunConfigurationVerificationCount");

        modelWriter.setLineWriter(this::writeModel);
        algorithmWriter.setLineWriter(this::writeAlgorithm);
        runDataWriter.setLineWriter(this::writeRunData);
        iterationDataWriter.setLineWriter(this::writeIterationData);

        final ModelReader<Formula> mr = new ModelReader<>();
        mr.setPathToFiles(interactionFinderEvaluator.modelPath);
        mr.setFormatSupplier(FormulaFormatManager.getInstance());

        if (evaluator.systemIterations.getValue() > 0) {
            evaluator.tabFormatter.setTabLevel(0);
            Logger.logInfo("Start");

            prepareAlgorithms();

            systemLoop:
            for (evaluator.systemIndex = 0; evaluator.systemIndex < evaluator.systemIndexMax; evaluator.systemIndex++) {
                evaluator.tabFormatter.setTabLevel(1);
                evaluator.logSystem();

                if (!readModel(mr)) {
                    continue systemLoop;
                }

                MIG mig = model.get(MIGProvider.fromFormula(false, false));
                LiteralList coreDead = new LiteralList(mig.getVertices().stream()
                        .filter(Vertex::isCore)
                        .mapToInt(Vertex::getVar)
                        .toArray());
                RandomConfigurationUpdater globalUpdater = new RandomConfigurationUpdater(model, new Random(0));

                for (evaluator.systemIteration = 1;
                        evaluator.systemIteration <= evaluator.systemIterations.getValue();
                        evaluator.systemIteration++) {

                    for (Integer interactionSizeValue : interactionFinderEvaluator.interactionSizeProperty.getValue()) {
                        interactionSize = interactionSizeValue;
                        for (Integer interactionCountValue :
                                interactionFinderEvaluator.interactionCountProperty.getValue()) {
                            interactionCount = interactionCountValue;

                            Random random1 = new Random(evaluator.randomSeed.getValue() + evaluator.systemIteration);
                            faultyConfigs = model.getResult(getConfigGenerator(random1))
                                    .map(SolutionList::getSolutions)
                                    .orElse(Logger::logProblems);
                            if (faultyConfigs == null) {
                                throw new RuntimeException();
                            }

                            Random random2 = new Random(evaluator.randomSeed.getValue() + evaluator.systemIteration);
                            faultyInteractions = faultyConfigs.stream()
                                    .map(c -> new LiteralList(Stream.generate(() -> (random2.nextInt(c.size()) + 1)) //
                                            .mapToInt(Integer::intValue) //
                                            .filter(l -> !coreDead.containsAnyVariable(l))
                                            .distinct() //
                                            .limit(interactionSize) //
                                            .map(l -> c.get(l - 1)) //
                                            .toArray()))
                                    .collect(Collectors.toList());
                            faultyInteractionsUpdated = faultyInteractions.stream()
                                    .map(globalUpdater::update)
                                    .filter(Optional::isPresent)
                                    .map(Optional::get)
                                    .collect(Collectors.toList());

                            for (Double fpNoiseValue : interactionFinderEvaluator.fpNoiseProperty.getValue()) {
                                fpNoise = fpNoiseValue;
                                for (Double fnNoiseValue : interactionFinderEvaluator.fnNoiseProperty.getValue()) {
                                    fnNoise = fnNoiseValue;

                                    ConfigurationOracle verifier = new ConfigurationOracle(
                                            faultyInteractions,
                                            interactionFinderEvaluator
                                                    .fpNoiseProperty
                                                    .getValue()
                                                    .get(0),
                                            interactionFinderEvaluator
                                                    .fnNoiseProperty
                                                    .getValue()
                                                    .get(0));

                                    algorithmLoop:
                                    for (algorithmIndex = 0; algorithmIndex < algorithmList.size(); algorithmIndex++) {
                                        InteractionFinder algorithm = algorithmList.get(algorithmIndex);
                                        for (Integer configCreationLimitValue :
                                                interactionFinderEvaluator.configCreationLimitProperty.getValue()) {
                                            configCreationLimit = configCreationLimitValue;
                                            for (Integer configVerificationLimitValue :
                                                    interactionFinderEvaluator.configVerificationLimitProperty
                                                            .getValue()) {
                                                configVerificationLimit = configVerificationLimitValue;
                                                for (Integer tValue : interactionFinderEvaluator.tProperty.getValue()) {
                                                    t = tValue;
                                                    algorithm.setConfigurationCreationLimit(configCreationLimit);
                                                    algorithm.setConfigurationVerificationLimit(
                                                            configVerificationLimit);
                                                    algorithm.setCore(coreDead);
                                                    algorithm.setVerifier(verifier);

                                                    for (algorithmIteration = 1;
                                                            algorithmIteration
                                                                    <= evaluator.algorithmIterations.getValue();
                                                            algorithmIteration++) {
                                                        runID++;

                                                        evaluator.tabFormatter.setTabLevel(2);
                                                        logRun();
                                                        evaluator.tabFormatter.setTabLevel(3);

                                                        algorithm.reset();
                                                        algorithm.setUpdater(new RandomConfigurationUpdater(
                                                                model,
                                                                new Random(evaluator.randomSeed.getValue()
                                                                        + evaluator.systemIteration)));
                                                        algorithm.addConfigurations(faultyConfigs);

                                                        String sampleFileName = interactionFinderEvaluator.getSystemID()
                                                                + "_" + interactionFinderEvaluator.systemIteration + "_"
                                                                + algorithmIndex + "_" + algorithmIteration + "_"
                                                                + runID + "_sample." + sampleFormat.getFileExtension();
                                                        try {
                                                            long startTime = System.nanoTime();
                                                            foundInteractions = algorithm.find(t);
                                                            long endTime = System.nanoTime();

                                                            if (foundInteractions != null) {
                                                                foundInteractionsMerged =
                                                                        LiteralList.merge(foundInteractions);
                                                                foundInteractionsMergedAndUpdated = globalUpdater
                                                                        .update(foundInteractionsMerged)
                                                                        .orElse(null);
                                                            } else {
                                                                foundInteractionsMerged = null;
                                                                foundInteractionsMergedAndUpdated = null;
                                                            }
                                                            // if (t >= interactionSize
                                                            // &&
                                                            // (!faultyInteractionsUpdated.get(0).containsAll(
                                                            // foundInteractionsMergedAndUpdated)
                                                            // ||
                                                            // !foundInteractionsMergedAndUpdated.containsAll(
                                                            // faultyInteractionsUpdated.get(0)))) {
                                                            // Logger.logInfo(faultyInteractionsUpdated.get(0));
                                                            // Logger.logInfo(foundInteractionsMergedAndUpdated);
                                                            // throw new RuntimeException();
                                                            // }
                                                            List<Statistic> statistics = algorithm.getStatistics();
                                                            lastStatistic = statistics.get(statistics.size() - 1);
                                                            elapsedTimeInMS = (endTime - startTime) / 1_000_000;

                                                            runDataWriter.writeLine();
                                                            for (Statistic s : statistics) {
                                                                statistic = s;
                                                                iterationDataWriter.writeLine();
                                                            }
                                                            // final SolutionList sample =
                                                            // new SolutionList(variables, algorithm.getSample());
                                                            // if (sample != null) {
                                                            // IO.save(
                                                            // sample,
                                                            // interactionFinderEvaluator.outputPath.resolve(
                                                            // sampleFileName),
                                                            // sampleFormat);
                                                            // }
                                                        } catch (final Exception e) {
                                                            Logger.logError(
                                                                    "Could not save sample file " + sampleFileName);
                                                            Logger.logError(e);
                                                            continue algorithmLoop;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                evaluator.tabFormatter.setTabLevel(0);
            }
            Logger.logInfo("Finished");
        } else {
            Logger.logInfo("Nothing to do");
        }
    }

    private boolean readModel(final ModelReader<Formula> mr) {
        model = mr.read(interactionFinderEvaluator.getSystemName())
                .map(ModelRepresentation::new)
                .orElse(Logger::logProblems);
        if (model == null) {
            Logger.logError("Could not read file " + interactionFinderEvaluator.getSystemName());
            return false;
        }
        modelWriter.writeLine();
        model.get(CNFProvider.fromFormula());
        return true;
    }

    protected void prepareAlgorithms() {
        algorithmList = new ArrayList<>();
        algorithmNameList = new ArrayList<>();

        algorithmIndex = 0;
        for (final String algorithmName : interactionFinderEvaluator.algorithmsProperty.getValue()) {
            InteractionFinder interactionFinderRandom;
            switch (algorithmName) {
                case "NaiveRandom": {
                    interactionFinderRandom =
                            new InteractionFinderWrapper(new NaiveRandomInteractionFinder(), true, false);
                    break;
                }
                case "Single": {
                    interactionFinderRandom = new InteractionFinderWrapper(new SingleInteractionFinder(), true, false);
                    break;
                }
                case "IterativeNaiveRandom": {
                    interactionFinderRandom =
                            new InteractionFinderWrapper(new NaiveRandomInteractionFinder(), true, true);
                    break;
                }
                case "IterativeSingle": {
                    interactionFinderRandom = new InteractionFinderWrapper(new SingleInteractionFinder(), true, true);
                    break;
                }
                case "ForwardBackward": {
                    interactionFinderRandom = new InteractionFinderCombinationForwardBackward();
                    break;
                }
                default:
                    continue;
            }
            algorithmList.add(interactionFinderRandom);
            algorithmNameList.add(algorithmName);
            algorithmWriter.writeLine();
            algorithmIndex++;
        }
        algorithmIndex = 0;
    }

    protected void writeModel(CSVWriter modelCSVWriter) {
        modelCSVWriter.addValue(interactionFinderEvaluator.getSystemID());
        modelCSVWriter.addValue(interactionFinderEvaluator.getSystemName());
        CNF cnf = model.get(CNFProvider.fromFormula());
        modelCSVWriter.addValue(cnf.getVariableMap().getVariableCount());
        modelCSVWriter.addValue(cnf.getClauses().size());
    }

    protected void writeAlgorithm(CSVWriter algorithmCSVWriter) {
        algorithmCSVWriter.addValue(algorithmIndex);
        algorithmCSVWriter.addValue(algorithmNameList.get(algorithmIndex));
    }

    protected void writeRunData(CSVWriter dataCSVWriter) {
        dataCSVWriter.addValue(interactionFinderEvaluator.getSystemID());
        dataCSVWriter.addValue(interactionFinderEvaluator.systemIteration);
        dataCSVWriter.addValue(algorithmIndex);
        dataCSVWriter.addValue(algorithmIteration);

        dataCSVWriter.addValue(runID);
        dataCSVWriter.addValue(t);
        dataCSVWriter.addValue(interactionSize);
        // dataCSVWriter.addValue(interactionCount);
        dataCSVWriter.addValue(str(faultyInteractions));
        dataCSVWriter.addValue(str(faultyInteractionsUpdated));
        // dataCSVWriter.addValue(fpNoise);
        // dataCSVWriter.addValue(fnNoise);
        // dataCSVWriter.addValue(configVerificationLimit);
        // dataCSVWriter.addValue(configCreationLimit);

        // dataCSVWriter.addValue(str(foundInteractions));
        // dataCSVWriter.addValue(str(foundInteractionsUpdated));
        if (foundInteractions != null) {
            dataCSVWriter.addValue(foundInteractions.size());
            dataCSVWriter.addValue(str(foundInteractionsMergedAndUpdated));
            dataCSVWriter.addValue(
                    faultyInteractionsUpdated.get(0).containsAll(foundInteractionsMergedAndUpdated) ? "T" : "F");
            dataCSVWriter.addValue(
                    foundInteractionsMergedAndUpdated.containsAll(faultyInteractionsUpdated.get(0)) ? "T" : "F");
            dataCSVWriter.addValue(foundInteractionsMerged.containsAll(faultyInteractions.get(0)) ? "T" : "F");
            dataCSVWriter.addValue(faultyInteractions.get(0).containsAll(foundInteractionsMerged) ? "T" : "F");
            dataCSVWriter.addValue(
                    foundInteractions.stream().anyMatch(i -> i.containsAll(faultyInteractions.get(0))) ? "T" : "F");
            dataCSVWriter.addValue(
                    foundInteractions.stream()
                                    .anyMatch(i -> faultyInteractions.get(0).containsAll(i))
                            ? "T"
                            : "F");

            dataCSVWriter.addValue(foundInteractionsMergedAndUpdated.countNonNull());
            dataCSVWriter.addValue(faultyInteractionsUpdated
                    .get(0)
                    .retainAll(foundInteractionsMergedAndUpdated)
                    .countNonNull());
            dataCSVWriter.addValue(faultyInteractionsUpdated
                    .get(0)
                    .removeAll(foundInteractionsMergedAndUpdated)
                    .countNonNull());
            dataCSVWriter.addValue(foundInteractionsMergedAndUpdated
                    .removeAll(faultyInteractionsUpdated.get(0))
                    .countNonNull());
        } else {
            dataCSVWriter.addValue(-1);
            dataCSVWriter.addValue("null");
            dataCSVWriter.addValue("N");
            dataCSVWriter.addValue("N");
            dataCSVWriter.addValue("N");
            dataCSVWriter.addValue("N");
            dataCSVWriter.addValue("N");
            dataCSVWriter.addValue("N");
            dataCSVWriter.addValue(-1);
            dataCSVWriter.addValue(-1);
            dataCSVWriter.addValue(-1);
            dataCSVWriter.addValue(-1);
        }
        dataCSVWriter.addValue(lastStatistic.getVerifyCounter());
        dataCSVWriter.addValue(elapsedTimeInMS);
    }

    protected void writeIterationData(CSVWriter dataCSVWriter) {
        dataCSVWriter.addValue(runID);
        dataCSVWriter.addValue(statistic.getT());
        dataCSVWriter.addValue(statistic.getIterationCounter());
        dataCSVWriter.addValue(statistic.getInteractionCounter());
        dataCSVWriter.addValue(statistic.getVerifyCounter());
    }

    private void logRun() {
        final StringBuilder sb = new StringBuilder();
        sb.append(interactionFinderEvaluator.getSystemName());
        sb.append(" (");
        sb.append(interactionFinderEvaluator.systemIndex + 1);
        sb.append("/");
        sb.append(interactionFinderEvaluator.systemNames.size());
        sb.append(") ");
        sb.append(interactionFinderEvaluator.systemIteration);
        sb.append("/");
        sb.append(interactionFinderEvaluator.systemIterations.getValue());
        sb.append(" | ");
        sb.append(faultyInteractions);
        sb.append(" | ");
        sb.append(algorithmNameList.get(algorithmIndex));
        sb.append(" (");
        sb.append(algorithmIndex + 1);
        sb.append("/");
        sb.append(algorithmList.size());
        sb.append(") ");
        sb.append(algorithmIteration);
        sb.append("/");
        sb.append(interactionFinderEvaluator.algorithmIterations.getValue());
        sb.append(" | (");
        sb.append(t);
        sb.append(", ");
        sb.append(configVerificationLimit);
        sb.append(", ");
        sb.append(configCreationLimit);
        sb.append(", ");
        sb.append(fpNoise);
        sb.append(", ");
        sb.append(fnNoise);
        sb.append(")");
        Logger.logInfo(sb.toString());
    }

    private String str(List<LiteralList> interactions) {
        StringBuilder sb = new StringBuilder();
        interactions.forEach(i -> sb.append(str(i)));
        return sb.toString();
    }

    private String str(LiteralList interaction) {
        return Arrays.toString(interaction.getLiterals());
    }

    private RandomConfigurationGenerator getConfigGenerator(Random random) {
        RandomConfigurationGenerator generator;
        generator = new FastRandomConfigurationGenerator();
        generator.setAllowDuplicates(false);
        generator.setRandom(random);
        generator.setLimit(interactionCount);
        return generator;
    }
}
