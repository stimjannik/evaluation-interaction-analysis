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

import de.featjar.analysis.sat4j.RandomConfigurationUpdater;
import de.featjar.clauses.LiteralList;
import de.featjar.clauses.solutions.analysis.InteractionFinder;
import de.featjar.clauses.solutions.analysis.InteractionFinder.Statistic;
import de.featjar.clauses.solutions.analysis.InteractionFinderWrapper;
import de.featjar.clauses.solutions.analysis.finder.InteractionFinderCombinationForwardBackward;
import de.featjar.clauses.solutions.analysis.finder.InteractionFinderCombinationForwardBackwardOld;
import de.featjar.clauses.solutions.analysis.finder.NaiveRandomInteractionFinder;
import de.featjar.clauses.solutions.analysis.finder.SingleInteractionFinder;
import de.featjar.clauses.solutions.io.ListFormat;
import de.featjar.formula.ModelRepresentation;
import de.featjar.util.extension.ExtensionLoader;
import de.featjar.util.io.IO;
import de.featjar.util.logging.Logger;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

/**
 * Command line interface for interaction finder evaluation.
 *
 * @author Sebastian Krieter
 */
public class InteractionFinderRunner {

    public static void main(String[] args) throws IOException {
        ExtensionLoader.load();

        ModelRepresentation model = ModelRepresentation.load(Paths.get(args[0])).orElse(Logger::logProblems);
        List<LiteralList> sample = IO.load(Paths.get(args[1]), new ListFormat())
                .orElse(Logger::logProblems)
                .getSolutions();
        Path outputPath = Paths.get(args[2]);
        InteractionFinder algorithm = parseAlgorithm(args[3]);
        int t = Integer.parseInt(args[4]);
        LiteralList core = parseLiteralList(args[5]);
        Long seed = Long.parseLong(args[6]);

        List<LiteralList> interactions = Arrays.stream(args[7].split(","))
                .map(InteractionFinderRunner::parseLiteralList)
                .collect(Collectors.toList());

        Double fpNoise = Double.parseDouble(args[8]);
        Double fnNoise = Double.parseDouble(args[9]);

        algorithm.reset();
        algorithm.setCore(core);
        algorithm.setVerifier(new ConfigurationOracle(interactions, fpNoise, fnNoise));
        algorithm.setUpdater(new RandomConfigurationUpdater(model, new Random(seed)));
        algorithm.addConfigurations(sample);

        long startTime = System.nanoTime();
        List<LiteralList> foundInteractions = algorithm.find(t);
        long endTime = System.nanoTime();

        List<Statistic> statistics = algorithm.getStatistics();
        Statistic lastStatistic = statistics.get(statistics.size() - 1);
        long elapsedTimeInMS = (endTime - startTime) / 1_000_000;

        StringBuilder sb = new StringBuilder();
        sb.append(elapsedTimeInMS);
        sb.append("\n");
        sb.append(lastStatistic.getVerifyCounter());
        sb.append("\n");
        if (foundInteractions != null) {
            for (LiteralList foundInteraction : foundInteractions) {
                for (int l : foundInteraction.getLiterals()) {
                    sb.append(l);
                    sb.append(";");
                }
                sb.replace(sb.length() - 1, sb.length(), "\n");
            }
            sb.delete(sb.length() - 1, sb.length());
        } else {
            sb.append("null");
        }
        Files.writeString(outputPath, sb.toString());
        System.exit(0);
    }

    public static LiteralList parseLiteralList(String arg) {
        return ("null".equals(arg))
                ? null
                : new LiteralList(Arrays.stream(arg.split(";"))
                        .mapToInt(Integer::parseInt)
                        .toArray());
    }

    private static InteractionFinder parseAlgorithm(String algorithm) {
        InteractionFinder interactionFinderRandom;
        switch (algorithm) {
            case "NaiveRandom": {
                interactionFinderRandom = new InteractionFinderWrapper(new NaiveRandomInteractionFinder(), true, false);
                break;
            }
            case "IterativeNaiveRandom": {
                interactionFinderRandom = new InteractionFinderWrapper(new NaiveRandomInteractionFinder(), true, true);
                break;
            }
            case "Single": {
                interactionFinderRandom = new InteractionFinderWrapper(new SingleInteractionFinder(), true, false);
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
            case "ForwardBackwardOld": {
                interactionFinderRandom = new InteractionFinderCombinationForwardBackwardOld();
                break;
            }
            case "Single2": {
                interactionFinderRandom = new InteractionFinderWrapper(new SingleInteractionFinder(), true, false);
                interactionFinderRandom.setLimitFactor(2);
                break;
            }
            case "IterativeSingle2": {
                interactionFinderRandom = new InteractionFinderWrapper(new SingleInteractionFinder(), true, true);
                interactionFinderRandom.setLimitFactor(2);
                break;
            }
            case "ForwardBackward2": {
                interactionFinderRandom = new InteractionFinderCombinationForwardBackward();
                interactionFinderRandom.setLimitFactor(2);
                break;
            }
            case "ForwardBackwardOld2": {
                interactionFinderRandom = new InteractionFinderCombinationForwardBackwardOld();
                interactionFinderRandom.setLimitFactor(2);
                break;
            }
            case "Single10": {
                interactionFinderRandom = new InteractionFinderWrapper(new SingleInteractionFinder(), true, false);
                interactionFinderRandom.setLimitFactor(10);
                break;
            }
            case "IterativeSingle10": {
                interactionFinderRandom = new InteractionFinderWrapper(new SingleInteractionFinder(), true, true);
                interactionFinderRandom.setLimitFactor(10);
                break;
            }
            case "ForwardBackward10": {
                interactionFinderRandom = new InteractionFinderCombinationForwardBackward();
                interactionFinderRandom.setLimitFactor(10);
                break;
            }
            case "ForwardBackwardOld10": {
                interactionFinderRandom = new InteractionFinderCombinationForwardBackwardOld();
                interactionFinderRandom.setLimitFactor(10);
                break;
            }
            default:
                interactionFinderRandom = null;
        }
        return interactionFinderRandom;
    }
}
