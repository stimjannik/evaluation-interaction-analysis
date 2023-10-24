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
package de.featjar.evaluation.interactionfinder;

import de.featjar.base.FeatJAR;
import de.featjar.base.FeatJAR.Configuration;
import de.featjar.base.computation.Cache;
import de.featjar.base.io.IO;
import de.featjar.base.log.Log;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentSpace;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.analysis.combinations.IncInteractionFinder;
import de.featjar.formula.analysis.sat4j.RandomConfigurationUpdater;
import de.featjar.formula.io.csv.BooleanAssignmentSpaceCSVFormat;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

/**
 * Command line interface for interaction finder evaluation.
 *
 * @author Sebastian Krieter
 */
public class InteractionFinderRunner {

    public static void main(String[] args) throws IOException {
        if (!FeatJAR.isInitialized()) {
            final Configuration configuration = new Configuration();
            configuration.logConfig.logAtMost(Log.Verbosity.ERROR);
            configuration.cacheConfig.setCachePolicy(Cache.CachePolicy.CACHE_TOP_LEVEL);
            FeatJAR.initialize(configuration);
        }

        BooleanAssignmentSpace model = load(args[0]);
        BooleanAssignmentSpace sample = load(args[1]);
        BooleanAssignmentSpace interaction = load(args[2]);
        Path outputPath = Paths.get(args[3]);

        IncInteractionFinder algorithm = parseAlgorithm(args[4]);
        int t = Integer.parseInt(args[5]);
        Long seed = Long.parseLong(args[6]);

        Double fpNoise = Double.parseDouble(args[7]);
        Double fnNoise = Double.parseDouble(args[8]);

        algorithm.reset();
        algorithm.setCore(model.getGroups().get(1).get(0).toClause());
        algorithm.setVerifier(
                new ConfigurationOracle(interaction.toClauseList(0).getAll(), fpNoise, fnNoise));
        algorithm.setUpdater(new RandomConfigurationUpdater(model.toClauseList(), seed));
        List<? extends ABooleanAssignment> list = sample.getGroups().get(0);
        algorithm.addConfigurations(list);

        long startTime = System.nanoTime();
        List<BooleanAssignment> foundInteractions = algorithm.find(t);
        long endTime = System.nanoTime();

        long elapsedTimeInMS = (endTime - startTime) / 1_000_000;

        StringBuilder sb = new StringBuilder();
        sb.append(elapsedTimeInMS);
        sb.append("\n");
        sb.append(algorithm.getVerifyCounter());
        sb.append("\n");
        if (foundInteractions != null) {
            for (BooleanAssignment foundInteraction : foundInteractions) {
                for (int l : foundInteraction.get()) {
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
    }

    private static BooleanAssignmentSpace load(String path) {
        return IO.load(Paths.get(path), new BooleanAssignmentSpaceCSVFormat()).orElseThrow();
    }

    public static BooleanClause parseLiteralList(String arg) {
        return ("null".equals(arg))
                ? null
                : new BooleanClause(Arrays.stream(arg.split(";"))
                        .mapToInt(Integer::parseInt)
                        .toArray());
    }

    private static IncInteractionFinder parseAlgorithm(String algorithm) {
        switch (algorithm) {
            case "inciident": {
                return new IncInteractionFinder();
            }
            case "random": {
                return new RandomInteractionFinder();
            }
            default:
                throw new IllegalArgumentException(algorithm);
        }
    }
}
