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
import de.featjar.base.computation.Computations;
import de.featjar.base.data.IntegerList;
import de.featjar.base.io.IO;
import de.featjar.base.log.Log;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentSpace;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.combinations.IncInteractionFinder;
import de.featjar.formula.analysis.sat4j.ComputeCoreDeadVariablesSAT4J;
import de.featjar.formula.analysis.sat4j.RandomConfigurationUpdater;
import de.featjar.formula.io.csv.BooleanAssignmentSpaceCSVFormat;
import de.featjar.formula.io.dimacs.BooleanAssignmentSpaceDimacsFormat;
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

    private static class FinderThread extends Thread {

        private List<BooleanAssignment> foundInteractions;
        private long elapsedTimeInMS = -1;

        private IncInteractionFinder algorithm;
        private int t;

        private boolean finished;

        @Override
        public void run() {
            long startTime = System.nanoTime();
            foundInteractions = algorithm.find(t);
            long endTime = System.nanoTime();
            elapsedTimeInMS = (endTime - startTime) / 1_000_000;
            synchronized (this) {
                finished = true;
            }
        }

        public boolean isFinished() {
            synchronized (this) {
                return finished;
            }
        }
    }

    public static void main(String[] args) throws IOException {
        boolean standalone = !FeatJAR.isInitialized();
        try {
            if (standalone) {
                final Configuration configuration = new Configuration();
                configuration.logConfig.logAtMost(Log.Verbosity.ERROR);
                configuration.cacheConfig.setCachePolicy(Cache.CachePolicy.CACHE_NONE);
                FeatJAR.initialize(configuration);
            }

            FinderThread thread = new FinderThread();

            BooleanAssignmentSpace model = loadDimacs(args[0]);
            BooleanClauseList cnf = model.toClauseList();
            BooleanAssignmentSpace core = loadDimacs(args[1]);
            BooleanAssignmentSpace sample = loadDimacs(args[2]);
            BooleanAssignmentSpace interaction = loadDimacs(args[3]);
            Path outputPath = Paths.get(args[4]);

            thread.algorithm = parseAlgorithm(args[5]);
            thread.t = Integer.parseInt(args[6]);
            Long seed = Long.parseLong(args[7]);

            Double fpNoise = Double.parseDouble(args[8]);
            Double fnNoise = Double.parseDouble(args[9]);
            Long timeout = Long.parseLong(args[10]);

            thread.algorithm.reset();
            thread.algorithm.setCore(core.getGroups().get(0).get(0).toClause());
            thread.algorithm.setVerifier(
                    new ConfigurationOracle(interaction.toClauseList(0).getAll(), fpNoise, fnNoise));
            thread.algorithm.setUpdater(new RandomConfigurationUpdater(cnf, seed));
            List<? extends ABooleanAssignment> list = sample.getGroups().get(0);
            thread.algorithm.addConfigurations(list);

            thread.start();
            try {
                thread.join(timeout);
            } catch (InterruptedException e) {
            }
            if (thread.isFinished()) {
                BooleanAssignment foundInteractionsMerged, foundInteractionsMergedAndUpdated;
                if (thread.foundInteractions != null) {
                    foundInteractionsMerged = new BooleanAssignment(IntegerList.merge(thread.foundInteractions));
                    foundInteractionsMergedAndUpdated = Computations.of(cnf)
                            .map(ComputeCoreDeadVariablesSAT4J::new)
                            .set(ComputeCoreDeadVariablesSAT4J.ASSUMED_ASSIGNMENT, foundInteractionsMerged)
                            .compute();
                } else {
                    foundInteractionsMerged = null;
                    foundInteractionsMergedAndUpdated = null;
                }
                writeResults(
                        outputPath,
                        thread.algorithm.getVerifyCounter(),
                        thread.elapsedTimeInMS,
                        thread.foundInteractions,
                        foundInteractionsMerged,
                        foundInteractionsMergedAndUpdated);
            } else {
                writeResults(outputPath, -1, -1, null, null, null);
            }
            if (standalone) {
                System.exit(0);
            }
        } catch (Exception e) {
            e.printStackTrace();
            if (standalone) {
                System.exit(1);
            }
        }
    }

    private static void writeResults(
            Path outputPath,
            int verifyCounter,
            long elapsedTimeInMS,
            List<BooleanAssignment> foundInteractions,
            BooleanAssignment foundInteractionsMerged,
            BooleanAssignment foundInteractionsMergedAndUpdated)
            throws IOException {
        StringBuilder sb = new StringBuilder();
        sb.append(elapsedTimeInMS);
        sb.append("\n");
        sb.append(verifyCounter);
        sb.append("\n");
        if (foundInteractionsMerged != null) {
            writeAssignment(sb, foundInteractionsMerged);
        } else {
            sb.append("null\n");
        }
        if (foundInteractionsMergedAndUpdated != null) {
            writeAssignment(sb, foundInteractionsMergedAndUpdated);
        } else {
            sb.append("null\n");
        }
        if (foundInteractions != null) {
            for (BooleanAssignment foundInteraction : foundInteractions) {
                writeAssignment(sb, foundInteraction);
            }
            if (!foundInteractions.isEmpty()) {
                sb.delete(sb.length() - 1, sb.length());
            }
        } else {
            sb.append("null");
        }
        Files.writeString(outputPath, sb.toString());
    }

    private static void writeAssignment(StringBuilder sb, BooleanAssignment foundInteraction) {
        for (int l : foundInteraction.get()) {
            sb.append(l);
            sb.append(";");
        }
        sb.replace(sb.length() - 1, sb.length(), "\n");
    }

    private static BooleanAssignmentSpace loadDimacs(String path) {
        if (path.endsWith(".csv")) {
            return IO.load(Paths.get(path), new BooleanAssignmentSpaceCSVFormat())
                    .orElseThrow();
        } else if (path.endsWith(".dimacs")) {
            return IO.load(Paths.get(path), new BooleanAssignmentSpaceDimacsFormat())
                    .orElseThrow();
        } else {
            throw new RuntimeException("Unkown file format");
        }
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
