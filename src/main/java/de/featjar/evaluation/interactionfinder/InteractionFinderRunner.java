/*
 * Copyright (C) 2024 FeatJAR-Development-Team
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

import de.featjar.analysis.sat4j.computation.ComputeCoreSAT4J;
import de.featjar.analysis.sat4j.computation.RandomConfigurationUpdater;
import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Cache;
import de.featjar.base.computation.Computations;
import de.featjar.base.data.IntegerList;
import de.featjar.base.io.IO;
import de.featjar.base.log.Log;
import de.featjar.formula.computation.interactionfinder.*;
import de.featjar.formula.assignment.ABooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanClause;
import de.featjar.formula.assignment.BooleanClauseList;
import de.featjar.formula.io.csv.BooleanAssignmentGroupsCSVFormat;
import de.featjar.formula.io.dimacs.BooleanAssignmentGroupsDimacsFormat;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
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
        private Exception error = null;

        private AInteractionFinder algorithm;
        private int t;

        private boolean finished;

        @Override
        public void run() {
            long startTime = System.nanoTime();
            try {
                foundInteractions = algorithm.find(t);
            } catch (Exception e) {
                error = e;
            }
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
                FeatJAR.configure()
                        .log(c -> c.logToSystemOut(Log.Verbosity.MESSAGE))
                        .log(c -> c.logToSystemErr(Log.Verbosity.ERROR))
                        .cache(c -> c.setCachePolicy(Cache.CachePolicy.CACHE_NONE))
                        .initialize();
            }

            FinderThread thread = new FinderThread();

            BooleanAssignmentGroups model = loadDimacs(args[0]);
            BooleanClauseList cnf = model.toClauseList();
            BooleanAssignmentGroups core = loadDimacs(args[1]);
            BooleanAssignmentGroups sample = loadDimacs(args[2]);
            BooleanAssignmentGroups interaction = loadDimacs(args[3]);
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
            List<BooleanAssignment> interactions = new ArrayList<>();
            if (thread.isFinished()) {
                if (thread.foundInteractions != null) {
                    BooleanAssignment foundInteractionsMerged =
                            new BooleanAssignment(IntegerList.merge(thread.foundInteractions));
                    interactions.add(foundInteractionsMerged);
                    interactions.add(Computations.of(cnf)
                            .map(ComputeCoreSAT4J::new)
                            .set(ComputeCoreSAT4J.ASSUMED_ASSIGNMENT, foundInteractionsMerged)
                            .compute());
                    interactions.addAll(thread.foundInteractions);
                } else {
                    interactions.add(null);
                    interactions.add(null);
                    interactions.add(null);
                }
                writeResults(
                        outputPath,
                        thread.algorithm.getVerifyCounter(),
                        thread.elapsedTimeInMS,
                        false,
                        thread.error != null,
                        interactions);
            } else {
                interactions.add(null);
                interactions.add(null);
                interactions.add(null);
                writeResults(outputPath, -1, -1, true, false, interactions);
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
            boolean timeout,
            boolean error,
            List<BooleanAssignment> interactions)
            throws IOException {
        StringBuilder sb = new StringBuilder();
        write(elapsedTimeInMS, sb);
        write(verifyCounter, sb);
        write(timeout, sb);
        write(error, sb);
        for (BooleanAssignment foundInteraction : interactions) {
            if (foundInteraction == null) {
                write(null, sb);
            } else {
                writeAssignment(sb, foundInteraction);
            }
        }
        Files.writeString(outputPath, sb.toString());
    }

    private static void write(Object object, StringBuilder sb) {
        sb.append(String.valueOf(object));
        sb.append("\n");
    }

    private static void writeAssignment(StringBuilder sb, BooleanAssignment foundInteraction) {
        for (int l : foundInteraction.get()) {
            sb.append(l);
            sb.append(";");
        }
        sb.replace(sb.length() - 1, sb.length(), "\n");
    }

    private static BooleanAssignmentGroups loadDimacs(String path) {
        if (path.endsWith(".csv")) {
            return IO.load(Paths.get(path), new BooleanAssignmentGroupsCSVFormat())
                    .orElseThrow();
        } else if (path.endsWith(".dimacs")) {
            return IO.load(Paths.get(path), new BooleanAssignmentGroupsDimacsFormat())
                    .orElseThrow();
        } else {
            throw new RuntimeException("Unkown file format");
        }
    }

    public static BooleanClause parseLiteralList(String arg) {
        return ("null".equals(arg))
                ? new BooleanClause()
                : new BooleanClause(Arrays.stream(arg.split(";"))
                        .mapToInt(Integer::parseInt)
                        .toArray());
    }

    private static AInteractionFinder parseAlgorithm(String algorithm) {
        switch (algorithm) {
            case "inciident": {
                return new IncInteractionFinder();
            }
            case "random": {
                return new RandomInteractionFinder();
            }
            case "dominant_bug": {
                return new IncInteractionFinderDominantBug();
            }
            case "only_working_configurations": {
                return new IncInteractionFinderOnlyWorkingConfigurations();
            }
            case "repeat": {
                return new IncInteractionFinderRepeat();
            }
            default:
                throw new IllegalArgumentException(algorithm);
        }
    }
}
