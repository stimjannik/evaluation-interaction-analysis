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
package de.featjar.evaluation.interactionfinder.phase;

import de.featjar.analysis.sat4j.computation.ComputeCoreSAT4J;
import de.featjar.analysis.sat4j.computation.ComputeSolutionSAT4J;
import de.featjar.base.FeatJAR;
import de.featjar.base.cli.ListOption;
import de.featjar.base.cli.Option;
import de.featjar.base.computation.Computations;
import de.featjar.base.data.Result;
import de.featjar.base.io.IO;
import de.featjar.base.io.csv.CSVFile;
import de.featjar.evaluation.Evaluator;
import de.featjar.formula.VariableMap;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanClauseList;
import de.featjar.formula.assignment.BooleanSolution;
import de.featjar.formula.io.csv.BooleanAssignmentGroupsCSVFormat;
import de.featjar.formula.io.dimacs.BooleanAssignmentGroupsDimacsFormat;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.IntStream;

/**
 * @author Sebastian Krieter
 */
public class CreateInteractionsPhase extends Evaluator {

    public static final ListOption<Integer> interactionSizeOption =
            new ListOption<>("interactionSize", Option.IntegerParser);
    public static final ListOption<Integer> interactionCountOption =
            new ListOption<>("interactionCount", Option.IntegerParser);

    private BooleanClauseList cnf;
    private BooleanSolution core;
    private Long randomSeed;
    private String modelName;
    private int modelID, modelIteration, interactionSize, interactionCount;
    private List<int[]> randomizedLiterals;
    private VariableMap variables;
    private CSVFile interactionsCSV;
    private int interactionID;

    @Override
    public List<Option<?>> getOptions() {
        ArrayList<Option<?>> options = new ArrayList<>(super.getOptions());
        options.add(interactionSizeOption);
        options.add(interactionCountOption);
        return options;
    }

    @Override
    public void runEvaluation() {
        try {
            interactionsCSV = new CSVFile(csvPath.resolve("interactions_gen.csv"));
            interactionsCSV.setHeaderFields(
                    "ModelID", "ModelIt", "Source", "InteractionCount", "InteractionSize", "InteractionID");
            interactionsCSV.flush();
            randomSeed = getOption(Evaluator.randomSeed);
            optionCombiner.init(systemsOption, systemIterationsOption, interactionCountOption, interactionSizeOption);
            optionCombiner.loopOverOptions(this::optionLoop);
        } catch (IOException e) {
            FeatJAR.log().error(e);
        }
    }

    private int optionLoop(int lastChanged) {
        switch (lastChanged) {
            case 0: {
                modelName = optionCombiner.getValue(0);
                modelID = systemNames.indexOf(modelName);
                Result<BooleanAssignmentGroups> load = IO.load(
                        genPath.resolve(modelName).resolve("cnf.dimacs"), new BooleanAssignmentGroupsDimacsFormat());
                if (load.isEmpty()) {
                    FeatJAR.log().problems(load.getProblems());
                    return 0;
                } else {
                    BooleanAssignmentGroups space = load.get();
                    variables = space.getVariableMap();
                    cnf = new BooleanClauseList(space.getGroups().get(0), variables.getVariableCount());
                }
                Result<BooleanAssignmentGroups> load2 = IO.load(
                        genPath.resolve(modelName).resolve("core.dimacs"), new BooleanAssignmentGroupsDimacsFormat());
                if (load2.isEmpty()) {
                    FeatJAR.log().problems(load2.getProblems());
                    return 0;
                } else {
                    BooleanAssignmentGroups space = load2.get();
                    core = space.getGroups().get(0).get(0).toSolution();
                }
                interactionID = 0;
            }
            case 1:
                modelIteration = optionCombiner.getValue(1);
                BooleanSolution solution = Computations.of(cnf)
                        .map(ComputeSolutionSAT4J::new)
                        .set(ComputeSolutionSAT4J.RANDOM_SEED, randomSeed + modelIteration)
                        .compute();
                int maxInteractionCount = getOption(interactionCountOption).stream()
                        .mapToInt(i -> i)
                        .max()
                        .getAsInt();
                int maxInteractionSize = getOption(interactionSizeOption).stream()
                        .mapToInt(i -> i)
                        .max()
                        .getAsInt();
                randomizedLiterals = new ArrayList<>(maxInteractionCount);
                long shuffleSeed = new Random(randomSeed + modelIteration).nextLong();
                for (int i = 0; i <= maxInteractionCount; i++) {
                    Random shuffleRandom = new Random(shuffleSeed + i);
                    int[] li = IntStream.generate(() -> (shuffleRandom.nextInt(solution.size()) + 1))
                            .filter(l -> !core.containsAnyVariable(l)) //
                            .distinct() //
                            .limit(maxInteractionSize) //
                            .map(l -> solution.get(l - 1)) //
                            .toArray();
                    randomizedLiterals.add(li);
                }
                try {
                    IO.save(
                            new BooleanAssignmentGroups(variables, List.of(List.of(solution))),
                            genPath.resolve(modelName)
                                    .resolve("samples")
                                    .resolve(String.format("sol_gs%d.csv", modelIteration)),
                            new BooleanAssignmentGroupsCSVFormat());
                } catch (IOException e) {
                    FeatJAR.log().error(e);
                    return 1;
                }
            case 2:
                interactionCount = optionCombiner.getValue(2);
            case 3:
                interactionSize = optionCombiner.getValue(3);
                ArrayList<BooleanAssignment> interactions = new ArrayList<>(interactionCount);
                ArrayList<BooleanAssignment> updatedInteractions = new ArrayList<>(interactionCount);
                for (int i = 0; i < interactionCount; i++) {
                    BooleanAssignment e =
                            new BooleanAssignment(Arrays.copyOf(randomizedLiterals.get(i), interactionSize));
                    interactions.add(e);
                    updatedInteractions.add(Computations.of(cnf)
                            .map(ComputeCoreSAT4J::new)
                            .set(ComputeCoreSAT4J.ASSUMED_ASSIGNMENT, e)
                            .compute());
                }
                try {
                    IO.save(
                            new BooleanAssignmentGroups(variables, List.of(interactions)),
                            genPath.resolve(modelName)
                                    .resolve("interactions")
                                    .resolve(String.format("int_g%d_gs%d.dimacs", interactionID, modelIteration)),
                            new BooleanAssignmentGroupsDimacsFormat());
                    IO.save(
                            new BooleanAssignmentGroups(variables, List.of(updatedInteractions)),
                            genPath.resolve(modelName)
                                    .resolve("interactions")
                                    .resolve(String.format("uint_g%d_gs%d.dimacs", interactionID, modelIteration)),
                            new BooleanAssignmentGroupsDimacsFormat());
                    CSVFile.writeCSV(interactionsCSV, w -> {
                        w.add(modelID);
                        w.add(modelIteration);
                        w.add("g");
                        w.add(interactionCount);
                        w.add(interactionSize);
                        w.add(String.format("g%d", interactionID));
                    });
                    interactionID++;
                } catch (IOException e) {
                    FeatJAR.log().error(e);
                    return 3;
                }
            default:
        }
        return -1;
    }
}
