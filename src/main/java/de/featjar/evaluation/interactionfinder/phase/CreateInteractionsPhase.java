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
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentSpace;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.sat4j.ComputeCoreDeadVariablesSAT4J;
import de.featjar.formula.analysis.sat4j.ComputeSolutionSAT4J;
import de.featjar.formula.io.csv.BooleanAssignmentSpaceCSVFormat;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.IntStream;

/**
 * @author Sebastian Krieter
 */
public class CreateInteractionsPhase implements EvaluationPhase<InteractionFinderEvaluator> {

    private BooleanClauseList cnf;
    private BooleanSolution core;
    private Long randomSeed;
    private String modelName;
    private int modelID, modelIteration, interactionSize, interactionCount;
    private List<int[]> randomizedLiterals;
    private VariableMap variables;
    private CSVFile interactionsCSV;
    private int interactionID;

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
                    core = space.getGroups().get(1).get(0).toSolution();
                }
                interactionID = 0;
            case 1:
                modelIteration = evaluator.cast(1);
                BooleanSolution solution = Computations.of(cnf)
                        .map(ComputeSolutionSAT4J::new)
                        .set(ComputeSolutionSAT4J.RANDOM_SEED, randomSeed + modelIteration)
                        .compute();
                //			int[] solutionLiterals = solution.get();
                int maxInteractionCount =
                        evaluator.getOption(InteractionFinderEvaluator.interactionCountOption).stream()
                                .mapToInt(i -> i)
                                .max()
                                .getAsInt();
                int maxInteractionSize = evaluator.getOption(InteractionFinderEvaluator.interactionSizeOption).stream()
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
                            new BooleanAssignmentSpace(variables, List.of(List.of(solution))),
                            evaluator
                                    .outputPath
                                    .resolve(modelName)
                                    .resolve("samples")
                                    .resolve(String.format("sol_gs%d.csv", modelIteration)),
                            new BooleanAssignmentSpaceCSVFormat());
                } catch (IOException e) {
                    FeatJAR.log().error(e);
                }
            case 2:
                interactionCount = evaluator.cast(2);
            case 3:
                interactionSize = evaluator.cast(3);
                ArrayList<BooleanAssignment> interactions = new ArrayList<>(interactionCount);
                ArrayList<BooleanAssignment> updatedInteractions = new ArrayList<>(interactionCount);
                for (int i = 0; i < interactionCount; i++) {
                    BooleanAssignment e =
                            new BooleanAssignment(Arrays.copyOf(randomizedLiterals.get(i), interactionSize));
                    interactions.add(e);
                    updatedInteractions.add(Computations.of(cnf)
                            .map(ComputeCoreDeadVariablesSAT4J::new)
                            .set(ComputeCoreDeadVariablesSAT4J.ASSUMED_ASSIGNMENT, e)
                            .compute());
                }
                try {
                    IO.save(
                            new BooleanAssignmentSpace(variables, List.of(interactions, updatedInteractions)),
                            evaluator
                                    .outputPath
                                    .resolve(modelName)
                                    .resolve("interactions")
                                    .resolve(String.format("int_g%d_gs%d.csv", interactionID, modelIteration)),
                            new BooleanAssignmentSpaceCSVFormat());
                    evaluator.writeCSV(interactionsCSV, w -> {
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
                }
            default:
        }
    }

    @Override
    public void run(InteractionFinderEvaluator evaluator) {
        try {
            interactionsCSV = new CSVFile(evaluator.csvPath.resolve("interactions_gen.csv"));
            interactionsCSV.setHeaderFields(
                    "ModelID", "ModelIt", "Source", "InteractionCount", "InteractionSize", "InteractionID");
            interactionsCSV.flush();
            randomSeed = evaluator.getOption(Evaluator.randomSeed);
            evaluator.optionLoop(
                    this,
                    InteractionFinderEvaluator.systemsOption,
                    InteractionFinderEvaluator.systemIterationsOption,
                    InteractionFinderEvaluator.interactionCountOption,
                    InteractionFinderEvaluator.interactionSizeOption);
        } catch (IOException e) {
            FeatJAR.log().error(e);
        }
    }
}
