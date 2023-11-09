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
import de.featjar.base.data.Pair;
import de.featjar.base.data.Result;
import de.featjar.base.io.IO;
import de.featjar.base.io.csv.CSVFile;
import de.featjar.evaluation.Evaluator;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentSpace;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.BooleanRepresentationComputation;
import de.featjar.formula.analysis.bool.BooleanSolution;
import de.featjar.formula.analysis.bool.IBooleanRepresentation;
import de.featjar.formula.analysis.sat4j.ComputeCoreDeadVariablesSAT4J;
import de.featjar.formula.analysis.sat4j.ComputeSolutionSAT4J;
import de.featjar.formula.io.csv.BooleanAssignmentSpaceCSVFormat;
import de.featjar.formula.io.dimacs.BooleanAssignmentSpaceDimacsFormat;
import de.featjar.formula.io.textual.ExpressionParser;
import de.featjar.formula.io.textual.ExpressionParser.ErrorHandling;
import de.featjar.formula.io.textual.Symbols;
import de.featjar.formula.structure.formula.IFormula;
import de.featjar.formula.transformer.ComputeCNFFormula;
import de.featjar.formula.transformer.ComputeDNFFormula;
import de.featjar.formula.transformer.ComputeNNFFormula;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Sebastian Krieter
 */
public class ReadInteractionsPhase extends Evaluator {

    private int modelID, modelIteration, interactionSize, interactionCount;
    private CSVFile interactionsCSV;

    @Override
    public void runEvaluation() {
        try {
            interactionsCSV = new CSVFile(csvPath.resolve("interactions_real.csv"));
            interactionsCSV.setHeaderFields(
                    "ModelID", "ModelIt", "Source", "InteractionCount", "InteractionSize", "InteractionID");
            interactionsCSV.flush();

            Long randomSeed = getOption(Evaluator.randomSeed);

            final ExpressionParser nodeReader = new ExpressionParser();
            nodeReader.setSymbols(Symbols.JAVA);
            nodeReader.setIgnoreMissingFeatures(ErrorHandling.REMOVE);

            final Path p = resourcePath.resolve("bug_list.csv");
            List<String> lines;
            lines = Files.readAllLines(p);
            modelIteration = 0;
            for (final String line : lines) {
                try {
                    modelIteration++;
                    final String[] values = line.split(";");
                    final String modelName = values[0];
                    modelID = systemNames.indexOf(modelName);
                    Result<BooleanAssignmentSpace> load = IO.load(
                            genPath.resolve(modelName).resolve("cnf.dimacs"), new BooleanAssignmentSpaceDimacsFormat());
                    if (load.isEmpty()) {
                        FeatJAR.log().problems(load.getProblems());
                        return;
                    }
                    BooleanAssignmentSpace space = load.get();
                    VariableMap variables = space.getVariableMap();
                    BooleanClauseList cnf =
                            new BooleanClauseList(space.getGroups().get(0), variables.getVariableCount());

                    final String formulaString = values[5];
                    final IFormula formula =
                            (IFormula) nodeReader.parse(formulaString).orElseThrow();
                    ComputeNNFFormula nnf = Computations.of(formula).map(ComputeNNFFormula::new);
                    Pair<IBooleanRepresentation, VariableMap> pcDnfRep = nnf.map(ComputeDNFFormula::new)
                            .map(BooleanRepresentationComputation::new)
                            .compute();
                    Pair<IBooleanRepresentation, VariableMap> pcCnfRep = nnf.map(ComputeCNFFormula::new)
                            .map(BooleanRepresentationComputation::new)
                            .compute();

                    BooleanClauseList pcCnf =
                            ((BooleanClauseList) pcCnfRep.getKey()).adapt(pcCnfRep.getValue(), variables);
                    BooleanClauseList pcDnf =
                            ((BooleanClauseList) pcDnfRep.getKey()).adapt(pcDnfRep.getValue(), variables);
                    Result<BooleanSolution> computeResult = Computations.of(cnf)
                            .map(ComputeSolutionSAT4J::new)
                            .set(ComputeSolutionSAT4J.RANDOM_SEED, randomSeed + modelIteration)
                            .set(ComputeSolutionSAT4J.ASSUMED_CLAUSE_LIST, pcCnf)
                            .computeResult();
                    if (computeResult.isEmpty()) {
                        FeatJAR.log().problems(computeResult.getProblems());
                    } else {
                        BooleanSolution solution = computeResult.orElse(null);
                        FeatJAR.log().debug(pcDnf);
                        IO.save(
                                new BooleanAssignmentSpace(variables, List.of(List.of(solution))),
                                genPath.resolve(modelName)
                                        .resolve("samples")
                                        .resolve(String.format("sol_rs%d.csv", modelIteration)),
                                new BooleanAssignmentSpaceCSVFormat());
                        interactionCount = pcDnf.size();
                        interactionSize =
                                pcDnf.stream().mapToInt(c -> c.size()).max().getAsInt();
                        ArrayList<BooleanAssignment> updatedInteractions = new ArrayList<>(interactionCount);
                        for (BooleanClause clause : pcDnf.getAll()) {
                            updatedInteractions.add(Computations.of(cnf)
                                    .map(ComputeCoreDeadVariablesSAT4J::new)
                                    .set(ComputeCoreDeadVariablesSAT4J.ASSUMED_ASSIGNMENT, clause)
                                    .compute());
                        }
                        IO.save(
                                new BooleanAssignmentSpace(variables, List.of(pcDnf.getAll())),
                                genPath.resolve(modelName)
                                        .resolve("interactions")
                                        .resolve(String.format("int_r%d_rs%d.dimacs", modelIteration, modelIteration)),
                                new BooleanAssignmentSpaceDimacsFormat());
                        IO.save(
                                new BooleanAssignmentSpace(variables, List.of(updatedInteractions)),
                                genPath.resolve(modelName)
                                        .resolve("interactions")
                                        .resolve(String.format("uint_r%d_rs%d.dimacs", modelIteration, modelIteration)),
                                new BooleanAssignmentSpaceDimacsFormat());
                        writeCSV(interactionsCSV, w -> {
                            w.add(modelID);
                            w.add(modelIteration);
                            w.add("r");
                            w.add(interactionCount);
                            w.add(interactionSize);
                            w.add(String.format("g%d", modelIteration));
                        });
                    }
                } catch (Exception e) {
                    FeatJAR.log().error(e);
                }
            }
        } catch (IOException e) {
            FeatJAR.log().error(e);
        }
    }
}
