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
import de.featjar.base.computation.Computations;
import de.featjar.base.data.Result;
import de.featjar.base.io.IO;
import de.featjar.base.io.csv.CSVFile;
import de.featjar.evaluation.Evaluator;
import de.featjar.formula.VariableMap;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanClause;
import de.featjar.formula.assignment.BooleanClauseList;
import de.featjar.formula.assignment.BooleanSolution;
import de.featjar.formula.assignment.ComputeBooleanRepresentation;
import de.featjar.formula.computation.ComputeCNFFormula;
import de.featjar.formula.computation.ComputeDNFFormula;
import de.featjar.formula.computation.ComputeNNFFormula;
import de.featjar.formula.io.csv.BooleanAssignmentGroupsCSVFormat;
import de.featjar.formula.io.dimacs.BooleanAssignmentGroupsDimacsFormat;
import de.featjar.formula.io.textual.ExpressionParser;
import de.featjar.formula.io.textual.ExpressionParser.ErrorHandling;
import de.featjar.formula.io.textual.JavaSymbols;
import de.featjar.formula.structure.IFormula;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Sebastian KrieterComputeCoreDeadVariablesSAT4J
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
            nodeReader.setSymbols(JavaSymbols.INSTANCE);
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
                    Result<BooleanAssignmentGroups> load = IO.load(
                            genPath.resolve(modelName).resolve("cnf.dimacs"),
                            new BooleanAssignmentGroupsDimacsFormat());
                    if (load.isEmpty()) {
                        FeatJAR.log().problems(load.getProblems());
                        return;
                    }
                    BooleanAssignmentGroups space = load.get();
                    VariableMap variables = space.getVariableMap();
                    BooleanClauseList cnf =
                            new BooleanClauseList(space.getGroups().get(0), variables.getVariableCount());

                    final String formulaString = values[5];
                    final IFormula formula =
                            (IFormula) nodeReader.parse(formulaString).orElseThrow();
                    ComputeNNFFormula nnf = Computations.of(formula).map(ComputeNNFFormula::new);
                    BooleanAssignmentGroups pcDnfRep = nnf.map(ComputeDNFFormula::new)
                            .map(ComputeBooleanRepresentation::new)
                            .compute();
                    BooleanAssignmentGroups pcCnfRep = nnf.map(ComputeCNFFormula::new)
                            .map(ComputeBooleanRepresentation::new)
                            .compute();

                    BooleanClauseList pcCnf = ((BooleanClauseList)
                                    pcCnfRep.getGroups().get(0))
                            .adapt(pcCnfRep.getVariableMap(), variables);
                    BooleanClauseList pcDnf = ((BooleanClauseList)
                                    pcDnfRep.getGroups().get(0))
                            .adapt(pcDnfRep.getVariableMap(), variables);
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
                                new BooleanAssignmentGroups(variables, List.of(List.of(solution))),
                                genPath.resolve(modelName)
                                        .resolve("samples")
                                        .resolve(String.format("sol_rs%d.csv", modelIteration)),
                                new BooleanAssignmentGroupsCSVFormat());
                        interactionCount = pcDnf.size();
                        interactionSize =
                                pcDnf.stream().mapToInt(c -> c.size()).max().getAsInt();
                        ArrayList<BooleanAssignment> updatedInteractions = new ArrayList<>(interactionCount);
                        for (BooleanClause clause : pcDnf.getAll()) {
                            updatedInteractions.add(Computations.of(cnf)
                                    .map(ComputeCoreSAT4J::new)
                                    .set(ComputeCoreSAT4J.ASSUMED_ASSIGNMENT, clause)
                                    .compute());
                        }
                        IO.save(
                                new BooleanAssignmentGroups(variables, List.of(pcDnf.getAll())),
                                genPath.resolve(modelName)
                                        .resolve("interactions")
                                        .resolve(String.format("int_r%d_rs%d.dimacs", modelIteration, modelIteration)),
                                new BooleanAssignmentGroupsDimacsFormat());
                        IO.save(
                                new BooleanAssignmentGroups(variables, List.of(updatedInteractions)),
                                genPath.resolve(modelName)
                                        .resolve("interactions")
                                        .resolve(String.format("uint_r%d_rs%d.dimacs", modelIteration, modelIteration)),
                                new BooleanAssignmentGroupsDimacsFormat());
                        CSVFile.writeCSV(interactionsCSV, w -> {
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
