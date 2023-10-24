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
import de.featjar.evaluation.interactionfinder.InteractionFinderEvaluator;
import de.featjar.evaluation.util.ModelReader;
import de.featjar.formula.analysis.VariableMap;
import de.featjar.formula.analysis.bool.ABooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignment;
import de.featjar.formula.analysis.bool.BooleanAssignmentList;
import de.featjar.formula.analysis.bool.BooleanAssignmentSpace;
import de.featjar.formula.analysis.bool.BooleanClause;
import de.featjar.formula.analysis.bool.BooleanClauseList;
import de.featjar.formula.analysis.bool.IBooleanRepresentation;
import de.featjar.formula.analysis.sat4j.ComputeAtomicSetsSAT4J;
import de.featjar.formula.io.FormulaFormats;
import de.featjar.formula.io.csv.BooleanAssignmentSpaceCSVFormat;
import de.featjar.formula.structure.formula.IFormula;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Sebastian Krieter
 */
public class PrepareFeatureModelPhase implements EvaluationPhase<InteractionFinderEvaluator> {

    private ModelReader<IFormula> modelReader;
    private CSVFile modelCSV;

    public void optionLoop(InteractionFinderEvaluator evaluator, int lastChanged) {
        // read fm
        String modelName = evaluator.cast(0);
        int modelID = evaluator.systemNames.indexOf(modelName);
        Result<IFormula> load = modelReader.read(modelName);
        if (load.isEmpty()) {
            FeatJAR.log().problems(load.getProblems());
        } else {
            // get core
            VariableMap variables =
                    IBooleanRepresentation.toVariableMap(load.get()).compute();
            BooleanClauseList cnf =
                    IBooleanRepresentation.toBooleanClauseList(load.get()).compute();
            BooleanAssignmentList atomic =
                    Computations.of(cnf).map(ComputeAtomicSetsSAT4J::new).compute();

            Iterator<BooleanAssignment> iterator = atomic.getAll().iterator();
            BooleanAssignment core = iterator.next();

            VariableMap atomicFreeVariables = new VariableMap(variables);
            List<int[]> atomicFreeClauseLiterals = new ArrayList<>();
            for (BooleanClause clause : cnf.getAll()) {
                atomicFreeClauseLiterals.add(clause.copy());
            }
            while (iterator.hasNext()) {
                BooleanAssignment next = iterator.next();
                if (next.size() > 1) {
                    int[] atomicLiterals = next.copy();
                    int substitute = atomicLiterals[0];
                    for (int i = 1; i < atomicLiterals.length; i++) {
                        atomicFreeVariables.remove(atomicLiterals[i]);
                    }
                    for (int[] clauseLiterals : atomicFreeClauseLiterals) {
                        for (int i = 0; i < clauseLiterals.length; i++) {
                            int clauseLiteral = clauseLiterals[i];
                            for (int j = 1; j < atomicLiterals.length; j++) {
                                int atomicLiteral = atomicLiterals[j];
                                if (clauseLiteral == atomicLiteral) {
                                    clauseLiterals[i] = substitute;
                                    break;
                                } else if (clauseLiteral == -atomicLiteral) {
                                    clauseLiterals[i] = -substitute;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            atomicFreeVariables.normalize();
            core = new BooleanAssignment(
                    core.adapt(variables, atomicFreeVariables).orElseThrow());
            List<BooleanClause> atomicFreeClauses = atomicFreeClauseLiterals.stream()
                    .map(literals ->
                            new BooleanClause(ABooleanAssignment.adapt(literals, variables, atomicFreeVariables, true)
                                    .orElseThrow()))
                    .collect(Collectors.toList());

            // save fm and core
            BooleanAssignmentSpace sp =
                    new BooleanAssignmentSpace(atomicFreeVariables, List.of(atomicFreeClauses, List.of(core)));
            try {
                IO.save(
                        sp,
                        evaluator.outputPath.resolve(modelName).resolve("cnf.csv"),
                        new BooleanAssignmentSpaceCSVFormat());
                evaluator.writeCSV(modelCSV, w -> {
                    w.add(modelID);
                    w.add(modelName);
                    w.add(variables.getVariableCount());
                    w.add(cnf.size());
                });
            } catch (IOException e) {
                FeatJAR.log().error(e);
            }
        }
    }

    @Override
    public void run(InteractionFinderEvaluator evaluator) {
        try {
            modelCSV = new CSVFile(evaluator.csvPath.resolve("model.csv"));
            modelCSV.setHeaderFields("ModelID", "ModelName", "VariableCount", "ClauseCount");
            modelCSV.flush();
            modelReader = new ModelReader<>(evaluator.resourcePath.resolve("models"), FormulaFormats.getInstance());
            evaluator.optionLoop(this, InteractionFinderEvaluator.systemsOption);
        } catch (IOException e) {
            FeatJAR.log().error(e);
        }
    }
}
