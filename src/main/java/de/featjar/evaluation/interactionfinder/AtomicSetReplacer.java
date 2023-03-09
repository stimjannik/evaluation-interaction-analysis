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

import de.featjar.clauses.LiteralList;
import de.featjar.formula.structure.AuxiliaryRoot;
import de.featjar.formula.structure.Formula;
import de.featjar.formula.structure.atomic.Atomic;
import de.featjar.formula.structure.atomic.literal.BooleanLiteral;
import de.featjar.formula.structure.atomic.literal.VariableMap;
import de.featjar.formula.structure.compound.Compound;
import de.featjar.util.tree.visitor.TreeVisitor;
import java.util.List;

public class AtomicSetReplacer implements TreeVisitor<Void, Formula> {
    final VariableMap variables;
    final List<LiteralList> atomicSets;

    public AtomicSetReplacer(VariableMap variables, List<LiteralList> atomicSets) {
        this.variables = variables;
        this.atomicSets = atomicSets;
    }

    @Override
    public VisitorResult firstVisit(List<Formula> path) {
        final Formula node = TreeVisitor.getCurrentNode(path);
        if (node instanceof Atomic) {
            return VisitorResult.SkipChildren;
        } else if ((node instanceof AuxiliaryRoot) || (node instanceof Compound)) {
            return VisitorResult.Continue;
        } else {
            return VisitorResult.Fail;
        }
    }

    @Override
    public VisitorResult lastVisit(List<Formula> path) {
        final Formula node = TreeVisitor.getCurrentNode(path);
        node.mapChildren(c -> {
            if (c instanceof BooleanLiteral) {
                BooleanLiteral l = (BooleanLiteral) c;
                int index = l.getIndex();
                for (LiteralList atomicSet : atomicSets) {
                    if (atomicSet.containsAnyLiteral(index)) {
                        int substitute = atomicSet.get(0);
                        if (index != substitute) {
                            if (l.isPositive()) {
                                return variables.createLiteral(Math.abs(substitute), substitute > 0);
                            } else {
                                return variables.createLiteral(Math.abs(substitute), substitute < 0);
                            }
                        }
                        break;
                    } else if (atomicSet.containsAnyLiteral(-index)) {
                        int substitute = atomicSet.get(0);
                        if (-index != substitute) {
                            if (l.isPositive()) {
                                return variables.createLiteral(Math.abs(substitute), substitute < 0);
                            } else {
                                return variables.createLiteral(Math.abs(substitute), substitute > 0);
                            }
                        }
                        break;
                    }
                }
            }
            return null;
        });
        return VisitorResult.Continue;
    }
}
