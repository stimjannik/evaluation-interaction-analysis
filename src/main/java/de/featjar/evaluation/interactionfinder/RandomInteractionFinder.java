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

import de.featjar.base.data.IntegerList;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanSolution;
import de.featjar.formula.computation.IncInteractionFinder;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Detect interactions from given set of configurations.
 *
 * @author Sebastian Krieter
 */
public class RandomInteractionFinder extends IncInteractionFinder {

    private static final double limitFactor = 10.0 / Math.log(2);

    public List<BooleanAssignment> find(int tmax) {
        if (failingConfs.isEmpty()) {
            return null;
        }
        verifyCounter = 0;
        lastMerge = null;

        List<int[]> result = findT(tmax);
        return isPotentialInteraction(result)
                ? List.of(new BooleanAssignment(
                        IntegerList.mergeInt(result.stream().collect(Collectors.toList()))))
                : null;
    }

    private List<int[]> findT(int t) {
        List<int[]> curInteractionList = computePotentialInteractions(t);
        if (curInteractionList == null) {
            return null;
        }
        setConfigurationVerificationLimit((int) Math.ceil(limitFactor * Math.log(curInteractionList.size())));

        while (curInteractionList.size() > 1 //
                && verifyCounter < configurationVerificationLimit) {
            BooleanSolution bestConfig =
                    updater.complete(null, null, curInteractionList).orElse(null);
            if (bestConfig == null) {
                break;
            }
            Map<Boolean, List<int[]>> partitions = group(curInteractionList, bestConfig);
            List<int[]> include = partitions.get(Boolean.TRUE);
            List<int[]> exclude = partitions.get(Boolean.FALSE);

            final boolean pass = verify(bestConfig);
            curInteractionList = pass ? exclude : include;
        }

        return curInteractionList.isEmpty() ? null : curInteractionList;
    }
}
