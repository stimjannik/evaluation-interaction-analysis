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
import de.featjar.clauses.solutions.analysis.ConfigurationVerifyer;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

public class ConfigurationOracle implements ConfigurationVerifyer {
    private final List<LiteralList> interactions;
    private final double fpNoise, fnNoise;

    public ConfigurationOracle(List<LiteralList> interactions, double fpNoise, double fnNoise) {
        this.interactions = interactions;
        this.fpNoise = fpNoise;
        this.fnNoise = fnNoise;
    }

    @Override
    public int test(LiteralList configuration) {
        final Random random = new Random(Arrays.hashCode(configuration.getLiterals()));

        int error = 1;
        for (LiteralList interaction : interactions) {
            final boolean isFailing = configuration.containsAll(interaction);
            if (isFailing) {
                break;
            }
            error++;
        }
        error %= interactions.size() + 1;

        return error == 0 //
                ? random.nextDouble() < fnNoise //
                        ? random.nextInt(interactions.size()) + 1 //
                        : 0 //
                : random.nextDouble() < fpNoise //
                        ? 0 //
                        : error;
    }
}
