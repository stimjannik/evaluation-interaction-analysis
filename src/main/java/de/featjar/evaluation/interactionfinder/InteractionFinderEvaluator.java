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

import de.featjar.evaluation.Evaluator;
import de.featjar.evaluation.properties.ListProperty;
import de.featjar.evaluation.properties.Property;

public class InteractionFinderEvaluator extends Evaluator {

    ListProperty<Integer> tProperty = new ListProperty<>("t", Property.IntegerConverter);
    ListProperty<Integer> interactionSizeProperty = new ListProperty<>("interactionSize", Property.IntegerConverter);
    ListProperty<Integer> interactionCountProperty = new ListProperty<>("interactionCount", Property.IntegerConverter);
    ListProperty<Double> fpNoiseProperty = new ListProperty<>("fpNoise", Property.DoubleConverter);
    ListProperty<Double> fnNoiseProperty = new ListProperty<>("fnNoise", Property.DoubleConverter);
    ListProperty<Integer> configVerificationLimitProperty =
            new ListProperty<>("configVerificationLimit", Property.IntegerConverter);
    ListProperty<Integer> configCreationLimitProperty =
            new ListProperty<>("configCreationLimit", Property.IntegerConverter);
    ListProperty<String> algorithmsProperty = new ListProperty<>("algorithm", Property.StringConverter);

    @Override
    public String getName() {
        return "interaction-finder";
    }
}
