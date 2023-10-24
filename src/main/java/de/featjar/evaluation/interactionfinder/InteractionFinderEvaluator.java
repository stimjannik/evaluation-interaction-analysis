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
package de.featjar.evaluation.interactionfinder;

import de.featjar.base.cli.ListOption;
import de.featjar.base.cli.Option;
import de.featjar.evaluation.Evaluator;
import java.util.ArrayList;
import java.util.List;

public class InteractionFinderEvaluator extends Evaluator {

    public static final Option<Integer> memoryOption = new Option<>("memory", Option.IntegerParser, 8);
    public static final ListOption<Integer> tOption = new ListOption<>("t", Option.IntegerParser);
    public static final ListOption<Integer> interactionSizeOption =
            new ListOption<>("interactionSize", Option.IntegerParser);
    public static final ListOption<Integer> interactionCountOption =
            new ListOption<>("interactionCount", Option.IntegerParser);
    public static final ListOption<Double> fpNoiseOption = new ListOption<>("fpNoise", Option.DoubleParser);
    public static final ListOption<Double> fnNoiseOption = new ListOption<>("fnNoise", Option.DoubleParser);
    public static final ListOption<String> algorithmsOption = new ListOption<>("algorithm", Option.StringParser);

    @Override
    public List<Option<?>> getOptions() {
        ArrayList<Option<?>> options = new ArrayList<>(super.getOptions());
        options.add(memoryOption);
        options.add(tOption);
        options.add(interactionSizeOption);
        options.add(interactionCountOption);
        options.add(fpNoiseOption);
        options.add(fnNoiseOption);
        options.add(algorithmsOption);
        return options;
    }
}
