package de.featjar.evaluation.interactionfinder.phase;

import de.featjar.analysis.sat4j.computation.RandomConfigurationUpdater;
import de.featjar.base.FeatJAR;
import de.featjar.base.computation.Cache;
import de.featjar.base.io.IO;
import de.featjar.base.log.Log;
import de.featjar.evaluation.interactionfinder.ConfigurationOracle;
import de.featjar.evaluation.interactionfinder.InteractionFinderRunner;
import de.featjar.formula.assignment.ABooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignmentGroups;
import de.featjar.formula.assignment.BooleanClauseList;
import de.featjar.formula.computation.interactionfinder.AInteractionFinder;
import de.featjar.formula.computation.interactionfinder.IncInteractionFinderRepeat;
import de.featjar.formula.io.csv.BooleanAssignmentGroupsCSVFormat;
import de.featjar.formula.io.dimacs.BooleanAssignmentGroupsDimacsFormat;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

public class testFindingPhase {


    private static BooleanAssignmentGroups loadDimacs(String path) {
        if (path.endsWith(".csv")) {
            return IO.load(Paths.get(path), new BooleanAssignmentGroupsCSVFormat())
                    .orElseThrow();
        } else if (path.endsWith(".dimacs")) {
            return IO.load(Paths.get(path), new BooleanAssignmentGroupsDimacsFormat())
                    .orElseThrow();
        } else {
            throw new RuntimeException("Unkown file format");
        }
    }


    public static void main(String[] args) {
        String[] arg = {
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/test/gen/calculate/cnf.dimacs",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/test/gen/calculate/core.dimacs",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/test/gen/calculate/samples/sol_gs2.csv",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/test/gen/calculate/interactions/int_g12_gs2.dimacs",
                "/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/test/temp/result.txt",
                "repeat",
                "1",
                "0",
                "0",
                "0",
                "500000000"
        };
//        try {
//            InteractionFinderRunner.main(arg);
//        } catch (IOException e) {
//            throw new RuntimeException(e);
//        }

        boolean standalone = !FeatJAR.isInitialized();
        try {
            if (standalone) {
                FeatJAR.configure()
                        .log(c -> c.logToSystemOut(Log.Verbosity.MESSAGE))
                        .log(c -> c.logToSystemErr(Log.Verbosity.ERROR))
                        .cache(c -> c.setCachePolicy(Cache.CachePolicy.CACHE_NONE))
                        .initialize();
            }

            AInteractionFinder thread = new IncInteractionFinderRepeat();

            BooleanAssignmentGroups model = loadDimacs(arg[0]);
            BooleanClauseList cnf = model.toClauseList();
            BooleanAssignmentGroups core = loadDimacs(arg[1]);
            BooleanAssignmentGroups sample = loadDimacs(arg[2]);
            BooleanAssignmentGroups interaction = loadDimacs(arg[3]);
            Path outputPath = Paths.get(arg[4]);
            Long seed = 10l;

            int t = Integer.parseInt(arg[6]);

            Double fpNoise = Double.parseDouble(arg[8]);
            Double fnNoise = Double.parseDouble(arg[9]);
            Long timeout = Long.parseLong(arg[10]);

            thread.reset();
            thread.setCore(core.getGroups().get(0).get(0).toClause());
            thread.setVerifier(
                    new ConfigurationOracle(interaction.toClauseList(0).getAll(), fpNoise, fnNoise));
            thread.setUpdater(new RandomConfigurationUpdater(cnf, seed));
            List<? extends ABooleanAssignment> list = sample.getGroups().get(0);
            thread.addConfigurations(list);
            thread.setCNF(cnf);
            System.out.println(thread.find(t));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }





//
//        FindingPhase findingPhase = new FindingPhase();
//        FindingPhase.ProcessResult processResult = findingPhase.readResults(Path.of("/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/2024-10-07_12-55-05/temp/result.txt"));
//        try {
//            CSVFile dataCSV = new CSVFile(Path.of("/home/tjs/BA/FeatJAR/evaluation-interaction-analysis/results/2024-10-07_12-55-05/temp/csv.csv"));
//            findingPhase.writeRunData(dataCSV);
//        } catch (IOException e) {
//            throw new RuntimeException(e);
//        }

    }
}
