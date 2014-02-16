import search.*;
import sort.*;
import testing.framework.TestSuite;
import testing.framework.TestSuiteResult;
import testing.framework.generator.PairwiseTestSuiteGenerator;
import testing.framework.generator.PairwiseTestSuiteGenerator2;
import testing.framework.generator.RandomTestSuiteGenerator;
import testing.framework.generator.TestSuiteGenerator;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

/**
 * Created by mhotan_dev on 2/14/14.
 */
public class Main {

    private static TestSuiteGenerator randomGen, pairwiseGen;

    public static void main(String[] args) {
        randomGen = new RandomTestSuiteGenerator();
        pairwiseGen = new PairwiseTestSuiteGenerator();
        // Print the help message.
        printHelp();

        while (true) {
            showHelp();
            String val = readLine("Input: ").trim();
            if (val.equals("h")) {
                printHelp();
            } else if (val.equals("q")) {
                println("Quiting Application");
                return;
            } else if (val.equals("1")) {
                regenerateTestCases();
            } else if (val.equals("2")) {
                runTests();
            } else {
                println("Invalid input! Try again");
            }
        }
    }

    private static int getInt(String message) {
        while (true) {
            String intStr = readLine(message);
            try {
                int val = Integer.valueOf(intStr);
                return val;
            } catch (NumberFormatException e) {
                println("Value is not an integer please try again.");
            }
        }
    }

    private static void regenerateTestCases() {
        // TODO Regenerate test cases
        randomGen.deleteCurrentTestSuite();
        pairwiseGen.deleteCurrentTestSuite();

        while (true) {
            try {
                int arraySize = getInt("Array size?");
                int range = getInt("Range of values per parameter?");
                pairwiseGen = new PairwiseTestSuiteGenerator2(arraySize, range);
                break;
            } catch (IllegalArgumentException e) {
                println("Illegal input \"" + e.getMessage() + "\"");
            }
        }

        while (true) {
            try {
                int numTest = getInt("Number of random tests");
                randomGen = new RandomTestSuiteGenerator(
                        numTest, pairwiseGen.getArraySize(), pairwiseGen.getIntRange());
                break;
            } catch (IllegalArgumentException e) {
                println("Illegal input \"" + e.getMessage() + "\"");
            }
        }

        println("Test Generation Complete!");
    }

    private static void runTests() {
        // TODO Run test cases
        TestSuite randomSuite = randomGen.getTestSuite();
        TestSuite pairwiseSuite = pairwiseGen.getTestSuite();

        Sorter goodSorter = new Sort();
        Searcher goodSearcher = new BinarySearch();

        List<Sorter> sorters = new ArrayList<Sorter>();
        sorters.add(new SortError1());
        sorters.add(new SortError2());
        sorters.add(new SortError3());
        for (Sorter sorter: sorters) {
            TestSuiteResult ranResult = randomSuite.run(goodSearcher, sorter);
            TestSuiteResult pairResult = pairwiseSuite.run(goodSearcher, sorter);
            println("Sorter: " + sorter.getType() + " Searcher: " + goodSearcher.getType());
            println("Random Test Suite result: " + ranResult);
            println("Pairwise Test Suite result: " + pairResult);
            println("\n");
        }

        List<Searcher> searchers = new ArrayList<Searcher>();
        searchers.add(new BinarySearchError1());
        searchers.add(new BinarySearchError2());
        searchers.add(new BinarySearchError3());
        for (Searcher searcher: searchers) {
            TestSuiteResult ranResult = randomSuite.run(searcher, goodSorter);
            TestSuiteResult pairResult = pairwiseSuite.run(searcher, goodSorter);
            println("Sorter: " + goodSorter.getType() + " Searcher: " + searcher.getType());
            println("Random Test Suite result: " + ranResult);
            println("Pairwise Test Suite result: " + pairResult);
            println("\n");
        }

    }

    private static void showHelp() {
        println("Press \"h\" for help");
    }

    private static void printHelp() {
        showHelp();
        println("Press \"q\" to quit");
        println("Press \"1\" to regenerate test cases");
        println("Press \"2\" to run test cases");
    }

    private static String readLine(String format, Object... args) {
        System.out.println(String.format(format, args));
        BufferedReader reader = new BufferedReader(new InputStreamReader(
                System.in));
        try {
            return reader.readLine();
        } catch (IOException e) {
            throw new RuntimeException("Unable to get console input");
        }
    }

    private static void println(String message) {
        System.out.println(message);
    }


}
