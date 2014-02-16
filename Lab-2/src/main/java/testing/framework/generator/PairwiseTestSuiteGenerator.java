package testing.framework.generator;

import org.json.simple.JSONObject;
import testing.framework.Pair;
import testing.framework.TestCase;
import testing.framework.TestSuite;

import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

/**
 * Created by mhotan_dev on 2/13/14.
 */
public class PairwiseTestSuiteGenerator extends TestSuiteGenerator {

    public PairwiseTestSuiteGenerator() {
        super();
    }

    public PairwiseTestSuiteGenerator(int arraySize, int rangeSize) {
        super(arraySize, rangeSize);
    }

    @Override
    protected Path getPath() {
        try {
            Path p = Paths.get(getClass().getClassLoader().getResource(".").toURI());
            p = p.resolve("Pairwise-Test-Cases.txt");
            return p;
        } catch (URISyntaxException e) {
            throw new RuntimeException("Unable to find path for Random-Test-Cases.txt: "
                    + e.getMessage());
        }
    }

    @Override
    protected TestSuite generateTestCases() {
        List<Integer> indexes = new ArrayList<Integer>();
        for (int i = 0; i < getArraySize(); ++i)
            indexes.add(i);

        // Create a pair of all indexes.
        Collection<Pair<Integer>> pairs = getPairs(indexes);

        // Random number generator
        Random random = new Random();

        // Set the default values.
        Integer[] defaults = new Integer[getArraySize()];
        for (int i = 0; i < defaults.length; ++i)
            defaults[i] = random.nextInt(getIntRange());

        // Set the default key.
        Integer defaultKey = random.nextInt(getIntRange());

        // Using a set ensures unique test cases.
        Set<TestCase> cases = new HashSet<TestCase>();
        for (Pair<Integer> p: pairs) {
            // Create a collection of test cases varying
            // the typical values of the elements assigned for the index determined by the pair.
            cases.addAll(generateTestCase(defaults, defaultKey, p));
        }
        return new TestSuite(cases);
    }

    private static Integer[] copy(Integer[] original) {
        Integer[] copy = new Integer[original.length];
        for (int i = 0; i < copy.length; ++i)
            copy[i] = original[i];
        return copy;
    }

    /**
     *
     * @param defaults
     * @param defaultKey
     * @param pair
     * @return
     */
    private List<TestCase> generateTestCase(Integer[] defaults, Integer defaultKey,
                                            Pair<Integer> pair) {
        List<TestCase> cases = new ArrayList<TestCase>();
        for (int i = 0; i < getIntRange(); ++i) {
            for (int j = 0; j < getIntRange(); ++j) {
                Integer[] defCopy = copy(defaults);
                Integer key = defaultKey;
                if (pair.getFirst() == getArraySize()) {
                    // If the first is the key
                    // Then use the second value as the index in the array.
                    key = i;
                    defCopy[pair.getSecond()] = j;
                } else if (pair.getSecond() == getArraySize()) {
                    // If the second is the key
                    // Then use the first value as the index in the array.
                    defCopy[pair.getFirst()] = i;
                    key = j;
                } else {
                    // The key is not used.
                    defCopy[pair.getFirst()] = i;
                    defCopy[pair.getSecond()] = j;
                }
                cases.add(new TestCase(defCopy, key));
            }
        }

        return cases;
    }

    @Override
    protected TestSuite load(JSONObject object) {
        return new TestSuite(object);
    }

    private static <T> Collection<Pair<T>> getPairs(List<T> values) {
        if (values == null)
            throw new NullPointerException();
        if (values.size() <= 1) // There can be no pairs.
            return new ArrayList<Pair<T>>();

        // Creating a set of pairs ensures uniqueness.
        Set<Pair<T>> pairs = new HashSet<Pair<T>>();

        for (int i = 0; i < values.size() - 1; ++i) {
            for (int j = i + 1; j < values.size(); ++j) {
                Pair<T> p = new Pair<T>(values.get(i), values.get(j));
                if (pairs.contains(p))
                    throw new IllegalArgumentException("Attempting to add the same pair twice");
                pairs.add(p);
            }
        }

//        assert pairs.size() == numCombinations(values.size(), 2):
//                "Number of combinations is incorrect";

        return pairs;
    }


    private static long numCombinations(long n, long r) {
        return factorial(n) / (factorial(r) * (factorial(n) - factorial(r)));

    }

    private static long factorial(long val) {
        if (val <= 0) return 1;
        long result = 1;
        for (int i = 1; i <= val; i++) {
            result = result * i;
        }
        return result;
    }

}
