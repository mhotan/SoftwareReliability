package testing.framework.generator;

import org.json.simple.JSONObject;
import testing.framework.TestCase;
import testing.framework.TestSuite;

import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

/**
 * Created by mhotan_dev on 2/13/14.
 */
public class RandomTestSuiteGenerator extends TestSuiteGenerator {

    private static final int DEFAULT_NUM_TEST = 100000;

    /**
     * Number of test.
     */
    private final int numTests;

    /**
     * Creates a random test suite generator.
     *
     * @param numTests Number of test to run.
     * @param arraySize Size of input array.
     * @param range Range of the possible typical values.
     */
    public RandomTestSuiteGenerator(int numTests, int arraySize, int range) {
        super(arraySize, range);
        if (numTests <= 0)
            throw new IllegalArgumentException("Illegal number of test: " + numTests);
        this.numTests = numTests;
    }

    public RandomTestSuiteGenerator() {
        super();
        this.numTests = DEFAULT_NUM_TEST;
    }

    public int getNumTests() {
        return numTests;
    }

    @Override
    protected Path getPath() {
        try {
            Path p = Paths.get(getClass().getClassLoader().getResource(".").toURI());
            p = p.resolve("Random-Test-Cases.txt");
            return p;
        } catch (URISyntaxException e) {
            throw new RuntimeException("Unable to find path for Random-Test-Cases.txt: "
                    + e.getMessage());
        }
    }

    @Override
    protected TestSuite generateTestCases() {
        Set<TestCase> cases = new HashSet<TestCase>();
        Random random = new Random();

        while (cases.size() < numTests) {
            Integer[] array = new Integer[getArraySize()];
            for (int i = 0; i < array.length; ++i)
                array[i] = random.nextInt(getIntRange());

            // Create a random key.
            cases.add(new TestCase(array, random.nextInt(getIntRange())));
        }

        return new TestSuite(cases);
    }

    @Override
    protected TestSuite load(JSONObject object) {
        return new TestSuite(object);
    }
}
