package testing.framework.generator;

import org.json.simple.JSONObject;
import testing.framework.TestCase;
import testing.framework.TestSuite;

import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

/**
 * Created by mhotan_dev on 2/15/14.
 */
public class PairwiseTestSuiteGenerator2 extends TestSuiteGenerator {

    public PairwiseTestSuiteGenerator2() {
        super();
    }

    public PairwiseTestSuiteGenerator2(int arraySize, int rangeSize) {
        super(arraySize, rangeSize);
    }

    @Override
    protected Path getPath() {
        try {
            Path p = Paths.get(getClass().getClassLoader().getResource(".").toURI());
            p = p.resolve("Pairwise-Test-Cases2.txt");
            return p;
        } catch (URISyntaxException e) {
            throw new RuntimeException("Unable to find path for Random-Test-Cases.txt: "
                    + e.getMessage());
        }
    }

    @Override
    protected TestSuite generateTestCases() {
        Collection<TestCase> testCases = new ArrayList<TestCase>();

        Random random = new Random();
        Integer[] baseArray = new Integer[getArraySize()];
        for (int i = 0; i < baseArray.length; ++i) {
            baseArray[i] = random.nextInt(getIntRange());
        }

        testCases.addAll(generateTestCases(baseArray));
        return new TestSuite(testCases);
    }

    private static List<TestCase> generateTestCases(Integer[] original) {
        Integer[] copy = Arrays.copyOf(original, original.length);
        Integer[] copySorted = Arrays.copyOf(original, original.length);
        Integer[] copyRevSorted = Arrays.copyOf(original, original.length);

        Arrays.sort(copySorted);
        Arrays.sort(copySorted, new Comparator<Integer>() {
            @Override
            public int compare(Integer o1, Integer o2) {
                return o1.compareTo(o2) * -1;
            }
        });

        List<Integer[]> arrays = new ArrayList<Integer[]>();
        arrays.add(copy);
        arrays.add(copySorted);
        arrays.add(copyRevSorted);

        List<TestCase> cases = new ArrayList<TestCase>();
        for (Integer[] array: arrays) {
            Integer[] acopy = Arrays.copyOf(array, array.length);
            cases.add(new TestCase(acopy, acopy[0]));
            cases.add(new TestCase(acopy, acopy[acopy.length - 1]));
            cases.add(new TestCase(acopy, acopy[acopy.length / 2]));
            cases.add(new TestCase(acopy, acopy[acopy.length / 4]));
            cases.add(new TestCase(acopy, acopy[acopy.length * 3 / 4]));
        }

        return cases;
    }

    @Override
    protected TestSuite load(JSONObject object) {
        return new TestSuite(object);
    }
}
