package testing.framework.generator;

import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import testing.framework.TestSuite;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * Created by mhotan_dev on 2/12/14.
 */
public abstract class TestSuiteGenerator {

    /**
     * The number of elements in the array to test.
     */
    private static final int ARRAY_SIZE = 20;

    /**
     * Choose a modest range of input arguments for the array to w
     */
//    private static final int INT_RANGE = ARRAY_SIZE * 2;

    private final int arraySize, intRange;

    private TestSuite suite;

    public TestSuiteGenerator() {
        this(ARRAY_SIZE, ARRAY_SIZE * 2);
    }

    public TestSuiteGenerator(int arraySize, int rangeSize) {
        if (arraySize <= 0)
            throw new IllegalArgumentException("Illegal array size: " + arraySize);
        if (rangeSize <= 0)
            throw new IllegalArgumentException("Illegal range size: " + arraySize);
        this.arraySize = arraySize;
        this.intRange = rangeSize;
    }

    public int getArraySize() {
        return arraySize;
    }

    public int getIntRange() {
        return intRange;
    }

    /**
     * Returns the path of the file to write
     *
     * @return The path of the file to use.
     */
    protected abstract Path getPath();

    /**
     * Generates new test cases.
     *
     * @return Return new test cases to.
     */
    protected abstract TestSuite generateTestCases();

    /**
     * Loads test suite from
     *
     * @param object Object to turn into to test suite
     * @return TestSuite
     */
    protected abstract TestSuite load(JSONObject object);

    /**
     * Saves test cases.
     *
     * @param suite Test Suite to save.
     */
    private void save(TestSuite suite) {
        try {
            // Create a writer that the JSONArray can write to.
            Writer writer = Files.newBufferedWriter(getPath(), Charset.defaultCharset());
            writer.write(suite.toJSON().toJSONString());
            writer.flush();
            writer.close();
        } catch (IOException e) {
            throw new RuntimeException("Unable to save suite " + suite);
        }
    }

    protected TestSuite load() {
        Path p = getPath();
        try {
            BufferedReader reader = Files.newBufferedReader(p, Charset.defaultCharset());
            JSONParser parser = new JSONParser();
            TestSuite suite = load((JSONObject)parser.parse(reader));
            reader.close();
            return suite;
        } catch (IOException e) {
            throw new RuntimeException("Unable to access file at " + p.toString());
        } catch (ParseException e) {
            throw new RuntimeException("Unable to parse file at " + p.toString());
        }
    }

    /**
     * Gets the saved test cases or generates new ones.
     *
     * @return The generated test cases.
     */
    public TestSuite getTestSuite() {
        // If the file exists.
        if (!Files.exists(getPath())) {
            suite = generateTestCases();
            save(suite);
            return suite;
        }

        // Keep reference to current suite.
        suite = load();
        return suite;
    }

    public void deleteCurrentTestSuite() {
        try {
            Files.deleteIfExists(getPath());
            suite = null;
        } catch (IOException e) {
            System.err.println("Unable to delete " + getPath());
        }
    }

//    /**
//     * Generates random test and loads them into the file output stream.
//     */
//    public static void generateRandom() {
//        try {
//
//            // Make sure we have a path to the txt file where we store random test cases.
//            Path p = g();
//
//            //  Delete the old file if it exists.
//            if (Files.deleteIfExists(p)) {
//                System.out.println("Deleted " + p.toString() + " in order to create a new" +
//                        " one");
//            }
//            // Create the new file.
//            p = Files.createFile(p);
//
//            // Generate DEFAULT_NUM_TEST random test cases.
//            JSONArray testCases = new JSONArray();
//            Random random = new Random();
//            for (int i = 0; i < DEFAULT_NUM_TEST; ++i) {
//
//                // Create a new test case represented as a JSON Object
//                JSONObject testCase = new JSONObject();
//
//                // Produce the array to input in as an argument.
//                JSONArray array = new JSONArray();
//                for (int j = 0; j < ARRAY_SIZE; ++j) {
//                    array.add(random.nextInt(INT_RANGE));
//                }
//
//                // Place the arguments in the Test case.
//                testCase.put(KEY_ARRAY, array);
//                testCase.put(KEY_KEY, random.nextInt(INT_RANGE));
//
//                testCases.add(testCase);
//            }
//
//            // Create a writer that the JSONArray can write to.
//            Writer writer = Files.newBufferedWriter(p, Charset.defaultCharset());
//
//            JSONObject obj = new JSONObject();
//            obj.put(KEY_TESTCASES, testCases);
//            writer.write(obj.toJSONString());
//
//            System.out.println("Random test generation successful");
//
//            // Must call close so that all the arrays will fit.
//            writer.flush();
//            writer.close();
//        } catch (IOException e) {
//            throw new RuntimeException("Unable to create test cases: " + e.getMessage());
//        }
//    }
//
//    public static List<TestCase> getRandomTestCases() {
//        List<TestCase> cases = new ArrayList<TestCase>();
//
//        Path p = getRandomPath();
//        if (!Files.exists(p)) {
//            generateRandom();
//        }
//
//        try {
//            JSONParser parser = new JSONParser();
//            Reader reader = Files.newBufferedReader(p, Charset.defaultCharset());
//            Object obj = parser.parse(reader);
//
//            JSONObject jsonObject = (JSONObject) obj;
//            JSONArray testCases = (JSONArray) jsonObject.get(KEY_TESTCASES);
//
//            for (Object o : testCases) {
//                JSONObject jo = (JSONObject) o;
//
//                // Construct the array.
//                JSONArray array = (JSONArray) jo.get(KEY_ARRAY);
//                Integer[] intArray = new Integer[ARRAY_SIZE];
//                for (int i = 0; i < array.size(); i++)
//                    intArray[i] = ((Long) array.get(i)).intValue();
//
//                cases.add(new TestCase(
//                        intArray,
//                        ((Long)jo.get(KEY_KEY)).intValue()));
//            }
//
//        } catch (IOException e) {
//            throw new RuntimeException("Unable to load file from " + p + " due to: "
//                    + e.getMessage());
//        } catch (ParseException e) {
//            throw new RuntimeException("Illegal JSONObject Structure: "
//                    + e.getMessage());
//        }
//
//        return cases;
//    }
}
