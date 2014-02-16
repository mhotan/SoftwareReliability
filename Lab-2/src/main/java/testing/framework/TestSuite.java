package testing.framework;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import search.Searcher;
import sort.Sorter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

/**
 * Created by mhotan_dev on 2/13/14.
 */
public class TestSuite implements Iterable<TestCase> {

    private static final String KEY_TEST_CASES = "testcases";

    private final Collection<TestCase> testCases;

    public TestSuite(Collection<TestCase> cases) {
        this.testCases = new ArrayList<TestCase>(cases);
    }

    public TestSuite(JSONObject object) {
        testCases = new ArrayList<TestCase>();
        JSONArray array = (JSONArray) object.get(KEY_TEST_CASES);
        for (Object o: array) {
            testCases.add(new TestCase((JSONObject) o));
        }
    }

    public JSONObject toJSON() {
        JSONObject suite = new JSONObject();
        JSONArray array = new JSONArray();
        for (TestCase tc: this.testCases) {
            array.add(tc.toJSON());
        }
        suite.put(KEY_TEST_CASES, array);
        return suite;
    }

    @Override
    public Iterator<TestCase> iterator() {
        return testCases.iterator();
    }

    public int size() {
        return testCases.size();
    }

    public TestSuiteResult run(Searcher searcher, Sorter sorter) {
        int numPassed = 0;
        for (TestCase c: this) {
            TestCase copy = c.clone();
            boolean actualVal = Oracle.decideMembership(copy);
            boolean testVal = isMemberUnSorted(copy, sorter, searcher);
            if (actualVal != testVal)
                return new TestSuiteResult(TestSuiteResult.RESULT.FAILURE_OCCURED, numPassed);
            numPassed++;
        }

        return new TestSuiteResult(TestSuiteResult.RESULT.ALL_PASSED, size());
    }

    public static boolean isMemberUnSorted(TestCase c, Sorter sorter, Searcher searcher) {
        assert c != null;

        // Quickly sort the array.
        sorter.sort(c.getArray());

        // Return whether the index was found after doing search.
        return (searcher.search(c.getArray(), c.getKey()) != -1);
    }
}
