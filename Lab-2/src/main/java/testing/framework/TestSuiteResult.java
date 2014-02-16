package testing.framework;

/**
 * Created by mhotan_dev on 2/14/14.
 */
public class TestSuiteResult {

    public enum RESULT {ALL_PASSED, FAILURE_OCCURED}

    private final RESULT result;
    private final int testPassed;

    public TestSuiteResult(RESULT result, int testsPassedUntilFailure) {
        this.result = result;
        this.testPassed = testsPassedUntilFailure;
    }

    public RESULT getResult() {
        return result;
    }

    public int getTestPassed() {
        return testPassed;
    }

    @Override
    public String toString() {
        return "TestSuiteResult{" +
                "result=" + result +
                ", testPassed=" + testPassed +
                '}';
    }
}
