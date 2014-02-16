package testing.framework;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

import java.util.Arrays;

/**
 * Created by mhotan_dev on 2/13/14.
 */
public class TestCase {

    /**
     * Representation Invariant:
     * this.array is not null
     * this.array.length == ARRAY_SIZE
     */

    private static final String KEY_KEY = "key";
    private static final String KEY_ARRAY = "array";

    private final Integer[] array;
    private final Integer key;

    public TestCase(Integer[] array, Integer key) {
        if (key == null || array == null) throw new NullPointerException();
        this.key = key;
        this.array = array;
    }

    public TestCase(JSONObject object) {
        JSONArray jArray = (JSONArray) object.get(KEY_ARRAY);
        this.array = new Integer[jArray.size()];
        for (int i = 0; i < jArray.size(); ++i) {
            array[i] = ((Long) jArray.get(i)).intValue();
        }
        this.key = ((Long)object.get(KEY_KEY)).intValue();
    }

    public JSONObject toJSON() {
        JSONObject object = new JSONObject();
        JSONArray array = new JSONArray();
        for (Integer i: this.array) {
            array.add(i);
        }
        object.put(KEY_ARRAY, array);
        object.put(KEY_KEY, this.key);
        return object;
    }

    public Integer[] getArray() {
        return array;
    }

    public Integer getKey() {
        return key;
    }

    public TestCase clone() {
        Integer[] aCopy = Arrays.copyOf(getArray(), getArray().length);
        return new TestCase(aCopy, getKey());
    }

    @Override
    public String toString() {
        return "TestCase{" +
                "array=" + Arrays.toString(array) +
                ", key=" + key +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TestCase)) return false;
        TestCase testCase = (TestCase) o;
        if (!Arrays.equals(array, testCase.array)) return false;
        if (!key.equals(testCase.key)) return false;
        return true;
    }

    @Override
    public int hashCode() {
        int result = Arrays.hashCode(array);
        result = 31 * result + key.hashCode();
        return result;
    }
}
