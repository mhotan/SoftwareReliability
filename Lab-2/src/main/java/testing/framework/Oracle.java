package testing.framework;

/**
 * Created by mhotan_dev on 2/13/14.
 */
public class Oracle {

    /**
     * Provides the distinct answer for whether a key is a member of an array.
     *
     * @param c TestCase to verify.
     * @return Whether or not the key was found in the array.
     */
    public static  boolean decideMembership(TestCase c) {
        assert c != null;
        for (Integer elem: c.getArray()) {
            if (c.getKey().equals(elem)) {
                return true;
            }
        }
        return false;
    }

}
