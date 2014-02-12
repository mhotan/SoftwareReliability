/**
 * Generally utility class for this project.
 *
 * Created by mhotan_dev on 2/12/14.
 */
public class Util {

    /**
     * Checks if the array is sorted.
     *
     * @param array Array to check
     * @param <T> The Comparable type of the array.
     * @return Whether or not the array is sorted
     */
    public static <T extends Comparable<? super T>> boolean isSorted(T[] array) {
        if (array == null)
            throw new IllegalArgumentException("Array cannot be null");

        // Any empty or one element array is sorted.
        if (array.length <= 1) return true;

        // Make sure every element is equals to or less the latter element.
        for (int i = 0; i < array.length - 1; ++i) {
            // If we ever find a
            if (array[i].compareTo(array[i +1 ]) > 1) {
                return false;
            }
        }

        return true;
    }


}
