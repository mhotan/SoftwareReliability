/**
 * Self implementation of Binary Search.
 *
 * Created by Michael Hotan on 2/11/14.
 */
public final class BinarySearch {

    /**
     * Searches the sorted array for a given key and returns the index of the location
     * of that key.  The location is a 0 based index.
     *
     * @param array Array search in.
     * @param key Key to find inside the array.
     * @param <T> The comparable type of object array.
     * @return The index (0 based) where the element was found at, or -1
     */
    /*@
      requires ()
      ensures
      also

      @*/
    public static <T extends Comparable<? super T>> int search(T[] array, T key) {
        if (array == null)
            throw new NullPointerException("argument array is null");
        if (key == null)
            throw new NullPointerException("argument key is null");

        // Make sure every element is not null.
        for (T elem: array) {
            if (elem == null)
                throw new IllegalArgumentException("All elements must not be null");
        }

        // Make sure the array is sorted.
        if (!isSorted(array))
            throw new IllegalArgumentException(BinarySearch.class.getSimpleName() +
                    " argument array is not sorted");

        int lo = 0;
        int hi = array.length - 1;
        while (lo <= hi) {
            // Key is in a[lo..hi] or not present.
            int mid = lo + (hi - lo) / 2;
            if (key.compareTo(array[mid]) < 0)
                hi = mid - 1;
            else if (key.compareTo(array[mid]) > 0)
                lo = mid + 1;
            else
                return mid;
        }
        return -1;
    }

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
