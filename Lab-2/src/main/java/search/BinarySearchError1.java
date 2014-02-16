package search;

/**
 * Implementation of Binary Search that introduces the error where the segmentation of the array is backwards.
 *
 * Created by mhotan_dev on 2/14/14.
 */
public class BinarySearchError1 implements Searcher {

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
        requires array == null || key == null;
        signals_only NullPointerException;
        also
        requires array != null && key != null &&
            (\exists int i; 0 <= i && i < array.length;
                array[i] == null);
        signals_only NullPointerException;
        requires array != null && key != null
            && array.length > 1
            && !(\forall int i; 0 <= i && i < array.length - 1;
                array[i].compareTo(array[i+1]) < 1);
        signals_only IllegalArgumentException;
        also
        requires array != null && key != null;
            && (\forall int i; 0 <= i && i < array.length - 1;
                array[i].compareTo(array[i+1]) < 1);
            && (\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures \result != -1 && array[\result] == key;
        also
        requires array != null && key != null
            && array.length > 1
            && (\forall int i; 0 <= i && i < array.length - 1;
                array[i].compareTo(array[i+1]) < 1)
            && !(\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures \result == -1;
     @*/
    public <T extends Comparable<? super T>> int search(T[] array, T key) {
        if (array == null)
            throw new NullPointerException("argument array is null");
        if (key == null)
            throw new NullPointerException("argument key is null");

        // Make sure every element is not null.
        for (T elem: array) {
            if (elem == null)
                throw new NullPointerException("All elements must not be null");
        }

        // Make sure the array is sorted.
        if (!Util.isSorted(array))
            throw new IllegalArgumentException(getClass().getSimpleName() +
                    " argument array is not sorted");

        int lo = 0;
        int hi = array.length - 1;
        while (lo < hi) {
            // Key is in a[lo..hi] or not present.
            int mid = lo + (hi - lo) / 2;
            if (key.compareTo(array[mid]) > 0)
                hi = mid - 1;
            else if (key.compareTo(array[mid]) < 0)
                lo = mid + 1;
            else
                return mid;
        }
        return -1;
    }

    @Override
    public String getType() {
        return "Search Error 1";
    }

}
