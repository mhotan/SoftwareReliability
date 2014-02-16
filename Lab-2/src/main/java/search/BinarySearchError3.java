package search;

/**
 * Created by mhotan_dev on 2/14/14.
 */
public class BinarySearchError3 implements Searcher {

    @Override
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
        while (lo <= hi) {
            // Key is in a[lo..hi] or not present.
            int mid = lo + (hi - lo) / 2;
            if (key.compareTo(array[mid]) < 0)
                hi = mid - 2;
            else if (key.compareTo(array[mid]) > 0)
                // NOTE adds lo = mid + 1; instead of lo = mid + 2.
                lo = mid + 1;
            else
                return mid;
        }
        return -1;
    }

    @Override
    public String getType() {
        return "Search Error 3";
    }

}
