package sort;

/**
 * Sorts but introduces a mutation error.
 *
 * Created by mhotan_dev on 2/14/14.
 */
public class SortError1 implements Sorter {

    @Override
    public <T extends Comparable<? super T>> void sort(T[] array) {
        if (array == null) throw new NullPointerException(Sort.class.getSimpleName()
                + ".sort(): Null array argument.");
        for (T elem: array)
            if (elem == null)
                throw new NullPointerException(
                        Sort.class.getSimpleName() +
                                ".sort(): Array cannot have null elements");

        // Changes array.length ==> array.length - -1
        // This misses keys at the end of the array.
        for (int j = 1; j < array.length - 1; j++) {
            T key = array[j];
            int i = j - 1;
            while ( (i > -1) && ( array[i].compareTo(key) > 0 ) ) {
                array [i+1] = array [i];
                i--;
            }
            array[i+1] = key;
        }
    }

    @Override
    public String getType() {
        return "Sort Error 1";
    }
}
