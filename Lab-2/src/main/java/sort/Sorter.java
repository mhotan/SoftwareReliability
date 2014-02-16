package sort;

/**
 * Created by mhotan_dev on 2/14/14.
 */
public interface Sorter {

    /**
     * Sorts the array in place.
     *
     * @param array Sorts the array
     * @param <T> Comparable type to be sorted.
     */
    public <T extends Comparable<? super T>> void sort(T[] array);

    public String getType();

}
