/**
 * Self implementation of quick sort.
 *
 * Created by Michael Hotan on 2/11/14.
 */
public final class QuickSort {

    /**
     * Sorts the array from smallest to largest.
     *
     * @param array Array to sort.
     * @param <T> Comparable type that uses compareTo.
     */
    /*@
   r    requires array != null && array.length > 1
        ensures (\forall int i; 0 <= i && i < array.length - 1;
            array[i].compareTo(array[i+1]) < 1);
        also
        requires (\exists int i; 0 <= i && i < array.length;
            array[i] == null);
        signals_only NullPointerException
        also
        requires array == null
        signals_only NullPointerException
     @*/
    public static <T extends Comparable<? super T>> void sort(T[] array){
        if (array == null) throw new NullPointerException(QuickSort.class.getSimpleName()
                + ".sort(): Null array argument.");
        for (T elem: array)
            if (elem == null)
                throw new NullPointerException(
                        QuickSort.class.getSimpleName() +
                                ".sort(): Array cannot have null elements");

        if (array.length <= 1) return;

        quickSort(array, 0, array.length);
    }

    /**
     * Sorts the array using quick sort.
     *
     * @param array array to sort.
     * @param <T> Comparable type that uses compareTo.
     */
    private static <T extends Comparable<? super T>> void quickSort(T[] array, int low, int high) {
        if (array == null || array.length <= 1) return;

        int i = low, j = high;
        T pivot = array[low + (high-low)/2];

        // Divide into two lists
        while (i <= j) {
            while (array[i].compareTo(pivot) < 0) {
                i++;
            }
            while (array[j].compareTo(pivot) > 0) {
                j--;
            }

            if (i <= j) {
                swap(array, i, j);
                i++;
                j--;
            }
        }
        // Recursion
        if (low < j)
            quickSort(array, low, j);
        if (i < high)
            quickSort(array, i, high);
    }

    private static <T> void swap(T[] array, int i, int j) {
        T temp = array[i];
        array[i] = array[j];
        array[j] = temp;
    }

}
