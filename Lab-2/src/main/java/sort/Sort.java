package sort;

/**
 * Self implementation of quick sort.
 *
 * Created by Michael Hotan on 2/11/14.
 */
public final class Sort implements Sorter {

    /**
     * Sorts the array from smallest to largest.
     *
     * @param array Array to sort.
     * @param <T> Comparable type that uses compareTo.
     */
    /*@
        requires array != null && array.length > 1
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
    @Override
    public <T extends Comparable<? super T>> void sort(T[] array) {
        if (array == null) throw new NullPointerException(Sort.class.getSimpleName()
                + ".sort(): Null array argument.");
        for (T elem: array)
            if (elem == null)
                throw new NullPointerException(
                        Sort.class.getSimpleName() +
                                ".sort(): Array cannot have null elements");

        for (int j = 1; j < array.length; j++) {
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
        return "Sort Normal";
    }

}
