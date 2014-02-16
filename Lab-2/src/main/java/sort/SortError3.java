package sort;

/**
 * Created by mhotan_dev on 2/14/14.
 */
public class SortError3 implements Sorter {

    @Override
    public <T extends Comparable<? super T>> void sort(T[] array) {
        if (array == null) throw new NullPointerException(Sort.class.getSimpleName()
                + ".sort(): Null array argument.");
        for (T elem: array)
            if (elem == null)
                throw new NullPointerException(
                        Sort.class.getSimpleName() +
                                ".sort(): Array cannot have null elements");

        // NOTE Change j = 1 ==> j = 2  Therefore doesn't sort the first value.
        for (int j = 2; j < array.length; j++) {
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
        return "Sort Error 3";
    }
}
