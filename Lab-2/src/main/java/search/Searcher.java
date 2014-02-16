package search;

/**
 * Created by mhotan_dev on 2/14/14.
 */
public interface Searcher {

    /*@
        requires array == null || key == null;
        signals_only NullPointerException;
        also
        requires array != null && key != null &&
            (\exists int i; 0 <= i && i < array.length;
                array[i] == null);
        signals_only NullPointerException;
        also
        requires array != null && key != null
            && (\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures \result != -1 && array[\result] == key;
        also
        requires array != null && key != null
            && !(\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures \result == -1;
     @*/
    public <T extends Comparable<? super T>> int search(T[] array, T key);

    public String getType();

}
