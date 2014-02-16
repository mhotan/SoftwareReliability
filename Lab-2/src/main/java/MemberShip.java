import search.Searcher;
import search.Util;
import sort.Sorter;
import testing.framework.TestCase;

/**
 * Class that determines whether a given key is in an array.
 *
 * Created by mhotan on 2/12/14.
 */
public final class MemberShip {

    /**
     * Checks whether key is in array.
     *
     * @param array Array to check inside
     * @param key Key to check for inside the array.
     * @param <T> Comparable type
     * @return Whether or not key is in array or not.
     */
    /*@
        requires array == null || key == null;
        signals_only NullPointerException;
        also
        requires array != null && key != null &&
            (\exists int i; 0 <= i && i < array.length;
                array[i] == null);
        signals_only NullPointerException;
        also
        requires array != null && key != null &&
            !(\exists int i; 0 <= i && i < array.length; array[i] == null)
            && !(\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures !\result;
        also
        requires array != null && key != null &&
            !(\exists int i; 0 <= i && i < array.length; array[i] == null)
            && (\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures \result;
     @*/
    public static boolean isMemberUnSorted(TestCase c, Sorter sorter, Searcher searcher) {
        assert c != null;

        // Quickly sort the array.
        sorter.sort(c.getArray());

        // Return whether the index was found after doing search.
        return (searcher.search(c.getArray(), c.getKey()) != -1);
    }

    /**
     * Checks whether the key is within the sorted array.
     *
     * @param c Test Case to use.
     * @param searcher Key to find in the sorted array
     * @param <T> Comparable type
     * @return Whether or not key is in the array or not.
     */
    /*@
        requires array == null || key == null;
        signals_only NullPointerException;
        also
        requires array != null && key != null &&
            (\exists int i; 0 <= i && i < array.length;
                array[i] == null);
        signals_only NullPointerException;
        also
        requires array != null && key != null &&
            !(\exists int i; 0 <= i && i < array.length; array[i] == null)
            && !(\forall int i; 0 <= i && i < array.length - 1;
                array[i].compareTo(array[i+1]) < 1);
        signals_only IllegalArgumentException
        also
        requires array != null && key != null &&
            !(\exists int i; 0 <= i && i < array.length; array[i] == null)
            && (\forall int i; 0 <= i && i < array.length - 1;
                array[i].compareTo(array[i+1]) < 1)
            && !(\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures !\result;
        also
        requires array != null && key != null &&
            !(\exists int i; 0 <= i && i < array.length; array[i] == null)
            && (\forall int i; 0 <= i && i < array.length - 1;
                array[i].compareTo(array[i+1]) < 1)
            && (\exists int i; 0 <= i && i < array.length;
                array[i] == key);
        ensures \result;
     @*/
    public static <T extends Comparable<? super T>> boolean isMemberSorted(TestCase c, Searcher searcher) {
        if (c == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + ".isMemberSorted() " +
                    "Test Case cannot be null");
        if (searcher == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + ".isMemberSorted() " +
                    "Searcher cannot be null");

        if (!Util.isSorted(c.getArray())) {
            throw new IllegalArgumentException(MemberShip.class.getSimpleName() + ".isMemberSorted() " +
                    "array must be sorted.");
        }

        return (searcher.search(c.getArray(), c.getKey()) != -1);
    }

}
