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
    public static <T extends Comparable<? super T>> boolean isMemberUnSorted(T[] array, T key) {
        if (array == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + ".isMemberUnSorted() " +
                    "array cannot be null");
        if (key == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + ".isMemberUnSorted() " +
                    "key cannot be null");

        // Quickly sort the array.
        QuickSort.sort(array);

        // Return whether the index was found after doing search.
        return isMemberSorted(array, key);
    }

    /**
     * Checks whether the key is within the sorted array.
     *
     * @param array Sorted array to search
     * @param key Key to find in the sorted array
     * @param <T> Comparable type
     * @return Whether or not key is in the array or not.
     */
    public static <T extends Comparable<? super T>> boolean isMemberSorted(T[] array, T key) {
        if (array == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + ".isMemberSorted() " +
                    "array cannot be null");
        if (key == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + ".isMemberSorted() " +
                    "key cannot be null");

        if (!Util.isSorted(array)) {
            throw new IllegalArgumentException(MemberShip.class.getSimpleName() + ".isMemberSorted() " +
                    "array must be sorted.");
        }

        return (BinarySearch.search(array, key) != -1);
    }

}
