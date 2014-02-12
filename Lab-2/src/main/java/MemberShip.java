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
    public static <T extends Comparable<? super T>> boolean isMember(T[] array, T key) {
        if (array == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + "isMember() " +
                    "array cannot be null");
        if (key == null)
            throw new NullPointerException(MemberShip.class.getSimpleName() + "isMember() " +
                    "key cannot be null");

        // Quickly sort the array.
        QuickSort.sort(array);

        // Return whether the index was found after doing search.
        return (BinarySearch.search(array, key) != -1);
    }

}
