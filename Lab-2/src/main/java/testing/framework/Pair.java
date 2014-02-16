package testing.framework;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Created by mhotan_dev on 2/13/14.
 */
public class Pair<T> implements Iterable<T> {

    private final T first, second;

    public Pair(T first, T second) {
        if (first == null || second == null) throw new NullPointerException();
        this.first = first;
        this.second = second;
    }

    public T getFirst() {
        return first;
    }

    public T getSecond() {
        return second;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Pair)) return false;
        Pair pair = (Pair) o;
        return first.equals(pair.first) && second.equals(pair.second) ||
                first.equals(pair.second) && second.equals(pair.first);
    }

    @Override
    public int hashCode() {
        int result = first != null ? first.hashCode() : 0;
        result = result + (second != null ? second.hashCode() : 0);
        return result;
    }

    @Override
    public Iterator<T> iterator() {
        List<T> elements = new ArrayList<T>();
        elements.add(first);
        elements.add(second);
        return elements.iterator();
    }

    @Override
    public String toString() {
        return "{" + first +
                "," + second +
                '}';
    }
}
