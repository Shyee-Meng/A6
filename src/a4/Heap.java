package a4;

import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.NoSuchElementException;

import org.junit.jupiter.api.Test;

public class Heap<E, P> implements PriorityQueue<E, P> {
	private final Comparator<? super P> cmp;
	
	private class Node implements Comparable<Node> {
		E value;
		P priority;
		Node(E value, P priority) {
			this.value = value; this.priority = priority;
		}
		
		public int compareTo(Node other) {
			return cmp.compare(this.priority, other.priority);
		}
		
		public String toString() {
			return value + " (" + priority + ")";
		}
	}
	
	/** invariant: is a heap. */
	private ArrayList<Node>     heap;
	
	/** invariant: heap[index[o]].value.equals(o) */
	private HashMap<E, Integer> index;
	
	public Heap(Comparator<P> cmp) {
		this.cmp   = cmp;
		this.heap  = new ArrayList<Node>();
		this.index = new HashMap<E, Integer>();
	}
	
	@Override
	public Comparator<? super P> comparator() {
		return this.cmp;
	}

	@Override
	public int size() {
		return this.heap.size();
	}
	
	@Override
	public String toString() {
		ArrayList<Node> result = new ArrayList<>(heap);
		result.sort(Comparator.naturalOrder());
		return result.toString();
	}

	@Override
	public E poll() throws NoSuchElementException {
		if (size() == 0)
			throw new NoSuchElementException();
		
		swap(0, size()-1);
		E result = this.heap.remove(size()-1).value;
		this.index.remove(result);
		
		bubbleDown(0);
		
		return result;
	}

	@Override
	public E peek() throws NoSuchElementException {
		if (this.size() == 0)
			throw new NoSuchElementException();
		return this.heap.get(0).value;
	}

	public P priority(E e) {
		int i = this.index.get(e);
		return heap.get(i).priority;
	}
	
	@Override
	public void add(E e, P p) throws IllegalArgumentException {
		if (this.index.containsKey(e))
			throw new IllegalArgumentException("Duplicate insertion into heap");

		this.heap.add(new Node(e,p));
		this.index.put(e, this.size()-1);
		bubbleUp(this.size() - 1);
	}

	@Override
	public void changePriority(E e, P p) throws NoSuchElementException {
		int i = this.index.get(e);
		this.heap.get(i).priority = p;
		bubbleUp(i);
		bubbleDown(i);
	}

	
	// helper methods //////////////////////////////////////////////////////////
	
	/** return the index of the parent of the node at index i */
	private int parent(int i) {
		if (i <= 0)
			return -1;
		
		return (i - 1)/2;
	}
	
	/** return the index of the left of the node at index i */
	private int left(int i) {
		return 2*i + 1;
	}
	
	/** return the index of the right of the node at index i */
	private int right(int i) {
		return 2*i + 2;
	}
	
	/** swap the nodes at positions i and j, maintaining the index */
	private void swap(int i, int j) {
		Node entryi = this.heap.get(i);
		Node entryj = this.heap.get(j);
		
		this.heap.set(i, entryj);
		this.heap.set(j, entryi);
		this.index.put(entryi.value, j);
		this.index.put(entryj.value, i);
	}
	
	private boolean hasLeft(int i) {
		return left(i) < size();
	}
	
	private boolean hasRight(int i) {
		return right(i) < size();
	}
	
	/** compare the priorities of nodes i and j.  indices with negative indices
	 * are treated as infinitely large, while indices past the end of the heap
	 * are treated as infinitely small. 
	 * 
	 * @return is < 0 if i < j, 0 if i = j, and > 0 if i > j 
	 */
	private int compare(int i, int j) {
		if (i < 0 && j < 0)
			return 0;
		if (i < 0)
			return 1;
		if (j < 0)
			return -1;
		if (i >= size() && j >= size())
			return 0;
		if (i >= size())
			return -1;
		if (j >= size())
			return 1;
		
		return cmp.compare(this.heap.get(i).priority, this.heap.get(j).priority);
	}
	
	/**
	 * Precondition: heap is a heap, except that node i might be larger than
	 * its parent
	 * 
	 * Postcondition: heap is a heap.
	 */
	private void bubbleUp(int i) {
		// invariant: heap is a heap, except that node i might be larger than its parent
		while (compare(i, parent(i)) > 0) {
			swap(i, parent(i));
			i = parent(i);
		}
	}
	
	/**
	 * Precondition: heap is a heap, except that node i might be smaller than
	 * one of its children.
	 * 
	 * Postcondition: heap is a heap.
	 */
	private void bubbleDown(int i) {
		// invariant: heap is a heap, except that node i might be less than one
		// of its children.
		while (compare(i,left(i)) < 0 || compare(i,right(i)) < 0) {
			int k = compare(left(i), right(i)) > 0 ? left(i) : right(i);
			swap(i,k);
			i = k;
		}
	}
	
	// Testing /////////////////////////////////////////////////////////////////
	
	private void checkInvariants() {
		assertEquals(heap.size(), index.size());
		for (int i = 0; i < size(); i++)
			assertTrue(compare(i,parent(i)) < 0);
		for (E o : this.index.keySet())
			assertEquals(o, this.heap.get(this.index.get(o)).value);
	}
	
	public static class Tests {

		@Test
		public void tests() {
			Comparator<Integer> cmp = Comparator.naturalOrder();
			Heap<String,Integer> h = new Heap<String,Integer>(cmp);
			h.checkInvariants();
			h.add("one", 1);
			h.add("two", 2);
			h.add("seven", 7);
			h.checkInvariants();
			assertEquals(3,h.size());
			assertEquals("seven", h.peek());
			assertEquals("seven", h.poll());
			h.checkInvariants();
			assertEquals("two", h.poll());
			h.checkInvariants();
			assertEquals("one", h.poll());
			h.checkInvariants();
			assertEquals(0, h.size());
		}
	}
}
