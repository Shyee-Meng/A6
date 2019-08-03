package a4;

import static org.junit.jupiter.api.Assertions.*;

import java.util.Comparator;
import java.util.NoSuchElementException;

import org.junit.jupiter.api.Test;

class HeapTest {
	
	/*
	 * Helper
	 */

	//Initializes an empty heap
	private Heap<String,Integer> initializeEmpty(){
		Comparator<Integer> cmp = Comparator.naturalOrder();
		return new Heap<String,Integer>(cmp);
	}
	
	/*
	 * A-level
	 */
	
	@Test
	void testPollError() {
		Heap<String,Integer> h = initializeEmpty();
		assertThrows(NoSuchElementException.class, () -> { h.poll(); });
	}
	
	@Test
	void testPeekError() {
		Heap<String,Integer> h = initializeEmpty();
		assertThrows(NoSuchElementException.class, () -> { h.peek(); });
	}
	
	@Test
	void testAddError() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		assertThrows(IllegalArgumentException.class, () -> { h.add("one",2); });
	}
	
	@Test
	void testChangePriorityError() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		assertThrows(NoSuchElementException.class, () -> { h.changePriority("two", 1); });
	}
	
	/*
	 * B-level
	 */
	
	@Test
	void testPeekSingleton() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		assertEquals(1, h.size());
		assertEquals("one", h.peek());
	}
	
	@Test
	void testPollSingleton() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		assertEquals(1, h.size());
		assertEquals("one", h.poll());
	}
	
	@Test
	void testEverything() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("three", 3);
		h.add("one", 1);
		h.add("five", 5);
		h.add("two", 2);
		h.add("four", 4);
		assertEquals(5, h.size());
		assertEquals("five", h.peek());
		h.changePriority("three", 10);
		assertEquals("three", h.poll());
		assertEquals(4, h.size());
		assertEquals("five", h.peek());
		assertEquals("five", h.poll());
		assertEquals("four", h.poll());
		assertEquals("two", h.poll());
		assertEquals(1, h.size());
	}
	
	/*
	 * C-level
	 */
	
	@Test
	void testConstructor() {
		Comparator<Integer> cmp = Comparator.naturalOrder();
		Heap<String,Integer> h = new Heap<String,Integer>(cmp);
		assertEquals(cmp, h.comparator());
		assertEquals(0, h.size());
		//assertEquals("[]",h.toString());
	}
	
	@Test
	void testSize() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		assertEquals(1, h.size());
		h.add("two", 2);
		assertEquals(2, h.size());
		h.add("three", 3);
		assertEquals(3, h.size());
	}
	
	@Test
	void testChangePriority() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		h.add("two", 2);
		assertEquals("two", h.peek());
		h.changePriority("one", 3);
		assertEquals("one", h.peek());
	}
	
	@Test
	void testAddInOrder() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		h.add("two", 2);
		h.add("three", 3);
		h.add("four", 4);
		h.add("five", 5);
		assertEquals("five", h.peek());
	}
	
	@Test
	void testAddOutOfOrder() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("three", 3);
		h.add("one", 1);
		h.add("five", 5);
		h.add("two", 2);
		h.add("four", 4);
		assertEquals("five", h.peek());
	}
	
	@Test
	void testPeek() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		h.add("two", 2);
		h.add("three", 3);
		h.add("four", 4);
		h.add("five", 5);
		assertEquals("five", h.peek());
		h.poll();
		h.poll();
		assertEquals("three", h.peek());
	}
	
	@Test
	void testPoll() {
		Heap<String,Integer> h = initializeEmpty();
		h.add("one", 1);
		h.add("two", 2);
		h.add("three", 3);
		h.add("four", 4);
		h.add("five", 5);
		assertEquals("five", h.poll());
		assertEquals("four", h.poll());
		assertEquals("three", h.poll());
		assertEquals("two", h.poll());
		//assertEquals("one", h.poll());
	}
}
