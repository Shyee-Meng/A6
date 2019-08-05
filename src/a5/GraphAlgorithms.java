package a5;
import game.FindState;
import game.FleeState;
import game.NodeStatus;
import game.SewerDiver;
//import game.Node;

import java.util.ArrayList;
import java.util.Comparator;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import a4.Heap;
import graph.Edge;
import graph.Graph;
import graph.Node;
import graph.LabeledEdge;

public class GraphAlgorithms  { 
	
	
//	public static List<>
	/** Return the Nodes reachable from start in depth-first-search order */
	public static <N extends Node<N,E>, E extends Edge<N,E>>
	List<N> dfs(N start) {
		
		Stack<N> worklist = new Stack<N>();
		worklist.add(start);
		
		Set<N>   visited  = new HashSet<N>();
		List<N>  result   = new ArrayList<N>();
		while (!worklist.isEmpty()) {
			// invariants:
			//    - everything in visited has a path from start to it
			//    - everything in worklist has a path from start to it
			//      that only traverses visited nodes
			//    - nothing in the worklist is visited
			N next = worklist.pop();
			visited.add(next);
			result.add(next);
			for (N neighbor : next.outgoing().keySet())
				if (!visited.contains(neighbor))
					worklist.add(neighbor);
		}
		return result;
	}
	
	private static class Path<N,E> {
		N           node;
		Path<N,E>   parent;
		int         distance;
		boolean     settled;
		
		public Path(N current, Path<N,E> parent, int distance) {
			this.node = current; this.parent = parent; this.distance = distance;
		}
		
		public List<N> toList() {
			List<N> rest = parent == null ? new ArrayList<>() : parent.toList();
			rest.add(node);
			return rest;
		}
	}
	
	/**
	 * Return a minimal path from start to end.  This method should return as
	 * soon as the shortest path to end is known; it should not continue to search
	 * the graph after that. 
	 * 
	 * @param <N> The type of nodes in the graph
	 * @param <E> The type of edges in the graph; the weights are given by e.label()
	 * @param start The node to search from
	 * @param end   The node to find
	 */
	public static <N extends Node<N,E>, E extends LabeledEdge<N,E,Integer>>
	List<N> shortestPath(N start, N end) {
		Heap<N,Integer>   worklist = new Heap<N,Integer>(Comparator.reverseOrder());
		Map<N,Path<N,E>> distance  = new HashMap<>();
		
		worklist.add(start,0);
		distance.put(start,new Path<N,E>(start,null,0));
		
		while(worklist.size() > 0) {
			// invariants:
			//   - distance[v] gives the shortest path to v passing only through
			//     visited nodes
			//   - distance[v] is defined for every node in the worklist and the
			//     visited set
			//   - the worklist's priority for v is equal to distance[v].distance
			N         current  = worklist.poll();
			Path<N,E> currPath = distance.get(current);
			currPath.settled = true;
			
			if (current.equals(end))
				return currPath.toList();
			
			for(E e : current.outgoing().values()) {
				int d = currPath.distance + e.label();
				Path<N,E> oldPath = distance.get(e.target());
				if (oldPath == null) {
					worklist.add(e.target(), d);
					distance.put(e.target(), new Path<>(e.target(), currPath, d));
				} else if (oldPath.settled) {
					continue;
				}
				else if (d < oldPath.distance) {
					oldPath.parent   = currPath;
					oldPath.distance = d;
					worklist.changePriority(e.target(), d);
				}
			}
		}
		return new ArrayList<>();
	}
	
}
