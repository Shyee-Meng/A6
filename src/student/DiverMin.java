package student;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import a4.Heap;
import a5.GraphAlgorithms;
import game.FindState;
import game.FleeState;
import game.NodeStatus;
import game.SewerDiver;
import game.Node;

import common.NotImplementedError;

public class DiverMin implements SewerDiver {

	/** Get to the ring in as few steps as possible. Once you get there, <br>
	 * you must return from this function in order to pick<br>
	 * it up. If you continue to move after finding the ring rather <br>
	 * than returning, it will not count.<br>
	 * If you return from this function while not standing on top of the ring, <br>
	 * it will count as a failure.
	 *
	 * There is no limit to how many steps you can take, but you will receive<br>
	 * a score bonus multiplier for finding the ring in fewer steps.
	 *
	 * At every step, you know only your current tile's ID and the ID of all<br>
	 * open neighbor tiles, as well as the distance to the ring at each of <br>
	 * these tiles (ignoring walls and obstacles).
	 *
	 * In order to get information about the current state, use functions<br>
	 * currentLocation(), neighbors(), and distanceToRing() in state.<br>
	 * You know you are standing on the ring when distanceToRing() is 0.
	 *
	 * Use function moveTo(long id) in state to move to a neighboring<br>
	 * tile by its ID. Doing this will change state to reflect your new position.
	 *
	 * A suggested first implementation that will always find the ring, but <br>
	 * likely won't receive a large bonus multiplier, is a depth-first walk. <br>
	 * Some modification is necessary to make the search better, in general. */
	@Override
	public void find(FindState state) {
		
		HashSet<Long> Visited= new HashSet<>();
		HashMap<Long, Long> backpointer= new HashMap<>();
		while (state.distanceToRing() != 0) {
			
			Collection<NodeStatus> neighbors= state.neighbors();
			
			Iterator<NodeStatus> iterator= neighbors.iterator();
			Iterator<NodeStatus> iterator2= neighbors.iterator();
			
			NodeStatus go= null;
			int count= 0;
			
			while (iterator.hasNext()) {
				
				if (count == 0) {
					NodeStatus temp= iterator.next();
					if (!Visited.contains(temp.getId())) {
						go= temp;
						count++ ;
					}
				} else {
					NodeStatus n= iterator.next();
					if (!Visited.contains(n.getId())) {
						count++ ;
						if (n.getDistanceToTarget() < state.distanceToRing()) {
							go= n;
						}
					}
				}
			}
			int s_count= 0;
			
			for (int i= 0; i < neighbors.size(); i++ ) {
				NodeStatus n= iterator2.next();
				if (Visited.contains(n.getId()))
					s_count++ ;
			}
			if (s_count == neighbors.size()) {
				state.moveTo(backpointer.get(state.currentLocation()));
			} else {
				Visited.add(go.getId());
				backpointer.put(go.getId(), state.currentLocation());
				state.moveTo(go.getId());
			}
		}
	}	
	
	/**Class for storing the current node and its backpointer.
	 * 
	 * @param Node the current node
	 * @param Node1 the backpointer node
	 */
	private static class path<Node,Node1> {
		Node           node;
		path<Node,Node1>   parent;
		int         distance;
		boolean     settled;
		
		public path(Node current, path<Node,Node1> parent, int distance) {
			this.node = current; this.parent = parent; this.distance = distance;
		}
		
		public List<Node> toList() {
			List<Node> rest = parent == null ? new ArrayList<>() : parent.toList();
			rest.add(node);
			return rest;
		}
	}
	
	
	/** Flee the sewer system before the steps are all used, trying to <br>
	 * collect as many coins as possible along the way. Your solution must ALWAYS <br>
	 * get out before the steps are all used, and this should be prioritized above<br>
	 * collecting coins.
	 *
	 * You now have access to the entire underlying graph, which can be accessed<br>
	 * through FleeState. currentNode() and getExit() will return Node objects<br>
	 * of interest, and getNodes() will return a collection of all nodes on the graph.
	 *
	 * You have to get out of the sewer system in the number of steps given by<br>
	 * getStepsRemaining(); for each move along an edge, this number is <br>
	 * decremented by the weight of the edge taken.
	 *
	 * Use moveTo(n) to move to a node n that is adjacent to the current node.<br>
	 * When n is moved-to, coins on node n are automatically picked up.
	 *
	 * You must return from this function while standing at the exit. Failing <br>
	 * to do so before steps run out or returning from the wrong node will be<br>
	 * considered a failed run.
	 *
	 * Initially, there are enough steps to get from the starting point to the<br>
	 * exit using the shortest path, although this will not collect many coins.<br>
	 * For this reason, a good starting solution is to use the shortest path to<br>
	 * the exit. */
	
	@Override
	public void flee(FleeState state) {
		shortestPath(state);
		return;
	}
		
	/**Helper method that uses Dijkstra's shortest path algorithm and moves DriverMin to the exit.
	 * 
	 */
	private void shortestPath(FleeState state) {
		//Shortest path part
		List<Node> way = new ArrayList<>();
		List<Node> worklist = new ArrayList<Node>();
		Map<Node,path<Node,Node>> distance  = new HashMap<>();
				
		worklist.add(state.currentNode());
		distance.put(state.currentNode(),new path<Node,Node>(state.currentNode(),null,0));
				
		int i = 0;
		Node      current  = worklist.get(i);
								
		while(worklist.size() > 0) {
					
		current  = worklist.get(i);
		path<Node,Node> currPath = distance.get(current);
		currPath.settled = true;
					worklist.remove(current);
					
					if (current.equals(state.getExit())) {
						way = currPath.toList();
						way.remove(state.currentNode());
						for (Node n:way) {
							state.moveTo(n);
						}
						return;
					}
					for(Node n : current.getNeighbors()) {
						int d = currPath.distance + current.getEdge(n).label();
						path<Node,Node> oldPath = distance.get(n);
						if (oldPath == null) {
							worklist.add(n);
							distance.put(n, new path<>(n, currPath, d));
						} else if (oldPath.settled) {
							i = 0;
							continue;
						}
						else if (d < oldPath.distance) {
							oldPath.parent   = currPath;
							oldPath.distance = d;
							i = worklist.indexOf(n);
						}
					} 
				}
				return;
	}
}

