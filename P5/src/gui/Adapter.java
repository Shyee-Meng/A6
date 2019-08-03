package gui;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import a5.GraphAlgorithms;
import common.Wrapper;

public class Adapter extends Wrapper<Graph> implements graph.Graph<Adapter.Node,Adapter.Edge> {
	public class Node extends Wrapper<NodeData> implements graph.Node<Node, Edge>{

		private Node(NodeData impl) {
			super(impl);
		}
	
		public Map<Node, Edge> edges(boolean thisIsSource) {
			Map<Node,Edge> result = new HashMap<>();
			
			for (EdgeData e : this.impl.getExits()) {
				NodeData other = e.getOther(this.impl);
				Node     otherWrapper = new Node(other);
				
				Edge wrapper = thisIsSource
						   ? new Edge(e,this,otherWrapper)
						   : new Edge(e,otherWrapper,this);
				result.put(otherWrapper, wrapper);
			}
			return result;
		}
		@Override public Map<Node, Edge> outgoing() { return edges(true); }
		@Override public Map<Node, Edge> incoming() { return edges(false); }

	}
	
	public class Edge extends Wrapper<EdgeData> implements graph.LabeledEdge<Node,Edge,Integer> {
		private Node     source;
		private Node     target;
		
		private Edge(EdgeData e, Node source, Node target) {
			super(e);
			this.source = source;
			this.target = target;
		}

		@Override
		public Node source() {
			return this.source;
		}

		@Override
		public Node target() {
			return this.target;
		}

		@Override
		public Integer label() {
			return this.impl.length;
		}
		
	}
	
	public Adapter(Graph g) {
		super(g);
	}

	@Override
	public boolean isEmpty() {
		return this.impl.getNodesSize() == 0;
	}

	@Override
	public Collection<? extends Node> nodes() {
		List<Node> result = new ArrayList<>();
		for (NodeData n : this.impl.getNodes())
			result.add(new Node(n));
		return result;
	}

	@Override
	public Collection<? extends Edge> edges() {
		List<Edge> result = new ArrayList<>();
		for (EdgeData e : this.impl.getEdges()) {
			Node n1 = new Node(e.getFirstExit());
			Node n2 = new Node(e.getSecondExit());
			result.add(new Edge(e, n1,n2));
			result.add(new Edge(e, n2,n1));
		}
		return result;
	}
	
	public Node wrap(NodeData d) {
		return new Node(d);
	}
	
	public static List<NodeData> shortest(NodeData start, NodeData end) {
		Adapter g = new Adapter(start.getGraph());
		Adapter.Node u = g.wrap(start);
		Adapter.Node v = g.wrap(end);
		List<Adapter.Node> nodes = GraphAlgorithms.shortestPath(u, v);
		List<NodeData> data = new ArrayList<>();
		for (Adapter.Node wrapper : nodes)
			data.add(wrapper.impl());
		return data;
	}
}
