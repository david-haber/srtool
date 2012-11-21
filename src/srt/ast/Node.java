package srt.ast;

import java.util.ArrayList;
import java.util.List;

import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.Tree;

public abstract class Node implements Cloneable {
	ArrayList<Node> children = new ArrayList<Node>();
	Object tokenInfo = null;
	
	public Node(Node basedOn) {
		if(basedOn != null) {
			tokenInfo = basedOn.getTokenInfo();
		}
	}
	
	public List<Node> getChildrenCopy() {
		return new ArrayList<Node>(children);
	}
	
	public Node withNewChildren(List<Node> newChildren) {
		try {
			Node newNode = (Node) super.clone();
			newNode.children = new ArrayList<Node>(newChildren);
			if(tokenInfo != null)
			{
				newNode.tokenInfo = new CommonTree((CommonTree) tokenInfo);
			}
			return newNode;
		} catch (CloneNotSupportedException e) {
			throw new RuntimeException(e);
		}
	}
	
	public Tree getTokenInfo() {
		if(tokenInfo == null) {
			return null;
		}
		else {
			return new CommonTree((CommonTree) tokenInfo);
		}
	}
	
}
