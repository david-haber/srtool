package srt.ast;

import java.util.List;

public class ExprList extends Node {
	
	public ExprList(Expr[] exprs) {
		this(exprs, null);
	}
	
	public ExprList(Expr[] exprs, Node basedOn) {
		super(basedOn);
		for(Expr e : exprs) {
			children.add(e);
		}
	}
	
	@SuppressWarnings("unchecked")
	public List<Expr> getExprs() {
		return (List<Expr>)children.clone();
	}
}
