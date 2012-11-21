package srt.tool;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.BinaryExpr;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.Node;
import srt.ast.visitor.impl.DefaultVisitor;

public class CollectConstraintsVisitor extends DefaultVisitor {
	
	public Set<String> variableNames = new HashSet<String>();
	
	public List<Node> transitionNodes = new ArrayList<Node>();
	public List<Expr> transitionExprs = new ArrayList<Expr>();
	
	public List<Node> propertyNodes = new ArrayList<Node>();
	public List<Expr> propertyExprs = new ArrayList<Expr>();
	
	
	public CollectConstraintsVisitor() {
		super(false);
	}
	
	@Override
	public Object visit(DeclRef declRef) {
		variableNames.add(declRef.getName());
		return super.visit(declRef);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
		propertyNodes.add(assertStmt);
		propertyExprs.add(assertStmt.getCondition());
		return super.visit(assertStmt);
	}

	@Override
	public Object visit(AssignStmt assignment) {
		transitionNodes.add(assignment);
		transitionExprs.add(new BinaryExpr(BinaryExpr.EQUAL, assignment
				.getLhs(), assignment.getRhs(), assignment));
		return super.visit(assignment);
	}
	
}




