package srt.tool;

import java.util.LinkedList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BlockStmt;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.ExprList;
import srt.ast.HavocStmt;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
import srt.ast.Stmt;
import srt.ast.StmtList;
import srt.ast.TernaryExpr;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class LoopAbstractionVisitor extends DefaultVisitor {

	public LoopAbstractionVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		
		// get loop components
		ExprList loopInvariants = whileStmt.getInvariantList();
		List<Expr> loopInvariantExprs = loopInvariants.getExprs();
		Expr loopCond = whileStmt.getCondition();
		Stmt loopBody = whileStmt.getBody();
		
		List<Stmt> stmts = new LinkedList<Stmt>();
		
		// establish that invariant holds on loop entry
		List<Stmt> loopInvariantAssertStmts = new LinkedList<Stmt>();
		// add assert statement for every invariant
		for (Expr e : loopInvariantExprs) {
			// 'based on' when creating assert stmt?
			loopInvariantAssertStmts.add(new AssertStmt(e));
		}
		stmts.addAll(loopInvariantAssertStmts);
		
		// teleport to arbitrary loop iteration satisfying invariants
		DeclRef havocVar = (DeclRef) loopCond.getChildrenCopy().get(0); // TODO THIS WILL BREAK FOR SURE
		stmts.add(new HavocStmt(havocVar)); 
		// generate assume statements for every invariant to cut off paths
		// that do not satisfy invariant
		List<Stmt> loopEntryAssumeStmts = new LinkedList<Stmt>();
		for (Expr e : loopInvariantExprs) {
			// 'based on' when creating assert stmt?
			loopEntryAssumeStmts.add(new AssumeStmt(e));
		}
		stmts.addAll(loopEntryAssumeStmts);
		
		// create if then body
		List<Stmt> ifStmtsBody = new LinkedList<Stmt>();
		// visit loop body
		ifStmtsBody.add((Stmt) visit(loopBody));
		// insert assert statements to check that loop invariant holds at end of body
		ifStmtsBody.addAll(loopInvariantAssertStmts);
		// insert assume(false) statement to block further loop execution
		ifStmtsBody.add(new AssumeStmt(new IntLiteral(0))); // TODO false?
		
		BlockStmt newIfThenBody = new BlockStmt(ifStmtsBody);
		// create complete if statement with loop condition
		Stmt ifStmt = new IfStmt(loopCond, newIfThenBody, null);
		
		stmts.add(ifStmt);
		
		return new BlockStmt(stmts);
	}

}
