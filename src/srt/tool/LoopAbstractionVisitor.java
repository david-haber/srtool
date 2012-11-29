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
		
		// establish that invariant holds on loop entry
		List<Stmt> loopInvariantAssertStmts = new LinkedList<Stmt>();
		// add assert statement for every invariant
		for (Expr e : loopInvariantExprs) {
			// 'based on' when creating assert stmt?
			loopInvariantAssertStmts.add(new AssertStmt(e));
		}
		Stmt loopEntryAssertBlockStmt = (Stmt) new BlockStmt(loopInvariantAssertStmts);
		
		// teleport to arbitrary loop iteration satisfying invariants
		DeclRef havocVar = (DeclRef) loopCond.getChildrenCopy().get(0); // TODO THIS WILL BREAK FOR SURE
		Stmt havocStmt = new HavocStmt(havocVar); 
		// generate assume statements for every invariant to cut off paths
		// that do not satisfy invariant
		List<Stmt> loopEntryAssumeStmts = new LinkedList<Stmt>();
		for (Expr e : loopInvariantExprs) {
			// 'based on' when creating assert stmt?
			loopEntryAssumeStmts.add(new AssumeStmt(e));
		}
		Stmt loopEntryAssumeBlockStmt = (Stmt)new BlockStmt(loopEntryAssumeStmts);
		
		// create if then body
		List<Stmt> stmts = new LinkedList<Stmt>();
		// visit loop body
		stmts.add((Stmt) visit(loopBody));
		// insert assert statements to check that loop invariant holds at end of body
		stmts.addAll(loopInvariantAssertStmts);
		// insert assume(false) statement to block further loop execution
		stmts.add(new AssumeStmt(new IntLiteral(0))); // TODO false?
		
		StmtList stmtList = new StmtList(stmts);
		BlockStmt newIfThenBody = new BlockStmt(stmtList);
		// create complete if statement with loop condition
		Stmt ifStmt = new IfStmt(loopCond, newIfThenBody, null);
		
		
		return new BlockStmt(new Stmt[] {loopEntryAssertBlockStmt, havocStmt, loopEntryAssumeBlockStmt, ifStmt},
				/* basedOn= */whileStmt);
	}

}
