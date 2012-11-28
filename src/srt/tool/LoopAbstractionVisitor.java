package srt.tool;

import java.util.List;

import srt.ast.AssertStmt;
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
		Stmt[] loopInvariantAsserts = new Stmt[loopInvariantExprs.size()];
		// add assert statement for every invariant
		for (int i = 0; i < loopInvariantExprs.size(); i++) {
			// 'based on' when creating assert stmt?
			loopInvariantAsserts[i] = new AssertStmt(loopInvariantExprs.get(i));
		}
		Stmt loopEntryAssertBlockStmt = (Stmt) new BlockStmt(loopInvariantAsserts);
		
		// teleport to arbitrary loop iteration satisfying invariants
		DeclRef havocVar = (DeclRef) loopCond.getChildrenCopy().get(0);
		Stmt havocedVar = new HavocStmt(havocVar); // TODO THIS WILL BREAK FOR SURE
		// generate assume statements for every invariant to cut off paths
		// that do not satisfy invariant
		Stmt[] loopEntryAssumes = new Stmt[loopInvariantExprs.size()];
		for (int i = 0; i < loopInvariantExprs.size(); i++) {
			// 'based on' when creating assert stmt?
			loopEntryAssumes[i] = new AssumeStmt(loopInvariantExprs.get(i));
		}
		Stmt loopEntryAssumeBlockStmt = (Stmt)new BlockStmt(loopEntryAssumes);
		
		// create if then body
		Stmt[] stmts = new Stmt[loopInvariantAsserts.length + 2];
		// visit loop body
		stmts[0] = (Stmt) visit(loopBody);
		// insert assert statements to check that loop invariant holds at end of body
		for (int i = 1; i <= loopInvariantAsserts.length; i++) {
			stmts[i] = loopInvariantAsserts[i-1];
		}
		// insert assume(false) statement to block further loop execution
		stmts[stmts.length-1] = new AssumeStmt(new IntLiteral(0)); // TODO false?
		
		StmtList stmtList = new StmtList(stmts);
		BlockStmt newIfThenBody = new BlockStmt(stmtList);
		// create complete if statement with loop condition
		Stmt ifStmt = new IfStmt(loopCond, newIfThenBody, null);
		
		return new BlockStmt(new Stmt[] {loopEntryAssertBlockStmt, havocedVar, loopEntryAssumeBlockStmt, ifStmt},
				/* basedOn= */whileStmt);
	}

}
