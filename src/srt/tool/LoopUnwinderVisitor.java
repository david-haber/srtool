package srt.tool;

import java.util.LinkedList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssumeStmt;
import srt.ast.BlockStmt;
import srt.ast.EmptyStmt;
import srt.ast.Expr;
import srt.ast.ExprList;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
import srt.ast.Stmt;
import srt.ast.UnaryExpr;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class LoopUnwinderVisitor extends DefaultVisitor {

	private boolean unwindingAssertions;
	private int defaultUnwindBound;

	public LoopUnwinderVisitor(boolean unwindingAssertions,
			int defaultUnwindBound) {
		super(true);
		this.unwindingAssertions = unwindingAssertions;
		this.defaultUnwindBound = defaultUnwindBound;
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		int bounds = (whileStmt.getBound() == null) ? defaultUnwindBound : whileStmt.getBound().getValue();
		List<Stmt> stmts = new LinkedList<Stmt>();
		Expr condition = whileStmt.getCondition();
		if (bounds == 0) {
			if (unwindingAssertions) {
				stmts.add(new AssertStmt(new UnaryExpr(UnaryExpr.LNOT, condition), condition));
			}
			stmts.add(new AssumeStmt(new UnaryExpr(UnaryExpr.LNOT, condition), condition));
			return new BlockStmt(stmts, whileStmt);
		}
		ExprList invariants = whileStmt.getInvariantList();
		if (invariants != null) {
			List<Expr> invariantsList = invariants.getExprs();
			for (Expr e : invariantsList) {
				stmts.add(new AssertStmt(e, e));
			}
		}
		List<Stmt> ifStmtBody = new LinkedList<Stmt>();
		ifStmtBody.add((Stmt) this.visit(whileStmt.getBody()));
		WhileStmt innerStmt = new WhileStmt(whileStmt.getCondition(), new IntLiteral(bounds-1), whileStmt.getInvariantList(), whileStmt.getBody(), whileStmt);
		ifStmtBody.add((Stmt) visit(innerStmt));
		stmts.add(new IfStmt(condition, new BlockStmt(ifStmtBody), new EmptyStmt()));
		return new BlockStmt(stmts, whileStmt);
	}

}
