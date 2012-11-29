package srt.tool;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BinaryExpr;
import srt.ast.BlockStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.HavocStmt;
import srt.ast.IfStmt;
import srt.ast.Stmt;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class PredicationVisitor extends DefaultVisitor {

	private String freshVariableSeed;

	private DeclRef parentPredicate;
	
	private DeclRef globalPredicate;
	private final String globalPredicateName;
	private int globalPredicateNumber;

	public PredicationVisitor() {
		super(true);
		globalPredicate = new DeclRef("$G");
		freshVariableSeed = "B";
		globalPredicateName = "$A";
		globalPredicateNumber = 0;
	}
	
	private void updateGlobalVariable() {
		globalPredicateNumber += 1;
	}
	
	private String getCurrentGlobalVariable() {
		return globalPredicateName + String.valueOf(globalPredicateNumber);
	}

	/**
	 * Fresh variable generator
	 * 
	 * @return a fresh variable that has not been used before
	 */
	private String getFreshVariable(boolean isPredicate) {
		String result = (isPredicate) ? "$"+ freshVariableSeed : freshVariableSeed;
		if (freshVariableSeed.charAt(freshVariableSeed.length()-1) == 'Z') {
			freshVariableSeed.concat("A");
		} else {
			char lastChar = freshVariableSeed.charAt(freshVariableSeed.length()-1);
			freshVariableSeed = freshVariableSeed.substring(0, freshVariableSeed.length()-1);
			freshVariableSeed += (char) (lastChar+1);
		}
		return result;
	}

	@Override
	public Object visit(IfStmt ifStmt) {
		// Get a fresh variable for this if condition
		BlockStmt stmts;
		Expr rhs;

		DeclRef newPredicate = new DeclRef(getFreshVariable(true));

		if (parentPredicate == null) {
			rhs = ifStmt.getCondition();
		} else {
			rhs = new BinaryExpr(BinaryExpr.LAND, parentPredicate, ifStmt.getCondition());
		}
		AssignStmt predicateIfAssignStmt = new AssignStmt(newPredicate, rhs);

		DeclRef oldParentPredicate = parentPredicate;
		parentPredicate = newPredicate;

		// Process everything in the IF body with the current predicate set to the fresh variable
		Stmt thenStmt = (Stmt) visit(ifStmt.getThenStmt());

		// If there is an else statement
		if (ifStmt.getElseStmt() != null) {
			// Create predicate with negated if-condition

			parentPredicate = oldParentPredicate;
			newPredicate = new DeclRef(getFreshVariable(true));
			if (parentPredicate == null) {
				rhs = new UnaryExpr(UnaryExpr.LNOT, ifStmt.getCondition());
			} else {
				rhs = new BinaryExpr(BinaryExpr.LAND, parentPredicate, new UnaryExpr(UnaryExpr.LNOT, ifStmt.getCondition()));
			}
			AssignStmt predicateElseAssignStmt = new AssignStmt(newPredicate, rhs);

			oldParentPredicate = parentPredicate;
			parentPredicate = newPredicate;		
			Stmt elseStmt = (Stmt) visit(ifStmt.getElseStmt());
			stmts = new BlockStmt(new Stmt[] { predicateIfAssignStmt, thenStmt,  predicateElseAssignStmt, elseStmt},
					/* basedOn= */ifStmt);
		} else {
			stmts = new BlockStmt(new Stmt[] { predicateIfAssignStmt, thenStmt},
					/* basedOn= */ifStmt);
		}
		parentPredicate = oldParentPredicate;
		return stmts;
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
		Expr rhs = assertStmt.getCondition();
		Expr lhs;
		if (parentPredicate != null) {
			lhs = new UnaryExpr(UnaryExpr.LNOT, new BinaryExpr(BinaryExpr.LAND, globalPredicate, parentPredicate));
		} else {
			lhs = new UnaryExpr(UnaryExpr.LNOT, globalPredicate);
		}
		return new AssertStmt(new BinaryExpr(BinaryExpr.LOR, lhs, rhs), assertStmt);
	}

	@Override
	public Object visit(AssignStmt assignment) {
		// Build Ternary Predicate
		Expr condition;
		if (parentPredicate != null) {
			condition = new BinaryExpr(BinaryExpr.LAND, globalPredicate, parentPredicate);
		} else {
			condition = globalPredicate;
		}
		Expr e = new TernaryExpr(condition, assignment.getRhs(), assignment.getLhs());
		return new AssignStmt(assignment.getLhs(), e);
		//return super.visit(assignment);
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {
		DeclRef freshVar = new DeclRef(getFreshVariable(true));
		Expr assignment;
		Expr lhs;
		if (parentPredicate != null) {
			lhs = new UnaryExpr(UnaryExpr.LNOT, new BinaryExpr(BinaryExpr.LAND, globalPredicate, parentPredicate));
		} else {
			lhs = new UnaryExpr(UnaryExpr.LNOT, globalPredicate);
		}
		Expr rhs = assumeStmt.getCondition();
		assignment = new BinaryExpr(BinaryExpr.LOR, lhs, rhs);
		Stmt newStatement = new AssignStmt(freshVar, assignment);
		// New action on G
		Stmt newG = new AssignStmt(globalPredicate, new BinaryExpr(BinaryExpr.LAND, globalPredicate, freshVar));
		BlockStmt stmts = new BlockStmt(new Stmt[] { newStatement, newG},
				/* basedOn= */assumeStmt);
		//return stmts;
		return super.visit(assumeStmt);

	}

	@Override
	public Object visit(HavocStmt havocStmt) {
		
		DeclRef x = havocStmt.getVariable();
		Expr condition;
		Expr havocedVar;
		String newDeclRef = getFreshVariable(false);
		
		// Check global and parent predicate
		if (parentPredicate != null) {
			condition = new BinaryExpr(BinaryExpr.LAND, globalPredicate, parentPredicate);
		} else {
			condition = globalPredicate;
		}

		havocedVar = new DeclRef(newDeclRef);
		Stmt s = new Decl(newDeclRef, "int");
		Stmt e = new AssignStmt(x, new TernaryExpr(condition, havocedVar, x), havocStmt);
		BlockStmt stmts = new BlockStmt(new Stmt[] { s, e},
				/* basedOn= */havocStmt);
		return stmts;
	}

}
