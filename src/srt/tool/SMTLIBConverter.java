package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import srt.ast.Expr;

public class SMTLIBConverter {
	
	private ExprToSmtlibVisitor exprConverter;
	private StringBuilder query;
	
	public SMTLIBConverter(Set<String> variableNames, List<Expr> transitionExprs, List<Expr> propertyExprs) {
		
		if(propertyExprs.size() == 0)
		{
			throw new IllegalArgumentException("No assertions.");
		}
		
		// QF_BV allows quantiﬁer-free expressions, including the family of bit-vector sorts and all of the
		// functions deﬁned in the Fixed_Size_BitVectors theory (but no other new sorts or functions).
		
		exprConverter = new ExprToSmtlibVisitor();
		query = new StringBuilder("(set-logic QF_BV)\n" +
				"(declare-sort Int 0)\n"+
				"(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n" +
				"(define-fun bv32tobool ((b  (_ BitVec 32))) (Bool) (= b (_ bv1 32) ))\n");
		// TODO: Define more functions above (for convenience), as needed.

		// TODO: Add constraints, add properties to check
		// here.
		
		// Declare Variables
		for (String var : variableNames) {
			String line = "(declare-fun " + var + " () (_ BitVec 32))\n";
			query.append(line);
		}
		
		// Add constraints
		for (Expr e : transitionExprs) {
			String line = "(assert (bv32tobool "+exprConverter.visit(e) + "))\n";
			query.append(line);
		}
		
		// Check that one of the assertion properties can fail
		// TODO what if no properties?
		String line = "(assert (not "+buildPropertyFormula(propertyExprs)+"))\n";
		query.append(line);
		query.append("(check-sat)\n");
		System.out.println(query.toString());
	}

	public String getQuery() {
		return query.toString();
	}
	
	public List<Integer> getPropertiesThatFailed(String queryResult) {
		List<Integer> res = new ArrayList<Integer>();
		
		return res;
	}
	
	private String buildPropertyFormula(List<Expr> expressions) {
		if (expressions.isEmpty()) {
			return "";
		}
		String result = "(and (bv32tobool %s) %s)";
		Expr expression = expressions.remove(0);
		String e = exprConverter.visit(expression);
		return String.format(result, e, buildPropertyFormula(expressions));
	}
	
}
