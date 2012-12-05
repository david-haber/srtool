package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
	// Contains a mapping between a variable and its latest value
	private Map<String, Integer> index = new HashMap<String, Integer>();

	public SSAVisitor() {
		super(true);
	}
	
	/**
	 * 
	 * @param name 
	 * @return the correct name of the given variable name after SSA
	 */
	private String getSSAName(String name) {
		Integer i = index.get(name);
		return name+"$"+i;
	}
	
	private void incrementSSAIndex(String name) {
		Integer oldI = index.get(name);
		index.put(name, oldI+1);
	}
	

	@Override
	/**
	 * Registers a variable for SSA renaming
	 * @param delc
	 * @return a new decl statement with SSA renaming applied
	 */
	public Object visit(Decl decl) {
		String name = decl.getName();
		index.put(name, 0);
		return new Decl(getSSAName(name), decl.getType(), decl);
	}
	
	@Override
	/**
	 * @return the declRef updated with its correct SSA 
	 * 	name (if declRef is not a predicate)
	 */
	public Object visit(DeclRef declRef) {
		String name = declRef.getName();
		// We only apply SSA to non-predicates
		if (name.charAt(0) == '$') {
			return declRef;
		} else {
			return new DeclRef(getSSAName(name), declRef);
		}
	}
	
	@Override
	public Object visit(AssignStmt assignment) {
		Expr rhs = (Expr) this.visit(assignment.getRhs());
		String oldName = assignment.getLhs().getName();
		if (oldName.charAt(0) != '$') {
			// Update the internal index value for the variable
			incrementSSAIndex(oldName);
		}
		DeclRef lhs = (DeclRef) this.visit(assignment.getLhs());
		return new AssignStmt(lhs,rhs,assignment);
	}

}
