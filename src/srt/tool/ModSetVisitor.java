package srt.tool;
/**
 * Used to collect modset (e.g. in LoopAbstractionVisitor)
 */

import java.util.HashSet;
import java.util.Set;

import srt.ast.AssignStmt;
import srt.ast.DeclRef;
import srt.ast.visitor.impl.DefaultVisitor;

public class ModSetVisitor extends DefaultVisitor {
	
	private Set<DeclRef> modSet;
	
	public ModSetVisitor() {
		super(true);
		this.modSet = new HashSet<DeclRef>();
	}
	
	@Override
	public Object visit(AssignStmt assignment) {
		DeclRef lhs = assignment.getLhs();
		modSet.add(lhs);
		return visitChildren(assignment);
	}
	
	protected Set<DeclRef> getModSet() {
		return this.modSet;
	}

}
