package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
	private Map<String, Integer> index = new HashMap<String, Integer>();

	public SSAVisitor() {
		super(true);
	}
	
	private String getSSAName(String name) {
		return null;
	}
	
	private void incrementSSAIndex(String name) {
		
	}
	
	@Override
	public Object visit(Decl decl) {
		return super.visit(decl);
	}
	
	@Override
	public Object visit(DeclRef declRef) {
		return super.visit(declRef);
	}
	
	@Override
	public Object visit(AssignStmt assignment) {
		return super.visit(assignment);
	}

}
