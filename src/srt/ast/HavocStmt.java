package srt.ast;

public class HavocStmt extends Stmt {
	
	public HavocStmt(DeclRef variable) {
		this(variable, null);
	}
	
	public HavocStmt(DeclRef variable, Node basedOn)
	{
		super(basedOn);
		children.add(variable);
	}
	
	public DeclRef getVariable() {
		return (DeclRef) children.get(0);
	}
}
