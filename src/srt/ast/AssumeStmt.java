package srt.ast;

public class AssumeStmt extends Stmt {
	
	public AssumeStmt(Expr condition) {
		this(condition, null);
	}
	
	public AssumeStmt(Expr condition, Node basedOn) {
		super(basedOn);
		children.add(condition);
	}
	
	public Expr getCondition() {
		return (Expr) children.get(0);
	}
}
