package srt.ast;

import java.util.List;

public class BlockStmt extends Stmt {
	
	public BlockStmt(StmtList stmtList) {
		this(stmtList, null);
	}
	
	public BlockStmt(StmtList stmtList, Node basedOn) {
		super(basedOn);
		children.add(stmtList);
	}
	
	public BlockStmt(Stmt[] statements) {
		this(statements, null);
	}
	
	public BlockStmt(Stmt[] statements, Node basedOn) {
		super(basedOn);
		children.add(new StmtList(statements, basedOn));
	}
	
	public BlockStmt(List<Stmt> statements) {
		this(statements, null);
	}
	
	public BlockStmt(List<Stmt> statements, Node basedOn) {
		super(basedOn);
		children.add(new StmtList(statements, basedOn));
	}
	
	public StmtList getStmtList() {
		return (StmtList) children.get(0);
	}
}
