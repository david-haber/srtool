package srt.ast;

public class Program extends Node {
	
  private String functionName;
  
	public Program(String functionName, DeclList declList, BlockStmt block) {
		this(functionName, declList, block,null);
	}
	
	public Program(String functionName, DeclList declList, BlockStmt block, Node basedOn) {
		super(basedOn);
		this.functionName = functionName;
		children.add(declList);
		children.add(block);
	}
	
	public DeclList getDeclList() {
		return (DeclList) children.get(0);
	}
	
	public BlockStmt getBlockStmt() {
		return (BlockStmt) children.get(1);
	}

  public String getFunctionName() {
    return functionName;
  }
	
}
