package srt.ast;

public class Decl extends Stmt {
	
	private String name;
	private String type;
	
	public Decl(String name, String type) {
		this(name, type, null);
	}
	
	public Decl(String name, String type, Node basedOn) {
		super(basedOn);
		this.name = name;
		this.type = type;
	}

	public String getName() {
		return name;
	}
	
	public String getType() {
		return type;
	}
	
}
