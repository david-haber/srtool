package srt.ast;

public class IntLiteral extends Expr {
	private int value;

	public IntLiteral(int value) {
		this(value, null);
	}
	
	public IntLiteral(int value, Node basedOn) {
		super(basedOn);
		this.value = value;
	}

	public int getValue() {
		return value;
	}
	
}
