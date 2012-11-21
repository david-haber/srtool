package srt.tool.exception;


public class SMTSolverTimeoutException extends Exception {

	private static final long serialVersionUID = 1L;

	public SMTSolverTimeoutException(String message) {
		super(message);
	}
	
}
