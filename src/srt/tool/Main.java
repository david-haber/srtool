package srt.tool;

import java.io.IOException;
import java.util.List;

import org.antlr.runtime.RecognitionException;

import srt.parser.SimpleCLexer;
import srt.tool.exception.CheckerExpception;
import srt.tool.exception.SMTSolverTimeoutException;
import srt.tool.exception.UnknownResultException;

import com.beust.jcommander.JCommander;

public class Main {

	/**
	 * @param args
	 * @throws RecognitionException
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public static void main(String[] args) throws IOException,
			RecognitionException, InterruptedException {
		
		// Parse command line args.
		CLArgs clArgs = new CLArgs();
		JCommander jcommander = new JCommander(clArgs, args);

		if (clArgs.help || clArgs.files.size() != 1) {
			jcommander.usage();
			return;
		}
		
		String inputFile = clArgs.files.get(0);
		
		SRTool tool = new SRTool(inputFile, clArgs);
		try {
			List<AssertionFailure> assertionFailures = tool.go();

			if (assertionFailures.size() > 0) {
				System.out.println("The following assertions can fail: ");
				for (AssertionFailure a : assertionFailures) {
					if (a == null || a.tokenInfo == null) {
						System.out.println("No assertion info was available!");
						continue;
					}
					System.out.print(" " + inputFile + ":"
							+ a.tokenInfo.getLine() + ":"
							+ a.tokenInfo.getCharPositionInLine());
					if (a.tokenInfo.getType() == SimpleCLexer.WHILE) {
						System.out.print(" (unwinding assertion)");
					}
					System.out.println();
				}
			} else {
				if (clArgs.unwindingAssertions) {
					System.out.println("No assertions can fail.");
				} else {
					System.out
							.println("Within the specified (unwinding) depths, "
									+ "no assertions can fail.");
				}
			}
		} catch (CheckerExpception e) {
			System.err.println(e.getCheckerError().message);
			System.exit(1);
		} catch (SMTSolverTimeoutException e) {
			System.err.println("Solver timed out!");
			System.exit(2);
		} catch (UnknownResultException e) {
			System.err.println("Solver returned unknown!");
			System.exit(3);
		}

		
	}

}
