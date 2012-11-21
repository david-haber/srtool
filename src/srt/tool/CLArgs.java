package srt.tool;

import java.util.ArrayList;
import java.util.List;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;

@Parameters(separators = " =:")
public class CLArgs {
	
	@Parameter(description = "file")
	public List<String> files = new ArrayList<String>();
	
	@Parameter(names = {"--help", "-help", "-h"}, description = "Show usage.", help = true)
	public boolean help;

	@Parameter(names = { "--unwind", "-unwind", "-u" }, description = "Unwinding depth.")
	public Integer unwindDepth = 5;
	
	@Parameter(names = { "--timeout", "-timeout", "-t" }, description = "Timeout for SMT query in seconds.")
	public Integer timeout = 5;
	
	@Parameter(names = { "--unwinding-assertions", "-unwinding-assertions",
			"-ua" }, description = "If true, the tool "
			+ "will verify that loop unwinding bounds are sufficiently large; "
			+ "a feasible path that exceeds the unwinding depth will "
			+ "cause verification to fail.", arity = 1)
	public boolean unwindingAssertions = true;
	
	@Parameter(names = { "--abstract-loops", "-abstract-loops" }, description = "If true, " +
			"loops will be abstracted.")
	public boolean abstractLoops = false;
	
}
