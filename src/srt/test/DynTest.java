package srt.test;

import java.io.File;
import java.util.List;

import junit.framework.Assert;
import junit.framework.TestCase;
import srt.tool.AssertionFailure;
import srt.tool.CLArgs;
import srt.tool.SRTool;

public class DynTest extends TestCase {
	private File file;
	private static final String HR = "--------";
	public CLArgs clargs;

	public DynTest(File file, CLArgs clargs) {
		super(file.getPath());
		this.file = file;
		this.clargs = clargs;
	}
	
	@Override
	protected void runTest() throws Throwable {
		System.out.println();
		System.out.println(HR + "Testing  " + file + HR);
		
		SRTool tool = new SRTool(file.getPath(), clargs);
		
		List<AssertionFailure> afs = tool.go();
		if(file.getName().contains("good")) {
			Assert.assertEquals("Expected 0 assertions that can fail.", 0, afs.size());
		} else if(file.getName().contains("bad")) {
			Assert.assertTrue("Expected at least 1 assertion that can fail.", afs.size()>0);
		} else {
			fail("Could not find 'good' or 'bad' within test filename.");
		}
		
		System.out.println(HR + "End Test " + file + HR);
		System.out.println();
	}

}
