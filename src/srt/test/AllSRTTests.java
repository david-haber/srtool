package srt.test;

import java.io.File;
import java.io.IOException;
import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

import junit.framework.Test;
import junit.framework.TestSuite;

import org.junit.runner.RunWith;
import org.junit.runners.AllTests;

import srt.tool.CLArgs;

@RunWith(AllTests.class)
public class AllSRTTests {

	public static Test suite() {
		TestSuite tests = new TestSuite();
		CLArgs clargs = new CLArgs();
		
		// bounded model checker tests
		tests.addTest(getTestsInDir("test", clargs));
		
		// unwinding-assertions=false tests
		// (comment out these lines while testing loop free programs)
		clargs = new CLArgs();
		clargs.unwindingAssertions = false;
		tests.addTest(getTestsInDir("testunsound", clargs));
		
		// loop abstraction tests
		// (comment out these lines while testing the bounded model checker)
		clargs = new CLArgs();
		clargs.abstractLoops = true;
		tests.addTest(getTestsInDir("testloopabs", clargs));

		return tests;
	}

	private static Test getTestsInDir(String dir, CLArgs clargs) {
		TestSuite tests = new TestSuite(dir);
		TreeSet<File> files = new TreeSet<File>(new Comparator<File>() {
			@Override
			public int compare(File o1, File o2) {
				return o1.getPath().compareToIgnoreCase(o2.getPath());
			}
		});
		File topDir = new File(dir);
		if (!topDir.isDirectory()) {
			System.err.println("Could not find testing directory: "
					+ topDir.getName());
			throw new RuntimeException(new IOException(
					"Could not find testing directory: " + topDir.getName()));
		}
		getFilesRecursive(topDir, files);
		for (File file : files) {
			tests.addTest(new DynTest(file, clargs));
		}
		return tests;
	}

	private static void getFilesRecursive(File dir, Set<File> res) {
		for (File file : dir.listFiles()) {
			if (file.isDirectory()) {
				getFilesRecursive(file, res);
			}
			if (!file.getName().endsWith(".sc"))
				continue;
			res.add(file);
		}
	}
}
