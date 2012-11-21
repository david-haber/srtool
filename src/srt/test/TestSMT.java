package srt.test;

import java.io.File;
import java.io.IOException;

import srt.exec.SMTQuery;

public class TestSMT {
	
	public static void main(String[] args) throws IOException, InterruptedException {
		SMTQuery query = new SMTQuery(new File("queryIn.txt"), 30000);
		String result = query.go();
		System.out.println(result);
	}
}
