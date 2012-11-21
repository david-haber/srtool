package srt.exec;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import srt.util.FileUtil;

public class SMTQuery {

	private ProcessBuilder processBuilder = null;
	private Process process = null;
	private Integer exitValue = null;
	private int timeout;
	
	private static long TO_MILLI = 1000000;
	private static String FILE_IN = "queryIn.txt";
	private static String FILE_OUT = "queryOut.txt";
	private static String FILE_ERR = "queryErr.txt";
	
	private static File getStringAsFile(String string) throws IOException {
		FileWriter fw = null;
		try {
			fw = new FileWriter(FILE_IN);
			fw.write(string + "\n");
		}
		finally {
			fw.close();
		}
		return new File(FILE_IN);
	}
	
	public SMTQuery(String query, int timeout) throws IOException {
		this(getStringAsFile(query), timeout);
	}
	
	public SMTQuery(File query, int timeout) {
		processBuilder = new ProcessBuilder("z3", "-smt2", "-file", query.getAbsolutePath());
		this.timeout = timeout;
	}
	
	/**
	 * Execute the SMT query and return the result.
	 * This will null if the timeout was exceeded.
	 * @return SMT query result or null if the timeout was exceeded.
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public String go() throws IOException, InterruptedException {
		if(process != null) {
			throw new IllegalStateException("Can only execute query once.");
		}
		
		Thread thread1=null;
		Thread thread2=null;
		
		try {
			int start = getTime();
			process = processBuilder.start();
			thread1 = FileUtil.copy(process.getInputStream(), new FileOutputStream(FILE_OUT));
			thread2 = FileUtil.copy(process.getErrorStream(), new FileOutputStream(FILE_ERR));
			while(!retrieveExitCode()) {
				int toWait = start + timeout - getTime();
				if(toWait < 1) { break; }
				Thread.sleep(10);
			}
		}
		finally {
			if(exitValue == null && process != null) { process.destroy(); }
		}
		
		if(exitValue == null)
			return null;
		
		thread1.join(1000);
		thread2.join(1000);
		
		BufferedReader in = null;
		StringBuilder sb = new StringBuilder();
		try {
			in = new BufferedReader(new FileReader(FILE_OUT));
			while(true)
			{
				String line = in.readLine();
				if(line == null)
					break;
				sb.append(line);
				sb.append("\n");
			}
		} finally {
			if(in != null) { in.close(); }
		}
		
		return sb.toString();
	}
	
	private int getTime() {
		return (int) (System.nanoTime()/TO_MILLI);
	}
	
	private boolean retrieveExitCode() {
		if(exitValue != null) return true;
		try {
			exitValue = process.exitValue();
			return true;
		} catch (IllegalThreadStateException e) {
			return false;
		}
	}
	
}
