package srt.tool;

import org.antlr.runtime.tree.Tree;

public class AssertionFailure {
	public Tree tokenInfo;

	public AssertionFailure(Tree tokenInfo) {
		this.tokenInfo = tokenInfo;
	}
	
}
