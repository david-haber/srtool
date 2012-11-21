package srt.ast;

import org.antlr.runtime.tree.Tree;
import srt.parser.SimpleCLexer;


public class ASTConverter {
	
	public ASTConverter() {
		
	}
	
	private class DummyNode extends Node {
		public DummyNode(Tree tree) {
			super(null);
			this.tokenInfo = tree;
		}
	}
	
	public Program go(Tree root)
	{
		return (Program)convert(root);
	}
	
	private Node convert(Tree tree)
	{
		DummyNode dummyNode = new DummyNode(tree);
		switch(tree.getType())
		{
		case SimpleCLexer.UMINUS:
		case SimpleCLexer.UPLUS:
		case SimpleCLexer.LNOT:
		case SimpleCLexer.BNOT:
			return new UnaryExpr(tree.getType(), (Expr)convert(tree.getChild(0)), dummyNode);
		case SimpleCLexer.ADD:
		case SimpleCLexer.BAND:
		case SimpleCLexer.BOR:
		case SimpleCLexer.BXOR:
		case SimpleCLexer.DIVIDE:
		case SimpleCLexer.GEQ:
		case SimpleCLexer.GT:
		case SimpleCLexer.LAND:
		case SimpleCLexer.LEQ:
		case SimpleCLexer.LOR:
		case SimpleCLexer.LSHIFT:
		case SimpleCLexer.LT:
		case SimpleCLexer.MOD:
		case SimpleCLexer.MULTIPLY:
		case SimpleCLexer.NEQUAL:
		case SimpleCLexer.EQUAL:
		case SimpleCLexer.RSHIFT:
		case SimpleCLexer.SUBTRACT:
			return new BinaryExpr(tree.getType(),
					(Expr) convert(tree.getChild(0)),
					(Expr) convert(tree.getChild(1)),
					dummyNode);
		case SimpleCLexer.ASSERT:
			return new AssertStmt((Expr) convert(tree.getChild(0)), dummyNode);
		case SimpleCLexer.ASSUME:
			return new AssumeStmt((Expr) convert(tree.getChild(0)), dummyNode);
		case SimpleCLexer.ASSIGNMENT:
			return new AssignStmt((DeclRef) convert(tree.getChild(0)), (Expr)convert(tree.getChild(1)), dummyNode);
		case SimpleCLexer.BLOCK:
			return new BlockStmt((StmtList) convert(tree.getChild(0)), dummyNode);
		case SimpleCLexer.COMPOUND_STATEMENT:
		{
			int max = tree.getChildCount();
			Stmt[] stmts = new Stmt[max];
			for(int i=0; i < max; ++i)
			{
				stmts[i] = (Stmt) convert(tree.getChild(i));
			}
			return new StmtList(stmts, dummyNode);
		}
		case SimpleCLexer.DECL:
			return new Decl(tree.getChild(0).getText(), tree.getChild(1).getText(), dummyNode);
		case SimpleCLexer.DECL_LIST:
		{
			int max = tree.getChildCount();
			Decl[] decls = new Decl[max];
			for(int i=0; i < max; ++i)
			{
				decls[i] = (Decl) convert(tree.getChild(i));
			}
			return new DeclList(decls, dummyNode);
		}
		case SimpleCLexer.DIGIT:
			throw new IllegalStateException("Should not reach digit");
		case SimpleCLexer.EMPTY_STMT:
			return new EmptyStmt(dummyNode);
		case SimpleCLexer.HAVOC:
			return new HavocStmt((DeclRef) convert(tree.getChild(0)), dummyNode);
		case SimpleCLexer.ID:
			return new DeclRef(tree.getText(), dummyNode);
		case SimpleCLexer.IF:
			return new IfStmt((Expr) convert(tree.getChild(0)),
					(Stmt) convert(tree.getChild(1)),
					tree.getChild(2) == null ? null : (Stmt) convert(tree
							.getChild(2)), dummyNode);
		case SimpleCLexer.INVARIANT_LIST:
		{
			int max = tree.getChildCount();
			Expr[] exprs = new Expr[max];
			for(int i=0; i < max; ++i)
			{
				exprs[i] = (Expr) convert(tree.getChild(i));
			}
			return new ExprList(exprs, dummyNode);
		}
		case SimpleCLexer.NUMBER:
			return new IntLiteral(Integer.parseInt(tree.getText()), dummyNode);
    case SimpleCLexer.PROGRAM:
      return new Program(tree.getChild(0).getText(),
          (DeclList) convert(tree.getChild(1)),
          (BlockStmt) convert(tree.getChild(2)), dummyNode);
    case SimpleCLexer.TERNARY:
			return new TernaryExpr((Expr) convert(tree.getChild(0)),
					(Expr) convert(tree.getChild(1)),
					(Expr) convert(tree.getChild(2)), dummyNode);
		case SimpleCLexer.WHILE:
		{
			Tree unwind = tree.getChild(1);
			assert unwind.getType() == SimpleCLexer.BOUND;
			IntLiteral unwindLiteral = unwind.getChild(0) == null ? null
					: (IntLiteral) convert(unwind.getChild(0));
			return new WhileStmt((Expr) convert(tree.getChild(0)),
					unwindLiteral, (ExprList) convert(tree.getChild(2)),
					(Stmt) convert(tree.getChild(3)), dummyNode);
		}
		case SimpleCLexer.WHITESPACE:
		default:
		}
		
		throw new IllegalStateException("Unexpected token in antlr AST");
	}
	
}
