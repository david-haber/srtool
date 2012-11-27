package srt.tool;

import srt.ast.BinaryExpr;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.IntLiteral;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class ExprToSmtlibVisitor extends DefaultVisitor {
	
	public ExprToSmtlibVisitor() {
		super(false);
	}

	@Override
	public String visit(BinaryExpr expr) {
		String operator = null;
		switch(expr.getOperator())
		{
			case BinaryExpr.ADD:
				operator = "(bvadd %s %s)";
				break;
			case BinaryExpr.BAND:
				operator = "(bvand %s %s)";
				break;
			case BinaryExpr.BOR:
				operator = "(bvor %s %s)";
				break;
			case BinaryExpr.BXOR:
				operator = "(bvxor %s %s)";
				break;
			case BinaryExpr.DIVIDE:
				// TODO assumes two's complement signed division
				operator = "(bvsdiv %s %s)";
				break;
			case BinaryExpr.LSHIFT:
				operator = "(bvshl %s %s)";
				break;
			case BinaryExpr.MOD:
				operator = "(bvsrem %s %s)";
				break;
			case BinaryExpr.MULTIPLY:
				operator = "(bvmul %s %s)";
				break;
			case BinaryExpr.RSHIFT:
				// preserve sign of number that is being shifted
				// most significant bits of the result always copy
				// the most significant bit of the second argument
				operator = "(bvashr %s %s)";	
				break;
			case BinaryExpr.SUBTRACT:
				operator = "(bvsub %s %s)";
				break;
			case BinaryExpr.LAND:
				// (and (bv32tobool (tobv32 (= i j))) (and (bv32tobool (tobv32 (= j i))) ))))
				operator = "(tobv32 (and (bv32tobool %s) (bv32tobool %s)))";
				break;
			case BinaryExpr.LOR:
				operator = "(tobv32 (or (bv32tobool %s) (bv32tobool %s)))";
				break;
			case BinaryExpr.GEQ:
				// TODO FOR ALL comparison operators: assume based on 32 bvs, also: Z3_ast Z3_API Z3_mk_ge
				// TODO is there a better way than converting to bv and then back to bool?
				operator = "(tobv32 (bvsge %s %s))";
				break;
			case BinaryExpr.GT:
				operator = "(tobv32 (bvsgt %s %s))";
				break;
			case BinaryExpr.LEQ:
				operator = "(tobv32 (bvsle %s %s))";
				break;
			case BinaryExpr.LT:
				operator = "(tobv32 (bvslt %s %s))";
				break;
			case BinaryExpr.NEQUAL:
				operator = "(tobv32 (not (= %s %s)))";
				break;
			case BinaryExpr.EQUAL:
				operator = "(tobv32 (= %s %s))";
				break;
			default:
				throw new IllegalArgumentException("Invalid binary operator");
		}
		
		return String.format(operator, visit(expr.getLhs()), visit(expr.getRhs()));
		
	}

	@Override
	public String visit(DeclRef declRef) {
		return declRef.getName();
	}

	@Override
	public String visit(IntLiteral intLiteral) {
		return "(_ bv"+Integer.toString(intLiteral.getValue())+" 32)";
		//return "(inttobv32 "+Integer.toString(intLiteral.getValue())+")";
	}

	@Override
	public String visit(TernaryExpr ternaryExpr) {
		return null;
	}

	@Override
	public String visit(UnaryExpr unaryExpr) {
		String operator = null;
		switch(unaryExpr.getOperator())
		{
		case UnaryExpr.UMINUS:
			operator = "(bvneg %s)";
			break;
		case UnaryExpr.UPLUS:
			// TODO ?
			// +3 = 3
			operator = "";
			break;
		case UnaryExpr.LNOT:
			operator = "(tobv32 (not (bv32tobool %s)))";
			break;
		case UnaryExpr.BNOT:
			operator = "(bvnot %s)";
			break;
		default:
			throw new IllegalArgumentException("Invalid binary operator");
		}
		
		return String.format(operator, visit(unaryExpr.getOperand()));
	}
	
	
	/* Overridden just to make return type String. 
	 * @see srt.ast.visitor.DefaultVisitor#visit(srt.ast.Expr)
	 */
	@Override
	public String visit(Expr expr) {
		return (String) super.visit(expr);
	}
	
	

}
