/*
 * HornTesting.java
 * G. Moschovis
 */
import java.util.HashMap;

public class HornTesting extends ForwardChaining{
	public void example1() {
		Vec2<HashMap<String,Literal>, HashMap<String, HornClause>> KB1 = new Vec2<HashMap<String,Literal>, HashMap<String, HornClause>>();
		
		HashMap<String, Literal> literals = new HashMap<String, Literal>();
		literals.put("F1", new Literal("A", false));
		literals.put("F2", new Literal("B", false));
		
		HashMap<String, HornClause> clauses = new HashMap<String, HornClause>();
		HornClause c1 = new HornClause();
        c1.getLiterals().add(new Literal("A", false));
        c1.getLiterals().add(new Literal("B", false));
        c1.setLiteral(new Literal("L", false)); // c1 = A AND B IMPLIES L
        clauses.put("C1", c1);
        
        HornClause c2 = new HornClause();
        c2.getLiterals().add(new Literal("A", false));
        c2.getLiterals().add(new Literal("P", false));
        c2.setLiteral(new Literal("L", false)); // c2 = A AND P IMPLIES L
        clauses.put("C2", c2);
        
        HornClause c3 = new HornClause();
        c3.getLiterals().add(new Literal("B", false));
        c3.getLiterals().add(new Literal("L", false));
        c3.setLiteral(new Literal("M", false)); // c3 = B AND L IMPLIES M
        clauses.put("C3", c3);
        
        HornClause c4 = new HornClause();
        c4.getLiterals().add(new Literal("L", false));
        c4.getLiterals().add(new Literal("M", false));
        c4.setLiteral(new Literal("P", false)); // c4 = L AND M IMPLIES P
        clauses.put("C4", c4);
        
        HornClause c5 = new HornClause();
        c5.getLiterals().add(new Literal("P", false));
        c5.setLiteral(new Literal("Q", false)); // c5 = P IMPLIES Q
        clauses.put("C5", c5);
        
        HornClause f = new HornClause();
        f.setLiteral(new Literal("Q", false)); // f = Q
        
        KB1.setTValue(literals);
        KB1.setYValue(clauses);
        KB1.setTSize(2);
        KB1.setYSize(5);
        boolean resolutionResult = PL_FC_Entails( KB1, f);
        System.out.println("Example 1: Task from Slides");
        System.out.print("Forward Chaining implementation results that ");
	   for(int i = 0; i < f.getLiterals().size(); i++) {
        	System.out.print(f.getLiterals().get(i).getName());
        	if(i !=  f.getLiterals().size() - 1) System.out.print(" AND ");
        	else System.out.print(" EQUALS ");
        }
        System.out.print(f.getLiteral().getName() + " is " + resolutionResult + ".\n \n");
	}
	
	public void example2(String filename) {
		Vec2<Vec2<HashMap<String,Literal>, HashMap<String, HornClause>>, HornClause> RET = this.initialize_Ex1(filename);
		Vec2<HashMap<String,Literal>, HashMap<String, HornClause>> KB2 = RET.getTValue();
		HornClause f = RET.getYValue();
		boolean resolutionResult = PL_FC_Entails(KB2, f);
		 System.out.println("Example 2: Complete Task from Slides; using ForwardChaining.txt");
		 System.out.print("Forward Chaining implementation results that ");
		   for(int i = 0; i < f.getLiterals().size(); i++) {
	        	System.out.print(f.getLiterals().get(i).getName());
	        	if(i !=  f.getLiterals().size() - 1) System.out.print(" AND ");
	        	else System.out.print(" EQUALS ");
	        }
	        System.out.print(f.getLiteral().getName() + " is " + resolutionResult + ".\n");
	}
	
	public void run() {
		HornTesting f = new HornTesting();
		f.example1();
		f.example2("ForwardChaining.txt");
	}
}
