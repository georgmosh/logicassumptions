/*
 * PRLHornTesting.java
 * G. Moschovis (3150113)
 */
import java.util.HashMap;

public class PRLHornTesting extends PRLForwardChaining{
	public void example1() {
		Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>> KB1 = new Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>>();
		
		HashMap<String, PRLLiteral> literals = new HashMap<String, PRLLiteral>();
		PRLLiteral l1 = new PRLLiteral("American", false);
		l1.getMembers().add(new Constant("West"));
		literals.put("F1", l1);
		
		PRLLiteral l2 = new PRLLiteral("Missile", false);
		l2.getMembers().add(new Constant("M1"));
		literals.put("F2", l2);
		
		PRLLiteral l3 = new PRLLiteral("Owns", false);
		l3.getMembers().add(new Constant("Nono"));
		l3.getMembers().add(new Constant("M1"));
		literals.put("F3", l3);
		
		PRLLiteral l4 = new PRLLiteral("Enemy", false);
		l4.getMembers().add(new Constant("Nono"));
		l4.getMembers().add(new Constant("America"));
		literals.put("F4", l4);
		
		HashMap<String, PRLHornClause> clauses = new HashMap<String, PRLHornClause>();
		PRLHornClause c1 = new PRLHornClause();
		PRLLiteral c1_l1 = new PRLLiteral("Missile", false);
		c1_l1.getMembers().add(new Variable("x1"));
        c1.getLiterals().add(c1_l1);
        PRLLiteral c1_l2 = new PRLLiteral("Owns", false);
		c1_l2.getMembers().add(new Constant("Nono"));
		c1_l2.getMembers().add(new Variable("x1"));
        c1.getLiterals().add(c1_l2);
        PRLLiteral c1_l3 = new PRLLiteral("Sells", false);
		c1_l3.getMembers().add(new Constant("West"));
		c1_l3.getMembers().add(new Variable("x1"));
		c1_l3.getMembers().add(new Constant("Nono"));
        c1.setLiteral(c1_l3); // Missile(M1) and Owns(Nono, x1) implies Sells(West, x1, Nono)
        clauses.put("C1", c1);
        
        PRLHornClause c2 = new PRLHornClause();
        PRLLiteral c2_l1 = new PRLLiteral("Enemy", false);
        c2_l1.getMembers().add(new Variable("x2"));
        c2_l1.getMembers().add(new Constant("America"));
        c2.getLiterals().add(c2_l1);
        PRLLiteral c2_l2 = new PRLLiteral("Hostile", false);
        c2_l2.getMembers().add(new Variable("x2"));
        c2.setLiteral(c2_l2); // Enemy(x2, America) implies Hostile(x2)
        clauses.put("C2", c2);
        
        PRLHornClause c3 = new PRLHornClause();
        PRLLiteral c3_l1 = new PRLLiteral("Missile", false);
        c3_l1.getMembers().add(new Variable("x3"));
        c3.getLiterals().add(c3_l1);
        PRLLiteral c3_l2 = new PRLLiteral("Weapon", false);
        c3_l2.getMembers().add(new Variable("x3"));
        c3.setLiteral(c3_l2); // Enemy(x2, America) implies Hostile(x2)
        clauses.put("C3", c3);
        
        PRLHornClause c4 = new PRLHornClause();
        PRLLiteral c4_l1 = new PRLLiteral("American", false);
        c4_l1.getMembers().add(new Variable("x4"));
        c4.getLiterals().add(c4_l1);
        PRLLiteral c4_l2 = new PRLLiteral("Weapon", false);
        c4_l2.getMembers().add(new Variable("y1"));
        c4.getLiterals().add(c4_l2);
        PRLLiteral c4_l3 = new PRLLiteral("Sells", false);
        c4_l3.getMembers().add(new Variable("x4"));
        c4_l3.getMembers().add(new Variable("y1"));
        c4_l3.getMembers().add(new Variable("z1"));
        c4.getLiterals().add(c4_l3);
        PRLLiteral c4_l4 = new PRLLiteral("Hostile", false);
        c4_l4.getMembers().add(new Variable("z1"));
        c4.getLiterals().add(c4_l4);
        PRLLiteral c4_l5 = new PRLLiteral("Criminal", false);
        c4_l5.getMembers().add(new Variable("x4"));
        c4.setLiteral(c4_l5); // American(x4) and Weapon(y1) and Sells(x4, y1, z1) and Hostile(z1) implies Criminal(x4)
        clauses.put("C4", c4);
        
        PRLHornClause f = new PRLHornClause();
        PRLLiteral f1 = new PRLLiteral("Criminal", false);
        f1.getMembers().add(new Constant("West"));
        f.getLiterals().add(f1);
        f.setLiteral(f1); // Criminal(West)
        
        KB1.setTValue(literals);
        KB1.setYValue(clauses);
        KB1.setTSize(4);
        KB1.setYSize(4);
        boolean resolutionResult = PL_FC_Entails( KB1, f);
        System.out.println("Example 1: Task from Slides");
        System.out.print("Forward Chaining implementation results that ");
	   for(int i = 0; i < f.getLiterals().size(); i++) {
        	System.out.print(f.getLiterals().get(i).getName());
        	for(int j = 0; j < f.getLiterals().get(i).getMembers().size(); j++) {
        		if(j == 0) System.out.print("(");
        		System.out.print( f.getLiterals().get(i).getMembers().get(i).getName());
        		if(j ==  f.getLiterals().get(i).getMembers().size()- 1) System.out.print(") ");
        	}
        	if(i !=  f.getLiterals().size() - 1) System.out.print(" AND ");
        }
        System.out.print( "is " + resolutionResult + ".\n \n");
	}
	
	public void example2(String filename) {
		 System.out.println("Example 2: Complete Task from Slides; using PRLForwardChaining.txt");
		 System.out.print("Forward Chaining implementation results that ");
		Vec2<Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>>, PRLHornClause> RET = this.initialize_Ex1(filename);
		Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>> KB2 = RET.getTValue();
		PRLHornClause f = RET.getYValue();
		boolean resolutionResult = PL_FC_Entails(KB2, f);
	        System.out.print( "is " + resolutionResult + ".\n \n");
	}
	
	public void run() {
		PRLHornTesting f = new PRLHornTesting();
		f.example1();
		f.example2("PRLForwardChaining.txt");
	}
}
