import java.util.Vector;

/*
 * CNFTesting.java
 * G. Moschovis
 */
public class CNFTesting extends Resolution{
	public void run() 
    {
    	System.out.println("Example 1: Lab Demo #1");
        example1();
        System.out.println("Example 2: Task from Wumpus");
        example2();
        System.out.println("Example 3: Complete Task from Wumpus; using Resolution.txt");
        example3("Resolution.txt");
    }

    //An example of the resolution between two clauses
    public static void example1(){
        CNFSubClause c1 = new CNFSubClause();
        c1.getLiterals().add(new Literal("l1", false));
        c1.getLiterals().add(new Literal("l2", false));
        c1.getLiterals().add(new Literal("l3", false)); // c1 = l1 OR l2 OR l3
        
        CNFSubClause c2 = new CNFSubClause();
        c2.getLiterals().add(new Literal("m1", false));
        c2.getLiterals().add(new Literal("l1", true));
        c2.getLiterals().add(new Literal("m3", false));
        c2.getLiterals().add(new Literal("m4", true)); // c2 = m1 OR !l1 OR m3 OR !m4

        Vector<CNFSubClause> newClauses = CNFSubClause.resolution(c1, c2);

        for(int i = 0; i < newClauses.size(); i++){
        	System.out.print("Literals of BOTH CNFSubclauses; except for the negation are ");
            newClauses.get(i).print();
        }
    }

    public static void example2() {
        CNFClause KB2 = new CNFClause();
        CNFSubClause A1 = new CNFSubClause();
        A1.getLiterals().add(new Literal("P21", true));
        A1.getLiterals().add(new Literal("B11", false));
        KB2.getSubclauses().add(A1);
        
        CNFSubClause A2 = new CNFSubClause();
        A2.getLiterals().add(new Literal("B11", true));
        A2.getLiterals().add(new Literal("P12", false));
        A2.getLiterals().add(new Literal("P21", false));
        KB2.getSubclauses().add(A2);
        
        CNFSubClause A3 = new CNFSubClause();
        A3.getLiterals().add(new Literal("P12", true));
        A3.getLiterals().add(new Literal("B11", false));
        KB2.getSubclauses().add(A3);
        
        CNFSubClause A4 = new CNFSubClause();
        A4.getLiterals().add(new Literal("B11", true));
        KB2.getSubclauses().add(A4);
        
        Literal finalClause = new Literal("P12", true);
        boolean resolutionResult = PL_Resolution(KB2, finalClause);
        System.out.print("Resolution implementation results that ");
        finalClause.print();
        System.out.print(" is " + resolutionResult + ".");
        System.out.println("\n");
    }
    
    public static void example3(String filename) {
    	CNFTesting f = new CNFTesting();
    	Vec2<CNFClause, Literal> RET = f.initialize_Ex1(filename);
    	CNFClause KB3 = RET.getTValue();
    	Literal finalClause = RET.getYValue();
    	boolean resolutionResult = PL_Resolution(KB3, finalClause);
    	System.out.print("Resolution implementation results that ");
        finalClause.print();
        System.out.print(" is " + resolutionResult + ".");
        System.out.println("\n");
    }
}
