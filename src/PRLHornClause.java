/*
 * PRLHornClause.java
 * G. Moschovis
 */
import java.util.ArrayList;

public class PRLHornClause {
	 private ArrayList<PRLLiteral> literals;
	 private PRLLiteral impliedLiteral;
     
	    public PRLHornClause(){
	        literals = new ArrayList<PRLLiteral>();
	        impliedLiteral = null;
	    }
	         
	    public  ArrayList<PRLLiteral> getLiterals(){
	        return literals;
	    }

	    public PRLLiteral getLiteral() {
	    	return impliedLiteral;
	    }
	    
	    public void setLiteral(PRLLiteral impliedLiteral) {
	    	this.impliedLiteral = impliedLiteral;
	    }
	         
	    public boolean isEmpty(){
	        return literals.isEmpty();
	    }
	    
	    public void print(){
	    	for(int i = 0; i < literals.size(); i++) {
	    		PRLLiteral l = literals.get(i);
	            l.print();
	            if(i < literals.size()-1)System.out.print(", ");
	    	}
	    	if(this.getLiteral()!= null) { System.out.print(" IMPLIES "); this.getLiteral().print();}
	        System.out.println("\n");
	    }
}

