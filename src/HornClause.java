/*
 * HornClause.java
 * G. Moschovis
 */
import java.util.ArrayList;
import java.util.Iterator;

public class HornClause {
	 private ArrayList<Literal> literals;
	 private Literal impliedLiteral;
     
	    public HornClause(){
	        literals = new ArrayList<Literal>();
	        impliedLiteral = null;
	    }
	         
	    public  ArrayList<Literal> getLiterals()            {
	        return literals;
	    }
	    
	    public Iterator<Literal> getLiteralsList(){
	        return literals.iterator();
	    }
	    
	    public Literal getLiteral() {
	    	return impliedLiteral;
	    }
	    
	    public void setLiteral(Literal impliedLiteral) {
	    	this.impliedLiteral = impliedLiteral;
	    }
	         
	    public boolean isEmpty(){
	        return literals.isEmpty();
	    }
	    
	    public void print(){
	        Iterator<Literal> iter = this.getLiteralsList();
	        while(iter.hasNext()){
	            Literal l = iter.next();
	            l.print();
	            if(iter.hasNext())System.out.print(", ");
	            else System.out.print(". ");
	        }
	        System.out.println("\n");
	    }
}
