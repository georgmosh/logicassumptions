/*
 * PRLLiteral.java
 * G. Moschovis
 */
import java.util.ArrayList;

public class PRLLiteral extends Literal {
	private ArrayList<PRLTerm> terms;
	private boolean containsVar;
	
	public PRLLiteral() {
		super();
		terms = new ArrayList<PRLTerm>();
	}
	
	public PRLLiteral(String n, boolean neg){
		super(n, neg);
		terms = new ArrayList<PRLTerm>();
	}
	
	 public  ArrayList<PRLTerm> getMembers()            {
	        return terms;
	    }
	 
	 public  void setMembers(ArrayList<PRLTerm>  terms)            {
	        this.terms = terms;
	    }
	 
	 public boolean getVar() {
		 return containsVar;
	 }
	 
	 public void setVar(boolean varChk) {
		 this.containsVar = varChk;
	 }
	
	public void print(){
        if(this.getNeg())
            System.out.print("NOT_" + this.getName());
        else
            System.out.print(this.getName());
        for(int i = 0; i < terms.size(); i++) {
        	if(i==0)System.out.print("(");
        	System.out.print(terms.get(i).getName());
        	if(i < terms.size()-1) System.out.print(", ");
        	else System.out.print(")");
        }
    }
	
	   //Override
    public boolean equals(Object obj){
        PRLLiteral l = (PRLLiteral)obj;
        if(l.getName().compareTo(this.getName()) ==0 && l.getNeg() == this.getNeg() && l.getMembers().size() == this.getMembers().size())  return true;
        else   return false;
    }
}
