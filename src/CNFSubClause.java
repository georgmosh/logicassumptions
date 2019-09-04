/*
 * CNFSubClause.java
 */
import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;

/*
 * A CNFSubClause in turn consists of a disjunction of literals
 */
public class CNFSubClause implements Comparable<CNFSubClause>{
    private HashSet<Literal> literals;
            
    public CNFSubClause(){
        literals = new HashSet<Literal>();
    }
         
    public  HashSet<Literal> getLiterals()            {
        return literals;
    }
    
    public Iterator<Literal> getLiteralsList(){
        return literals.iterator();
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

    /* 
     * Applies resolution on two CNFSubClauses
     * The resulting clause will contain all the literals of both CNFSubclauses
     * except the pair of literals that are a negation of each other.
     */
    public static Vector<CNFSubClause> resolution(CNFSubClause CNF_SC_1, CNFSubClause CNF_SC_2){
    	Vector<CNFSubClause> newClauses = new Vector<CNFSubClause>();
        Iterator<Literal> iter = CNF_SC_1.getLiteralsList();
        while(iter.hasNext()){            
            Literal l = iter.next();
            Literal m = new Literal(l.getName(), !l.getNeg());
            if(CNF_SC_2.getLiterals().contains(m)){
                CNFSubClause newClause = new CNFSubClause();
                HashSet<Literal> CNF_SC_1_Lits = new HashSet(CNF_SC_1.getLiterals());
                HashSet<Literal> CNF_SC_2_Lits = new HashSet(CNF_SC_2.getLiterals());
                CNF_SC_1_Lits.remove(l);
                CNF_SC_2_Lits.remove(m);
                newClause.getLiterals().addAll(CNF_SC_1_Lits);
                newClause.getLiterals().addAll(CNF_SC_2_Lits);
                newClauses.add(newClause);
            }
        }
        return newClauses;
    }
    
  //Override
    public boolean equals(Object obj){
        CNFSubClause l = (CNFSubClause)obj;
        Iterator<Literal> iter = l.getLiteralsList();
        while(iter.hasNext()){
            Literal lit = iter.next();
            if(!this.getLiterals().contains(lit)) return false;
        }
        if(l.getLiterals().size() != this.getLiterals().size()) return false;
        return true;
    }
	
    //@Override
    public int hashCode(){
        Iterator<Literal> iter = this.getLiteralsList();
        int code = 0;
        while(iter.hasNext()){
            Literal lit = iter.next();
               code = code + lit.hashCode();
        }
        return code;
    }
	
    //@Override
    public int compareTo(CNFSubClause x){
        int cmp = 0;
        Iterator<Literal> iter = x.getLiteralsList();
        while(iter.hasNext()){
            Literal lit = iter.next();
            Iterator<Literal> iter2 = this.getLiterals().iterator();     
            while(iter2.hasNext()) {                
                Literal lit2 = iter2.next();
                cmp = cmp + lit.compareTo(lit2);
            }
        }
        return cmp;
    }
}
