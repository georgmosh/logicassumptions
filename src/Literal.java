/*
 * Literal.java
 */

/*
 * Represents a literal; a variable
 */
public class Literal implements Comparable<Literal>{
    private String Name;
    private boolean negation;
    
    public Literal(){ }
    
    public Literal(String n, boolean neg){
        this.Name = n;
        this.negation = neg;
    }
    
    public void print(){
        if(negation)
            System.out.print("NOT_" + Name);
        else
            System.out.print(Name);
    }
        
    public void setName(String n){
        this.Name = n;
    }
    
    public String getName(){
        return this.Name;
    }
    
    public void setNeg(boolean b){
        this.negation = b;
    }
    
    public boolean getNeg(){
        return this.negation;
    }
    
   //Override
    public boolean equals(Object obj){
        Literal l = (Literal)obj;
        if(l.getName().compareTo(this.Name) ==0 && l.getNeg() == this.negation)  return true;
        else   return false;
    }
	
    //Override
    public int hashCode() {
            if(this.negation) {
                return this.Name.hashCode() + 1;
            }
            else{
                return this.Name.hashCode() + 0;                        
            }
    }
	
    //Override
    public int compareTo(Literal x)  {
            int a = 0;
            int b = 0;
            if(x.getNeg())  a = 1;
            if(this.getNeg()) b = 1;
            return x.getName().compareTo(Name) + a-b;
    }    
}
