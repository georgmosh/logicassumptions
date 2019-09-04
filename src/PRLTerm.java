/*
 * PRLTerm.java
 * G. Moschovis
 */
public class PRLTerm {
	private String Name;
	
	 public PRLTerm(String n){
        this.Name = n;
    }
        
    public void setName(String n){
        this.Name = n;
    }
    
    public String getName(){
        return this.Name;
    }
}