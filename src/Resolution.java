/*
 * Resolution.java
 */
import java.util.Vector;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

public class Resolution { 
	protected static Vec2<CNFClause, Literal> RET;
	protected static CNFClause KB;
	
	public Vec2<CNFClause, Literal> initialize_Ex1(String filename) {
		BufferedReader br = null;
		try {
			br = new BufferedReader(new FileReader(filename));
			String sCurrentLine, firstLine = br.readLine();
			Literal finalClause;
			CNFSubClause intermediateClause;
			KB = new CNFClause();
			RET = new Vec2<CNFClause, Literal>();
			firstLine = firstLine.trim().replaceAll(" +", " ");	
			String[] sizes = firstLine.split(" ");
			boolean check = true;
			if(sizes.length != 1) check = false;
			if (check) {
				int aCurrentSize;
				while (((sCurrentLine = br.readLine()) != null) && (check)) {
					sCurrentLine = sCurrentLine.trim().replaceAll(" +", " ");;
					String[] aCurrentLine = sCurrentLine.split(" "); // separator is: " " = [whitespace]
					aCurrentSize = aCurrentLine.length;
					if(aCurrentLine[0].equals("PROVE")) {
						if((aCurrentSize == 3)&& (aCurrentLine[1].equals("NOT"))) {
				 			finalClause = new Literal(aCurrentLine[aCurrentLine.length - 1], true);
					        RET.setYValue(finalClause);
				    	}else if ((aCurrentSize == 2)&& (!aCurrentLine[1].equals("NOT"))) {
							finalClause = new Literal(aCurrentLine[aCurrentLine.length - 1], false);
					        RET.setYValue(finalClause);
				 		}else check = false;
					} else {
						intermediateClause = new CNFSubClause();
						int j;
						for(j = 0; j < aCurrentLine.length; j++) {
							if((!(aCurrentLine[j].equals("OR"))) && (!(aCurrentLine[j].equals("NOT")))) {
								intermediateClause.getLiterals().add(new Literal(aCurrentLine[j], false));
							}
							else if(aCurrentLine[j].equals("NOT")) {
								intermediateClause.getLiterals().add(new Literal(aCurrentLine[++j], true));
							}
						}
						KB.getSubclauses().add(intermediateClause);
					}
				}
				if(check)  RET.setTValue(KB);
			}else {
				System.out.println("Wrong file format; please try again.");
			}
		} catch (IOException e) {
			System.err.println("The system could not find the file specified");
			e.printStackTrace();
		} finally { // Stream closure should be executed at any case
				try {
					if (br != null) br.close();
				} catch (IOException exception) {
					exception.printStackTrace();
				}
		}
		return RET;
	}
	
    public static boolean PL_Resolution(CNFClause KB, Literal a){
        CNFClause clauses = new CNFClause();
        clauses.getSubclauses().addAll(KB.getSubclauses());
        Literal aCopy = new Literal(a.getName(), !a.getNeg());
        CNFSubClause aClause = new CNFSubClause();
        aClause.getLiterals().add(aCopy);
        clauses.getSubclauses().add(aClause);
        boolean stop = false;
        while(!stop){
            Vector<CNFSubClause> newsubclauses = new Vector<CNFSubClause>();
            Vector<CNFSubClause> subclauses = clauses.getSubclauses();
            for(int i = 0; i < subclauses.size(); i++){
                CNFSubClause Ci = subclauses.get(i);
                for(int j = i+1; j < subclauses.size(); j++){
                    CNFSubClause Cj = subclauses.get(j);
                    Vector<CNFSubClause> new_subclauses_for_ci_cj = CNFSubClause.resolution(Ci, Cj);
                    for(int k = 0; k < new_subclauses_for_ci_cj.size(); k++){
                        CNFSubClause newsubclause = new_subclauses_for_ci_cj.get(k);
                        if(newsubclause.isEmpty()) return true;
                        if(!newsubclauses.contains(newsubclause) && !clauses.contains(newsubclause))newsubclauses.add(newsubclause);
                    }                           
                }
            }
            boolean newClauseFound = false;
            for(int i = 0; i < newsubclauses.size(); i++) {
                if(!clauses.contains(newsubclauses.get(i))){
                    clauses.getSubclauses().addAll(newsubclauses);                    
                    newClauseFound = true;
                }                        
            }
            if(!newClauseFound){
                System.out.println("Not found new clauses");
                stop = true;
            }   
        }
        return false;
    }    
}