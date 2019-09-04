/*
 * ForwardChaining.java
 * G. Moschovis
 */
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;

public class ForwardChaining {
	protected static Vec2<Vec2<HashMap<String,Literal>, HashMap<String, HornClause>>, HornClause> RET;
	protected static Vec2<HashMap<String,Literal>, HashMap<String, HornClause>> KB;
	protected static HashMap<String, Literal> literals;
	protected static HashMap<String, HornClause> clauses;
	
	public Vec2<Vec2<HashMap<String,Literal>, HashMap<String, HornClause>>, HornClause> initialize_Ex1(String filename) {
		BufferedReader br = null;
		try {
			br = new BufferedReader(new FileReader(filename));
			String sCurrentLine, firstLine = br.readLine();
			HornClause finalClause, intermediateClause;
			RET = new Vec2<Vec2<HashMap<String,Literal>, HashMap<String, HornClause>>, HornClause>();
			KB = new Vec2<HashMap<String,Literal>, HashMap<String, HornClause>>();
			literals = new HashMap<String, Literal>();
			clauses = new HashMap<String, HornClause>();
			firstLine = firstLine.trim().replaceAll(" +", " ");	
			String[] sizes = firstLine.split(" ");
			boolean check = true;
			if(sizes.length != 2) check = false;
			else {
				KB.setTSize(Integer.parseInt(sizes[0]));
		        KB.setYSize(Integer.parseInt(sizes[1]));
			}
			if(!(KB.getYSize() > 0)|| !(KB.getTSize() > 0) ) check = false;
			if (check) {
				int aCurrentSize, litCnt = 0, clsCnt = 0;
				boolean implicationDiscovery;
				while (((sCurrentLine = br.readLine()) != null) && (check)) {
					sCurrentLine = sCurrentLine.trim().replaceAll(" +", " ");;
					String[] aCurrentLine = sCurrentLine.split(" "); // separator is: " " = [whitespace]
					aCurrentSize = aCurrentLine.length;
					if(aCurrentLine[0].equals("PROVE")) {
						if(aCurrentSize > 3) {
							implicationDiscovery = false;
							finalClause = new HornClause();
							int j;
							for(j = 1; j < aCurrentLine.length; j++) {
								if((!(aCurrentLine[j].equals("AND"))) && (!(aCurrentLine[j].equals("IMPLIES"))) && (!(aCurrentLine[j].equals("NOT")))) {
									finalClause.getLiterals().add(new Literal(aCurrentLine[j], false));
								}else if(aCurrentLine[j].equals("IMPLIES")) implicationDiscovery = true;
								else if(aCurrentLine[j].equals("NOT")) {
									finalClause.getLiterals().add(new Literal(aCurrentLine[++j], true));
								}
								if(implicationDiscovery)break;
							}
							if(implicationDiscovery) {
								if(aCurrentLine[j].equals("NOT")) finalClause.setLiteral(new Literal(aCurrentLine[aCurrentLine.length - 1], true));
								else  finalClause.setLiteral(new Literal(aCurrentLine[aCurrentLine.length - 1], false));
								RET.setYValue(finalClause);
							}else if(finalClause.getLiterals().size()> 0) {
								for(int i = 0; i < finalClause.getLiterals().size()|| !implicationDiscovery; i++) {
									if(!finalClause.getLiterals().get(i).getNeg()) {  // True literal is one per Horn Clause
										 finalClause.setLiteral(finalClause.getLiterals().get(i));
										 finalClause.getLiterals().remove(i);
										 RET.setYValue(finalClause);
										 implicationDiscovery = true;
									}
								}
							}else check = false;
				 		}else if((aCurrentSize == 3)&& (aCurrentLine[1].equals("NOT"))) {
				 			finalClause = new HornClause();
					        finalClause.setLiteral(new Literal(aCurrentLine[aCurrentLine.length - 1], true));
					        RET.setYValue(finalClause);
				    	}else if ((aCurrentSize == 2)&& (!aCurrentLine[1].equals("NOT"))) {
							finalClause = new HornClause();
					        finalClause.setLiteral(new Literal(aCurrentLine[aCurrentLine.length - 1], false));
					        RET.setYValue(finalClause);
				 		}else check = false;
					} else {
						if(aCurrentSize < 3) {
							if((aCurrentSize == 2)&& (aCurrentLine[0].equals("NOT")))literals.put("F"+(++litCnt), new Literal(aCurrentLine[1], true));
							else if((aCurrentSize == 1)&& (!aCurrentLine[0].equals("NOT"))) literals.put("F"+(++litCnt), new Literal(aCurrentLine[0], false));
							else check = false;
						}else {
							implicationDiscovery = false;
							intermediateClause = new HornClause();
							int j;
							for(j = 0; j < aCurrentLine.length; j++) {
								if((!(aCurrentLine[j].equals("AND"))) && (!(aCurrentLine[j].equals("IMPLIES"))) && (!(aCurrentLine[j].equals("NOT")))) {
									intermediateClause.getLiterals().add(new Literal(aCurrentLine[j], false));
								}else if(aCurrentLine[j].equals("IMPLIES")) implicationDiscovery = true;
								else if(aCurrentLine[j].equals("NOT")) {
									intermediateClause.getLiterals().add(new Literal(aCurrentLine[++j], true));
								}
								if(implicationDiscovery)break;
							}
							if(implicationDiscovery) {
								if(aCurrentLine[j].equals("NOT")) intermediateClause.setLiteral(new Literal(aCurrentLine[aCurrentLine.length - 1], true));
								else  intermediateClause.setLiteral(new Literal(aCurrentLine[aCurrentLine.length - 1], false));
								clauses.put("C"+(++clsCnt),intermediateClause);
							}else if(intermediateClause.getLiterals().size()> 0) {
								for(int i = 0; i < intermediateClause.getLiterals().size(); i++) {
									if(!intermediateClause.getLiterals().get(i).getNeg()) { // True literal is one per Horn Clause
										intermediateClause.setLiteral(intermediateClause.getLiterals().get(i));
										intermediateClause.getLiterals().remove(i);
										 implicationDiscovery = true;
									}
									if(implicationDiscovery) {
										clauses.put("C"+(++clsCnt),intermediateClause);
										break;
									}
								}
							} else check = false;
						}
					}
				}
				if(check) {
					 KB.setTValue(literals);
				     KB.setYValue(clauses);
				}
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
		RET.setTValue(KB);
		return RET;
	}
	
	public boolean PL_FC_Entails(Vec2<HashMap<String,Literal>, HashMap<String, HornClause>> KB, HornClause finalClause) {
		Literal currentFact = new Literal();
		HornClause currentClause;
		int factDiscoveries = 0, countResults = 0;
		boolean factDiscovery;
		int count[] = new int[ KB.getYSize()];
		for(int i = 1; !(i > KB.getYSize()); i++){
	 		currentClause = KB.getYValue().get("C"+i);
			factDiscovery = false;
			for(int j = 0; j < currentClause.getLiterals().size(); j++) {
					for(int k = 1; !(k > KB.getTSize()+ factDiscoveries); k++){
						if(KB.getTValue().get("F"+k).equals(currentClause.getLiterals().get(j)))factDiscovery = true;
					}
					if(!factDiscovery) {
						KB.getTValue().put("F"+((++factDiscoveries)+KB.getTSize()), currentClause.getLiterals().get(j));
					}
					factDiscovery = false;
					countResults++;
			}
			count[i-1] = countResults;
			countResults = 0;
		}
		boolean infarred[] = new boolean[factDiscoveries + KB.getTSize()];
		for(int i = 0; i < infarred.length; i++) infarred[i] = false;
		HashSet<Literal> agenda = new HashSet<Literal>();
		for(int i = 1; !(i > KB.getTSize()); i++)agenda.add(KB.getTValue().get("F"+i));
		factDiscovery = false;
		for(int g = 1; !(agenda.isEmpty()); g++) {
			if(!(g > KB.getTSize())) {
				currentFact = KB.getTValue().get("F"+g);
				agenda.remove(KB.getTValue().get("F"+g));
				infarred[g-1] = factDiscovery = true;
			}else {
				for(int j = KB.getTSize() + 1; ( !(j > factDiscoveries+KB.getTSize()) || !factDiscovery); j++) {
					if(agenda.contains(KB.getTValue().get("F"+j))) {
						currentFact = KB.getTValue().get("F"+j);
						agenda.remove(KB.getTValue().get("F"+j));
						infarred[j-1] = factDiscovery = true;
					}
				}
			}
			if(factDiscovery) {
		 		for(int i = 1; !(i > KB.getYSize()); i++){
		 			currentClause = KB.getYValue().get("C"+i);
		 			if(currentClause.getLiterals().contains(currentFact)) {
		 				count[i-1]--;
						if((count[i-1] == 0)&&(currentClause.getLiteral().equals(finalClause.getLiteral()))) return true;
						if(!(currentClause.getLiteral().equals(finalClause.getLiteral())) ) {
							for(int j = KB.getTSize() + 1;  !(j > factDiscoveries + KB.getTSize()) ; j++) {
								if((KB.getTValue().get("F"+j).equals(currentClause.getLiteral())&& (!infarred[j-1]))) {
									agenda.add(currentClause.getLiteral());
								}
							}
						}
		 			}
		 		}
				factDiscovery = false;
			}
		}
		return false;
	}
}
