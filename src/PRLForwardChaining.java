/*
 * PRLForwardChaining.java
 * G. Moschovis
 */
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.ArrayList;

public class PRLForwardChaining {
	protected static Vec2<Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>>, PRLHornClause> RET;
	protected static Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>> KB;
	protected static HashMap<String, PRLLiteral> literals;
	protected static HashMap<String, PRLHornClause> clauses;
	
	public Vec2<Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>>, PRLHornClause> initialize_Ex1(String filename) {
		BufferedReader br = null;
		try {
			br = new BufferedReader(new FileReader(filename));
			String sCurrentLine, firstLine = br.readLine();
			PRLHornClause finalClause, intermediateClause;
			PRLLiteral finalLiteral, intermediateLiteral;
			RET = new Vec2<Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>>, PRLHornClause>();
			KB = new Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>>();
			literals = new HashMap<String, PRLLiteral>();
			clauses = new HashMap<String, PRLHornClause>();
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
				String implCurrentLine, andCurrentLine;
				int aCurrentSize, aCurrentSize1, aCurrentSize2, implCurrentSize, andCurrentSize, litCnt = 0, clsCnt = 0;
				boolean implicationDiscovery;
				while (((sCurrentLine = br.readLine()) != null) && (check)) {
					sCurrentLine = sCurrentLine.trim().replaceAll(" +", " ");;
					String[] aCurrentLine = sCurrentLine.split(" "); // separator is: " " = [whitespace]
					aCurrentSize = aCurrentLine.length;
					if(aCurrentLine[0].equals("PROVE")) {
						System.out.print(sCurrentLine.substring(6, sCurrentLine.length()) + " ");
						if(sCurrentLine.contains("IMPLIES")) {
							finalClause = new PRLHornClause();
							int j;
							String[] implArrCurrentLine = sCurrentLine.split(" IMPLIES "); // separator is: " IMPLIES " = [whitespace]+"IMPLIES"+[whitespace]
							implCurrentSize = implArrCurrentLine.length;
							if(implCurrentSize != 2)check = false;
							else {
								/*Implied Literal Handling*/
								String[] aCurrentLine2 = implArrCurrentLine[1].split(" "); // separator is: " " = [whitespace]
								aCurrentSize2 = aCurrentLine2.length;
								 if(implArrCurrentLine[1].contains("NOT")&& aCurrentLine2[0].equals("NOT")){ 
						 			String[] aCurrentLine1 = aCurrentLine2[1].split("("); // separator is: "(" = [left parenthesis]
									aCurrentSize1 = aCurrentLine1.length;
									if(aCurrentSize1 != 2)check = false;
									else {
										finalLiteral = new PRLLiteral(aCurrentLine1[0], true);
										if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
										else {
											finalLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
											for(int k = 2; k < aCurrentSize2; k++) {
												if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
													check = false;
													break;
												}
												else{
													if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x"))  
														finalLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
													else finalLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
												}
											}
											finalClause.setLiteral(finalLiteral);
										}
									}
								}else if (!implArrCurrentLine[1].contains("NOT")){
									String[] aCurrentLine1 = aCurrentLine[0].split("\\("); // separator is: "(" = [left parenthesis]
									aCurrentSize1 = aCurrentLine1.length;
									if(aCurrentSize1 != 2)check = false;
									else {
										finalLiteral = new PRLLiteral(aCurrentLine1[0], false);
										if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
										else {
											for(int k = 1; k < aCurrentSize2; k++) {
												if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
													check = false;
													break;
												}
												else{
													if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x")) 
														finalLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
													else finalLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
												}
											}
											finalClause.setLiteral(finalLiteral);
										}
									}
								} else check = false;
								/*Initial Series of Literals Handling*/
								 if(implArrCurrentLine[0].substring(0, 6).contains("PROVE")) {
									String[] andArrCurrentLine = implArrCurrentLine[0].substring(0, 6).split(" AND "); // separator is: " AND " = [whitespace]+AND+[whitespace]
									andCurrentSize = andArrCurrentLine.length;
									for(j = 0; j < andCurrentSize; j++) {
										aCurrentLine2 = andArrCurrentLine[j].split(" "); // separator is: " " = [whitespace]
										aCurrentSize2 = aCurrentLine2.length;
										if(andArrCurrentLine[j].contains("NOT")&& aCurrentLine2[0].equals("NOT")){ 
								 			String[] aCurrentLine1 = aCurrentLine2[1].split("\\("); // separator is: "(" = [left parenthesis]
											aCurrentSize1 = aCurrentLine1.length;
											if(aCurrentSize1 != 2)check = false;
											else {
												finalLiteral = new PRLLiteral(aCurrentLine1[0], true);
												if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
												else {
													finalLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
													for(int k = 2; k < aCurrentSize2; k++) {
														if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
															check = false;
															break;
														}
														else{
															if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x"))  
																finalLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
															else finalLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
														}
													}
													finalClause.getLiterals().add(finalLiteral);
												}
											}
										}else if (!implArrCurrentLine[1].contains("NOT")){
											String[] aCurrentLine1 = aCurrentLine2[0].split("\\("); // separator is: "(" = [left parenthesis]
											aCurrentSize1 = aCurrentLine1.length;
											if(aCurrentSize1 != 2)check = false;
											else {
												finalLiteral = new PRLLiteral(aCurrentLine1[0], false);
												if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
												else {
													for(int k = 1; k < aCurrentSize2; k++) {
														if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
															check = false;
															break;
														}
														else{
															if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x")) 
																finalLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
															else finalLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
														}
													}
													finalClause.getLiterals().add(finalLiteral);
												}
											}
										}
									}
									/*Clause Handling*/
							        RET.setYValue(finalClause);
								 }else check = false;
							}
						}else if(sCurrentLine.contains("AND")) {
							 if(sCurrentLine.substring(0, 6).contains("PROVE")) {
								String[] andArrCurrentLine = sCurrentLine.substring(0, 6).split(" AND "); // separator is: " AND " = [whitespace]+AND+[whitespace]
								andCurrentSize = andArrCurrentLine.length;
								finalClause = new PRLHornClause();
								int j;
								for(j = 0; j < andCurrentSize; j++) {
									String[] aCurrentLine2 = andArrCurrentLine[j].split(" "); // separator is: " " = [whitespace]
									aCurrentSize2 = aCurrentLine2.length;
									 if(andArrCurrentLine[j].contains("NOT")&& aCurrentLine2[0].equals("NOT")){ 
							 			String[] aCurrentLine1 = aCurrentLine2[1].split("("); // separator is: "(" = [left parenthesis]
										aCurrentSize1 = aCurrentLine1.length;
										if(aCurrentSize1 != 2)check = false;
										else {
											finalLiteral = new PRLLiteral(aCurrentLine1[0], true);
											if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
											else {
												finalLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
												for(int k = 2; k < aCurrentSize2; k++) {
													if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
														check = false;
														break;
													}
													else{
														if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x"))  
															finalLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
														else finalLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
													}
												}
												finalClause.getLiterals().add(finalLiteral);
											}
										}
									 }
								}
								/*Clause Handling*/
						        RET.setYValue(finalClause);
							 } else check = false;
				 		}else if(sCurrentLine.contains("NOT") && aCurrentLine[1].equals("NOT")){ 
				 			finalClause = new PRLHornClause();
 				 			String[] aCurrentLine1 = aCurrentLine[2].split("\\("); // separator is: "(" = [left parenthesis]
							aCurrentSize1 = aCurrentLine1.length;
							if(aCurrentSize1 != 2)check = false;
							else {
								finalLiteral = new PRLLiteral(aCurrentLine1[0], true);
								if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
								else {
									finalLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
									for(int j = 3; j < aCurrentSize; j++) {
										if((j < aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ',')|| (j == aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ')') ) {
											check = false;
											break;
										}
										else{
											finalLiteral.getMembers().add(new Constant(aCurrentLine[j].substring(0, aCurrentLine[j].length()-1)));
										}
									}
									finalClause.setLiteral(finalLiteral);
							        RET.setYValue(finalClause);
								}
							}
				 		}else if (!sCurrentLine.contains("NOT")){
				 			finalClause = new PRLHornClause();
				 			String[] aCurrentLine1 = aCurrentLine[1].split("\\("); // separator is: "(" = [left parenthesis]
							aCurrentSize1 = aCurrentLine1.length;
							if(aCurrentSize1 != 2)check = false;
							else {
								finalLiteral = new PRLLiteral(aCurrentLine1[0], false);
								if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
								else {
									finalLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
									for(int j = 2; j < aCurrentSize; j++) {
										if((j < aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ',')|| (j == aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ')') ) {
											check = false;
											break;
										}
										else{
											finalLiteral.getMembers().add(new Constant(aCurrentLine[j].substring(0, aCurrentLine[j].length()-1)));
										}
									}
									finalClause.setLiteral(finalLiteral);
							        RET.setYValue(finalClause);
								}
							}
				 		} else check = false;
					} else {
						if(sCurrentLine.contains("IMPLIES")){ 
							//implicationDiscovery = false;
							intermediateClause = new PRLHornClause();
							int j;
							String[] implArrCurrentLine = sCurrentLine.split(" IMPLIES "); // separator is: " IMPLIES " = [whitespace]+"IMPLIES"+[whitespace]
							implCurrentSize = implArrCurrentLine.length;
							if(implCurrentSize != 2)check = false;
							else {
								/*Implied Literal Handling*/
								String[] aCurrentLine2 = implArrCurrentLine[1].split(" "); // separator is: " " = [whitespace]
								aCurrentSize2 = aCurrentLine2.length;
								 if(implArrCurrentLine[1].contains("NOT")&& aCurrentLine2[0].equals("NOT")){ 
						 			String[] aCurrentLine1 = aCurrentLine2[1].split("\\("); // separator is: "(" = [left parenthesis]
									aCurrentSize1 = aCurrentLine1.length;
									if(aCurrentSize1 != 2)check = false;
									else {
										intermediateLiteral = new PRLLiteral(aCurrentLine1[0], true);
										if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
										else {
											if(aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).length() == 2 && aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).startsWith("x")) 
												intermediateLiteral.getMembers().add(new Variable(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
										else intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
											for(int k = 2; k < aCurrentSize2; k++) {
												if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
													check = false;
													break;
												}
												else{
													if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x"))  
															intermediateLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
													else intermediateLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
												}
											}
											intermediateClause.setLiteral(intermediateLiteral);
										}
									}
								}else if (!implArrCurrentLine[1].contains("NOT")){
									String[] aCurrentLine1 = aCurrentLine2[0].split("\\("); // separator is: "(" = [left parenthesis]
									aCurrentSize1 = aCurrentLine1.length;
									if(aCurrentSize1 != 2)check = false;
									else {
										intermediateLiteral = new PRLLiteral(aCurrentLine1[0], false);
										if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
										else {
											if(aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).length() == 2 && aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).startsWith("x")) 
												intermediateLiteral.getMembers().add(new Variable(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
										else intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
											for(int k = 1; k < aCurrentSize2; k++) {
												if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
													check = false;
													break;
												}
												else{
													if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x")) 
															intermediateLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
													else intermediateLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
												}
											}
											intermediateClause.setLiteral(intermediateLiteral);
										}
									}
								} else check = false;
								/*Initial Series of Literals Handling*/
								String[] andArrCurrentLine = implArrCurrentLine[0].split(" AND "); // separator is: " AND " = [whitespace]+AND+[whitespace]
								andCurrentSize = andArrCurrentLine.length;
								for(j = 0; j < andCurrentSize; j++) {
									aCurrentLine2 = andArrCurrentLine[j].split(" "); // separator is: " " = [whitespace]
									aCurrentSize2 = aCurrentLine2.length;
									 if(andArrCurrentLine[j].contains("NOT")&& aCurrentLine2[0].equals("NOT")){ 
								 			String[] aCurrentLine1 = aCurrentLine2[1].split("\\("); // separator is: "(" = [left parenthesis]
											aCurrentSize1 = aCurrentLine1.length;
											if(aCurrentSize1 != 2)check = false;
											else {
												intermediateLiteral = new PRLLiteral(aCurrentLine1[0], true);
												if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
												else {
													intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
													if(aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).length() == 2 && aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).startsWith("x")) 
														intermediateLiteral.getMembers().add(new Variable(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
												else intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
													for(int k = 2; k < aCurrentSize2; k++) {
														if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
															check = false;
															break;
														}
														else{
															if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x"))  
																	intermediateLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
															else intermediateLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
														}
													}
													intermediateClause.getLiterals().add(intermediateLiteral);
												}
											}
										}else if (!implArrCurrentLine[1].contains("NOT")){
											String[] aCurrentLine1 = aCurrentLine2[0].split("\\("); // separator is: "(" = [left parenthesis]
											aCurrentSize1 = aCurrentLine1.length;
											if(aCurrentSize1 != 2)check = false;
											else {
												intermediateLiteral = new PRLLiteral(aCurrentLine1[0], false);
												if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
												else {
													if(aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).length() == 2 && aCurrentLine1[1].substring(0, aCurrentLine1[1].length() - 1).startsWith("x")) 
														intermediateLiteral.getMembers().add(new Variable(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
												else intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
													for(int k = 1; k < aCurrentSize2; k++) {
														if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
															check = false;
															break;
														}
														else{
															if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x")) 
																	intermediateLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
															else intermediateLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
														}
													}
													intermediateClause.getLiterals().add(intermediateLiteral);
												}
											}
										} else check = false;
								}
								/*Clause Handling*/
								clauses.put("C"+(++clsCnt),intermediateClause);
							}
						}else if (sCurrentLine.contains("AND")) {
							String[] andArrCurrentLine = sCurrentLine.split(" AND "); // separator is: " AND " = [whitespace]+AND+[whitespace]
							andCurrentSize = andArrCurrentLine.length;
							intermediateClause = new PRLHornClause();
							int j;
							for(j = 0; j < andCurrentSize; j++) {
								String[] aCurrentLine2 = andArrCurrentLine[j].split(" "); // separator is: " " = [whitespace]
								aCurrentSize2 = aCurrentLine2.length;
								 if(andArrCurrentLine[j].contains("NOT")&& aCurrentLine2[0].equals("NOT")){ 
						 			String[] aCurrentLine1 = aCurrentLine2[1].split("\\("); // separator is: "(" = [left parenthesis]
									aCurrentSize1 = aCurrentLine1.length;
									if(aCurrentSize1 != 2)check = false;
									else {
										intermediateLiteral = new PRLLiteral(aCurrentLine1[0], true);
										if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
										else {
											intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
											for(int k = 2; k < aCurrentSize2; k++) {
												if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
													check = false;
													break;
												}
												else{
													if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x"))  
															intermediateLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
													else intermediateLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
												}
											}
											intermediateClause.getLiterals().add(intermediateLiteral);
										}
									}
								}else if (sCurrentLine.contains("NOT")){
									String[] aCurrentLine1 = aCurrentLine[0].split("\\("); // separator is: "(" = [left parenthesis]
									aCurrentSize1 = aCurrentLine1.length;
									if(aCurrentSize1 != 2)check = false;
									else {
										intermediateLiteral = new PRLLiteral(aCurrentLine1[0], false);
										if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' &&  aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
										else {
											for(int k = 1; k < aCurrentSize2; k++) {
												if((k < aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ',')|| (k == aCurrentSize2 - 1 && aCurrentLine2[k].charAt(aCurrentLine2[k].length() - 1)!= ')') ) {
													check = false;
													break;
												}
												else{
													if(aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).length() == 2 && aCurrentLine2[k].substring(0, aCurrentLine2[k].length() - 1).startsWith("x")) 
															intermediateLiteral.getMembers().add(new Variable(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
													else intermediateLiteral.getMembers().add(new Constant(aCurrentLine2[k].substring(0, aCurrentLine2[k].length()-1)));
												}
											}
											intermediateClause.getLiterals().add(intermediateLiteral);
										}
									}
								} else check = false;
							}
							implicationDiscovery = false;
							/*Initial Series of Literals Handling*/
							if(check && intermediateClause.getLiterals().size()> 0) {
								for(int i = 0; i < intermediateClause.getLiterals().size(); i++) {
									if(!intermediateClause.getLiterals().get(i).getNeg()) { // True literal is one per Horn Clause
										intermediateClause.setLiteral(intermediateClause.getLiterals().get(i));
										intermediateClause.getLiterals().remove(i);
										 implicationDiscovery = true;
									}
									/*Clause Handling*/
									if(implicationDiscovery) {
										clauses.put("C"+(++clsCnt),intermediateClause);
										break;
									}
								}
							} else check = false;
						} else if(sCurrentLine.contains("NOT")&& aCurrentLine[0].equals("NOT")){ 
				 			String[] aCurrentLine1 = aCurrentLine[1].split("\\("); // separator is: "(" = [left parenthesis]
							aCurrentSize1 = aCurrentLine1.length;
							if(aCurrentSize1 != 2)check = false;
							else {
								intermediateLiteral = new PRLLiteral(aCurrentLine1[0], true);
								if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' && aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
								else {
									intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
									for(int j = 2; j < aCurrentSize; j++) {
										if((j < aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ',')|| (j == aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ')') ) {
											check = false;
											break;
										}
										else{
											intermediateLiteral.getMembers().add(new Constant(aCurrentLine[j].substring(0, aCurrentLine[j].length()-1)));
										}
									}
									literals.put("F"+(++litCnt), intermediateLiteral);
								}
							}
						}else if (!sCurrentLine.contains("NOT")){
							String[] aCurrentLine1 = aCurrentLine[0].split("\\("); // separator is: "(" = [left parenthesis]
							aCurrentSize1 = aCurrentLine1.length;
							if(aCurrentSize1 != 2)check = false;
							else {
								intermediateLiteral = new PRLLiteral(aCurrentLine1[0], false);
								if( aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ',' && aCurrentLine1[1].charAt(aCurrentLine1[1].length() - 1)!= ')')check = false;
								else {
									intermediateLiteral.getMembers().add(new Constant(aCurrentLine1[1].substring(0, aCurrentLine1[1].length()-1)));
									for(int j = 1; j < aCurrentSize; j++) {
										if((j < aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ',')|| (j == aCurrentSize - 1 && aCurrentLine[j].charAt(aCurrentLine[j].length() - 1)!= ')') ) {
											check = false;
											break;
										}
										else{
											intermediateLiteral.getMembers().add(new Constant(aCurrentLine[j].substring(0, aCurrentLine[j].length()-1)));
										}
									}
									literals.put("F"+(++litCnt), intermediateLiteral);
								}
							}
						} else check = false;
					}
				}
				/* D E B U G G I N G
				System.out.println("\n L I T E R A L S");
				 for(int i = 1; i < literals.size()+1; i++) { literals.get("F"+i).print(); System.out.print("\n");}
				 System.out.println("\n C L A U S E S");
				 for(int i = 1; i < clauses.size() + 1; i++) clauses.get("C"+i).print();  */
				 if(check) {
					 KB.setTValue(literals);
				     KB.setYValue(clauses);
				}else {
					System.out.println("Wrong file format; please try again.");
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
	
	public boolean PL_FC_Entails(Vec2<HashMap<String,PRLLiteral>, HashMap<String, PRLHornClause>> KB, PRLHornClause finalClause) {
		PRLLiteral currentFact = new PRLLiteral();
		PRLHornClause currentClause;
		int factDiscoveries = 0, countResults = 0;
		boolean factDiscovery, syntaxMatch;
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
		ArrayList<PRLLiteral> agenda = new ArrayList<PRLLiteral>();
		for(int i = 1; !(i > KB.getTSize()); i++)agenda.add(KB.getTValue().get("F"+i));
		factDiscovery = false;
		for(int g = 1; !(agenda.isEmpty()); g++) {
			if(!(g > KB.getTSize())) {
				currentFact = KB.getTValue().get("F"+g);
				agenda.remove(KB.getTValue().get("F"+g));
				infarred[g-1] = factDiscovery = true;
			}else {
				for(int j = KB.getTSize() + 1; ( !(j > factDiscoveries+KB.getTSize()) || !factDiscovery); j++) {
					syntaxMatch = false;
					for(int k = 0; k < agenda.size(); k++) {
						if(agenda.get(k).equals(KB.getTValue().get("F"+j))) { 
							currentFact = agenda.get(k);
							agenda.remove(k);
							infarred[j-1] = factDiscovery = true;
							break;
						}
					}
				}
			}
			if(factDiscovery) {
				ArrayList<Vec2<Constant, Variable>> varValue = new ArrayList<Vec2<Constant, Variable>>();
		 		for(int i = 1; !(i > KB.getYSize()); i++){
		 			currentClause = KB.getYValue().get("C"+i);
		 			syntaxMatch = true; 
		 			for(int j = 0; j < currentClause.getLiterals().size(); j++) {
		 				if (currentClause.getLiterals().get(j).equals(currentFact)) {
		 					syntaxMatch = true;
		 					if(currentClause.getLiterals().get(j).getVar()) {
		 						for(int k = 0; k < currentClause.getLiterals().get(j).getMembers().size(); k++) {
		 							 if(currentClause.getLiterals().get(j).getMembers().get(k) instanceof Variable) 
		 								 varValue.add(new Vec2<Constant, Variable>((Constant)currentFact.getMembers().get(k),(Variable)currentClause.getLiterals().get(j).getMembers().get(k) ) );
		 						}
		 					}
		 					break;
		 				}
		 			}
		 			if(syntaxMatch) {
		 				count[i-1]--;
		 				boolean finishMatch = currentClause.getLiteral().equals(finalClause.getLiteral()); 
						if((count[i-1] == 0)&&(finishMatch)) return true;
						if(!(currentClause.getLiteral().equals(finalClause.getLiteral())) ) {
							/* equals checks name+size; missing control */
							for(int j = KB.getTSize() + 1;  !(j > factDiscoveries + KB.getTSize()) ; j++) {
								if((KB.getTValue().get("F"+j).equals(currentClause.getLiteral())&& (!infarred[j-1]))) {
									PRLLiteral impLitTemp = currentClause.getLiteral();
									ArrayList<PRLTerm> newTerms = new ArrayList<PRLTerm>();
									if(varValue.size() != 0) {
										for(int k0 = 0; k0 < impLitTemp.getMembers().size(); k0++) {
				 							 if(impLitTemp.getMembers().get(k0) instanceof Variable) {
				 								for(int k1 = 0; k1 < varValue.size(); k1++) {
				 									if(impLitTemp.getMembers().get(k0).getName().equals(varValue.get(k1).getYValue().getName())) {
				 										newTerms.add(varValue.get(k1).getTValue());
				 										break;
				 									}
				 								}
				 							 }else {
				 								 newTerms.add(impLitTemp.getMembers().get(k0));
				 							 }
				 						}
										impLitTemp.setMembers(newTerms);
									}
									agenda.add(impLitTemp);
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