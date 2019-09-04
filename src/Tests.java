public class Tests{
	private CNFTesting Test1;
	private HornTesting Test2;
	private PRLHornTesting Test3;
	
	public Tests() {
		Test1 = new CNFTesting();
		Test2 = new HornTesting();
		Test3 = new PRLHornTesting();
	}
	
	public void run() {
		System.out.println("RESOLUTION IN CONTEXTUAL LOGIC"); Test1.run();
		System.out.println("\nFORWARD CHAINING IN CONTEXTUAL LOGIC"); Test2.run();
		System.out.println("\n \nFORWARD CHAINING IN PRIMARY OBJECTIVE LOGIC");Test3.run();
	}
	
	public static void main(String[] args) {
		Tests t = new Tests();
		t.run();
	}
}