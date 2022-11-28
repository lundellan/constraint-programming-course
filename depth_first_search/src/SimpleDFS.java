import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

public class SimpleDFS  {

	boolean trace = false;
	Store store;
	IntVar[] variablesToReport;
	int depth = 0;
	public int costValue = IntDomain.MaxInt; /* Represents the cost value of currently best solution for FloatVar cost.*/
	public IntVar costVariable = null; /*  Represents the cost variable. */
	public long N=0; /* Number of visited nodes */
	public long failedNodes = 0; /* Number of failed nodes excluding leave nodes */

	public SimpleDFS(Store s) {
		store = s;
	}

	/* This function is called recursively to assign variables one by one. */
	public boolean label(IntVar[] vars) {
		N++;
		
		if (trace) {
			for (int i = 0; i < vars.length; i++) {
				System.out.print (vars[i] + " ");
				System.out.println ();
			}
		}

		ChoicePoint choice = null;
		boolean consistent;

		if (costVariable != null) {
			try {
				if (costVariable.min() <= costValue - 1)	{
					costVariable.domain.in(store.level, costVariable, costVariable.min(), costValue - 1);
				}	else	{
					return false;
				}
			} catch (FailException f) {
				return false;
			}
		}

		consistent = store.consistency();
	
		if (!consistent) {
			return false;
		} else {
			if (vars.length == 0) {
				if (costVariable != null)		{
					costValue = costVariable.min();
				}

			reportSolution();
			return costVariable == null; // true is satisfiability search and false if minimization
		}

		choice = new ChoicePoint(vars);
		levelUp();

		store.impose(choice.getConstraint());

		// choice point imposed.
				
		consistent = label(choice.getSearchVariables());

		if (consistent) {
			levelDown();
			return true;
		} else {
			failedNodes++;
			restoreLevel();
			store.impose(new Not(choice.getConstraint()));

			// negated choice point imposed.
			consistent = label(vars);

			levelDown();

			if (consistent) {
				return true;
			} else {
				return false;
			}
				}
		}
	}

	void levelDown() {
		store.removeLevel(depth);
		store.setLevel(--depth);
	}

	void levelUp() {
		store.setLevel(++depth);
	}

	void restoreLevel() {
		store.removeLevel(depth);
		store.setLevel(store.level);
	}

	public void reportSolution() {
		System.out.println("Nodes visited: " + N);

		if (costVariable != null)
				System.out.println ("Cost is " + costVariable);

		for (int i = 0; i < variablesToReport.length; i++) 
				System.out.print (variablesToReport[i] + " ");
		System.out.println ("\n---------------");
	}

	public void setVariablesToReport(IntVar[] v) {
		variablesToReport = v;
	}

	public void setCostVariable(IntVar v) {
		costVariable = v;
	}

	public class ChoicePoint {

		IntVar var;
		IntVar[] searchVariables;
		int value;

		public ChoicePoint (IntVar[] v) {
			var = selectVariable(v);
			value = selectValue(var);
		}

		public IntVar[] getSearchVariables() {
			return searchVariables;
		}

		/**
		 * example variable selection; input order
		 */ 
		IntVar selectVariable(IntVar[] v) {
			if (v.length != 0) {

				searchVariables = new IntVar[v.length-1];
				for (int i = 0; i < v.length-1; i++) {
						searchVariables[i] = v[i+1]; 
				}

				return v[0];

			} else {
				System.err.println("Zero length list of variables for labeling");
				return new IntVar(store);
			}
		}

		/**
		 * example value selection; indomain_min
		 */ 
		int selectValue(IntVar v) {
				return v.min();
		}

		/**
		 * example constraint assigning a selected value
		 */
		public PrimitiveConstraint getConstraint() {
				return new XeqC(var, value);
		}
	}
}
