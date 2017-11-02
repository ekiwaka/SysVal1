/**
 * This class encapsulates one dimensional lookup table.
 */
class LookupTable1d {

	/** The only (one dimension, x) scale for this lookup table. */
	//@ invariant scaleX != null;
	LookupScale scaleX;
	
	/** The lookup values of this table. Contrary to the scales 
	 *  there are no sortedness requirements of any kind.
	 */
	int[] lookupValues;
	
	// INVARIANT
	//@ invariant scaleX.values.length == lookupValues.length;
	
	/**
	 * Constructs the lookup table
	 * @param scale the associated (x) scale
	 * @param lookupValues the table values
	 */
	// CONTRACT
	//@ normal_behavior
	//@ requires scale != null;
	//@ requires scale.values.length == lookupValues.length;
	//@ ensures \forall int i; 0<=i && i<scale.values.length; scaleX.values[i] == scale.values[i];
	//@ ensures \forall int j; 0<=j && j<lookupValues.length; lookupValues[j] == this.lookupValues[j];
	LookupTable1d(LookupScale scale, int[] lookupValues) {
		this.scaleX = scale;
		this.lookupValues = lookupValues;
	}
	
	/**
	 * Looks up the sensor value in the this table.
	 * @param sv the sensor value to look up
	 * @return the (interpolated) value from the table
	 */
	//@ requires sv != null;
	//@ requires sv.minValue <= sv.value && sv.value <= sv.maxValue;
	//@ pure;
	int getValue(SensorValue sv) {
		ScaleIndex si = scaleX.lookupValue(sv);
		int i = si.getIntPart();
		int f = si.getFracPart();
		int v = lookupValues[i];
		if(i<lookupValues.length-1) {
			int vn = lookupValues[i+1];
			//v = v + f; mistake
			v = v + (vn-v) * f / 100;
		}
		// ASSERTION(S)
		// (note, what you want to check here would normally
		//  be part of the postcondition, but would produce a very
		//  elaborate specification).
		if(i == lookupValues.length) {
			//@ assert v == lookupValues[i];
		}else {
			 //@ assert v == lookupValues[i] + (f * (lookupValues[i+1] - lookupValues[i])) / 100;
		}

		
		return v;
	}
}
