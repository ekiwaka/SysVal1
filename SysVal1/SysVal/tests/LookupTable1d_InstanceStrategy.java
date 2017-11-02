/*
 * Test data strategy for LookupTable1d.
 *
 * Generated by JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178), 2017-10-20 18:28 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.InstantiationIterator;
import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.NonNullMultiIterator;
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import org.jmlspecs.jmlunitng.strategy.ObjectStrategy;

/**
 * Test data strategy for LookupTable1d. Provides
 * instances of LookupTable1d for testing, using
 * parameters from constructor tests.
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2017-10-20 18:28 +0200
 */
public /*@ nullable_by_default */ class LookupTable1d_InstanceStrategy extends ObjectStrategy {
  /**
   * @return local-scope instances of LookupTable1d.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Object>
    (new Object[]
     { /* add LookupTable1d values or generators here */ });
  }

  /**
   * @return default instances of LookupTable1d, generated
   *  using constructor test parameters.
   */ 
  public RepeatedAccessIterator<LookupTable1d> defaultValues() {
    final List<RepeatedAccessIterator<LookupTable1d>> iters = 
      new LinkedList<RepeatedAccessIterator<LookupTable1d>>();

    // an instantiation iterator for the default constructor
    // (if there isn't one, it will fail silently)
    iters.add(new InstantiationIterator<LookupTable1d>
      (LookupTable1d.class, 
       new Class<?>[0], 
       new ObjectArrayIterator<Object[]>(new Object[][]{{}})));

    // parameters for method LookupTable1d(LookupScale, int[])
    iters.add(new InstantiationIterator<LookupTable1d>
      (LookupTable1d.class, 
       new Class<?>[]
       {LookupScale.class, 
        int[].class},
       LookupTable1d_JML_Test.p_LookupTable1d__LookupScale_scale__int1DArray_lookupValues__0().wrapped()));

    return new NonNullMultiIterator<LookupTable1d>(iters);
  }

  /**
   * Constructor. The boolean parameter to <code>setReflective</code>
   * determines whether or not reflection will be used to generate
   * test objects, and the int parameter to <code>setMaxRecursionDepth</code>
   * determines how many levels reflective generation of self-referential classes
   * will recurse.
   *
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public LookupTable1d_InstanceStrategy() {
    super(LookupTable1d.class);
    setReflective(true);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
