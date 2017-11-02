/*
 * Test data strategy for IgnitionModule.
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
 * Test data strategy for IgnitionModule. Provides
 * instances of IgnitionModule for testing, using
 * parameters from constructor tests.
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2017-10-20 18:28 +0200
 */
public /*@ nullable_by_default */ class IgnitionModule_InstanceStrategy extends ObjectStrategy {
  /**
   * @return local-scope instances of IgnitionModule.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Object>
    (new Object[]
     { /* add IgnitionModule values or generators here */ });
  }

  /**
   * @return default instances of IgnitionModule, generated
   *  using constructor test parameters.
   */ 
  public RepeatedAccessIterator<IgnitionModule> defaultValues() {
    final List<RepeatedAccessIterator<IgnitionModule>> iters = 
      new LinkedList<RepeatedAccessIterator<IgnitionModule>>();

    // an instantiation iterator for the default constructor
    // (if there isn't one, it will fail silently)
    iters.add(new InstantiationIterator<IgnitionModule>
      (IgnitionModule.class, 
       new Class<?>[0], 
       new ObjectArrayIterator<Object[]>(new Object[][]{{}})));

    // parameters for method IgnitionModule(SensorValue)
    iters.add(new InstantiationIterator<IgnitionModule>
      (IgnitionModule.class, 
       new Class<?>[]
       {SensorValue.class},
       IgnitionModule_JML_Test.p_IgnitionModule__SensorValue_rpmSensor__0().wrapped()));

    return new NonNullMultiIterator<IgnitionModule>(iters);
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
  public IgnitionModule_InstanceStrategy() {
    super(IgnitionModule.class);
    setReflective(true);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}