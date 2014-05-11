package org.projog.core.term;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.projog.TestUtils.atom;
import static org.projog.TestUtils.doubleNumber;
import static org.projog.TestUtils.integerNumber;
import static org.projog.TestUtils.list;
import static org.projog.TestUtils.structure;
import static org.projog.TestUtils.variable;

import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

/**
 * Test implementations of {@link Term}
 * <p>
 * As so much of the tests are about interactions between different classes of Terms it was decided to have a generic
 * TermTest class to test generic behaviour and have only specific behaviour tested in separate test classes specific to
 * a particular Term implementation.
 * 
 * @see AtomTest
 * @see AnonymousVariableTest
 * @see DoubleNumberTest
 * @see EmptyListTest
 * @see IntegerNumberTest
 * @see ListTest
 * @see StructureTest
 * @see VariableTest
 */
public class TermTest {
   private static final Term[] IMMUTABLE_TERMS = {atom("a"), atom("b"), atom("c"), atom("A"), atom("B"), atom("C"), atom("abc"), atom("ABC"), atom("AbC"), atom("0"), atom("1"), atom("-1"), atom("[]"),

   integerNumber(0), integerNumber(1), integerNumber(-1), integerNumber(Integer.MIN_VALUE), integerNumber(Integer.MAX_VALUE),

   doubleNumber(0), doubleNumber(1), doubleNumber(-1), doubleNumber(0.0001), doubleNumber(-0.0001), doubleNumber(Double.MIN_VALUE), doubleNumber(Double.MAX_VALUE),

   structure("abc"), structure("abc", atom()), structure("abc", atom(), atom()), structure("ABC"), structure("ABC", atom()), structure("ABC", atom(), atom()), structure("1"), structure("1", atom()), structure("1", atom(), atom()), structure("[]"),

   list(atom(), atom()), list(atom(), atom(), atom()), list(atom("a"), integerNumber(1), doubleNumber(1), structure("abc")),

   EmptyList.EMPTY_LIST};

   /** check both unify and strictEquality methods against various immutable Terms */
   @Test
   public void testUnifyAndStrictEquality() {
      for (Term t1 : IMMUTABLE_TERMS) {
         for (Term t2 : IMMUTABLE_TERMS) {
            assertUnify(t1, t2, t1 == t2);
            assertStrictEquality(t1, t2, t1 == t2);
         }
      }
   }

   /** check calling copy() on an immutable Term returns the Term */
   @Test
   public void testCopy() {
      for (Term t1 : IMMUTABLE_TERMS) {
         Map<Variable, Variable> sharedVariables = new HashMap<>();
         Term t2 = t1.copy(sharedVariables);
         assertSame(t1, t2);
         assertTrue(sharedVariables.isEmpty());
      }
   }

   /** check calling getValue() on an immutable Term returns the Term */
   @Test
   public void testGetValue() {
      for (Term t1 : IMMUTABLE_TERMS) {
         Term t2 = t1.getTerm();
         assertSame(t1, t2);
      }
   }

   @Test
   public void testIsImmutable() {
      for (Term element : IMMUTABLE_TERMS) {
         assertTrue(element.isImmutable());
      }
   }

   /** check calling backtrack() has no effect on an immutable Term */
   @Test
   public void testBacktrack() {
      for (Term t : IMMUTABLE_TERMS) {
         // keep track of the Term's current properties
         TermType originalType = t.getType();
         int originalNumberOfArguments = t.getNumberOfArguments();
         String originalToString = t.toString();

         // perform the backtrack()
         t.backtrack();

         // check properties are the same as prior to the backtrack()
         assertSame(originalType, t.getType());
         assertSame(originalNumberOfArguments, t.getNumberOfArguments());
         assertEquals(originalToString, t.toString());
      }
   }

   @Test
   public void testUnifyAndStrictEqualityWithVariable() {
      for (Term t : IMMUTABLE_TERMS) {
         Variable v = variable("X");

         // check equal
         assertStrictEquality(t, v, false);

         // check can unify (with unify called on t with v passed as a parameter)
         assertTrue(t.unify(v));

         // check equal after unification
         assertVariableIsUnifiedToTerm(v, t);

         // backtrack
         v.backtrack();

         // check backtrack undid result of unification
         assertSame(TermType.NAMED_VARIABLE, v.getType());
         assertStrictEquality(t, v, false);

         // check can unify again (but this time with unify called on v with t passed as a parameter)
         assertTrue(t.unify(v));

         // check equal after unification
         assertVariableIsUnifiedToTerm(v, t);

         // backtrack
         v.backtrack();

         // check backtrack undid result of unification
         assertSame(TermType.NAMED_VARIABLE, v.getType());
         assertStrictEquality(t, v, false);

         // unify v to something else
         v.unify(atom("some atom"));

         // check v and t can no longer be unified
         assertUnify(t, v, false);
      }
   }

   /** test {@link AnonymousVariable} unifies with everything and is strictly equal to nothing */
   @Test
   public void testUnifyAndStrictEqualityWithAnonymousVariable() {
      for (Term t : IMMUTABLE_TERMS) {
         assertUnify(t, AnonymousVariable.ANONYMOUS_VARIABLE, true);
         assertStrictEquality(t, AnonymousVariable.ANONYMOUS_VARIABLE, false);
      }
   }

   private void assertVariableIsUnifiedToTerm(Variable v, Term t) {
      assertStrictEquality(t, v, true);
      assertEquals(t.toString(), v.toString());
      assertSame(t.getType(), v.getType());
      assertSame(t, v.getTerm());
      assertSame(t, v.copy(null));
      assertUnify(t, v, true);
   }

   private void assertUnify(Term t1, Term t2, boolean expected) {
      assertEquals(expected, t1.unify(t2));
      assertEquals(expected, t2.unify(t1));
   }

   private void assertStrictEquality(Term t1, Term t2, boolean expected) {
      assertEquals(expected, t1.strictEquality(t2));
      assertEquals(expected, t2.strictEquality(t1));
   }
}