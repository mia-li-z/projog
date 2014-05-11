package org.projog.core.term;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import static org.projog.TestUtils.atom;
import static org.projog.TestUtils.doubleNumber;
import static org.projog.TestUtils.integerNumber;
import static org.projog.TestUtils.list;
import static org.projog.TestUtils.structure;
import static org.projog.TestUtils.variable;

import java.util.Set;

import org.junit.Test;
import org.projog.core.ProjogException;

public class TermUtilsTest {
   @Test
   public void testEmptyArray() {
      assertEquals(0, TermUtils.EMPTY_ARRAY.length);
   }

   @Test
   public void testCopy() {
      // setup input terms
      Atom a = atom("a");
      Variable x = variable("X");
      Variable y = variable("Y");
      Variable z = variable("Z");
      assertTrue(x.unify(a));
      Structure p = structure("p", x, y);
      Term[] input = {a, p, x, y, z};

      // perform copy
      Term[] output = TermUtils.copy(input);

      // check result
      assertEquals(input.length, output.length);

      assertSame(a, output[0]);

      Term t = output[1];
      assertSame(TermType.STRUCTURE, t.getType());
      assertSame(p.getName(), t.getName());
      assertEquals(2, t.getNumberOfArguments());
      assertSame(a, t.getArgument(0));
      Term copyOfY = t.getArgument(1);
      assertVariable(copyOfY, "Y");

      assertSame(a, output[2]);

      assertSame(copyOfY, output[3]);

      assertVariable(output[4], "Z");
   }

   private void assertVariable(Term t, String id) {
      assertSame(TermType.NAMED_VARIABLE, t.getType());
      assertSame(t, t.getTerm());
      assertEquals(id, ((Variable) t).getId());
   }

   @Test
   public void testBacktrack() {
      // setup input terms
      Atom a = atom("a");
      Atom b = atom("b");
      Atom c = atom("c");
      Variable x = variable("X");
      Variable y = variable("Y");
      Variable z = variable("Z");
      assertTrue(x.unify(a));
      assertTrue(y.unify(b));
      assertTrue(z.unify(c));
      Term original[] = {x, a, b, y, c, z};
      Term input[] = {x, a, b, y, c, z};

      // perform the backtrack
      TermUtils.backtrack(input);

      // assert variables have backtracked
      assertSame(x, x.getTerm());
      assertSame(y, y.getTerm());
      assertSame(z, z.getTerm());

      // assert array was not manipulated
      for (int i = 0; i < input.length; i++) {
         assertSame(original[i], input[i]);
      }
   }

   @Test
   public void testUnifySuccess() {
      // setup input terms
      Variable x = variable("X");
      Variable y = variable("Y");
      Variable z = variable("Z");
      Atom a = atom("a");
      Atom b = atom("b");
      Atom c = atom("c");
      Term[] input1 = {x, b, z};
      Term[] input2 = {a, y, c};

      // attempt unification
      assertTrue(TermUtils.unify(input1, input2));

      // assert all variables unified to atoms
      assertSame(a, x.getTerm());
      assertSame(b, y.getTerm());
      assertSame(c, z.getTerm());
   }

   @Test
   public void testUnifyFailure() {
      // setup input terms
      Variable x = variable("X");
      Variable y = variable("Y");
      Variable z = variable("Z");
      Atom a = atom("a");
      Atom b = atom("b");
      Atom c = atom("c");
      Term[] input1 = {x, b, z, b};
      Term[] input2 = {a, y, c, a};

      // attempt unification
      assertFalse(TermUtils.unify(input1, input2));

      // assert all variables in input1 were backed tracked
      assertSame(x, x.getTerm());
      assertSame(z, z.getTerm());

      // as javadocs states, terms passed in second argument to unify may not be backtracked 
      assertSame(b, y.getTerm());
   }

   @Test
   public void testGetAllVariablesInTerm() {
      Variable q = variable("Q");
      Variable r = variable("R");
      Variable s = variable("S");
      Variable t = variable("T");
      Variable v = variable("V");
      Variable w = variable("W");
      Variable x = variable("X");
      Variable y = variable("Y");
      Variable z = variable("Z");
      Variable[] variables = {q, r, s, t, v, w, x, y, z};
      Structure input = structure("p1", x, v, AnonymousVariable.ANONYMOUS_VARIABLE, EmptyList.EMPTY_LIST, y, q, integerNumber(1), structure("p2", y, doubleNumber(1.5), w), list(s, y, integerNumber(7), r, t), z);
      Set<Variable> result = TermUtils.getAllVariablesInTerm(input);
      assertEquals(variables.length, result.size());
      for (Variable variable2 : variables) {
         assertTrue(result.contains(variable2));
      }
   }

   @Test
   public void testCastToNumericIntegerNumber() {
      IntegerNumber i = integerNumber();
      assertSame(i, TermUtils.castToNumeric(i));
   }

   @Test
   public void testCastToNumericDoubleNumber() {
      DoubleNumber d = doubleNumber();
      assertSame(d, TermUtils.castToNumeric(d));
   }

   @Test
   public void testCastToNumericAtom() {
      try {
         Atom a = atom("1");
         TermUtils.castToNumeric(a);
         fail();
      } catch (ProjogException e) {
         assertEquals("Expected Numeric but got: ATOM with value: 1", e.getMessage());
      }
   }

   @Test
   public void testCastToNumericVariable() {
      Variable v = variable();
      try {
         TermUtils.castToNumeric(v);
         fail();
      } catch (ProjogException e) {
         assertEquals("Expected Numeric but got: NAMED_VARIABLE with value: X", e.getMessage());
      }
      IntegerNumber i = integerNumber();
      v.unify(i);
      assertSame(i, TermUtils.castToNumeric(v));
   }

   @Test
   public void testGetAtomName() {
      Atom a = atom("testAtomName");
      assertEquals("testAtomName", TermUtils.getAtomName(a));
   }

   @Test
   public void testGetAtomNameException() {
      Structure p = structure("testAtomName");
      try {
         assertEquals("testAtomName", TermUtils.getAtomName(p));
      } catch (ProjogException e) {
         assertEquals("Expected an atom but got: STRUCTURE with value: testAtomName()", e.getMessage());
      }
   }
}