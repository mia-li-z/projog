/*
 * Copyright 2020 S. Webber
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.projog.core.predicate.udp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.verifyNoMoreInteractions;
import static org.mockito.Mockito.when;
import static org.projog.TestUtils.array;
import static org.projog.TestUtils.assertClass;
import static org.projog.TermFactory.atom;
import static org.projog.TestUtils.createClauseModel;
import static org.projog.core.term.TermUtils.EMPTY_ARRAY;

import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.ArgumentCaptor;
import org.projog.core.ProjogException;
import org.projog.core.kb.KnowledgeBase;
import org.projog.core.kb.KnowledgeBaseUtils;
import org.projog.core.predicate.Predicate;
import org.projog.core.predicate.PredicateFactory;
import org.projog.core.predicate.PredicateKey;
import org.projog.core.predicate.udp.ClauseActionFactory.AlwaysMatchedFact;
import org.projog.core.predicate.udp.ClauseActionFactory.ImmutableConsequentRule;
import org.projog.core.predicate.udp.ClauseActionFactory.ImmutableFact;
import org.projog.core.predicate.udp.ClauseActionFactory.MutableFact;
import org.projog.core.predicate.udp.ClauseActionFactory.MutableRule;
import org.projog.core.predicate.udp.ClauseActionFactory.VariableAntecedantClauseAction;
import org.projog.core.predicate.udp.ClauseActionFactory.ZeroArgConsequentRule;
import org.projog.core.term.Atom;
import org.projog.core.term.Term;
import org.projog.core.term.TermType;
import org.projog.core.term.Variable;

import com.tngtech.java.junit.dataprovider.DataProviderRunner;

@RunWith(DataProviderRunner.class)
public class ClauseActionFactoryTest {
   private KnowledgeBase kb;
   private PredicateFactory mockPredicateFactory;
   private Predicate mockPredicate1;
   private Predicate mockPredicate2;

   @Before
   public void before() {
      mockPredicate1 = mock(Predicate.class);
      mockPredicate2 = mock(Predicate.class);

      mockPredicateFactory = mock(PredicateFactory.class);
      when(mockPredicateFactory.getPredicate(EMPTY_ARRAY)).thenReturn(mockPredicate1, mockPredicate2);

      kb = KnowledgeBaseUtils.createKnowledgeBase();
      KnowledgeBaseUtils.bootstrap(kb);
      kb.getPredicates().addPredicateFactory(new PredicateKey("test", 0), mockPredicateFactory);
   }

   @After
   public void after() {
      verifyNoInteractions(mockPredicate1, mockPredicate2);
      verifyNoMoreInteractions(mockPredicateFactory);
   }
   @Test
   public void testVariableAntecedant_getPredicate_known_predicate() {
      Term[] queryArgs = array(atom("test"));
      VariableAntecedantClauseAction a = create(VariableAntecedantClauseAction.class, "p(X) :- X.");
      assertSame(mockPredicate1, a.getPredicate(queryArgs));
      assertSame(mockPredicate2, a.getPredicate(queryArgs));
      verify(mockPredicateFactory, times(2)).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testZeroArgConsequentRule_getPredicate() {
      ZeroArgConsequentRule a = create(ZeroArgConsequentRule.class, "p :- test.");
      assertSame(mockPredicate1, a.getPredicate(EMPTY_ARRAY));
      assertSame(mockPredicate2, a.getPredicate(EMPTY_ARRAY));
      verify(mockPredicateFactory, times(2)).getPredicate(EMPTY_ARRAY);
   }

   // TODO p :- test(X). p(X) :- test(X). p(a) :- test(X).
   @Test
   public void testImmutableConsequentRule_getPredicate_query_args_match_clause() {
      ImmutableConsequentRule a = create(ImmutableConsequentRule.class, "p(a,b,c) :- test.");
      Term[] queryArgs = array(atom("a"), atom("b"), atom("c"));
      assertSame(mockPredicate1, a.getPredicate(queryArgs));
      assertSame(mockPredicate2, a.getPredicate(queryArgs));
      verify(mockPredicateFactory, times(2)).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testImmutableConsequentRule_getPredicate_query_args_all_distinct_variables() {
      ImmutableConsequentRule a = create(ImmutableConsequentRule.class, "p(a,b,c) :- test.");
      Variable x = new Variable("X");
      Variable y = new Variable("Y");
      Variable z = new Variable("Z");
      assertSame(mockPredicate1, a.getPredicate(array(x, y, z)));
      assertEquals(atom("a"), x.getTerm());
      assertEquals(atom("b"), y.getTerm());
      assertEquals(atom("c"), z.getTerm());
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testImmutableConsequentRule_getPredicate_query_args_mixture_of_atom_and_distinct_variables() {
      ImmutableConsequentRule a = create(ImmutableConsequentRule.class, "p(a,b,c) :- test.");
      Variable x = new Variable("X");
      Variable y = new Variable("Y");
      assertSame(mockPredicate1, a.getPredicate(array(atom("a"), x, y)));
      assertEquals(atom("b"), x.getTerm());
      assertEquals(atom("c"), y.getTerm());
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testImmutableConsequentRule_getPredicate_shared_variables_match() {
      ImmutableConsequentRule a = create(ImmutableConsequentRule.class, "p(a,b,a) :- test.");
      Variable x = new Variable("X");
      Variable y = new Variable("Y");
      assertSame(mockPredicate1, a.getPredicate(array(x, y, x)));
      assertEquals(atom("a"), x.getTerm());
      assertEquals(atom("b"), y.getTerm());
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testMutableRule_getPredicate_distinct_variable_arguments() {
      MutableRule a = create(MutableRule.class, "p(X,Y,Z) :- test.");
      Variable v1 = new Variable("A");
      Variable v2 = new Variable("B");
      Variable v3 = new Variable("C");
      assertSame(mockPredicate1, a.getPredicate(array(v1, v2, v3)));
      // assert query variables have been unified with clause variables
      assertSame(TermType.VARIABLE, v1.getTerm().getType());
      assertNotSame(v1, v1.getTerm());
      assertEquals("X", ((Variable) v1.getTerm()).getId());
      assertSame(TermType.VARIABLE, v2.getTerm().getType());
      assertNotSame(v2, v2.getTerm());
      assertEquals("Y", ((Variable) v2.getTerm()).getId());
      assertSame(TermType.VARIABLE, v3.getTerm().getType());
      assertNotSame(v3, v3.getTerm());
      assertEquals("Z", ((Variable) v3.getTerm()).getId());
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testMutableRule_getPredicate_query_args_unify_with_clause() {
      MutableRule a = create(MutableRule.class, "p(a,X,c) :- test.");
      assertSame(mockPredicate1, a.getPredicate(array(atom("a"), atom("b"), atom("c"))));
      assertSame(mockPredicate2, a.getPredicate(array(atom("a"), atom("d"), atom("c"))));
      verify(mockPredicateFactory, times(2)).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testMutableRule_getPredicate_query_args_shared_variable_unify_with_clause() {
      MutableRule a = create(MutableRule.class, "p(a,X,a) :- test.");
      Variable x = new Variable("X");
      assertSame(mockPredicate1, a.getPredicate(array(x, atom("b"), x)));
      assertEquals(atom("a"), x.getTerm());
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testMutableRule_getPredicate_query_args_unify_with_clause_shared_variable() {
      MutableRule a = create(MutableRule.class, "p(X,b,X) :- test.");
      assertSame(mockPredicate1, a.getPredicate(array(atom("a"), atom("b"), atom("a"))));
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testMutableRule_getPredicate_query_args_variable_unifies_with_clause_variable() {
      MutableRule a = create(MutableRule.class, "p(a,X,c) :- test.");
      Variable variable = new Variable("A");
      assertSame(mockPredicate1, a.getPredicate(array(atom("a"), variable, atom("c"))));
      // assert query variable has been unified with clause variable
      assertSame(TermType.VARIABLE, variable.getTerm().getType());
      assertNotSame(variable, variable.getTerm());
      assertEquals("X", ((Variable) variable.getTerm()).getId());
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @Test
   public void testMutableRule_getPredicate_query_args_variable_unifies_with_clause_atom() {
      MutableRule a = create(MutableRule.class, "p(a,X,c) :- test.");
      Variable x = new Variable("X");
      assertSame(mockPredicate1, a.getPredicate(array(atom("a"), atom("b"), x)));
      assertEquals(atom("c"), x.getTerm());
      verify(mockPredicateFactory).getPredicate(EMPTY_ARRAY);
   }

   @SuppressWarnings("unchecked")
   private <T extends ClauseAction> T create(Class<?> type, String syntax) {
      ClauseModel model = createClauseModel(syntax);
      ClauseAction result = ClauseActionFactory.createClauseAction(kb, model);
      assertClass(type, result);
      assertSame(model, result.getModel());
      return (T) result;
   }
}
