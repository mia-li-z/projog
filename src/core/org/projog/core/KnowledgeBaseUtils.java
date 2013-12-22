/*
 * Copyright 2013 S Webber
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
package org.projog.core;

import java.util.ArrayList;
import java.util.List;

import org.projog.core.function.AbstractSingletonPredicate;
import org.projog.core.term.Term;
import org.projog.core.term.TermType;

/**
 * Helper methods for performing common tasks on {@link KnowledgeBase} instances.
 */
public final class KnowledgeBaseUtils {
   /**
    * The functor of structures representing conjunctions ({@code ,}).
    */
   public static final String CONJUNCTION_PREDICATE_NAME = ",";
   /**
    * The functor of structures representing implications ({@code :-}).
    */
   public static final String IMPLICATION_PREDICATE_NAME = ":-";
   /**
    * The functor of structures representing questions (i.e. queries) ({@code ?-}).
    */
   public static final String QUESTION_PREDICATE_NAME = "?-";

   /**
    * Private constructor as all methods are static.
    */
   private KnowledgeBaseUtils() {
      // do nothing
   }

   /**
    * Returns list of all user defined predicates with the specified name.
    */
   public static List<PredicateKey> getPredicateKeysByName(KnowledgeBase kb, String predicateName) {
      List<PredicateKey> matchingKeys = new ArrayList<PredicateKey>();
      for (PredicateKey key : kb.getUserDefinedPredicates().keySet()) {
         if (predicateName.equals(key.getName())) {
            matchingKeys.add(key);
         }
      }
      return matchingKeys;
   }

   /**
    * Returns a {@link Predicate} instance for the specified {@link Term}.
    */
   public static Predicate getPredicate(KnowledgeBase kb, Term t) {
      return kb.getPredicateFactory(t).getPredicate(t.getArgs());
   }

   /**
    * Returns {@code true} if the specified {@link Term} represents a question, else {@code false}.
    * <p>
    * A {@link Term} is judged to represent a question if it is a structure with a functor of
    * {@link #QUESTION_PREDICATE_NAME} and a single argument.
    */
   public static boolean isQuestionFunctionCall(Term t) {
      return t.getType() == TermType.STRUCTURE && QUESTION_PREDICATE_NAME.equals(t.getName()) && t.getNumberOfArguments() == 1;
   }

   /**
    * Returns {@code true} if the specified {@link Term} represent a {@code dynamic} function call, else {@code false}.
    * <p>
    * A {@link Term} is judged to represent a dynamic function call (i.e. a request to mark a user defined predicate as
    * "dynamic") if it is a structure with a functor of {@code dynamic} and a single argument.
    */
   public static boolean isDynamicFunctionCall(Term t) {
      return "dynamic".equals(t.getName()) && t.getNumberOfArguments() == 1;
   }

   /**
    * Returns {@code true} if the predicate represented by the specified {@link Term} never succeeds on re-evaluation.
    */
   public static boolean isSingleAnswer(KnowledgeBase kb, Term term) {
      if (isConjunction(term)) {
         return isConjunctionWithSingleResult(kb, term);
      } else {
         PredicateFactory ef = kb.getPredicateFactory(term);
         return ef instanceof AbstractSingletonPredicate;
      }
   }

   /**
    * Returns an array of all {@link Term}s that make up the conjunction represented by the specified {@link Term}.
    * <p>
    * If the specified {@link Term} does not represent a conjunction then it will be used as the only element in the
    * returned array.
    */
   public static Term[] toArrayOfConjunctions(Term t) {
      List<Term> l = new ArrayList<Term>();
      while (isConjunction(t)) {
         l.add(0, t.getArgs()[1]);
         t = t.getArgs()[0];
      }
      l.add(0, t);
      return l.toArray(new Term[l.size()]);
   }

   private static boolean isConjunctionWithSingleResult(KnowledgeBase kb, Term antecedant) {
      Term[] functions = toArrayOfConjunctions(antecedant);
      return isAllSingleAnswerFunctions(kb, functions);
   }

   private static boolean isAllSingleAnswerFunctions(KnowledgeBase kb, Term[] functions) {
      for (Term t : functions) {
         if (!isSingleAnswer(kb, t)) {
            return false;
         }
      }
      return true;
   }

   /**
    * Returns {@code true} if the specified {@link Term} represent a conjunction, else {@code false}.
    * <p>
    * A {@link Term} is judged to represent a conjunction if is a structure with a functor of
    * {@link #CONJUNCTION_PREDICATE_NAME} and exactly two arguments.
    */
   public static boolean isConjunction(Term t) {
      // is relying on assumption that conjunctions are only, and always, represented by a comma
      return t.getType() == TermType.STRUCTURE && CONJUNCTION_PREDICATE_NAME.equals(t.getName()) && t.getArgs().length == 2;
   }
}