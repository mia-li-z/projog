package org.projog.core.udp.interpreter;

import java.util.HashMap;
import java.util.Map;

import org.projog.core.PredicateFactory;
import org.projog.core.term.Term;
import org.projog.core.term.Unifier;
import org.projog.core.term.Variable;
import org.projog.core.udp.TailRecursivePredicate;
import org.projog.core.udp.TailRecursivePredicateMetaData;

/**
 * A implementation of {@link TailRecursivePredicate} for interpreted user defined predicates.
 * <p>
 * The user defined predicate must be judged as eligible for <i>tail recursion optimisation</i> using the criteria used
 * by {@link TailRecursivePredicateMetaData}.
 * </p>
 * <img src="doc-files/InterpretedTailRecursivePredicateFactory.png">
 * 
 * @see InterpretedTailRecursivePredicateFactory
 * @see TailRecursivePredicateMetaData
 */
final class InterpretedTailRecursivePredicate extends TailRecursivePredicate {
   // TODO doesn't currently respect spypoints

   private final int numArgs;
   private final Term[] currentQueryArgs;
   private final boolean isRetryable;
   private final PredicateFactory[] firstClausePredicateFactories;
   private final Term[] firstClauseConsequentArgs;
   private final Term[] firstClauseOriginalTerms;
   private final PredicateFactory[] secondClausePredicateFactories;
   private final Term[] secondClauseConsequentArgs;
   private final Term[] secondClauseOriginalTerms;

   InterpretedTailRecursivePredicate(Term[] inputArgs, PredicateFactory[] firstClausePredicateFactories, Term[] firstClauseConsequentArgs, Term[] firstClauseOriginalTerms, PredicateFactory[] secondClausePredicateFactories,
            Term[] secondClauseConsequentArgs, Term[] secondClauseOriginalTerms, boolean isRetryable) {
      this.numArgs = inputArgs.length;
      this.currentQueryArgs = new Term[numArgs];
      for (int i = 0; i < numArgs; i++) {
         currentQueryArgs[i] = inputArgs[i].getTerm();
      }

      this.firstClausePredicateFactories = firstClausePredicateFactories;
      this.firstClauseConsequentArgs = firstClauseConsequentArgs;
      this.firstClauseOriginalTerms = firstClauseOriginalTerms;
      this.secondClausePredicateFactories = secondClausePredicateFactories;
      this.secondClauseConsequentArgs = secondClauseConsequentArgs;
      this.secondClauseOriginalTerms = secondClauseOriginalTerms;
      this.isRetryable = isRetryable;
   }

   @Override
   protected boolean matchFirstRule() {
      final Map<Variable, Variable> sharedVariables = new HashMap<>();
      final Term[] newConsequentArgs = new Term[numArgs];
      for (int i = 0; i < numArgs; i++) {
         newConsequentArgs[i] = firstClauseConsequentArgs[i].copy(sharedVariables);
      }

      if (Unifier.preMatch(currentQueryArgs, newConsequentArgs) == false) {
         return false;
      }

      for (int i = 0; i < firstClauseOriginalTerms.length; i++) {
         Term t = firstClauseOriginalTerms[i].copy(sharedVariables);
         if (!firstClausePredicateFactories[i].getPredicate(t.getArgs()).evaluate(t.getArgs())) {
            return false;
         }
      }

      return true;
   }

   @Override
   protected boolean matchSecondRule() {
      final Map<Variable, Variable> sharedVariables = new HashMap<>();
      final Term[] newConsequentArgs = new Term[numArgs];
      for (int i = 0; i < numArgs; i++) {
         newConsequentArgs[i] = secondClauseConsequentArgs[i].copy(sharedVariables);
      }

      if (Unifier.preMatch(currentQueryArgs, newConsequentArgs) == false) {
         return false;
      }

      for (int i = 0; i < secondClauseOriginalTerms.length - 1; i++) {
         Term t = secondClauseOriginalTerms[i].copy(sharedVariables);
         if (!secondClausePredicateFactories[i].getPredicate(t.getArgs()).evaluate(t.getArgs())) {
            return false;
         }
      }

      Term finalTermArgs[] = secondClauseOriginalTerms[secondClauseOriginalTerms.length - 1].getArgs();
      for (int i = 0; i < numArgs; i++) {
         currentQueryArgs[i] = finalTermArgs[i].copy(sharedVariables);
      }

      return true;
   }

   @Override
   protected void backtrack() {
      for (int i = 0; i < numArgs; i++) {
         currentQueryArgs[i].backtrack();
      }
   }

   @Override
   public boolean couldReEvaluationSucceed() {
      return isRetryable;
   }

   @Override
   public boolean isRetryable() {
      return isRetryable;
   }
}