package org.projog.core.function.compound;

import java.util.HashMap;

import org.projog.core.KnowledgeBase;
import org.projog.core.Predicate;
import org.projog.core.PredicateFactory;
import org.projog.core.function.AbstractRetryablePredicate;
import org.projog.core.term.Term;
import org.projog.core.term.TermUtils;
import org.projog.core.term.Unifier;
import org.projog.core.term.Variable;

/* TEST
 %TRUE true, true
 %FALSE true, fail
 %FALSE fail, true
 %FALSE fail, fail
 
 %TRUE true, true, true
 %FALSE true, fail, fail
 %FALSE fail, true, fail
 %FALSE fail, fail, true
 %FALSE true, true, fail
 %FALSE true, fail, true 
 %FALSE fail, true, true
 %FALSE fail, fail, fail
 
 :- b.
 :- c.
 :- d.
 :- y.
 a :- b,c,d.
 x :- y,z.
 %TRUE a
 %FALSE x

 :- p2(1).
 :- p2(2).
 :- p2(3).

 :- p3(a).
 :- p3(b).
 :- p3(c).

 :- p4(1, b, [a,b,c]).
 :- p4(3, c, [1,2,3]).
 :- p4(X, Y, [q,w,e,r,t,y]).

 p1(X, Y, Z) :- p2(X), p3(Y), p4(X,Y,Z).
 
 %QUERY p1(X, Y, Z)
 %ANSWER
 % X=1
 % Y=a
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=1
 % Y=b
 % Z=[a,b,c]
 %ANSWER
 %ANSWER
 % X=1
 % Y=b
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=1
 % Y=c
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=2
 % Y=a
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=2
 % Y=b
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=2
 % Y=c
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=3
 % Y=a
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=3
 % Y=b
 % Z=[q,w,e,r,t,y]
 %ANSWER
 %ANSWER
 % X=3
 % Y=c
 % Z=[1,2,3]
 %ANSWER
 %ANSWER
 % X=3
 % Y=c
 % Z=[q,w,e,r,t,y]
 %ANSWER
 
 %QUERY p2(X), p2(X), p2(X)
 %ANSWER X=1
 %ANSWER X=2
 %ANSWER X=3

 %FALSE p2(X), p3(X), p2(X)
 */
/**
 * <code>X,Y</code> - conjunction.
 * <p>
 * <code>X,Y</code> specifies a conjunction of goals. <code>X,Y</code> succeeds if <code>X</code> succeeds <i>and</i>
 * <code>Y</code> succeeds. If <code>X</code> succeeds and <code>Y</code> fails then an attempt is made to re-satisfy
 * <code>X</code>. If <code>X</code> fails the entire conjunction fails.
 * </p>
 */
public final class Conjunction extends AbstractRetryablePredicate {
   // TODO test using a junit test rather than just a Prolog script
   // as over complexity in internal workings (e.g. when and what it backtracks)
   // may not be detectable via a system test. 

   private PredicateFactory secondPredicateFactory;
   private Predicate firstPredicate;
   private Predicate secondPredicate;
   private boolean firstGo = true;
   private Term secondArg;
   private Term tmpInputArg2;

   public Conjunction() {
   }

   private Conjunction(KnowledgeBase knowledgeBase) {
      setKnowledgeBase(knowledgeBase);
   }

   @Override
   public Conjunction getPredicate(Term... args) {
      return getPredicate(args[0], args[1]);
   }

   public Conjunction getPredicate(Term arg1, Term arg2) {
      return new Conjunction(getKnowledgeBase());
   }

   @Override
   public boolean evaluate(Term... args) {
      return evaluate(args[0], args[1]);
   }

   public boolean evaluate(Term inputArg1, Term inputArg2) {
      if (firstGo) {
         firstPredicate = getKnowledgeBase().getPredicateFactory(inputArg1).getPredicate(inputArg1.getArgs());

         while ((firstGo || firstPredicate.isRetryable()) && firstPredicate.evaluate(inputArg1.getArgs())) {
            firstGo = false;
            if (preMatch(inputArg2) && secondPredicate.evaluate(secondArg.getArgs())) {
               return true;
            }
            TermUtils.backtrack(tmpInputArg2.getArgs());
         }

         return false;
      }

      do {
         final boolean evaluateSecondPredicate;
         if (secondArg == null) {
            evaluateSecondPredicate = preMatch(inputArg2);
         } else {
            evaluateSecondPredicate = secondPredicate.isRetryable();
         }

         if (evaluateSecondPredicate && secondPredicate.evaluate(secondArg.getArgs())) {
            return true;
         }

         TermUtils.backtrack(tmpInputArg2.getArgs());
         secondArg = null;
      } while (firstPredicate.isRetryable() && firstPredicate.evaluate(inputArg1.getArgs()));

      return false;
   }

   private boolean preMatch(Term inputArg2) {
      tmpInputArg2 = inputArg2.getTerm();
      secondArg = tmpInputArg2.copy(new HashMap<Variable, Variable>());
      if (Unifier.preMatch(tmpInputArg2.getArgs(), secondArg.getArgs())) {
         if (secondPredicateFactory == null) {
            secondPredicateFactory = getKnowledgeBase().getPredicateFactory(secondArg);
         }
         secondPredicate = secondPredicateFactory.getPredicate(secondArg.getArgs());
         return true;
      } else {
         return false;
      }
   }

   @Override
   public boolean couldReEvaluationSucceed() {
      return firstPredicate == null || firstPredicate.couldReEvaluationSucceed() || secondPredicate == null || secondPredicate.couldReEvaluationSucceed();
   }
}