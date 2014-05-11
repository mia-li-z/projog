package org.projog.core.function.compare;

import org.projog.core.function.AbstractSingletonPredicate;
import org.projog.core.term.Term;

/* SYSTEM TEST
 % %TRUE% a=a
 % %FALSE% a=b
 % %QUERY% a=X
 % %ANSWER% X=a
 % %FALSE% 2=1+1
 % %FALSE% p(b,c)=p(b,d)
 % %FALSE% p(b,c)=p(c,b)
 % %QUERY% p(b,c)=p(b,X)
 % %ANSWER% X=c
 % %QUERY% p(Y,c)=p(b,X)
 % %ANSWER% 
 % Y=b 
 % X=c
 % %ANSWER%
 % %TRUE% [a,b,c]=[a,b,c]
 % %FALSE% [a,b,c]=[a,b,d]
 */
/**
 * <code>X=Y</code> - an equality test.
 * <p>
 * If <code>X</code> can be matched with <code>Y</code> the goal succeeds else the goal fails. A <code>X=Y</code> goal
 * will consider an uninstantiated variable to be equal to anything. A <code>X=Y</code> goal will always succeed if
 * either argument is uninstantiated.
 * </p>
 */
public final class Equal extends AbstractSingletonPredicate {
   @Override
   public boolean evaluate(Term... args) {
      return evaluate(args[0], args[1]);
   }

   /**
    * Overloaded version of {@link #evaluate(Term...)} that avoids the overhead of creating a new {@code Term} array.
    * 
    * @see org.projog.core.Predicate#evaluate(Term...)
    */
   public boolean evaluate(Term arg1, Term arg2) {
      return arg1.unify(arg2);
   }
}