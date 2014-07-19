package org.projog.example;

import static org.projog.core.term.TermUtils.castToNumeric;

import org.projog.core.Calculatable;
import org.projog.core.KnowledgeBase;
import org.projog.core.term.IntegerNumber;
import org.projog.core.term.Numeric;
import org.projog.core.term.Term;

public class CalculatableExample implements Calculatable {
   @Override
   public void setKnowledgeBase(KnowledgeBase kb) {
   }

   @Override
   public Numeric calculate(Term... args) {
      Numeric input = castToNumeric(args[0]);
      long rounded = Math.round(input.getDouble());
      return new IntegerNumber((int) rounded);
   }
}