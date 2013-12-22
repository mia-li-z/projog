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
package org.projog.core.function.debug;

import static org.projog.core.KnowledgeBaseUtils.getPredicateKeysByName;

import java.util.List;

import org.projog.core.PredicateKey;
import org.projog.core.ProjogException;
import org.projog.core.SpyPoints;
import org.projog.core.function.AbstractSingletonPredicate;
import org.projog.core.term.Term;

/**
 * Extended by {@code Predicate}s that enable or disable spy points.
 */
abstract class AbstractAlterSpyPointFunction extends AbstractSingletonPredicate {
   private final boolean valueToSetSpyPointTo;

   /**
    * The {@code valueToSetSpyPointTo} parameter specifies whether spy points matched by the {@link #evaluate(Term)}
    * method should be enabled or disabled.
    * 
    * @param valueToSetSpyPointTo {@code true} to enable spy points, {@code false} to disable spy points
    */
   protected AbstractAlterSpyPointFunction(boolean valueToSetSpyPointTo) {
      this.valueToSetSpyPointTo = valueToSetSpyPointTo;
   }

   @Override
   public boolean evaluate(Term... args) {
      return evaluate(args[0]);
   }

   /**
    * Overloaded version of {@link #evaluate(Term...)} that avoids the overhead of creating a new {@code Term} array.
    * 
    * @see org.projog.core.Predicate#evaluate(Term...)
    */
   public boolean evaluate(Term t) {
      switch (t.getType()) {
         case ATOM:
            List<PredicateKey> keys = getPredicateKeysByName(getKnowledgeBase(), t.getName());
            setSpyPoints(keys);
            break;
         case STRUCTURE:
            PredicateKey key = PredicateKey.createFromNameAndArity(t);
            setSpyPoint(key);
            break;
         default:
            throw new ProjogException("Expected an atom or a structure but got a " + t.getType() + " with value: " + t);
      }
      return true;
   }

   private void setSpyPoints(List<PredicateKey> keys) {
      for (PredicateKey key : keys) {
         setSpyPoint(key);
      }
   }

   private void setSpyPoint(PredicateKey key) {
      SpyPoints spyPoints = getKnowledgeBase().getSpyPoints();
      spyPoints.setSpyPoint(key, valueToSetSpyPointTo);
   }
}