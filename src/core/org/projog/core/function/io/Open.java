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
package org.projog.core.function.io;

import static org.projog.core.term.TermUtils.getAtomName;

import org.projog.core.FileHandles;
import org.projog.core.ProjogException;
import org.projog.core.term.Term;

/* SYSTEM TEST
 % %LINK% prolog-io
 */
/**
 * <code>open(X,Y,Z)</code> - opens a file.
 * <p>
 * <code>X</code> is an atom representing the name of the file to open. <code>Y</code> is an atom that should have
 * either the value <code>read</code> to open the file for reading from or <code>write</code> to open the file for
 * writing to. <code>Z</code> is instantiated by <code>open</code> to a special term that must be referred to in
 * subsequent commands in order to access the stream.
 * </p>
 */
public final class Open extends org.projog.core.function.AbstractSingletonPredicate {
   private static final String READ = "read";
   private static final String WRITE = "write";

   @Override
   public boolean evaluate(Term... args) {
      return evaluate(args[0], args[1], args[2]);
   }

   /**
    * Overloaded version of {@link #evaluate(Term...)} that avoids the overhead of creating a new {@code Term} array.
    * 
    * @see org.projog.core.Predicate#evaluate(Term...)
    */
   public boolean evaluate(Term fileNameAtom, Term operationAtom, Term variableToAssignTo) {
      String operation = getAtomName(operationAtom);
      String fileName = getAtomName(fileNameAtom);
      Term handle;
      if (READ.equals(operation)) {
         handle = openInput(fileName);
      } else if (WRITE.equals(operation)) {
         handle = openOutput(fileName);
      } else {
         throw new ProjogException("Second argument is not '" + READ + "' or '" + WRITE + "' but: " + operation);
      }
      variableToAssignTo.unify(handle);
      return true;
   }

   private Term openInput(String fileName) {
      try {
         FileHandles fh = getKnowledgeBase().getFileHandles();
         return fh.openInput(fileName);
      } catch (Exception e) {
         throw new ProjogException("Unable to open input for: " + fileName, e);
      }
   }

   private Term openOutput(String fileName) {
      try {
         FileHandles fh = getKnowledgeBase().getFileHandles();
         return fh.openOutput(fileName);
      } catch (Exception e) {
         throw new ProjogException("Unable to open output for: " + fileName + " " + e, e);
      }
   }
}