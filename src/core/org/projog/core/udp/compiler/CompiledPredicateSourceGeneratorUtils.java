package org.projog.core.udp.compiler;

import org.projog.core.PredicateKey;
import org.projog.core.term.Term;
import org.projog.core.term.TermType;
import org.projog.core.term.Variable;

/**
 * Contains static methods which aid the construction of {@link CompiledPredicate} source code.
 */
final class CompiledPredicateSourceGeneratorUtils {
   /**
    * Private constructor as all methods are static.
    */
   private CompiledPredicateSourceGeneratorUtils() {
      // do nothing
   }

   static String getClassNameMinusPackage(Object o) {
      String className = o.getClass().getName();
      return className.substring(className.lastIndexOf('.') + 1);
   }

   static String encodeName(Term t) {
      return encodeName(t.getName());
   }

   static String encodeName(String s) {
      return "\"" + s.replace("\\", "\\\\") + "\"";
   }

   static String getKeyGeneration(PredicateKey key) {
      return "new PredicateKey(" + encodeName(key.getName()) + ", " + key.getNumArgs() + ")";
   }

   static boolean isNoMoreThanTwoElementList(Term t) {
      if (t.getType() != TermType.LIST) {
         return false;
      }
      Term tail = t.getArgument(1);
      return tail.getType() != TermType.LIST;
   }

   static String getUnifyStatement(String variable1, String variable2) {
      return variable1 + ".unify(" + variable2 + ")";
   }

   static String getNewVariableSyntax(Term variable) {
      return "new Variable(\"" + ((Variable) variable).getId() + "\")";
   }

   static String getNewListSyntax(String head, String tail) {
      return "ListFactory.createList(" + head + ", " + tail + ")";
   }
}