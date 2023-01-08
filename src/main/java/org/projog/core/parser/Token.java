/*
 * Copyright 2013-2014 S. Webber
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
package org.projog.core.parser;

/** @see TokenParser#next() */
class Token {
   private static final Token[] EMPTY_ARGS = new Token[0];

   private final String value;
   private final TokenType type;
   private final Token[] args;

   Token(String value, TokenType type) {
      this(value, type, EMPTY_ARGS);
   }

   Token(String value, TokenType type, Token[] args) {
      this.value = value;
      this.type = type;
      this.args = args;
   }

   String getName() {
      return value;
   }

   TokenType getType() {
      return type;
   }

   Token getArgument(int i) {
      return args[i];
   }

   void setArgument(int i, Token t) {
      args[i] = t;
   }

   int getNumberOfArguments() {
      return args.length;
   }

   @Override
   public String toString() {
      return value;
   }
}
