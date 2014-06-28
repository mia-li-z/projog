% projog-bootstrap.pl
% This file contains Prolog syntax that is interpreted when a projog console is started.
% This file contains code that configures the projog environment with
% "core" built-in predicates (e.g. "true", "consult", etc.) and numerical operations (e.g. "+", "-", etc.).
% It also defines operators in order to provide a more convenient syntax for writing terms.
% This file is included in the projog-core.jar that contains the projog class files.
% This file can be overridden by providing another file named "projog-bootstrap.pl" 
% in the root directory where the console is launched, or in the classpath before the projog-core.jar.
% See http://www.projog.org/javadoc/org/projog/core/KnowledgeBase.html#bootstrap()

'?-'( pj_add_predicate('/'(op, 3), 'org.projog.core.function.io.Op') ).
'?-'( op(1200, fx, '?-') ).
?- op(400, yfx, '/').

% boolean
?- pj_add_predicate(true, 'org.projog.core.function.bool.True').
?- pj_add_predicate(fail, 'org.projog.core.function.bool.Fail').

% classify
?- pj_add_predicate(var/1, 'org.projog.core.function.classify.IsVar').
?- pj_add_predicate(nonvar/1, 'org.projog.core.function.classify.IsNonVar').
?- pj_add_predicate(atom/1, 'org.projog.core.function.classify.IsAtom').
?- pj_add_predicate(number/1, 'org.projog.core.function.classify.IsNumber').
?- pj_add_predicate(atomic/1, 'org.projog.core.function.classify.IsAtomic').
?- pj_add_predicate(integer/1, 'org.projog.core.function.classify.IsInteger').
?- pj_add_predicate(float/1, 'org.projog.core.function.classify.IsFloat').
?- pj_add_predicate(compound/1, 'org.projog.core.function.classify.IsCompound').
?- pj_add_predicate(is_list/1, 'org.projog.core.function.classify.IsList').

% compare
?- pj_add_predicate('='/2, 'org.projog.core.function.compare.Equal').
?- pj_add_predicate('=='/2, 'org.projog.core.function.compare.StrictEquality').
?- pj_add_predicate('=:='/2, 'org.projog.core.function.compare.NumericEquality').
?- pj_add_predicate('=\='/2, 'org.projog.core.function.compare.NumericInequality').
?- pj_add_predicate('<'/2, 'org.projog.core.function.compare.NumericLessThan').
?- pj_add_predicate('=<'/2, 'org.projog.core.function.compare.NumericLessThanOrEqual').
?- pj_add_predicate('>'/2, 'org.projog.core.function.compare.NumericGreaterThan').
?- pj_add_predicate('>='/2, 'org.projog.core.function.compare.NumericGreaterThanOrEqual').
?- pj_add_predicate('@<'/2, 'org.projog.core.function.compare.TermLessThan').
?- pj_add_predicate('@>'/2, 'org.projog.core.function.compare.TermGreaterThan').
?- pj_add_predicate('@>='/2, 'org.projog.core.function.compare.TermGreaterThanOrEqual').
?- pj_add_predicate('@=<'/2, 'org.projog.core.function.compare.TermLessThanOrEqual').
?- pj_add_predicate('\='/2, 'org.projog.core.function.compare.NotUnifiable').
?- pj_add_predicate(compare/3, 'org.projog.core.function.compare.Compare').

% compound
?- pj_add_predicate(','/2, 'org.projog.core.function.compound.Conjunction').
?- pj_add_predicate(';'/2, 'org.projog.core.function.compound.Disjunction').
?- pj_add_predicate('/'('\+', 1), 'org.projog.core.function.compound.Not').
?- pj_add_predicate(not/1, 'org.projog.core.function.compound.Not').
?- pj_add_predicate(call/1, 'org.projog.core.function.compound.Call').
?- pj_add_predicate(once/1, 'org.projog.core.function.compound.Once').
?- pj_add_predicate(bagof/3, 'org.projog.core.function.compound.BagOf').
?- pj_add_predicate(findall/3, 'org.projog.core.function.compound.FindAll').
?- pj_add_predicate(setof/3, 'org.projog.core.function.compound.SetOf').

% construct
?- pj_add_predicate(functor/3, 'org.projog.core.function.construct.Functor').
?- pj_add_predicate(arg/3, 'org.projog.core.function.construct.Arg').
?- pj_add_predicate('=..'/2, 'org.projog.core.function.construct.Univ').
?- pj_add_predicate(atom_chars/2, 'org.projog.core.function.construct.AtomChars').
?- pj_add_predicate(number_chars/2, 'org.projog.core.function.construct.NumberChars').
?- pj_add_predicate(atom_concat/3, 'org.projog.core.function.construct.AtomConcat').

% debug
?- pj_add_predicate(debugging, 'org.projog.core.function.debug.Debugging').
?- pj_add_predicate(nodebug, 'org.projog.core.function.debug.NoDebug').
?- pj_add_predicate(nospy/1, 'org.projog.core.function.debug.NoSpy').
?- pj_add_predicate(notrace, 'org.projog.core.function.debug.NoTrace').
?- pj_add_predicate(spy/1, 'org.projog.core.function.debug.Spy').
?- pj_add_predicate(trace, 'org.projog.core.function.debug.Trace').

% io
?- pj_add_predicate(close/1, 'org.projog.core.function.io.Close').
?- pj_add_predicate(current_input/1, 'org.projog.core.function.io.CurrentInput').
?- pj_add_predicate(current_output/1, 'org.projog.core.function.io.CurrentOutput').
?- pj_add_predicate(get_char/1, 'org.projog.core.function.io.GetChar').
?- pj_add_predicate(nl, 'org.projog.core.function.io.NewLine').
?- pj_add_predicate(open/3, 'org.projog.core.function.io.Open').
?- pj_add_predicate(put_char/1, 'org.projog.core.function.io.PutChar').
?- pj_add_predicate(read/1, 'org.projog.core.function.io.Read').
?- pj_add_predicate(set_input/1, 'org.projog.core.function.io.SetInput').
?- pj_add_predicate(set_output/1, 'org.projog.core.function.io.SetOutput').
?- pj_add_predicate(write/1, 'org.projog.core.function.io.Write').
?- pj_add_predicate(write_canonical/1, 'org.projog.core.function.io.WriteCanonical').

% kb (knowledge base)
?- pj_add_predicate(pj_add_calculatable/2, 'org.projog.core.function.kb.AddCalculatable').
?- pj_add_predicate(asserta/1, 'org.projog.core.function.kb.AssertA').
?- pj_add_predicate(assertz/1, 'org.projog.core.function.kb.AssertZ').
?- pj_add_predicate(clause/2, 'org.projog.core.function.kb.InspectClause').
?- pj_add_predicate(listing/1, 'org.projog.core.function.kb.Listing').
?- pj_add_predicate(retract/1, 'org.projog.core.function.kb.Retract').
?- pj_add_predicate(consult/1, 'org.projog.core.function.kb.Consult').

% math
?- pj_add_predicate(is/2, 'org.projog.core.function.math.Is').

% flow control
?- pj_add_predicate(repeat, 'org.projog.core.function.flow.RepeatInfinitely').
?- pj_add_predicate(repeat/1, 'org.projog.core.function.flow.RepeatSetAmount').
?- pj_add_predicate('!', 'org.projog.core.function.flow.Cut').

% list
?- pj_add_predicate(length/2, 'org.projog.core.function.list.Length').
?- pj_add_predicate(reverse/2, 'org.projog.core.function.list.Reverse').
?- pj_add_predicate(member/2, 'org.projog.core.function.list.Member').
?- pj_add_predicate(memberchk/2, 'org.projog.core.function.list.MemberCheck').
?- pj_add_predicate(append/3, 'org.projog.core.function.list.Append').
?- pj_add_predicate(subtract/3, 'org.projog.core.function.list.SubtractFromList').
?- pj_add_predicate(keysort/2, 'org.projog.core.function.list.KeySort').
?- pj_add_predicate(flatten/2, 'org.projog.core.function.list.Flatten').
?- pj_add_predicate(sort/2, 'org.projog.core.function.list.SortAsSet').
?- pj_add_predicate(msort/2, 'org.projog.core.function.list.Sort').
?- pj_add_predicate(delete/3, 'org.projog.core.function.list.Delete').
?- pj_add_predicate(subset/2, 'org.projog.core.function.list.Subset').

% numerical operations
?- pj_add_predicate(arithmetic_function/1, 'org.projog.core.function.math.AddArithmeticFunction').
?- pj_add_calculatable('+'/2, 'org.projog.core.function.math.Add').
?- pj_add_calculatable('/'('-', 1), 'org.projog.core.function.math.Minus').
?- pj_add_calculatable('/'('-', 2), 'org.projog.core.function.math.Subtract').
?- pj_add_calculatable('/'/2, 'org.projog.core.function.math.Divide').
?- pj_add_calculatable('//'/2, 'org.projog.core.function.math.IntegerDivide').
?- pj_add_calculatable('*'/2, 'org.projog.core.function.math.Multiply').
?- pj_add_calculatable('**'/2, 'org.projog.core.function.math.Power').
?- pj_add_calculatable(mod/2, 'org.projog.core.function.math.Modulo').
?- pj_add_calculatable(rem/2, 'org.projog.core.function.math.Remainder').

% definite clause grammers (DCG)
?- op(1200, xfx, '-->').
?- op(901, fx, '{').
?- op(900, xf, '}').

% operators
?- op(1200, xfx, ':-').
?- op(1200, fx, ':-').
?- op(1100, xfy, ';').
?- op(1000, xfy, ',').
?- op(900, fy, '\+').
?- op(700, xfx, '=').
?- op(700, xfx, '==').
?- op(700, xfx, '=:=').
?- op(700, xfx, '=\=').
?- op(700, xfx, '=..').
?- op(700, xfx, '<').
?- op(700, xfx, '>').
?- op(700, xfx, '=<').
?- op(700, xfx, '>=').
?- op(700, xfx, '@<').
?- op(700, xfx, '@=<').
?- op(700, xfx, '@>').
?- op(700, xfx, '@>=').
?- op(700, xfx, '\=').
?- op(700, xfx, 'is').
?- op(500, yfx, '+').
?- op(500, yfx, '-').
?- op(400, yfx, '*').
?- op(400, yfx, '**').
?- op(400, yfx, '//').
?- op(400, yfx, 'mod').
?- op(400, yfx, 'rem').
?- op(200, fy, '-').
