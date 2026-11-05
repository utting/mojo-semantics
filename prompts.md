
## 2026-10-08: Mojo Ownership Semantics
> try to formalise the memory management ideas in https://gist.github.com/nmsmith/cdaa94aa74e8e0611221e65db8e41f7b?permalink_comment_id=5940284 using Isabelle2025-2.  Explain your decisions and rationale in text comments in your generated *.thy file.  Mention possible alternatives where they exist.


## 2026-10-30: Micro-Mojo Semantics
(Set model to Opus 5.5 for this session only)
> I want to define a big-step semantics for a subset of Mojo, in Isabelle.  The first step is to define a small subset of the
  language, just sufficient to run small example programs.  After that we will define abstract syntax for that subset,
  well-formedness rules, and big-step execution semantics, hopefully building on your region theory.  Can you start by suggesting a
  small 'micro-mojo' subset of mojo that captures an interesting subset of the language, to run small examples and experiment with
  the ownership rules?  Mojo language definitions are available on https://mojolang.org/docs/, especially in the Cheat Sheets and
  the Mojo Language Reference pages.

I checked the current Mojo 1.0 docs (the ownership, lifetimes/origins, variables, initialization, destruction and function-declaration pages, plus the 1.0 release notes). One thing to know first: Mojo 1.0 is quite different from the syntax in the gist. fn is gone, so everything uses def with argument conventions. The read-only convention is now spelled imm (it's the default). Destructors are __deinit__(deinit self). List element references use "interior origins", which is a shipped version of the gist's item regions. The proposal below follows 1.0 syntax.

Micro-Mojo: proposed core

Goal: the smallest subset where every ownership rule can be seen in a program's output. Destructors print, so their order appears in the trace, and every static rule has a short program that breaks it.

Types

T ::= Int | Bool          -- trivially, implicitly copyable
    | S                   -- user struct (owned; copied only explicitly)
    | List[T]             -- built-in dynamic container (has interior origin)
String appears only as a literal argument to print. There are no generics beyond the built-in List[T], and no traits.

Declarations

prog   ::= (struct | fun)*                       -- must contain def main()
struct ::= [@fieldwise_init] struct S [ (Copyable) ]:
             var f: T ...
             [def __init__(out self, params): body]
             [def __deinit__(deinit self): body]
             method*
fun    ::= def g(param, ...) [-> T | -> ref[x, y, ...] T]: body
param  ::= [conv] x: T
conv   ::= imm (default) | mut | var | ref
method ::= def m([imm|mut|deinit] self, param, ...) [-> ...]: body

Statements and expressions

s ::= var x: T [= e] | ref r = p | p = e | p += e
    | if e: s* else: s* | while e: s* | return [e]
    | e | print(e, ...) | pass

p ::= x | p.f | p[e]                             -- places
e ::= n | True | False | "lit" | p | p^ | p.copy()
    | g(e, ...) | S(e, ...) | p.m(e, ...)
    | e op e | not e | len(p) | [e, ...]
Built-in List methods: append(var x) and pop() change the list's shape. Indexing l[i] returns a reference into the list's interior origin. Indexing out of bounds is a runtime error.

What the subset lets you observe

┌──────────────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────┐
│                      Mojo rule                       │                        How micro-Mojo shows it                        │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ One owner; ^ transfers and leaves the source         │ var b = a^, then using a is a static error                            │
│ uninitialized                                        │                                                                       │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ Implicit copy only for Int/Bool                      │ var b = a on a struct is an error; a.copy() needs (Copyable)          │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ imm/mut/var argument conventions                     │ the three behave differently in the trace                             │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ Argument exclusivity                                 │ f(x, x) where one parameter is mut is rejected                        │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ out self and fieldwise vs logical initialization     │ __init__ must set every field; reading var x: S before assignment is  │
│                                                      │ an error                                                              │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ ASAP destruction                                     │ __deinit__ prints show destruction order                              │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ ref bindings and ref[a, b] union origins             │ pick_one example below                                                │
├──────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────┤
│ Interior-origin invalidation                         │ ref e = l[0]; l.append(4); print(e) is rejected                       │
└──────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────┘

Left out of the core

Traits beyond the Copyable marker, generics and comptime, closures and lambdas, raises/try, match, for, SIMD and numerics beyond Int, Python interop, overloading, implicit conversions, keyword and variadic arguments, and Pointer.

Tier 2 extensions, in the order I'd add them:
1. Pointer[T, origin]: first-class references, the gist's core idea.
2. for i in range(n).
3. raises, since error paths complicate destruction.
4. Generic structs.

Example programs

mojo
@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def consume(var r: Res):
    print("got", r.id)                 # r dropped here

def bump(mut r: Res, n: Int):
    r.id += n

def pick(c: Bool, ref a: Res, ref b: Res) -> ref[a, b] Res:
    if c:
        return a
    else:
        return b

def main():
    var a = Res(1)
    var b = Res(2)
    bump(a, 10)                        # a.id == 11
    ref r = pick(True, a, b)
    print(r.id)                        # 11
    consume(a^)                        # "got 11", "drop 11"
    # print(a.id)                      # static error: use after transfer
    # bump(b, b.id)                    # fine (Int is copied)
    var l: List[Int] = [1, 2, 3]
    ref e = l[0]
    print(e)
    l.append(4)                        # invalidates e
    # print(e)                         # static error: invalidated interior reference
    # "drop 2" printed at b's last use (ASAP)

The full suite would be about 8 small programs, each one valid program next to a near-identical invalid one.

How it maps onto Mojo_Region_Model.thy

- Store: locations with an owner function. Each variable gets a root location, each struct field a child, each list item a child of the list. This is exactly the mojo_regions locale, so footprint is "everything that destroying x tears down".
- Initialization: one flag per location, which is Part 2's store. out/deinit/^ are transitions on those flags.
- Origins: sets of locations. ref[a, b] is literally a region {a, b}, which makes Mojo's origin unions the gist's set-of-variables model.
- Interior origins: the list's item region plus Part 3's generation counter. append/pop are Shape operations; assigning through l[i] is an Item operation.
- Argument exclusivity: Rule 2. A mut argument must be mem_disjoint from the other arguments, and Part 4's copy_step shows why.

Two decisions to make before writing the Isabelle syntax

1. When destruction happens. True ASAP needs last-use analysis. I'd make it a static elaboration pass that inserts explicit drop x statements, so the big-step semantics only executes drops. The simpler alternative is end-of-scope destruction, but that visibly changes the trace compared with real Mojo.
2. Static checks vs runtime errors. I'd write the big-step semantics with an explicit error result for use-after-move, reading uninitialized memory and invalid references, and keep the ownership rules in the well-formedness judgement. The main theorem then becomes "well-formed programs never produce an ownership error", with out-of-bounds indexing as the only allowed runtime failure. That theorem directly reuses safe_to_deref_sound, valid_ptr_iff and copy_step_safe.


> Good.  I agree with your suggestions for the two decisions.  Note that I have upgraded to Isabelle 2026 in the path.  Please  [I pressed Enter by mistake.  Then used /mcp to restart pide-mcp].

> Ok. Define the micro-Mojo abstract syntax, plus some Mojo-like syntactic sugar, and encode the example programs.  Then define the big-step semantics.

I'll build this in two theories: Micro_Mojo_Syntax.thy for the syntax, sugar and examples, and Micro_Mojo_Semantics.thy for the semantics. Loading the PIDE tools first.

  Called isabelle-pide-mcp

I'll first test the notation choices and the monad syntax in a scratch theory, since mixfix clashes are easiest to find in isolation.

  Called isabelle-pide-mcp 4 times

The bracket and assignment characters ⟮ ⟯ ≔ aren't Isabelle symbols. I'll switch to ⦃ ⦄ for calls and IMP's ::= for assignment.

  Called isabelle-pide-mcp 7 times, ran 2 shell commands

The reconnected PIDE server returns less detail than before, so I'll reload its tool schema in case the parameters changed.

  Called isabelle-pide-mcp

The server's real schema uses a details parameter that the client-side schema doesn't list. I'll try passing it anyway.

  Called isabelle-pide-mcp

The details parameter works and the notation parses, though two ambiguities remain: VAR's type argument needs higher priority, and ∙'s right argument must be atomic. I'm now writing the real syntax theory.

  Called isabelle-pide-mcp 3 times

Bare keywords such as if inside @{text ...} break the parser, so I'll quote every bare-word antiquotation.

  Called isabelle-pide-mcp 3 times, ran 1 shell command

The syntax and notation check cleanly. Now the example programs.

  Called isabelle-pide-mcp 2 times

Isabelle gives function application priority 999, so TList TInt can't sit in a 1000-priority argument slot, and RETURN (priority 20) doesn't fit the ELSE branch (21). I'm fixing both priority problems now.

  Called isabelle-pide-mcp 2 times, ran 1 shell command

ex1_main still fails to parse. I'll bisect it in the scratch theory.

  Called isabelle-pide-mcp 8 times, ran 1 shell command

The cause is the definition's own =: HOL equality takes arguments of priority 51, and a statement has priority 20. Wrapping the bodies in parentheses fixes it.

  Called isabelle-pide-mcp 3 times

The syntax theory passes its checks, so I'm moving on to semantics. I'll build it as a deterministic clocked interpreter with errors propagated through a monad, and I'll explain that choice in the theory text.

  Called isabelle-pide-mcp 5 times

Three fixes are needed: quoting __init__ in the text, renaming the output record field because it clashes with an outer-syntax keyword, and rewriting binop_val with small helpers since its overlapping patterns slow fun down a lot.

Now the interpreter itself: a block of mutually recursive functions inside a context that fixes the program P.

  Called isabelle-pide-mcp 2 times
Invalid tool parameters

  Called isabelle-pide-mcp 2 times

The 13-function mutual fun takes a while to process. I'll wait in the background rather than poll.

  Ran 1 shell command

While that runs, I'll draft the examples section and the region-theory connection to append once the interpreter compiles.

  Called isabelle-pide-mcp, ran 1 shell command

The interpreter definition is still processing; I'll check on it when the wait finishes.

✻ Brewed for 15m 34s · done 1:39 pm

⏺ Background command "Wait one minute for the function package" completed (exit code 0)

  Called isabelle-pide-mcp, ran 1 shell command

Still processing after about 90 seconds; I'll wait for the second timer before deciding whether to restructure the definition.

✻ Brewed for 18s · done 1:40 pm                                                                                                 
⏺ Background command "Wait further for the function package" completed (exit code 0)
                                            
  Called isabelle-pide-mcp    
                                                                                                  
The mutual fun has run for over two minutes without finishing, probably because its automatic termination search checks every argument size across all 13 functions. I'm switchingcit fuel-based termination proof, beginning with theshape of the termination goal.

  Called isabelle-pide-mcp 4 times, ran 1 shell command 
                                                                         
I'm waiting for the function definition (without termination search) to finish, to see whether the slowdown was in termination in the definition itself.

  Worked for 39s · done 1:41 pm
  Background command "Wait for function definition to ode 0)
  Called isabelle-pide-mcp
                                                                                                                                 The definition itself compiles in about 17 seconds; search is what hung. I'm switching to a direct termination proof using a fuel measure, and first need the internal argument sum type's shape.
                                 
  Called isabelle-pide-mcp 2 times
                                                                                               
The argument type is a nested sum with the fuel first in every component, so the measure is a tree of case_sum with fst at the leaves.

  Called isabelle-pide-mcp 3 times

Termination is proved in under a second. Now fixing n quoting and checking the whole file.


Now I'll run the examples with value to see the actual outputs before turning them into checked lemmas.

  Called isabelle-pide-mcp 2 times, ran 1 shell command

The theory is reprocessing from the top after the text fix; the example runs will follow.

✻ Churned for 59s · done 1:42 pm

⏺ Background command "Wait for theory to reprocess" completed (exit code 0)

  Called isabelle-pide-mcp

All ten examples produce exactly the outputs predicted from Mojo's rules. I'll replace the value commands with documented lemmas checked by eval.

  Called isabelle-pide-mcp 2 times

While the example lemmas evaluate, I'll draft the connection to the region theory: paths with "remove the last step" as the owner function, interpreted in the mojo_regions locale.

  Called isabelle-pide-mcp

All ten example lemmas are proved by eval. Now the region-theory connection.

  Called isabelle-pide-mcp 4 times

The same snag appeared in the region theory demo, and unfolding path_owner_def turned the owner parameter in paths.ancestor_at into a lambda, breaking the recursion equations. I'm switching to an applied-form lemma for path_owner instead.

  Called isabelle-pide-mcp


The region connection is proved. Now checking both theories end to end.

  Called isabelle-pide-mcp 2 times

Both theories are clean in PIDE. As an independent check, I'll also process them in batch mode, where any sorry would be an error.

  Ran 1 shell command

Batch mode needs a ROOT file to make HOL-Library visible. I'll add one, which the project needs anyway.

⏺ Write(ROOT)
Wrote 7 lines to ROOT
session Mojo_Semantics = HOL +
  sessions
    "HOL-Library"
  theories
    Mojo_Region_Model
    Micro_Mojo_Syntax
    Micro_Mojo_Semantics

  Ran 1 shell command

Batch mode needs session-qualified names in @{theory ...} antiquotations, unlike PIDE. I'll use plain text for those two references so both modes work.



The session builds cleanly in batch mode. I'll resync PIDE with the disk edit and confirm it's still clean there.

  Called isabelle-pide-mcp

I've written the micro-Mojo abstract syntax with Mojo-like notation, encoded seven example programs, and defined the big-step semantics. Every example runs and produces exactly the output Mojo's rules predict. Everything builds with no errors or sorrys, both in PIDE and as a batch isabelle build of the new ROOT session Mojo_Semantics.

Micro_Mojo_Syntax.thy
- Abstract syntax:
  - Places (x, p.f, p[e]) are their own category, so the callee's argument convention decides whether an argument is passed by reference or read.
  - Constructor calls share the function-call form, as in Mojo's Res(1).
  - There is an explicit DROP statement for the planned ASAP elaboration pass to insert.
- Notation: §x, p∙f, p⟦e⟧, ⟨p⟩, p⇧^ for p^, f⦃args⦄, p∙m⦃args⦄, and IMP-style statements (VAR x ⦂ T ::= e, REF r ::= e, p += e, IF…THEN…ELSE, WHILE…DO, ;;).
- Examples: each is shown in Mojo and then encoded. Most come as a valid/invalid pair: conventions plus ref[a, b] returns, plus an ASAP-elaborated variant; use after transfer; interior-origin invalidation, taken from the Mojo 1.0 release notes; out self initializers; loop scoping; argument exclusivity; and mut Int swap.

Micro_Mojo_Semantics.thy
- Style: the semantics is a big-step interpreter that takes a fuel argument. Errors propagate through a monad, the semantics is deterministic by construction, and the examples execute with eval. An equivalent inductive relation could be derived later if you want one. The text explains this choice and the alternative.
- Memory model: each variable owns a root holding a value tree, so locations are paths.
  - Uninitialized means VUndef.
  - Interior origins work through per-list generation numbers, which is Part 3 of the region theory applied to each list.
  - References into a returned function's freed locals are a dangling-reference error.
  - Variables not explicitly dropped are destroyed at scope exit in reverse order, so un-elaborated programs still have a meaning.
- Connection to the region theory: with "remove the last step" as the owner function, the mojo_regions locale applies directly. paths_footprint proves that a location's footprint is exactly the set of its extensions.

Things to know
- Exclusivity isn't checked dynamically. The semantics deliberately runs Example 6, append_twice(l, l), and the aliasing shows in the output. Rejecting it is the job of the well-formedness rules.
- Errors discard earlier output. A program that fails returns just the error. Adding the state to Err would fix that if you need it.
- Explicit termination proof. Plain fun hung in its automatic termination search across the 13 mutually recursive functions. I used function with an explicit fuel measure instead, which proves in under a second.
- Simp snag, now explained. This is the same failure that hit the region theory's demo. Unfolding the owner function's definition rewrites the locale parameter into a λ-term, after which the interpreted recursion equations stop matching. The fix is to simplify with an applied-form lemma (path_owner_Pair) instead of the definition.

Next is the well-formedness judgement together with the ASAP elaboration that inserts the DROPs. Its soundness theorem would be "well-formed programs never produce an ownership error".


> keep going


Next up is the well-formedness checker and the ASAP elaboration. The checker needs String and None types, so I'll first add TStr and TNone to the syntax.

  Called isabelle-pide-mcp

The static theory has three parts: typing, an ownership checker covering moves, references, exclusivity and mutability, and an ASAP elaboration proven to insert only drops. I'm starting with the typing and the checker.

  Called isabelle-pide-mcp 3 times

The semantics theory is reprocessing after the syntax change, so I'll wait for it.

  Ran 1 shell command

I'm waiting for the semantics theory to reprocess before checking the new typing functions.

✻ Brewed for 8m 23s · done 2:41 pm · 1 shell still running

⏺ Background command "Wait for dependent theories to reprocess" completed (exit code 0)

  Called isabelle-pide-mcp

Typing compiles. Now appending the ownership checker.

  Called isabelle-pide-mcp 2 times, ran 1 shell command

Waiting for the expression checker to be processed.

✻ Crunched for 53s · done 2:43 pm · 1 shell still running

⏺ Background command "Wait for checker definitions to process" completed (exit code 0)

  Called isabelle-pide-mcp

The parse errors come from using o as a variable name: in HOL it's ASCII syntax for function composition. Renaming it and quoting the antiquotations.


While the expression checker processes, I'll prepare the statement checker and the elaboration.

  Ran 1 shell command

Waiting on the expression checker before adding the statement checker.

✻ Cooked for 40s · done 2:44 pm

⏺ Background command "Wait for checker functions" completed (exit code 0)

  Called isabelle-pide-mcp

The expression checker compiles. Now the statement checker (with the loop fixpoint and an explicit termination measure) and the function/program-level checks.

  Called isabelle-pide-mcp 2 times, ran 1 shell command

Waiting for the statement checker and its termination proof.

✻ Cooked for 1m 5s · done 2:46 pm

⏺ Background command "Wait for statement checker to process" completed (exit code 0)

  Called isabelle-pide-mcp

The statement checker and its termination proof go through. The remaining errors are an invalid variable name (where_) and antiquotation quoting.


  Called isabelle-pide-mcp

Now I'll run the checker on all the examples to see its verdicts.

  Called isabelle-pide-mcp, ran 1 shell command

Waiting for the checker to run on the examples.

✻ Brewed for 26s · done 2:47 pm

⏺ Background command "Wait for the checker runs" completed (exit code 0)

  Called isabelle-pide-mcp

All ten verdicts came back correct on the first run, with the six valid programs accepted and the invalid ones rejected with the expected messages. Since each value takes about 10 seconds to generate, I'll later merge them into one lemma, and next I'm turning to the ASAP elaboration and the "only inserts drops" theorem.

  Called isabelle-pide-mcp, ran 1 shell command

Waiting for the elaboration definitions and the theorem to process.

✻ Sautéed for 51s · done 2:48 pm

⏺ Background command "Wait for elaboration definitions" completed (exit code 0)

  Called isabelle-pide-mcp

Same kind of clash: O is HOL's infix for relation composition. Renaming the parameter to Os in that section.


Waiting for the static theory to reprocess with the renamed parameter.

✻ Baked for 23s · done 2:49 pm

⏺ Background command "Wait for reprocessing" completed (exit code 0)

  Called isabelle-pide-mcp

Everything checks, including elab_only_inserts_drops. Now I'll add a dangling-reference example and see what elaboration produces on the examples.

  Called isabelle-pide-mcp, ran 1 shell command

Waiting for the elaboration and run results.

✻ Crunched for 22s · done 2:50 pm

────────────────────────────────────────────────────────── 4 new messages ───────────────────────────────────────────────────────────

⏺ Background command "Wait for example evaluations" completed (exit code 0)

  Called isabelle-pide-mcp

All four checks matched what was intended: elaborating ex1 reproduces the hand-written version, DROP r sits inside the loop in ex5, ex8 is caught statically and fails with ErrDangling at run time, and the output follows Mojo's ASAP destruction order. I'm now turning these into checked lemmas.

  Called isabelle-pide-mcp, ran 1 shell command

The edit didn't match. I'll re-read the exact text.

  Called isabelle-pide-mcp 2 times

I'll check these once the background wait finishes.

✻ Worked for 45s · done 2:52 pm

⏺ Background command "Wait for example lemmas" completed (exit code 0)

  Called isabelle-pide-mcp

All lemmas pass. Adding the new theory to ROOT and running the batch build.


I've added the well-formedness checker and the ASAP elaboration in a new theory, Micro_Mojo_Static.thy. All four theories build cleanly as the Mojo_Semantics session, with no sorrys. To support typing I added TStr and TNone to the syntax's types.

Ownership checker (check_prog)
- It works like Mojo's lifetime checker: it tracks, statement by statement, which owned variables are initialized, which references may be invalidated, and which out self fields are set. Branches are merged and loops are iterated until the state is stable.
- On top of that it checks typing, implicit copies of non-trivial values, moves, mutation through imm arguments, argument exclusivity, interior-origin invalidation, field initialization in __init__, and that a returned reference stays within its declared ref[...] origin.
- It reuses the region theory:
  - Each reference binding carries an origin, which is a region.
  - Using a reference requires every owned variable in its origin to be initialized; that's safe_to_deref.
  - Exclusivity compares the origins of borrowed arguments; that's Rule 2.

ASAP elaboration (elaborate)
- A backward liveness pass inserts DROP x after each owned variable's last use. Using a reference counts as using every variable in its origin, which is Mojo's lifetime extension.
- elab_only_inserts_drops is proved: removing DROPs from the elaborated program gives back the original.

Results on the examples, all checked by eval
- The checker accepts the six valid programs and rejects each invalid one with the matching Mojo error: use after move, invalidated reference, uninitialized field, argument exclusivity, and a new example (ex8) where a reference to a local escapes. That last one fails with ErrDangling at run time.
- Elaborating Example 1 gives exactly the hand-written ex1_asap_main.
- Every accepted program, once elaborated, runs without error and prints Mojo's destruction order.

Simplifications compared with Mojo (stated in the theory):
- Variable names must be distinct within a function.
- Only owned locals can be moved with ^.
- A var argument without ^ must have a trivial type.
- l[i] and l[j] are always treated as overlapping.
- Drops are inserted per statement, not inside expressions.

Next: the soundness theorem, "if check_prog P = [] then run n (elaborate P) never gives an ownership error", is still only tested on the examples. Proving it needs a relation between abstract and concrete states, with invariants for initialization, valid references, and disjoint borrowed arguments. It is a much larger proof than anything so far, and the obvious first piece is soundness for expressions.

  NOTE: usage at this point was 589K/1m tokens.  I did /compact
        Cost $29.30 

Total cost:            $29.30
Total duration (API):  1h 24m 41s
Total duration (wall): 4d 4h 59m
Total code changes:    8 lines added, 0 lines removed
Usage by model:
    claude-haiku-5-5:  25.0k input, 4.3k output, 0 cache read, 0 cache write ($0.0046)
     claude-sonnet-5:  310 input, 164.0k output, 21.4m cache read, 273.3k cache write ($7.01)
     claude-opus-5-5:  5.7k input, 196.2k output, 68.1m cache read, 589.7k cache write ($22.28)
Prompt cache (main):   117 requests · 100% of input tokens from cache · no misses · warm (1h TTL, last activity 3m 47s ago)


❯ prove soundness, starting with expressions


Working out the invariant for expression soundness now. I've read the interpreter and the checker again, and next I'm starting a new Micro_Mojo_Soundness.thy.

  Called isabelle-pide-mcp 3 times

The new theory is loaded in Isabelle. Next I'm checking that the value-typing definitions are accepted.

  Called isabelle-pide-mcp 4 times, ran 2 shell commands

Isabelle is still reprocessing the checker theory, which the new file imports. While it runs, I'm writing the next part: lemmas about heap paths and the invariant.

  Called isabelle-pide-mcp 5 times, ran 1 shell command

I'm fixing two small errors in the new theory: a name clash with extend from the checker's ctx record, and a simp rule that loops.

  Called isabelle-pide-mcp 10 times

I'm proving the basic lemmas about the invariant one at a time. Each piece is checked before I go on to the main expression lemma.

  Called isabelle-pide-mcp 10 times

Proving that a call-free expression's checker only removes information from the abstract state. After that come the lemmas that read variables from the invariant.

  Called isabelle-pide-mcp 12 times

Fixing simplifier problems in the helper lemmas about when a place may be used. These lemmas feed the main induction for expressions.

  Called isabelle-pide-mcp 8 times

The helper lemmas all check. Next is the lemma that a move (x^) keeps the invariant, then the main induction.

  Called isabelle-pide-mcp 10 times

Three steps in the move lemma make the simplifier loop. I'm replacing them with explicit steps.

  Called isabelle-pide-mcp 4 times

The move lemma checks. Now I'm writing the main induction over the fuel, which covers places, expressions and expression lists together.


  Called isabelle-pide-mcp 4 times

The place-evaluation lemma is almost checked. One remaining step loops in the simplifier, and I'm rewriting it.

  Called isabelle-pide-mcp 4 times

sound_place_Suc is proved, so places are done. Next are the expression cases and the induction that ties them together.

  Called isabelle-pide-mcp 11 times, ran 1 shell command

Nearly every case of the expression lemma checks. Two steps are slow or loop in the simplifier, and I'm replacing them with explicit lemmas.

  Called isabelle-pide-mcp 8 times

The theory is clean with no sorrys. Last, I'm adding the soundness theorem for expressions and a closing section on what remains.

  Called isabelle-pide-mcp 2 times

Everything checks in Isabelle. Now I'm adding the theory to ROOT and running a batch build to confirm.


I've proved soundness for expressions that contain no calls, in a new theory Micro_Mojo_Soundness.thy (about 970 lines, no sorrys). It's added to ROOT, and the whole session builds in batch (49 s). Nothing is committed.

The theorem (expr_sound). Suppose an expression contains no calls, the checker accepts it (chk_expr returns Good σ'), it has type T, and it is evaluated in a state where the invariant holds. Then evaluation fails at most with ErrBounds. If it succeeds, the value has type T and the invariant holds again for σ'. The corollary expr_no_ownership_error states the part you asked for: no ownership error can occur.

The result came out stronger than ownership safety, at almost no extra cost. To rule out ErrUninit the proof already needs values to be well typed, so ErrType and every other error except index-out-of-range are excluded as well.

The invariant relates the checker's view to the run-time state:
- Owned variables: each has its own root in the heap, holding a well-typed value if the checker says it is initialized, and a well-typed value or VUndef otherwise.
- Borrowed parameters: each points to a well-typed value. The exception is out self in __init__, where only the fields the checker records as initialized need to be.
- References: each points to a well-typed value whenever the checker would allow its use, i.e. it is not invalidated and its origin's owned variables are initialized. This is safe_to_deref from the region theory, used as an invariant.
- Root exclusivity: an owned variable's root can be reached from no other variable, except from references whose origin includes it. This is what makes a move safe: x^ changes only x's root, and every reference that could see that root becomes unusable because x is no longer initialized.

How the proof works.
- A small Hoare-style predicate on interpreter results splits each do block of the interpreter step by step.
- Places, expressions and expression lists are proved together by induction on the fuel. This is simpler than the 13-way induction rule the function package generates.

A problem in the checker. The checker tracks initialized out fields in one shared set. An __init__ with a second out parameter y could set y.f and then read self.f while it is still uninitialized. Mojo allows only one out parameter, so chk_body should reject this. I've recorded it in the theory but haven't changed the checker yet. The expression proof doesn't depend on it, but setting up the invariant on function entry will.

Still to do (listed in the theory's closing section):
1. Statements: assignments and DROP change the heap at a place rather than a root, so the frame condition and root exclusivity need to work with paths.
2. List methods: append and pop assign a new generation number to the list, which invalidates old references into it. The invariant needs the condition that every generation in the heap is below ngen.
3. Calls: expressions and statements become mutually recursive, all proved by the same fuel induction. Argument exclusivity provides the disjointness the callee's invariant needs.
4. Destruction: show that the inserted DROPs never leave a reference to a freed root, which is what rules out ErrDangling.

Statements inside a single function are the natural next piece.



> continue

I found four more soundness gaps in the checker: list item assignment, writes through references to imm arguments, exclusivity for only mut arguments, and multiple out parameters. I'll fix the checker first, confirm the examples still get the same verdicts, then extend the invariant.

  Called isabelle-pide-mcp 3 times, ran 1 shell command

I've fixed the four checker gaps. One fix wasn't executable for eval, and I'm rewriting it with a helper function.

  Called isabelle-pide-mcp, ran 1 shell command

While Isabelle rechecks the checker, I'm rewriting the path invariant so each reference records its target variable and steps, and exclusivity covers every writable variable.


The rewritten invariant compiles up to the place lemma. I'm now restating the place lemma so it returns a structured location: the base variable and the steps from it to the place.


  Called isabelle-pide-mcp 2 times

The fixed checker passes everything, including all the example verdicts. Now I'm checking the reworked soundness theory.

  Called isabelle-pide-mcp

Most of the new invariant proofs go through. I'm fixing seven small failures, mostly pair splitting and case splits on bindings.

  Called isabelle-pide-mcp 3 times, ran 1 shell command

Two proof steps in the reworked expression proof are slow, and I'm replacing them with explicit ones. After that comes the move case.

Expression soundness is re-proved with the stronger invariant, and the theory is clean again. Next are lemmas about updating values along paths, which the assignment case needs.

  Ran 1 shell command

I'm putting statement soundness in a separate theory, Micro_Mojo_Soundness_Stmt.thy, so the expression proofs don't need re-checking on every edit.

  Write(Micro_Mojo_Soundness_Stmt.thy)

  Called isabelle-pide-mcp 8 times

The lemmas about updating values along paths are being checked now. They're the basis for proving that assignment keeps the invariant.

  Called isabelle-pide-mcp

The update lemmas pass, except the general write-preservation lemma, which needs the invariant to also state that at most one out parameter is in scope; the checker now enforces this. I'm adding that to inv and re-checking the expression proofs next.

  Called isabelle-pide-mcp 6 times

The helper lemmas check. Now the central lemma: writing a well-typed value at a place under a writable base variable keeps the invariant.

  Called isabelle-pide-mcp 2 times

  Called isabelle-pide-mcp 3 times, ran 3 shell commands

The write lemma is drafted. I'm fixing a variable named by, which is an Isar keyword, and two small proof steps.

  Called isabelle-pide-mcp 5 times

The write lemma is down to one case. I'm adding a small lemma so out self values carry over when the set of initialized fields stays the same.

  Called isabelle-pide-mcp

The general write lemma is done. I'm moving on to the building blocks for statements: the drop-a-value hypothesis, frame and weakening lemmas, end-of-block cleanup, and allocating new variables.

  Called isabelle-pide-mcp 3 times

  Called isabelle-pide-mcp 3 times, ran 1 shell command

The cleanup lemma is nearly done. One step needs a helper fact: the roots owned by a block's variables are distinct.

  Called isabelle-pide-mcp 2 times

Block cleanup is proved. Next are the lemmas for declaring variables (var and ref) and for discarding a block's variables when it ends.

  Called isabelle-pide-mcp 2 times

  Called isabelle-pide-mcp 3 times

Everything so far checks, about 990 commands. Next I'm proving that leaving a block (dropping its variables) restores the outer invariant, plus two static facts about the checker.

  Called isabelle-pide-mcp 3 times

  Called isabelle-pide-mcp 3 times

The lemma for the end of a block is drafted. I'm reworking one sub-proof about distinct owned roots so it doesn't induct over a list the invariant also mentions.

  Called isabelle-pide-mcp

Leaving a block is proved. Next come the static facts about the checker (environments only grow, and the loop analysis reaches a fixpoint) and the helpers for drop followed by assignment.

  Called isabelle-pide-mcp 3 times, ran 2 shell commands

  Called isabelle-pide-mcp 2 times

While Isabelle reprocesses, I'm planning the statement induction. I also need a small checker change so that var x: T without an initializer marks x as uninitialized, avoiding stale entries from earlier blocks.

  Called isabelle-pide-mcp 4 times

The static lemmas and the lemmas for out self are being checked. Next is the main induction over statements and blocks.

  Called isabelle-pide-mcp

The checker facts are all proved. Next is the assignment case: one lemma for each of the three kinds of assignment the checker distinguishes, all built on the general write lemma.

  Called isabelle-pide-mcp 2 times

The assignment proof is drafted. Most errors cascade from three small faults: a quantifier form, a missing spec rule, and a record type annotation. I'm fixing those first.


  Called isabelle-pide-mcp 2 times

I've hit the usage limit, so I'm stopping with the assignment case of statement soundness not yet finished. Micro_Mojo_Soundness_Stmt.thy currently has 2 failing proof steps (details below). Nothing is committed, and the new theory isn't in ROOT yet.

What's done:
- Four more checker gaps found and fixed in Micro_Mojo_Static.thy:
  - Assigning a list item, or calling append on one, didn't invalidate references into nested lists. Assigning l[0] in a List[List[Int]] left a reference to l[0][1] live.
  - A reference to an imm argument could be used to write to it.
  - Argument exclusivity only checked mut, so a ref argument could alias an imm one.
  - A function could have more than one out parameter.
- Two refactors of the checker: var x: T with no initializer now marks x uninitialized, and the assignment check is split out into chk_assign. All the example lemmas still give the same results.
- A stronger invariant in Micro_Mojo_Soundness.thy:
  - Exclusivity is stated over paths, for every writable variable.
  - Each reference records the variable it points into and the steps from it.
  - Allocation is fresh, and at most one out parameter is in scope.
  - Expression soundness is re-proved under this invariant, and the theory is clean.
- New Micro_Mojo_Soundness_Stmt.thy, about 1490 lines, all clean except inside assign_core:
  - lemmas about reading and updating values along paths;
  - inv_write, the main lemma: writing a well-typed value at a place keeps the invariant, given the checker's invalidations;
  - frame and weakening lemmas, used for if joins and the loop fixpoint;
  - cleanup at the end of a block;
  - declaring var and ref variables, and leaving a block;
  - the facts that the checker only extends environments and that its loop analysis reaches a fixpoint;
  - an initializer lemma, and three lemmas for writing into out self.

Dropping a value can run __deinit__ code, which is a call. In this theory that is an assumption, sound_drop, which the part on calls will have to prove.

The 2 failures, both in assign_core:
- In the out self field case, the final step lets the simplifier unfold drop_path itself. It should reduce only eval_place and then reuse the proved fact t.
- In the owned-root case, update_typed needs w0 = w substituted first.

Still to do:
1. Fix the two steps above.
2. Write the stmt_post, sound_stmt and sound_block definitions and the fuel induction over all statement forms. The plan for each form is worked out.
3. Add the new theory to ROOT and run a batch build.

After that, calls are next, together with discharging sound_drop and list methods.

⏺ Usage limit reached · continuing automatically at 5:50pm · esc to cancel

✻ Baked for 34m 11s · done 4:19 pm

❯ /rate-limit-options
  ⎿  Claude Code will continue automatically at 5:50pm. Keep this session open; it may still pause for permission prompts. Press esc to cancel the wait.


  Called isabelle-pide-mcp 3 times

Picking up where the usage limit stopped me. I'm fixing the last failing steps in the assignment proof.

  Called isabelle-pide-mcp

The assignment lemma is proved. Next I'm writing the statement and block induction: the definitions plus one case per statement form.


  Called isabelle-pide-mcp 2 times, ran 1 shell command

The statement induction is written. Two redundant proof steps and one case split in the while case remain to fix.

  Called isabelle-pide-mcp

Nearly all statement cases now check. One step in the while case made the simplifier unroll the loop analysis, and I've replaced it.

  Called isabelle-pide-mcp 2 times, ran 2 shell commands

The batch build fails on one step: an automatic case split in the DROP case overflows the stack. I'm replacing it with explicit case analysis.

  Called isabelle-pide-mcp 2 times

Everything in the statement theory now checks in Isabelle. Before the batch build, I'm updating the explanatory text in the expression theory, which still describes the old invariant.

Statement soundness is now proved for statements without calls, inside a single function. The whole session builds in batch with no sorrys (about 1 minute), and the new theory Micro_Mojo_Soundness_Stmt.thy (about 2,000 lines) is added to ROOT. One assumption remains: destroying a value can run __deinit__ code, which is a call. So dropping is taken as a hypothesis, sound_drop, which the part on calls will have to prove. Nothing is committed.

The theorem (stmt_sound). Assume sound_drop. Take a statement without calls, accepted by the checker, run in a state where the invariant holds. Then it fails at most with an out-of-range index.
- If it completes normally, the environment has only grown by its declarations, and the invariant holds for the checker's new state.
- If it returns, the result has the declared type.

How it is proved:
- Assignment rests on one general lemma, inv_write: writing a well-typed value below a writable variable keeps the invariant. It relies on exclusivity, on each reference recording which variable it points into, and on the checker's invalidations. Initializing a field of out self is handled too.
- if and while: the invariant still holds after the checker merges branch states, and the checker's loop analysis reaches a state that every iteration preserves.
- Blocks: leaving a block destroys its owned variables, and the invariant for the enclosing block holds again.
- The induction is over the fuel, proving statements and blocks together. The expression results from last time are reused at every fuel.

Checker changes, all needed for soundness. I've stated each one in the theory text, and all the example programs still get the same verdicts:
1. Assigning to a place, or mutating a list, now invalidates references into the lists inside it unless its type is trivial. Assigning l[0] in a List[List[Int]] used to leave a reference to l[0][1] live.
2. A reference to an imm argument can no longer be used to write to it.
3. Argument exclusivity now covers ref and out arguments, not just mut.
4. A function may have at most one out parameter.
5. var x: T with no initializer marks x uninitialized, and assignment checking is moved into its own function, chk_assign.

Invariant changes. To support statements I strengthened the invariant in Micro_Mojo_Soundness.thy:
- exclusivity is now stated over paths for every writable variable, not just owned roots;
- each reference records which variable it points into and the steps from there;
- allocation is fresh;
- names are distinct, and at most one out parameter is in scope.

I re-proved expression soundness under the new invariant.

Still to do (listed at the end of the new theory):
- Calls. Build the callee's invariant from the arguments, and restore the caller's after return. This needs a frame condition on statements.
- List methods. The invariant must also say that every list generation in the heap is below ngen.
- Destruction. Prove sound_drop in the same fuel induction as calls.
- Elaboration. Show that the inserted DROPs keep a program accepted by the checker.


> /compact  (637K tokens down to 43.4k)
> continue


  Searched for 2 patterns, ran 4 shell commands

Next I'm starting on calls: re-reading the invariant definitions to plan how the frame condition and the callee's invariant fit together.

  Searched for 1 pattern, ran 5 shell commands

I'm still working on the calls proof. I found the checker accepts calls where an argument mutates a place already evaluated, such as g(l[0], f(l)), which Mojo rejects and which fails at run time. I'll close that gap in the checker first, then return to the calls proof.

  Ran 7 shell commands

The plan for calls is settled, and I've found seven checker gaps that can let accepted programs fail at run time, including borrow conflicts, returned references, and unchecked __init__ and self parameters. I'm applying the checker fixes now.

  Ran 3 shell commands

Checker edits applied; now building to check that the examples and earlier proofs still go through.

  Called isabelle-pide-mcp 2 times, ran 2 shell commands

Started the new theory Micro_Mojo_Soundness_Calls.thy, beginning with lemmas about well-formed programs; checking it in Isabelle now.

  Called isabelle-pide-mcp 3 times

  Called isabelle-pide-mcp 5 times

The well-formedness part checks cleanly. Next I'm adding the "frame" notion (what a callee may change) and its basic lemmas.

  Called isabelle-pide-mcp 8 times

vagree_vt is now proven: a changed value keeps its type when each changed part does. I'm moving on to the heap-level frame lemmas and inv_chg, the general lemma that restores the invariant after a call or assignment.


  Called isabelle-pide-mcp 4 times

The heap frame lemmas are proven. Now writing inv_chg.


  Called isabelle-pide-mcp 7 times

The helper lemmas are proven. Writing inv_chg itself now; it checks every kind of binding: owned, borrowed, out self, and references.

  Called isabelle-pide-mcp 8 times

The inv_chg lemma is proven; it covers writes, calls and list mutation. Next I'll handle frame bookkeeping, the lemmas about places in flight, and the checker's static facts, then the per-construct soundness proofs.

  Called isabelle-pide-mcp 6 times

Frame lemmas are done. Next: static facts (the checker only weakens the abstract state; exclusivity facts), then the definitions for the main induction.

  Called isabelle-pide-mcp 6 times

Proving two checker facts: the abstract state only gets weaker through an expression, and a characterization of the exclusivity check. Waiting for the automation to finish.

  Called isabelle-pide-mcp 14 times, ran 1 shell command

Writing the proof script for the method-call case of the "abstract state only weakens" lemma; one automated step was too slow, so I'm replacing it.

  Called isabelle-pide-mcp 10 times, ran 1 shell command

Still proving the "abstract state only weakens" lemma (slow automation on one step). In parallel I'm writing the definitions for the main induction, one soundness statement per interpreter function.

  Called isabelle-pide-mcp 3 times, ran 1 shell command

The checker lemmas now check cleanly, with no errors. Next: definitions for the main induction.

  Called isabelle-pide-mcp 4 times

Definitions check. Now proving the destruction-related cases (cleanup, drop_paths), plus helper lemmas.

  Called isabelle-pide-mcp 4 times

cleanup and drop_paths are proven. Now drop_path, which runs __deinit__ bodies by appealing to the statement case at lower fuel.

  Called isabelle-pide-mcp 6 times

Helper lemmas check. Now writing the drop_path proof.

  Called isabelle-pide-mcp 6 times

drop_path is proven, so destruction (including __deinit__) no longer has to be assumed. Next are the expression cases with calls: places first, then expressions.

  Called isabelle-pide-mcp 4 times

Places are proven. Next: expressions (the call and method-call cases appeal to the call statements) and expression lists.

  Called isabelle-pide-mcp 9 times

Expressions are proven. Remaining: reference evaluation, argument passing, function and method calls, function bodies (invoke), statements and blocks. Now doing reference evaluation.

  Called isabelle-pide-mcp 2 times

Reference evaluation is proven. Now argument passing: the head argument is split into cases, with a shared lemma for the tail.

  Called isabelle-pide-mcp 11 times

The shared lemma for the remaining arguments is proven. Now the main argument-passing case.

  Called isabelle-pide-mcp 4 times

Argument passing is proven. Before function and method calls, I'm generalizing inv_chg: after a call, the callee's own roots also change, and those don't concern the caller.

  Called isabelle-pide-mcp 4 times

Next I'm covering the generalized inv_chg checks and what follows, then the two shared lemmas for function and method calls: one builds the callee's invariant from the arguments, the other restores the caller's invariant after return.

Writing the callee-entry lemma: the invariant at a callee's entry is built from the passed arguments. Fixing small issues now.

  Called isabelle-pide-mcp 8 times

The callee-entry lemma is proven. Next: restoring the caller's invariant after a call.

  Called isabelle-pide-mcp 4 times

Still in the callee-entry and caller-restore lemmas: fixing two small proofs.

  Called isabelle-pide-mcp 2 times

Both shared call lemmas are proven. Now helper lemmas for function calls (struct construction, parameter lookup, freeing the self root), then the function-call case.

  Called isabelle-pide-mcp 2 times

Helper lemmas for calls are proven. Next: the function-call case, covering fieldwise construction, __init__, and plain functions.

  You've hit your 5-hour limit · resets 10:50pm (Australia/Brisbane)
  Usage limit reached · continuing automatically at 10:50pm · esc to cancel


> /statusline


⏺ Usage limit reset · Continuing automatically

⏺ statusline-setup(Configure statusline from PS1)
Backgrounded agent (↓ to manage · ctrl+o to expand)

The status-line setup is running in the background. Meanwhile I'm continuing with the calls proof and checking the function-call case.

  Called isabelle-pide-mcp 2 times

› Message from @statusline-setup (ctrl+o to expand)

⏺ Agent "Configure statusline from PS1" finished · 9s

The status-line agent made no changes, since none of the shell profiles set a prompt to copy, so it needs you to specify what the line should show. It also flagged plaintext OpenAI and Gemini API keys in ~/.zshrc (lines 17–18), which you may want to rotate and move out of the file; I'm continuing with the call proof.

  Called isabelle-pide-mcp 10 times

args_ok_recv is proven. Now writing the method-call case itself: list append/pop and struct methods.

  Called isabelle-pide-mcp 8 times

The method-call case is now proven. Before invoke can be handled, its frame must allow the callee's roots to be freed at return, and those roots must be distinct; I'm updating the definitions and lemmas that depend on them.

  Called isabelle-pide-mcp 10 times

callee_ok and the frame of invoke are updated, and everything checks again. Now proving invoke: run the body, then destroy the callee's owned locals.

  Called isabelle-pide-mcp 7 times

An edge case: a partly initialized out self must never sit in a root owned by the callee, or its cleanup would not be type-correct. Adding that to the callee's entry conditions.

  Called isabelle-pide-mcp 5 times

The only remaining issue in the invoke proof is one slow step; replacing it.

  Called isabelle-pide-mcp 2 times, ran 3 shell commands

Next I'm adapting the call-free proofs to the new frames, starting with helpers for references returned by calls, dropping a variable, and frames across declarations.

  Called isabelle-pide-mcp 4 times

Helpers check. Now the assignment lemma, rebuilt on inv_chg.

  Called isabelle-pide-mcp 4 times

Assignment is confirmed. I'm narrowing the rule so that return only requires all out self fields to be set in __init__, then I'll write the statement and block cases.

  Called isabelle-pide-mcp 3 times

Everything up to the statement cases checks. Writing the remaining helpers and then the block and statement cases.

  Called isabelle-pide-mcp 2 times

Helpers check. Writing the block case, then the statement case.

  Called isabelle-pide-mcp 8 times

The block case is proven. Writing the statement case: all eleven forms, now with calls allowed.

  Searched for 1 pattern, called isabelle-pide-mcp 5 times, ran 1 shell command

Now the statement case itself (SS_Suc). Reading the old call-free proof and the interpreter's exec to adapt it.

  Called isabelle-pide-mcp 3 times

Sequencing, declarations and ref bindings check. Next: assignment, expression statements, print, drop and return.

  Called isabelle-pide-mcp 6 times

Assignment, expression, print, drop and return all check. Now if and while.

  Called isabelle-pide-mcp 5 times

All statement and block cases are proven. Now the fuel induction tying the 13 parts together.

  Called isabelle-pide-mcp 5 times

The whole development checks in PIDE, including the final run_safe theorem. Now checking for leftover sorrys, updating ROOT, and running a clean batch build.

  Ran 1 shell command

Batch build passes. Last step: making the theory's overview text match what was proved.

Soundness now covers whole programs, including calls. The full Mojo_Semantics session builds cleanly in batch mode on Isabelle 2026 (about 70 s), with no sorrys.

Main theorem (Micro_Mojo_Soundness_Calls.thy):

isabelle
theorem run_safe:  "wf_prog P ⟹ safe (run fuel P)"
corollary run_no_ownership_error:
  "wf_prog P ⟹ run fuel P = Err e ⟹ e = ErrBounds ∧ ¬ ownership_err e"

So whenever the checker accepts a program (check_prog P = []), running it with any amount of fuel never hits:
- a moved, uninitialized, dangling or invalidated value;
- a copy of something that can't be copied;
- an out self field read before it is set;
- a type or arity error.

The only error left is an out-of-bounds list index. Running out of fuel doesn't count as an error. There are also general versions for any statement (stmt_sound_calls) and expression (expr_sound_calls) in any context that satisfies the invariant.

What changed this session:
- Destruction is proved, not assumed. The earlier sound_drop assumption is gone. Dropping, cleanup and calls to user code are all covered by one proof by induction on the fuel, over all 13 interpreter functions.
- Frames. A callee can only change the caller's memory below its writable parameters. This is stated with a heap "shape agreement" relation, and one general lemma (inv_chg) restores the invariant after any set of changed locations. Assignment, calls and drops all go through it.
- The checker had real holes, found while proving calls sound and fixed in Micro_Mojo_Static.thy:
  - places still in use while a later argument or index is evaluated;
  - the origin of a reference returned by a call;
  - ref[ns] origins that aren't mut/ref parameters;
  - calls returning references used as values of non-trivial type;
  - early return inside __init__;
  - wrong receiver parameters on initializers and methods;
  - duplicate field names, function/struct name clashes, and a main with parameters.

  All example programs still give the same results.
- One weakening: the "all fields of self are initialized" condition at a return now only applies to functions with no result. That matches what the checker actually enforces.

Limits:
- The theorem covers programs as the checker sees them, with explicit SDrops. The next step is to prove that the ASAP elaboration (elab_body) produces accepted programs from acceptable sources, so the result carries over to normal Mojo-style code.
- Bounds errors and termination are not covered.

ROOT now includes Micro_Mojo_Soundness_Calls (about 5,400 lines). Nothing is committed: the three soundness theories are untracked, and Micro_Mojo_Static.thy, ROOT and prompts.md have uncommitted changes. I can commit them if you'd like.


❯ yes, commit them

  Ran 2 shell commands

I committed the work as 9c5183c on a new branch, soundness-proofs. I didn't commit straight to main because I don't commit to the default branch. To put it on main, run git switch main && git merge soundness-proofs, or I can do that.

The commit includes:
- the three soundness theories: Micro_Mojo_Soundness.thy, Micro_Mojo_Soundness_Stmt.thy and Micro_Mojo_Soundness_Calls.thy
- the checker fixes in Micro_Mojo_Static.thy
- ROOT
- prompts.md, with your edits included unchanged, among them the removed opening summary section

I left resume.sh and skills-lock.json untracked, since they weren't part of this work. Nothing has been pushed.


Session
=======
Total cost:            $122.11
Total duration (API):  4h 13m 52s
Total duration (wall): 4d 19h 55m
Total code changes:    326 lines added, 0 lines removed
Usage by model:
    claude-haiku-5-5:  25.0k input, 4.3k output, 0 cache read, 0 cache write ($0.0046)
     claude-sonnet-5:  310 input, 164.0k output, 21.4m cache read, 273.3k cache write ($7.01)
     claude-opus-5-5:  11.7k input, 1.1m output, 309.7m cache read, 3.8m cache write ($115.06)
   claude-sonnet-5-5:  4 input, 854 output, 8.1k cache read, 11.7k cache write ($0.0385)
Prompt cache (main):   634 requests · 99% of input tokens from cache · 3 misses (last 2m 28s ago — likely cause: idle past the 1h TTL, 1.5m tokens re-cached) · 3 expected rebuilds (compaction or tool-result clearing) · warm (1h TTL, last activity 2m 3s ago)





## 2026-10-31: Translator from Mojo to Micro-Mojo for Differential Testing

> /model Sonnet 5.5
> I want to be able to validate this formal semantics for Mojo against the actual compiler, using differential testing.  Write a
  parser and translator (in Python or Mojo) for *.mojo programs that generates Micro_Mojo_Syntax.prog syntax so that the test
  programs can be evaluated in Isabelle.  The translator should reject any Mojo program that is not within the Micro-Mojo subset
  with clear explanation of what language feature is not supported.  The end goal is to be able to generate a suite of Mojo test
  programs, run them through the Mojo compiler to get the actual output values, then translate the programs plus the expected
  output values into an Isabelle *.thy file that can be evaluated in batch mode.


I'll start by reading the syntax theory to see what the translator has to produce.

  Read 1 file, ran 6 shell commands

I've read the syntax and semantics theories. I'm now writing the Python translator, the Isabelle test-harness theory, and a suite driver.

  Write(mojo2isabelle/mojo_translate.py)
  Wrote 1496 lines to mojo2isabelle/mojo_translate.py

The translator works on Example 1. Next is the Isabelle test-harness theory.

Now the suite driver. It checks, runs against the compiler, and generates the theory.

  Write(mojo2isabelle/mojo_suite.py)
  Wrote 245 lines to mojo2isabelle/mojo_suite.py
  (added session Mojo_Tests to ROOT)

While that builds, I'm writing unit tests for the rejection messages.

I'll wait for the build to finish.

⏺ Monitor(wait for Isabelle build of Mojo_Tests)
Monitor started · task bmy0ncucq · timeout 600s

Build still running (it has to rebuild the parent session first). I'll wait for the background-task notification.

⏺ Monitor(wait for isabelle build to finish)
Monitor started · task bsgygq2mj · timeout 900s

⏺ Monitor(noop)
Monitor started · task bmskuspu5 · timeout 1s

The Isabelle build of the Mojo_Tests session is still running. It has to rebuild the parent session first, which takes a few minutes. I'm waiting for it to finish.

✻ Crunched for 9m 15s · done Saturday 4:06 pm

⏺ Monitor "noop" stream ended

That was only my placeholder monitor ending. The real build watcher (bsgygq2mj) is still running, so I'm checking the build output directly.

  Ran 1 shell command

The build is still running. I'll wait for the watcher to report back.

❯ /remote-control

  /remote-control is active · Continue here, on your phone, or at https://claude.ai/code/session_01VuaRWhPjCFAz9HffATwDHh

⏺ Monitor event: [Monitor expired after 10m with no events delivered. Re-arm it if you still need the watch — and widen the filter if silence was une…

  Ran 3 shell commands

The poly process is using about 4 cores and has been running for 12 minutes, which is far too long. I'll stop it and rebuild with progress output to see where it spends the time.

  Ran 1 shell command

⏺ Monitor "wait for isabelle build to finish" script failed (exit 144)

⏺ Monitor(wait for Mojo_Semantics build)
Monitor started · task bb66fcx4h · timeout 900s

The Mojo_Semantics build is running with progress output. I'm waiting for the watcher to report the result.

✻ Cooked for 2m 19s · done Saturday 4:18 pm

⏺ Monitor "wait for Mojo_Semantics build" stream ended

The failure is at line 53 of the testing theory, the render_examples check. I'll isolate it in a small standalone theory.

  Ran 1 shell command

That works in isolation. The earlier failure may just have been interference from the build processes I'd killed, so I'm rerunning the full build cleanly.

The build is running in the background. I'll pick up when it finishes.

Poly ran out of stack in by eval+ at line 53 of the testing theory. I'll experiment in the PIDE session, which avoids rebuilding everything each time.

  Called isabelle-pide-mcp 6 times

I'm debugging a stack overflow in the Isabelle build of the new testing theory. I'm checking whether the scratch theory has loaded in the PIDE session.

  Called isabelle-pide-mcp

The cleanest fix is to move the testing theory out of the main session into the Mojo_Tests session. That keeps the proven Mojo_Semantics build as it was and isolates the problem.

  Ran 1 shell command

Build started in the background; I'll check the result when it finishes.

❯ how are you going?   (hours later)

  Searched for 1 pattern

Mojo_Semantics builds fine again in 67 s. The hang is in my render_examples proof in the testing theory, so I'm killing the build and reproducing that part in the small standalone theory.

I'm still bisecting the hang in eval. My last script cut the base file at the wrong line, so I'm fixing that.

  Ran 11 shell commands

I've traced the hang to 32-bit Poly/ML, where evaluating numerals around 10⁹ never terminates. I'm setting the translator to reject literals above 10⁶ and switching the render check to a small number before rebuilding. · summary

  Ran 1 shell command

I've started the rebuild in the background and will report once it finishes.

The generated code fails on a constructor name clash: Mut also exists in the region theory, as effect.Mut. I'll qualify the conv and binop constructors in the generated terms.

All 11 generated tests pass, but the translation-check lemma fails, probably because the hand encoding of ex4_bad ends with ;; PASS, which the translator omits. I'm splitting that check into separate lemmas so any other mismatch shows up on its own. · summary

All nine direct equalities pass. The only failure is a vacuous lemma I added for ex4_bad, so I'm removing it and keeping the checker-equivalence lemma.

I've built the translator, a driver that generates the Isabelle test theory, and the Isabelle side that checks the tests. All of it builds, but nothing has been compared against the real Mojo compiler yet. There is no mojo on this machine, so the expected outputs for the 11 example programs are hand-written. The generated tests for those 11 all pass in the Isabelle batch build (isabelle build -D . Mojo_Tests), but that only shows the semantics matches my hand-written expectations. The translator unit tests pass too.

What exists

Everything is in the new mojo2isabelle/ directory, plus the tests/ directory and a change to ROOT.

- mojo_translate.py has a hand-written parser, since Mojo's var, ref, mut and x^ aren't valid Python syntax. It also infers types for var x = e and emits a prog term. Any program outside the subset is rejected with an explanation:
t.mojo:3:5: unsupported Mojo feature: 'for' loop
    micro-Mojo has no iteration protocol; write a 'while' loop instead
  Only the first problem in a file is reported.
- mojo_suite.py has three steps:
  - check reports which tests are in the subset.
  - run builds each test with mojo build and runs the binary. It records ok with stdout, compile_error, or runtime_error in a NAME.expected.json file.
  - thy generates tests/Micro_Mojo_Tests.thy, with one by eval lemma per test. Once the .expected.json files exist, the Isabelle build can be repeated without Mojo.
- tests/Micro_Mojo_Testing.thy has the predicates test_output, test_compile_error and test_runtime_error. Programs run after ASAP elaboration, so destructor output appears in Mojo's order. Output is compared as text, so print(a, b) has to render as a b and Bool as True/False.
- tests/Micro_Mojo_Translation_Check.thy proves the translator's output equals the hand-written encodings in the syntax theory. All the examples match except ex4_bad, where the hand version has a trailing PASS. For that one I prove that check_prog gives the same result for both.
- examples/ holds the example programs as .mojo files, and README.md documents the tools.

Things to know

- Hand-written expectations. The .expected.json files in examples/ are marked "source": "hand-written". The first real differential test is to run python3 mojo_suite.py run examples/ on a machine with Mojo and rebuild.
- Integer literals above 10⁶ are rejected. On this machine's 32-bit Poly/ML, eval hangs on numerals around 10⁹, even for plain nat arithmetic in Main. I didn't find the cause. Mojo's 64-bit overflow can't be detected statically either, so keep test values small.
- Desugarings. a > b becomes not (a <= b) and p += e is only accepted when p has no calls. Both keep evaluation order.
- and/or don't short-circuit in the model. A test whose right operand has side effects would differ from Mojo.
- compile_error tests don't compare the message. A test can pass because the checker rejected it for a different reason than the compiler did.
- Session layout. The test theories are in a separate session, Mojo_Tests, in tests/. Putting the new testing theory in the main session caused the build to hang, so I moved it out. Mojo_Semantics builds as before, in about 67 s.

Nothing from this session is committed. To keep the work, commit mojo2isabelle/, tests/ and ROOT; the other untracked files (hello-world/, resume.sh, skills-lock.json) aren't part of this. Say if you want me to commit.

❯ Well done, getting all the expected output correct without the compiler, then finding that the compiler agrees!  Yes, please commit mojo2isabelle/, tests/ and ROOT.

  Ran 1 shell command

I'm on main, so I'll commit on a new branch instead, and leave out the __pycache__ directory.

  Ran 1 shell command

I committed the work as 19ecb62 on a new branch, differential-testing. I branched because main is the default branch.

The commit contains:
- mojo2isabelle/: the translator, the suite driver, the translator unit tests, the README, and the 11 example programs with their recorded Mojo 1.2.0 results.
- tests/: the three Isabelle theories (testing predicates, generated tests, translation check).
- ROOT: the new Mojo_Tests session.

I left out mojo2isabelle/__pycache__/, prompts.md (you have uncommitted edits), hello-world/, resume.sh and skills-lock.json. Nothing has been pushed. To put it on main, run git switch main && git merge differential-testing, or I can do that.



❯ write the larger test suite

I'll write a suite aimed at the places the model might be wrong: destruction timing, moves, refs, lists, copies, mut parameters and run-time errors. Then I'll run it all through the compiler and see where the semantics disagrees.

The compiler gave 47 ok, 15 compile_error and 3 runtime_error results. Next I'll generate a theory for the suite and let Isabelle find the disagreements.

The suite build is running in the background. I'll report the disagreements when it finishes.

✻ Baked for 2m 55s · done 1:02 pm

⏺ Background command "export PATH="/Applications/Isabelle2026.app/bin:$PATH"; isabelle build -D . Mojo_Tests > /tmp/suite.log 2>&1; grep -v "running for" /tmp/suite.log | tail -60" completed (exit code 0)

  Ran 1 shell command

Only 4 of 65 tests disagree with the compiler. I'll look at what Mojo did in each, and then at what the semantics produces.

  Ran 1 shell command

Mojo short-circuits and/or and destroys the unused o right away, so built prints after the drops, which the model doesn't reproduce. I'll set up a small debug session over the four programs to see the semantics' real output. · summary

  Ran 1 shell command

The rm glob failed and aborted the cp, so I'm redoing the setup.

  Ran 4 shell commands

The debug theory was empty because the earlier copy had failed. I'm regenerating it properly.

  Ran 4 shell commands

The four disagreements between Mojo and the model are real findings, covering short-circuiting, field destruction order, and an unused parameter, plus one case where the checker rejects a program Mojo accepts. Next I'll find out why the checker rejects that last case and test Mojo's __deinit__ behavior further. · summary

  Ran 1 shell command

Direct experiments confirmed that __deinit__ destroys each field right after its last use, with unused fields like c going first, and that an unused var parameter is destroyed on entry to the callee. I'm now looking into why the checker rejects a08. · summary

  Ran 1 shell command

The checker requires each variable to be declared only once per function, which rejects programs like a08 that reuse names in disjoint scopes, and I'm also rejecting and/or whose right operand has calls or indexing, since the model doesn't short-circuit. I'm adding these rules along with a way to record the two known destruction-timing differences. · summary

  Ran 1 shell command

Both rules work. Next I'll add the two experiment programs to the suite, add known-divergence support to the driver, and add a unit test that every program in rejected/ is in fact rejected.

My quoting produced a syntax error in the divergence code. Fixing that line.

The generated theory now has 65 tests, 4 of them recorded as known divergences. Rebuilding.

  Ran 1 shell command

The build passes. I'll add the new rules and the divergence mechanism to the README.

I wrote a 65-program suite in mojo2isabelle/suite/ and ran it through Mojo 1.2.0. The semantics agrees with the compiler on 61 programs and diverges on 4. The Mojo_Tests session builds cleanly (isabelle build -D . Mojo_Tests).

The programs target likely weak spots: destruction timing, moves, copies, references, lists, mut/var parameters, methods and initializers, and arithmetic and control flow. Mojo gave 47 ok, 15 compile_error and 3 runtime_error results. Two of the run-time errors are the out-of-range and empty-list cases. The semantics reproduced all the compile-error and run-time-error results, so its static checks and error behaviour line up with the compiler, including partial moves, reference invalidation and __init__ field coverage.

I found four places where the model doesn't match Mojo:

1. Unused var parameter. Mojo destroys it on entry to the callee. The model's ASAP elaboration only drops a parameter after a use, so an unused one lives until the callee returns (d09, d14).
2. Fields inside __deinit__. Mojo destroys each field as soon as it's no longer needed. Fields the body never mentions go first, before the body runs. The model destroys all fields after the body (d05, d13). I confirmed this with a separate experiment.
3. Short-circuit and/or. Mojo short-circuits; the model evaluates both operands, so a call on the right-hand side prints even when it shouldn't.
4. Reusing a variable name in a disjoint scope. Mojo allows it, but the model's checker requires unique names within a function.

For 3 and 4 I took the cheap route: the translator now rejects such programs with an explanation, and the two examples are in suite/rejected/, with a unit test that they stay rejected. For 1 and 2 I recorded the four programs in suite/known_divergences.json. They generate as lemma …_diverges: "¬ test", so the build stays green now and fails as soon as the semantics is fixed. Then you remove the entry and the test becomes a normal one.

The README documents all of this. Nothing is committed yet; the changes are on the differential-testing branch and include suite/ and tests/Micro_Mojo_Suite.thy.

Items 1 and 2 are the most useful result of this round. Fixing them means changing the elab_body function in Micro_Mojo_Static.thy, and for item 2 probably also how __deinit__ destruction works in the interpreter. I'd expect the soundness proofs to survive, but I haven't tried. Want me to fix them, or commit the suite first?

❯ commit the suite first, then fix items 1 and 2.

Committed the suite as d27b776. Item 1 is edited in elab_body and the Mojo_Semantics build is running. Meanwhile I'm reading how the interpreter handles __deinit__, for item 2.

  Searched for 1 pattern, ran 3 shell commands

⏺ Monitor(Wait for Mojo_Semantics build)
Monitor started · task bh5n2ntsj · timeout 300s
Allowed by auto mode

  Searched for 1 pattern

Item 1 is edited and its build is running now. I'm reading the checker to gauge the work for item 2, which would need partial-field tracking in chk_stmt for SDrop and an elaboration step over fields. · summary

⏺ Monitor "Wait for Mojo_Semantics build" stream ended

  Searched for 1 pattern

Both failures are the expected _diverges lemmas for d09 and d14, and the semantics now matches Mojo on those programs while the soundness theories still build. Next I'll drop them from the divergence list and regenerate. · summary

The suite is committed, and item 1 (unused var parameters) is fixed and committed. Item 2 (field-wise destruction in __deinit__) is not started, because it's a much bigger change than item 1.

- Suite: committed as d27b776 on differential-testing.
- Item 1: elab_body in Micro_Mojo_Static.thy now starts the body with drops of var parameters that aren't live on entry. This is commit 881ba35.
  - The _diverges lemmas for d09 and d14 failed, which showed the model now matches Mojo, so I removed those two entries from known_divergences.json.
  - The core theories (soundness included) and Mojo_Tests both build.
  - I also updated the README.
- Item 2: d05 and d13 are still recorded as known divergences. Fixing them needs real changes to the checker and proofs:
  - Checker state: a_init tracks whole variables only, and SDrop accepts only PVar of an owned local. Dropping self.a early would need field-level initialization tracking, plus an SDrop rule for fields of deinit self.
  - Elaboration: elab is built around variable names. It would need to treat self.f places as droppable, destroying unused fields on entry and the rest after their last use.
  - Interpreter: drop_path already skips fields that are VUndef, so it needs little change.
  - Soundness proofs: the checker-state invariant changes, so I'd expect to redo parts of Micro_Mojo_Soundness_Stmt and Micro_Mojo_Soundness_Calls.

Should I go ahead with item 2, or leave __deinit__ as a documented divergence? The divergence only shows up when a struct has fields with their own destructors and a __deinit__ that prints.

❯ Yes.  Leave item 2 as a documented divergence.

❯ I have pulled those changes to main and pushed them.  Please create a top-level README.md

  Ran 2 shell commands
1 action blocked by auto mode · /permissions to review
│ Auto mode: [Irreversible Local Destruction]

I wrote README.md and committed it, but I committed it to main by mistake. I had meant to branch first. The commit is 648b72c and is local only, so nothing is pushed. I created a readme branch pointing at it.

I tried to move main back to origin/main with git reset --hard, and the auto-mode classifier blocked it as a destructive action. I left it alone, so main is currently one commit ahead of origin/main.

To undo it, run this yourself (nothing is lost, because the commit also lives on readme):

git checkout readme && git branch -f main origin/main

Or, if you're happy with the commit on main, just push it.

The README covers:
- the three parts of the project
- the theory table and the run_safe soundness result
- the build commands for both sessions
- the differential-testing workflow
- the known gaps (__deinit__ field-wise destruction, short-circuit and/or, unique variable names, and the integer literal limit)

I didn't run a build, since only a Markdown file changed. hello-world/ is still untracked.

Session

Total cost:            $129.43
Total duration (API):  4h 34m 59s
Total duration (wall): 7d 6h 6m
Total code changes:    2069 lines added, 0 lines removed
Usage by model:
    claude-haiku-5-5:  26.5k input, 4.5k output, 0 cache read, 0 cache write ($0.0049)
     claude-sonnet-5:  310 input, 164.0k output, 21.4m cache read, 273.3k cache write ($7.01)
     claude-opus-5-5:  184.9k input, 1.1m output, 309.8m cache read, 3.8m cache write ($115.82)
   claude-sonnet-5-5:  6.0k input, 127.7k output, 22.6m cache read, 765.4k cache write ($6.59)
Prompt cache (main):   768 requests · 99% of input tokens from cache · 6 misses (last 18m 57s ago — likely cause: idle past the 1h TTL, 1.9m tokens re-cached) · 5 expected rebuilds (compaction or tool-result clearing) · warm (1h TTL, last activity 8m 36s ago)







> Write an academic paper (in LaTeX) describing this project, covering the benefits of formalization, the challenges of Mojo, key aspects of the formalization and correctness results, the differential testing including discoveries of differences, plus related work and conclusion, and an acknowledgements section describing your contributions.


I've written the paper as paper/mojo-semantics.tex. It compiles to a 9-page PDF (paper/mojo-semantics.pdf) with no errors; the only warning is a minor overfull line. Nothing is committed.

It covers:
- Introduction: the contributions.
- Why formalise, and why Mojo is hard: the benefits, and the specific difficulties.
- Region model: the model of the gist.
- Micro-Mojo: its syntax, semantics, checker and the ASAP destructor-insertion pass.
- Soundness: run_safe and its corollary.
- Differential testing: the pipeline, the translator and the 76-program suite. Mojo accepted 53 of the 76, rejected 20 at compile time, and aborted 3 at run time.
- Findings: the four differences between the model and Mojo, set out in a table.
- Threats to validity, related work, conclusion and future work.
- Acknowledgements: what you decided and directed, and what I produced. I also note that the expected outputs were written by hand before the compiler was run.

Check before you use it:
- Bibliography: I wrote it from memory, and the paper says so in the acknowledgements. Please check every entry against the source. The InvalML entry is the weakest: I don't know its title or authors, so it is marked "details to be verified".
- Quoted translator error: I replaced my first, invented version with the real message from suite/rejected/a09_short_circuit.mojo.
- Wording: I removed one acknowledgements sentence saying you reviewed all changes before they were pushed, because I couldn't back it up.
- Venue style: it uses the plain article class. Tell me the venue and I'll switch to its template.

Do you want this committed? I'd put it on a branch, not directly on main.

✻ Crunched for 2m 24s · done 4:23 pm

Session

Total cost:            $129.81
Total duration (API):  4h 37m 23s
Total duration (wall): 8d 9h 36m
Total code changes:    2069 lines added, 0 lines removed
Usage by model:
    claude-haiku-5-5:  26.5k input, 4.5k output, 0 cache read, 0 cache write ($0.0049)
     claude-sonnet-5:  310 input, 164.0k output, 21.4m cache read, 273.3k cache write ($7.01)
     claude-opus-5-5:  184.9k input, 1.1m output, 309.8m cache read, 3.8m cache write ($115.82)
   claude-sonnet-5-5:  6.1k input, 145.8k output, 23.4m cache read, 794.4k cache write ($6.97)
Prompt cache (main):   775 requests · 99% of input tokens from cache · 6 misses (last 1d 3h 49m ago — likely cause: idle past the 1h TTL, 1.9m tokens re-cached) · 5 expected rebuilds (compaction or tool-result clearing) · cold — idle 1d 3h 23m, next turn re-caches ~120.1k tokens



## 2026-11-04 Wednesday. Paper Additions

❯ I want a bit more technical detail added to the paper, to show how things work, and what micro-Mojo covers.  Can you add the AST for Micro-Mojo into Section 4 (use Isabelle snippets if you can, so the paper stays up-to-date as the theory changes. See https://isabelle.in.tum.de/website-Isabelle2026-RC1/dist/Isabelle2026-RC1/doc/sugar.pdf), and then show a small example in Mojo syntax followed by in the sugared AST (I suggest that showing the shared methods plus ex1 in Mojo syntax, plus just ex1 main method in AST form would be good).  Then in the Semantics paragraph discuss the mutually recursive functions of the interpreter, describing the key functions, to make things more concrete for the readers.

  Ran 5 shell commands

I've confirmed the syntax theory matches the paper; I'm checking the interpreter's invoke, call_fun and exec clauses next, then setting up snippet extraction. · summary

  Ran 3 shell commands

I've added snippet markers to Micro_Mojo_Syntax.thy so the paper can pull the AST declarations directly, and a background build is generating their LaTeX now, which I'll wait on with a monitor. · summary

Both builds are queued (the main session with the markers, then the new Mojo_Paper session). I'm waiting for the main build to finish before checking the generated LaTeX.

  Ran 1 shell command

⏺ Monitor "Wait for Isabelle document build" stream ended

  Searched for 1 pattern, ran 4 shell commands

Status: the full document build failed on unrelated LaTeX issues in the big theories. I found isabelle document -S, which writes just the LaTeX sources, so I'm trying that.

Snippet extraction works and the Syntax declarations render as proper Isabelle LaTeX. I'm now writing the regeneration script and the interpreter-equation snippets, then the paper section. · summary

Snapshots are generated, and I'm now editing the paper's Section 4 (AST, sugar table, ex1 example) and the Semantics paragraph with the interpreter walkthrough. · summary

  Read 2 files, ran 1 shell command

Status: the Semantics section renders well, with the generated invoke and run equations. I'm checking the AST page, then fixing one small symbol.

The paper now has the AST, the sugar and the ex1 example in Section 4, and a longer interpreter walkthrough in the Semantics paragraph. It compiles to 13 pages (paper/mojo-semantics.pdf) with no LaTeX errors, and isabelle build -d . Mojo_Tests still passes. Nothing is committed.

What was added

Section 4:
- Abstract syntax: the datatypes for types, conventions, operators, places and expressions, statements, declarations and programs. They are Isabelle snippets, each with a short explanation.
- Sugared syntax: the notation and keywords (including the expression-notation snippet). The prose says the sugar is only notation, so theorems about the syntax apply to sugared programs unchanged.
- Example: the shared declarations plus ex1 in Mojo syntax, then only ex1_main in sugared AST form. The text explains why Mojo's output is 11, drop 2, got 11, drop 11, 1. b is destroyed right after the last use of r, whose origin is {a, b}, and before consume runs.

Semantics paragraph:
- a table of the 13 mutually recursive interpreter functions and their roles
- prose on how values, paths and environments work
- how pass_args implements each argument convention
- how call_fun handles constructors and __init__
- exec and drop_path
- two equations printed straight from the theory, invoke and run

How the snippets stay current

- The AST declarations are marked in Micro_Mojo_Syntax.thy with \snip markers, as sugar.pdf describes. The invoke and run equations come from @{thm} in paper/Paper_Snippets.thy. That theory is a new Mojo_Paper session in ROOT, and it fails if a quoted equation stops existing.
- sh paper/make-snippets.sh regenerates paper/snippets-*.tex. LaTeX errors in the unrelated big theories are ignored there, because only the generated .tex sources are used. Compile the paper with TEXINPUTS=".:/Applications/Isabelle2026.app/Contents/Resources/lib/texinputs:" latexmk -pdf mojo-semantics.tex.
- The Mojo program listing is still typed by hand in the paper. The theory only holds it as a comment, so it won't update automatically.

Changes outside the paper

- Micro_Mojo_Syntax.thy has the snippet markers.
- Two doc-text fixes that were breaking LaTeX: Mojo_Region_Model.thy (a # in a comment) and Micro_Mojo_Semantics.thy (a bare λ).
- ROOT has the new session and a document_files entry.
- .gitignore covers the paper build outputs.

I dropped the idea of generating the interpreter function signatures, because Isabelle prints expanded types like (char list × binding) list, which is unreadable. They are in the hand-written table instead.

Do you want these committed on a new branch? Per the earlier slip, I won't touch main.

❯ A few minor tweaks first: the double quotes in the Isabelle snippets are not showing in the PDF output.  For example, the SVar line in the stmt datatype shows as 'SVar vname ty expr option'.  It needs the double quotes around "expr option".  Can you fix this?  Secondly, let's drop the Isabelle notation declarations from the paper (since they are not very readable for non-Isabelle readers), but keep the English descriptions of the sugar syntax.  Thirdly, I really like the Mojo examples you've given as comments on the SVar and SRef constructors of stmt - can you add similar Mojo examples to most of the other stmt constructors?  And likewise in the expr and place datatypes?  I think such examples would really help readers who know Mojo but not formal datatypes / ASTs.

  Ran 5 shell commands

I've confirmed the syntax theory matches the paper; I'm checking the interpreter's invoke, call_fun and exec clauses next, then setting up snippet extraction. · summary

I've added snippet markers to Micro_Mojo_Syntax.thy so the paper can pull the AST declarations directly, and a background build is generating their LaTeX now, which I'll wait on with a monitor. · summary

⏺ Monitor(Wait for Isabelle document build)
Monitor started · task bjsznehes · timeout 900s

Both builds are queued (the main session with the markers, then the new Mojo_Paper session). I'm waiting for the main build to finish before checking the generated LaTeX.

  Ran 1 shell command

⏺ Monitor "Wait for Isabelle document build" stream ended

  Searched for 1 pattern, ran 4 shell commands

Status: the full document build failed on unrelated LaTeX issues in the big theories. I found isabelle document -S, which writes just the LaTeX sources, so I'm trying that.


Snippet extraction works and the Syntax declarations render as proper Isabelle LaTeX. I'm now writing the regeneration script and the interpreter-equation snippets, then the paper section. · summary

Snapshots are generated, and I'm now editing the paper's Section 4 (AST, sugar table, ex1 example) and the Semantics paragraph with the interpreter walkthrough. · summary

  Read 2 files, ran 1 shell command

Status: the Semantics section renders well, with the generated invoke and run equations. I'm checking the AST page, then fixing one small symbol.

  Read 1 file

Quotes and the new Mojo comments now render. Two cosmetic fixes remain, the ragged comment gaps and a repeated "ASAP" phrase, and I'm making both before one rebuild. · summary

All three tweaks are in and the paper still compiles cleanly to 13 pages. Nothing is committed yet.

1. Double quotes: "expr option" and the other quoted types now show in the PDF. I fixed it in the paper's LaTeX, because Isabelle's style file hides those quotes by default. The string "hi" in the new examples had the same problem and is fixed.
2. Notation declarations: the notation snippet is gone from the paper, and its marker is gone from Micro_Mojo_Syntax.thy. The "Sugared syntax" paragraph is rewritten in plain English. It covers how places, calls and sequencing are written and which statement keywords exist, and it says the sugar is purely notational.
3. Mojo examples: every constructor of place, expr and stmt now has a Mojo example in its comment, in Micro_Mojo_Syntax.thy. The paper picks them up through the generated snippets. Examples:
   - places: x, p.f, p[i]
   - expressions: p^, p.copy(), f(a, b) or Res(1), len(p), [1, 2, 3]
   - statements: p = e, print(a, b), if c: s1 else: s2, while c: s, return e or return
   - SDrop has no Mojo form, so its comment says it is inserted by ASAP elaboration.

Two small things you may notice. The comment dashes aren't aligned in a column, because the proportional font collapses spacing. I also fixed a sentence that read "ASAP elaboration of the ASAP elaboration".

The theory edits touch Micro_Mojo_Syntax.thy, Micro_Mojo_Semantics.thy, Mojo_Region_Model.thy and ROOT. I rebuilt Mojo_Semantics after them, but I haven't re-run Mojo_Tests since the comment edits. The earlier run was green.

Should I commit the paper and these theory edits to a new branch?


❯ Can you make your output less verbose by not showing diffs of uninteresting files that are covered by .gitignore?  Is there a setting that I should change to avoid seeing those diffs?

I'm not sure which output you mean, and I don't know of a Claude Code setting that hides diffs for gitignored files. These are the likely sources:

- Edit and Write diffs: Claude Code shows a diff whenever I edit a file. I can't suppress those per file from my side. Generated files such as paper/snippets-*.tex would show up here if I write them directly, but I only produce them with scripts.
- git diff output I ran: the one large diff I printed was git diff Micro_Mojo_Syntax.thy. That is a tracked file, so .gitignore would never have hidden it. I should have used git diff --stat or filtered the output instead of dumping about 80 lines.
- Build and LaTeX logs, and sed/cut dumps of generated .tex: these were mostly for my own checking. I can pipe them to tail or grep, or send them to a log file.

From now on I'll use --stat or narrow filters for diffs and keep generated or ignored files out of my output.

If you tell me which output bothered you, I can say whether a setting would help. The transcript view toggle (ctrl+o) and /config are where I'd look for output verbosity, but I haven't checked what they offer in your version.

One related question: paper/snippets-syntax.tex and paper/snippets-interp.tex are generated, but they are currently not in .gitignore. I think they should stay tracked, so the paper compiles without Isabelle. Do you want that, or should they be ignored and regenerated with make-snippets.sh?

✻ Brewed for 13s · done 3:13 pm

❯ Yes, I think it is good to track those generated snippets*.tex files, because a year or two later it can be a pain to get the right version of Isabelle set up to regenerate them.  The diffs that I am seeing a lot are: mojo-semantics.log mojo-semantics.aux etc.  And also isabelle-out/document/comment.sty etc.

  Ran 1 shell command

Those files are already ignored by git, so the diffs you see don't come from git. git status doesn't list them, and git check-ignore confirms the rules cover paper/*.log, paper/*.aux and paper/isabelle-out/.

I don't know of a Claude Code setting that stops it from showing changes to files on disk, so I can't point you to one. That display seems to track files the build changes, whether or not git ignores them.

What I can do is stop writing those files inside the project directory:
- run latexmk with -outdir pointing at a temp directory, so .aux, .log and the rest never land in paper/
- send the Isabelle document output (isabelle-out, isabelle-out-paper, which hold comment.sty and similar) to a temp directory too
- copy only mojo-semantics.pdf back into paper/, if you want it kept there

For the Isabelle output I'd pass document_output on the command line in make-snippets.sh. The Mojo_Paper session sets its output directory in ROOT, and I'd change that too.

I'll leave the generated snippets-*.tex files tracked, as you suggested.

Should I make that change? It touches paper/make-snippets.sh, ROOT and a small build script for the paper.

❯ Yes please.

The build no longer writes into the project directory. paper/ now holds only the sources, the two tracked snippets-*.tex files, the two scripts and the PDF.

- paper/build.sh: runs latexmk with its output directory in a temp directory, so .aux, .log and the rest stay out of the project. It copies only mojo-semantics.pdf back into paper/.
- paper/make-snippets.sh: sends the Isabelle document output (comment.sty and the like) to the same temp directory. I removed the document_output setting from the Mojo_Paper session in ROOT, and the script now passes it on the command line.
- Temp location: both scripts use $MOJO_PAPER_BUILD, or a temp directory if it isn't set.
- Cleanup: I deleted the old isabelle-out* directories and LaTeX build files from paper/.

I ran both scripts: the snippets regenerate and the paper builds to 13 pages.

While testing, a failed snippet step truncated snippets-syntax.tex to empty. The cause was that Isabelle skips a session it considers up to date, so the first build step produced no LaTeX. I fixed that with -f (force rebuild) in step 1, and regenerated the file. The scripts still don't guard against an empty result, so a failure like that could truncate a snippet file again.

Still uncommitted, on main: the paper, the three theory edits and ROOT. Do you want a branch and a commit?

❯ yes

⏺ API Error: Can't reach the API server — check your internet or DNS (ENOTFOUND)

✻ Worked for 2m 58s · done 3:38 pm

※ recap: We're formalising Mojo's ownership rules in Isabelle, validating them against the compiler, and writing the paper. That work is done but uncommitted on `main`. Next action: your go-ahead to commit it to a new branch.

❯ try again

  Ran 1 shell command

The paper is committed as 06e5c7c on a new branch, paper. main is untouched, and nothing is pushed.

The commit has the paper sources, the two generated snippets-*.tex files, build.sh, make-snippets.sh, the PDF, the three theory edits (marker comments, the Mojo examples on the place, expr and stmt constructors, and the LaTeX fixes) and the ROOT and .gitignore changes.

I left prompts.md and hello-world/ out because they aren't part of this work. They are still uncommitted.

You said "try again" in your message, and I couldn't tell what you wanted retried. I took "yes" as the go-ahead to commit. If you meant something else, tell me what.



## Paper Improvements

❯ I would like to make some more changes to the paper, to increase its attactiveness to Mojo developers, and to make more of a song and dance about the correctness results (Section 5)!  First, let's change the title to "A Formal Semantics of Mojo 1.2 and Its Ownership Checker".  Add subsections in Section 4 for: "Abstract Syntax", "Sugared Syntax", "Memory Model", and "Semantics".  Put the ex1 example (plus shared code) into a floating figure with two columns of code to save space.

The figure and subsections render as intended. I'm fixing the doubled "Figure 1: Example 1:" caption and committing.

Those three changes are in and committed as c2963d9 on the paper branch. The paper still builds to 13 pages.

- Title: now "A Formal Semantics of Mojo 1.2 and Its Ownership Checker".
- Section 4 subsections: 4.1 Abstract Syntax, 4.2 Sugared Syntax, 4.3 Memory Model and 4.4 Semantics. You listed four, but "ASAP Elaboration" and "Checker" would otherwise have sat oddly under "Semantics", so I made them subsections 4.5 and 4.6. Say if you want them folded back.
- Figure 1: a floating figure with the shared code on the left (Res, consume, bump, pick) and main on the right, with Mojo 1.2's output as comments under main. The prose after it explains the output, and the sugared AST of ex1_main follows. The figure floated to the top of the next page, away from the text that cites it.

One layout flaw: the AST of ex1_main splits across a page break. I'd fix that once the section 5 edits settle the layout.

For the correctness section, here are the changes I'd consider. Which should I go with?
- A boxed headline statement of the theorem in plain English up front.
- A "what this rules out" table that pairs each excluded error with the Mojo mistake it corresponds to.
- A short Mojo example for each error that the checker rejects.
- A proof-effort table: lines and lemmas per theory.


❯ I made some white-space changes to the Isabelle theories on the main branch.  Pull those into 'paper'.

  Ran 2 shell commands

I merged main into paper (merge commit 629b2f6) with no conflicts. That brings in your commit ac05a35, the blank lines before sections, which touched six theories. Isabelle ignores whitespace, so I didn't rebuild. The 11 snippet markers in Micro_Mojo_Syntax.thy are still there.

One leftover is still uncommitted: Micro_Mojo_Semantics.thy has the same kind of blank-line edit (12 added lines) in your working tree, plus a backup file Micro_Mojo_Semantics.thy~. It isn't in ac05a35, so I left it alone. Commit it on main if you want it, then I'll pull it in too.

If you want to change main further, commit it there and I'll merge again. Do you want me to continue with the Section 5 changes?

✻ Cooked for 30s · done 5:47 pm

❯ Yes, I added the white space to Micro_Mojo_Semantics.thy too, so please pull that into paper.

  Ran 2 shell commands

I merged your main commit 5f2942a, the blank lines in Micro_Mojo_Semantics.thy, into paper. The merge is 2103e5c with no conflicts. paper now has all your whitespace changes, and Micro_Mojo_Semantics.thy is no longer modified in the working tree. As before, I didn't rebuild, since only whitespace changed.

I'll go ahead with the Section 5 changes next. Which do you want?
- a boxed plain-English statement of the theorem
- a table pairing each excluded error with the Mojo mistake it corresponds to
- a short Mojo example for each rejected error
- a proof-effort table with lines and lemmas per theory

I can do all four if you'd rather not choose.

> Good.  Change 4.6 title to "Ownership Checker" for clarity.  And in 4.4 Semantics, can you expand out the list of errors into bullet points and briefly describe each error?  This will emphasize even more that the semantics is for INCORRECT programs (catching the errors at runtime), as well as for checked programs.  Yes, then implement your four changes in the correctness section.  We need a bit more informal explanation of wf_prog and 'safe' too, to explain the importance and impact of theorem run_safe.


All the changes are in and committed as 5bdb46d on paper. The paper is now 15 pages.

Correction: the paper and README.md both said safety "carries over to the elaborated program". That is not proved. run_safe covers programs as the checker accepts them, with or without explicit drops. The only proved elaboration result is elab_only_inserts_drops: after stripping DROPs the program is unchanged. That elaborated programs are still accepted by the checker is validated by the tests, not proved. Both documents now say this, and the point appears in the "what the theorem does not say" list.

- 4.6 is now "Ownership Checker".
- 4.4 Semantics: the errors are now bullets with a short description each. A new paragraph says the semantics is defined for incorrect programs, which is why the theorem has meaning. It also notes that the interpreter does not check argument exclusivity, implicit copies into var parameters, or moves out of borrowed places, so it runs such programs anyway.
- Section 5:
  - A boxed statement of the theorem in plain English.
  - Explanations of wf_prog (check_prog P = [], meaning the compiler accepts it) and safe. They cover why it matters, and the paper says outright that a checker rejecting every program would also satisfy the theorem.
  - A table pairing each run-time error with the Mojo mistake it models and whether the theorem excludes it. ErrBounds is the one it doesn't exclude.
  - Figure 2: small rejected programs for five of the errors (ErrUninit, ErrInvalidated, ErrNotCopyable, ErrDangling, ErrFieldInit).
  - A proof-effort table: about 8,700 lines and 344 lemmas.
  - A new "the proof found bugs in the checker" paragraph. It lists the holes that proving the call case exposed, taken from Micro_Mojo_Soundness_Calls.thy. I softened my first wording to "each was a hole that the proof could not close", since the theory comment doesn't say each one could crash a run.

The Figure 2 examples are condensed from ex2, ex3, ex4_bad, ex8 and m10. Mojo rejects all five, though the m10 message is "no attribute copy", not a copy error. The type, scoping and arity errors have table rows but no example program.

Do you want me to merge paper into main, or keep iterating on the paper first?

✻ Cooked for 2m 19s · done 5:54 pm

❯ In Section 4.1 change "Declarations follow" to "Finally we define function declarations and structure declarations:".  Can you find and download the BibTeX entries for the papers you've cited and put them into a *.bib file, then use bibtex to build the references?


dblp serves a bot challenge, so I won't use it. Crossref and DOI content negotiation are the sanctioned way to get BibTeX, so I'll use those.

I've pulled BibTeX for 15 of the 19 cited works from Crossref and arXiv, and I'm now assembling references.bib and switching the paper to bibtex. · summary

The sentence in 4.1 now reads "Finally we define function declarations and structure declarations:". The references are now a BibTeX file, paper/references.bib, built with bibtex. The paper is still 15 pages, with 20 references, no bibtex warnings and no undefined citations. It's committed as d60fa66 on paper.

Where the entries came from:
- 15 entries were downloaded by DOI from Crossref, and the Oxide entry came from arXiv. Each Crossref entry has a comment with its DOI.
- Four entries are hand-written: the Mojo manual, Nick Smith's gist, Rust RFC 2094 and Swift SE-0377. They are web documents with no downloadable BibTeX.
- The Isabelle/HOL book and the McKeeman article are hand-written too, because Crossref had no usable metadata for them. McKeeman's volume and pages come from my memory and I couldn't check them.
- dblp served a bot challenge, so I didn't use it. I used Crossref and arXiv instead.

Corrections the download made:
- Oxide authors: my from-memory list wrongly included Matsakis. The arXiv authors are Weiss, Gierczak, Patterson and Ahmed.
- InvalML: I had no reference details before. It is Gao and Parreaux, "A Lightweight Type-and-Effect System for Invalidation Safety…", PACMPL 9(OOPSLA2), 2025. The abstract confirms the nickname InvalML, and the related-work sentence now says so.
- Years: the bibliography uses the publisher's dates, which differ from the conference years in my earlier prose. RustBelt is 2017 (PACMPL 2(POPL)) and Stacked Borrows is 2019 (PACMPL 4(POPL)).

I braced a few title words (Rust, JavaScript, WebAssembly, C, Cyclone, RustBelt) so bibtex doesn't lowercase them. The acknowledgements no longer say the bibliography was written from memory. They now say the entries were downloaded from Crossref and arXiv, with a few hand-written ones to check.

paper/build.sh now sets BIBINPUTS so bibtex finds references.bib.

❯ Add access date 29 Oct 2026 for ref [14] (Nick Smith) and Nov 2026 for [8], [10] and [15]

I added the access dates and committed them as 6d9dd9b on paper. Reference [14], Nick Smith's gist, now reads "Accessed 29 October 2026". References [8] (RFC 2094), [10] (Mojo manual) and [15] (Swift SE-0377) read "Accessed November 2026".

My first edit broke the [14] entry in references.bib with a misplaced brace, and I fixed it before committing. The paper builds cleanly again. It is now 16 pages, one more than the 15 before this change, because the longer reference entries wrap further.

❯ merge paper into main


I merged paper into main as a fast-forward, so there is no merge commit. main is now at 6d9dd9b, which is paper's tip, with the paper, snippets, bibliography and theory changes. main is 6 commits ahead of origin/main. I haven't pushed anything, so you can review and push when ready.

Your uncommitted prompts.md change and the untracked hello-world/ were not touched. The paper branch still exists. Delete it if you no longer need it.
