# A Formal Semantics for Mojo (Micro-Mojo) with Regions

## 2026-10-08: Mojo Ownership Semantics
> try to formalise the memory management ideas in https://gist.github.com/nmsmith/cdaa94aa74e8e0611221e65db8e41f7b?permalink_comment_id=5940284 using Isabelle2025-2.  Explain your decisions and rationale in text comments in your generated *.thy file.  Mention possible alternatives where they exist.

Summary

I formalized the memory-management proposal from nmsmith's gist (including the crucial comment-thread clarifications) in Mojo_Region_Model.thy, a 1173-line Isabelle2025-2 theory that compiles cleanly with zero errors/warnings/sorries. Structure:

Part 1 — Regions as sets of variables. A mojo_regions locale parameterized by an ownership function owner :: 'l ⇒ 'l option. Defines footprint/region_footprint and two disjointness notions — set_disjoint vs. mem_disjoint — because the comment thread (verdagon/seanbaxter/nmsmith) revealed the gist's main text conflates them. Proves the "forest" theorem: well-formed regions (Rule 1) have pairwise-disjoint footprints, via a from-scratch linearity lemma about ownership chains. A worked Thing/ThingX instantiation reproduces the {thing} vs {thing.x} counterexample from comment 5278470 exactly.

Part 2 — Dereference safety. safe_to_deref models "reject if any region member may be uninitialized," with a soundness lemma and a replay of the gist's own x/y/reinit example.

Part 3 — Dynamic containers. A generation-counter model (Shape vs. Item operations) proves pointers survive item-only mutation but die on any shape change, regardless of position — formalizing "mutating items without mutating the entire buffer."

Part 4 — Aliasing-xor-mutability on regions (Rule 2). The centerpiece: copy_step models name[] = value[], deinitializing a target's whole footprint before reading the sourcever gets stuck (sufficiency) and that a region can never be mem_disjoint from itself when nonempty, with a matching failure lemma (necessity) — reconstructing both the
set_names and p1[]=p2[] examples.

Part 5 — Mutation as effect. subsumes formalizes " and contrasts read_step (unconditionallyalias-safe) against copy_step (needs mem_disjoint) to explain why reads are free but mutation isn't.

Final section is pure commentary connecting every open question back to source material: the Variant/InlineFixedVector open
questions, Rust's NLL as a rejected alternative frestingly — MattPD's InvalML pointer (OOPSLA 2025)and nmsmith's own admission that InvalML can't express first-class pointers into dynamic containers, which is exactly why Part
3 is built the way it is.

Every design decision and alternative-not-taken it ‹...› blocks. The file is at/Users/uqmuttin/git/rust/mojo-semantics/Mojo_Region_Model.thy.

✻ Cooked for 56m 49s · done 9:11 am


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



