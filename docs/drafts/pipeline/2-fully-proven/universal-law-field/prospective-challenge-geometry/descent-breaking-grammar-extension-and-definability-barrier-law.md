# Descent-breaking grammar extension and definability-barrier law

- **ID:** ULF-PCG-2
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT LAW-GENESIS MECHANISM THEOREM
- **Statement:** Extending a legal context grammar creates genuinely new eventual distinctions
  exactly when the new operation fails to descend to the old future-behaviour quotient. Every
  operation definable by an old context word is inert.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [FRONTIER-WIDE DIAGNOSTIC] [CLASSICAL QUOTIENT/SYNTAX PARENTS]
  [LEAN-PROVED] [NOT RH]

## 1. Frontier forcing

The current RH frontier is not blocked by one missing connector. Its first open premises fall into
five different classes:

1. singular source descent;
2. all-prime oscillatory transport;
3. adaptive spectral orientation;
4. whole-space coercivity;
5. positive carrier existence.

Their common negative feature is precise. Existing source operations, closures, observers, and
completions do not manufacture the required next legal operation. Prospective Challenge Geometry
detects future distinctions under a fixed grammar, but its permanent-plateau law proves that a
fixed grammar cannot explain genuine reopening.

The higher question is therefore mechanistic:

> When does adjoining a new legal operation change future law, rather than merely rename an old
> execution?

## 2. Old and extended grammars

Let `X` be a set, let

\[
 f,g:X\to X
 \tag{DB.1}
\]

be the old legal context generators, and let `r:X->B` be a reporter. Write `W_2` for finite words
in `f,g`. The old future kernel is

\[
 K(x,y)
 \quad\Longleftrightarrow\quad
 r(wx)=r(wy)\text{ for every }w\in W_2.
 \tag{DB.2}
\]

Adjoin one proposed legal operation

\[
 h:X\to X
 \tag{DB.3}
\]

and let `W_3` be finite words in `f,g,h`. The extended future kernel is

\[
 K^h(x,y)
 \quad\Longleftrightarrow\quad
 r(vx)=r(vy)\text{ for every }v\in W_3.
 \tag{DB.4}
\]

Say that `h` **descends to the old future quotient** when

\[
 K(x,y)\Longrightarrow K(hx,hy).
 \tag{DB.5}
\]

This definition uses no chosen quotient set. It is exactly the condition needed for `h` to induce
an operation on equivalence classes of `K`.

## 3. Conservative-extension and exact-genesis theorem

### Theorem 3.1

For every `f,g,h,r`:

1. the extended grammar is conservative on old contexts:
   \[
   \boxed{K^h\subseteq K;}
   \tag{DB.6}
   \]
2. the following are equivalent:
   \[
   \boxed{
   h\text{ preserves }K
   \quad\Longleftrightarrow\quad
   K^h=K;}
   \tag{DB.7}
   \]
3. therefore genuine law birth occurs exactly when `h` breaks quotient descent:
   \[
   \boxed{
   (\exists x,y,\ K(x,y)\text{ and }\neg K(hx,hy))
   \quad\Longleftrightarrow\quad
   K^h\subsetneq K.}
   \tag{DB.8}
   \]

### Proof

Every old word embeds in `W_3`, so agreement under every extended word implies agreement under
every old word. This proves `(DB.6)`.

The relation `K^h` is preserved by `f`, `g`, and `h`, because prefixing any extended word by one
generator gives another extended word. If `K^h=K`, this preservation immediately implies that `h`
preserves `K`.

Conversely suppose `h` preserves `K`. The old future kernel is already preserved by `f` and `g`,
and it lies in the present reporter kernel by the empty word. Induction on an extended word now
shows that every `K`-pair remains a `K`-pair after executing that word; applying the reporter gives
`K subset K^h`. Together with `(DB.6)`, this proves `(DB.7)`.

If descent fails, choose `x,y` with `K(x,y)` and `not K(hx,hy)`. By definition of `K`, some old word
`w` separates `hx,hy`. The extended word which first executes `h` and then `w` separates `x,y`.
Thus `(x,y)` lies in `K` but not `K^h`, proving strictness. The converse follows from `(DB.7)`.
QED.

## 4. Definability barrier

For old words `u,v`, let `uv` denote concatenation, with execution law

\[
 (uv)x=v(ux).
 \tag{DB.9}
\]

### Theorem 4.1 -- old-term definability cannot generate law

If there is an old word `u` such that

\[
 h(x)=u(x)\quad\text{for every }x,
 \tag{DB.10}
\]

then

\[
 \boxed{K^h=K.}
 \tag{DB.11}
\]

### Proof

Suppose `K(x,y)`. For every old word `v`, concatenation gives

\[
 r(v(hx))=r((uv)x)=r((uv)y)=r(v(hy)).
\]

Hence `K(hx,hy)`: the operation `h` preserves `K`. Theorem 3.1 gives `(DB.11)`. QED.

This is the exact anti-redressing law. A new formula, completion, category, operator, or physical
analogy produces no new eventual source distinction when its semantic action is already an old
context term.

The converse is deliberately not asserted. A semantically nondefinable operation can still
preserve `K` and be inert. Quotient escape, not syntactic novelty, is the exact criterion.

## 5. Delayed witness and observer erasure

When descent fails, the witness need not be visible immediately after `h`. Equation `(DB.8)` only
guarantees an old continuation `w` for which

\[
 r(w(hx))\ne r(w(hy)).
 \tag{DB.12}
\]

Thus law birth is a contextual event, not necessarily a one-step reporter change.

The event is also reporter-relative. Take three states `a,b,c`; let old generators be identities;
let `r(a)=r(b)=0`, `r(c)=1`; and let `h(a)=a`, `h(b)=c`, `h(c)=c`. Then `h` breaks the old future
kernel and the extended kernel is strictly finer. Postcompose `r` with the constant reporter. Its
future kernel is universal and is preserved by `h`, so the same grammar extension becomes inert.

Observation did not undo source execution. It erased the exact pair which certified quotient
escape.

## 6. Mechanism laws forced by the theorem

The theorem supports a field mechanism, not a universal carrier.

### Law I -- prospective quotient

Current law is measured by all admitted future executions, not present output alone.

### Law II -- genesis by descent failure

A new operation is effective exactly when it acts transversely to the current prospective
quotient. Merely adjoining syntax is not genesis.

### Law III -- definability barrier

Every operation generated by old syntax is conservative on eventual distinctions. Repackaging old
operations cannot reopen a saturated law phase.

### Law IV -- contextual witness

Failure of descent produces a finite composite witness: one new operation followed by an old
context. The new law need not be directly observable at its birth site.

### Law V -- observer relativity

Postobservation may turn an effective extension into an inert one by coarsening the prospective
quotient. Hence genesis must be typed relative to its reporter doctrine.

### Law VI -- reflexive update gate

The theorem tests a proposed update but does not generate `h`. The open field mechanism is a
source-normal rule

\[
 \text{persistent typed failure}
 \longmapsto
 \text{minimal legal }h\text{ breaking the current descent},
 \tag{DB.13}
\]

with conservativity on old syntax, coherent composition, and presentation-stable lineage.

## 7. Frontier-wide consequence

The five frontier classes demand different operation types, but the same acceptance test.

| Frontier class | Required grammar mutation | Exact acceptance test |
|---|---|---|
| singular descent | partial/admission-changing operation | fails to descend through old admitted future quotient |
| oscillatory transport | joint phase-preserving cofinal operation | separates a pair invisible to every old bounded/factorized context |
| adaptive orientation | response-indexed test constructor | prior response selects an operation transverse to old quotient |
| whole-space coercivity | global profile/properness challenge | detects a coherent escape history invisible at every old local test |
| positive carrier existence | coupled positive gluing operation | creates a legal positive realization not determined by old moment reporters |

This table is not a claim that the five operations are isomorphic. It says every alleged advance
must exhibit a descent-breaking source operation. If it cannot, Theorem 3.1 proves it is a semantic
redressing regardless of how different its target language looks.

## 8. Hostile loops

1. **New syntax implies law birth.** `[FALSIFIED]` by Theorem 4.1.
2. **Semantic nondefinability implies law birth.** `[FALSIFIED]`. With a constant reporter, the
   future kernel is universal and every operation preserves it.
3. **Failure to preserve the present reporter kernel is the exact test.** `[FALSIFIED]` by delayed
   contextual detection. The full future kernel is load-bearing.
4. **Every descent-breaking operation is source-generated.** `[FALSIFIED]`. Arbitrary state-indexed
   operations can break any nontrivial quotient. Equation `(DB.13)` remains open.
5. **One prospective quotient is the universal field object.** `[FALSIFIED]`. Effective extensions
   replace the quotient itself; the mechanism is the law of transition between quotients.
6. **This proves one RH route.** `[FALSIFIED]`. No arithmetic source or RH endpoint occurs.

## 9. Parent boundary

Term substitution, definitional/conservative extension, syntactic congruence, invariant
equivalence relations, and quotient descent are classical. Relevant broad parents include
Fiore--Mahmoud, *Second-Order Algebraic Theories* (arXiv:1308.5409), and Fujii,
*A unified framework for notions of algebraic theory* (arXiv:1904.08541). The field contribution
claimed here is the mechanism-level conjunction with future-behaviour quotients, observer
contraction, and reflexive grammar change across heterogeneous mathematical doctrines.

## 10. Exact scope and next gate

1. All operations are total unary maps.
2. Context words are finite.
3. No topology, partial admission, higher arity, positivity, or cost is built into the theorem.
4. The theorem classifies effectiveness of a supplied `h`; it does not source-generate `h`.
5. A full theory must replace total unary words by typed partial/multilinear/pro-compositional
   grammars without losing `(DB.7)`.

The next non-theatrical target is not another object. It is a law producing the minimal
descent-breaking grammar mutation from persistent failure while forbidding arbitrary update
oracles.

## 11. Lean certification

Module `GaloisForLFunctions.HTGeometry.ConstitutiveDescentBreakingGrammarExtension` certifies:

1. three-generator context words and execution;
2. old-word embedding and conservative inclusion;
3. equivalence between quotient preservation and kernel equality;
4. strict birth from a descent-breaking witness;
5. old-word definability barrier;
6. the three-state observer-erasure cell;
7. one unconditional capstone.

The direct source elaboration is warning-free. No project axiom, computation proof, or route premise
is used. Final owned-module and Universal Law Field umbrella builds are recorded on the Stage-3
certificate.

## Log

- 2026-08-10 -- extracted from the five first-open-premise classes in the current RH frontier map.
- 2026-08-10 -- old-term-definability conjecture dependency-closed; exact survivor strengthened to
  quotient-preservation iff no prospective refinement.
- 2026-08-10 -- exact descent criterion, strict-refinement form, definability barrier, and observer
  erasure cell formalized in Lean.
