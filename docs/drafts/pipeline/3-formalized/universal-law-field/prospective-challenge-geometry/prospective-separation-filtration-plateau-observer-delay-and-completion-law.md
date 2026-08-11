# Prospective separation filtration, permanent plateau, observer delay, and completion law

- **ID:** ULF-PCG-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM / NON-ARCHIMEDEAN LAW GEOMETRY
- **Statement:** Finite legal contexts induce a nested separation filtration whose limit is the
  future reporter kernel; one plateau is permanent; postobservation delays or erases separation;
  and coherent finite-horizon signatures need not be source-realized.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [LEAN-PROVED MECHANISM CORE] [LEAN-PROVED COMPLETION CLOSURE]
  [CLASSICAL AUTOMATA/COALGEBRA PARENTS] [NOT RH]

## 1. Setup

Let `X` be a set, let

\[
 f,g:X\to X
 \tag{PCG1.1}
\]

be legal context generators, and let `r:X->B` be a reporter. Let `W` be the free word monoid on
letters `L,R`, acting by `f,g`; write `|w|` for word length and `w x` for execution.

For `n in N`, define the prospective agreement relation

\[
 A_n^r(x,y)
 \quad\Longleftrightarrow\quad
 r(wx)=r(wy)\text{ for every }w\in W\text{ with }|w|<n.
 \tag{PCG1.2}
\]

Define the full future reporter kernel

\[
 A_\infty^r(x,y)
 \quad\Longleftrightarrow\quad
 r(wx)=r(wy)\text{ for every }w\in W.
 \tag{PCG1.3}
\]

## 2. Non-Archimedean filtration theorem

### Theorem 2.1

For every reporter `r`:

1. every `A_n^r` is an equivalence relation;
2. `A_(n+1)^r` is contained in `A_n^r`;
3. for every `x,y,z`,
   \[
   A_n^r(x,y)\wedge A_n^r(y,z)\Longrightarrow A_n^r(x,z);
   \tag{PCG1.4}
   \]
4. the full kernel is the intersection of finite horizons:
   \[
   \boxed{A_\infty^r(x,y)\Longleftrightarrow\forall n,\ A_n^r(x,y).}
   \tag{PCG1.5}
   \]

Consequently the classes of `A_n^r` form nested non-Archimedean balls. If one defines the first
separating depth

\[
 \tau_r(x,y)=\min\{|w|:r(wx)\ne r(wy)\},
 \tag{PCG1.6}
\]

with value `infinity` when no word separates, then

\[
 d_r(x,y)=
 \begin{cases}
 0,&\tau_r(x,y)=\infty,\\
 2^{-\tau_r(x,y)},&\text{otherwise}
 \end{cases}
 \tag{PCG1.7}
\]

is a pseudoultrametric and its zero relation is `A_infinity^r`.

### Proof

Reflexivity, symmetry, and transitivity of `A_n^r` hold pointwise for every admitted word; this
proves items 1 and 3. Every word of length `<n` also has length `<n+1`, proving item 2.

If `(PCG1.3)` holds, every finite restriction holds. Conversely, assume all finite restrictions and
fix `w`. Taking `n=|w|+1` admits `w` in `(PCG1.2)`, proving equality for that word and hence
`(PCG1.3)`. This proves `(PCG1.5)`.

For the pseudoultrametric, if `x,y` and `y,z` agree on every word shorter than `n`, transitivity of
reporter equality says `x,z` do too. Therefore

\[
 \tau_r(x,z)\ge \min(\tau_r(x,y),\tau_r(y,z)),
\]

with the evident convention for infinity. Exponentiation reverses this order and gives

\[
 d_r(x,z)\le\max(d_r(x,y),d_r(y,z)).
\]

Symmetry and the zero-kernel assertion are immediate. QED.

## 3. Context shift and permanent plateau

### Theorem 3.1 -- one-step shift

For every `n`,

\[
 A_{n+1}^r(x,y)\Longrightarrow
 A_n^r(fx,fy)\wedge A_n^r(gx,gy).
 \tag{PCG1.8}
\]

### Proof

If `w` has length `<n`, prefixing it by either generator gives a word of length `<n+1` whose
execution on `x,y` is execution of `w` on `fx,fy` or `gx,gy`. Apply `(PCG1.2)`. QED.

### Theorem 3.2 -- permanent-plateau law

If for some `n`

\[
 \forall x,y,\quad A_n^r(x,y)\Longleftrightarrow A_{n+1}^r(x,y),
 \tag{PCG1.9}
\]

then

\[
 \boxed{
 \forall m\ge n\ \forall x,y,\quad
 A_m^r(x,y)\Longleftrightarrow A_n^r(x,y)
 \Longleftrightarrow A_\infty^r(x,y).}
 \tag{PCG1.10}
\]

### Proof

By `(PCG1.8)` and `(PCG1.9)`, `A_n^r` is preserved by `f` and `g`. Equation `(PCG1.9)` also puts
`A_n^r` inside the present reporter kernel: for `A_n^r(x,y)`, pass to `A_(n+1)^r` and use the empty
word, whose length is `<n+1`.

The future reporter kernel is the greatest equivalence preserved by `f,g` and contained in the
present reporter kernel (ULF-OPM-5, Theorem 2.1). Hence

\[
 A_n^r\subseteq A_\infty^r.
\]

The reverse inclusion follows from `(PCG1.5)`. Thus `A_n^r=A_infinity^r`. For `m>=n`, nesting gives

\[
 A_\infty^r\subseteq A_m^r\subseteq A_n^r,
\]

proving `(PCG1.10)`. QED.

This is the sharp fixed-grammar no-reopening theorem. A later exact distinction forces a change of
grammar, reporter, carrier, admission, or truth status of the alleged plateau.

## 4. Observer-delay theorem

Let `p:B->C` be any postobserver and write `pr=p circ r`.

### Theorem 4.1

For every `n,x,y`,

\[
 \boxed{A_n^r(x,y)\Longrightarrow A_n^{pr}(x,y).}
 \tag{PCG1.11}
\]

Equivalently, separation by the observed reporter at horizon `n` implies separation by the source
reporter by the same horizon. If `p` is injective, `(PCG1.11)` is an equivalence at every horizon.

### Proof

Apply `p` to each reporter equality in `(PCG1.2)`. If `p` is injective, equality after `p` reflects
equality before `p`. QED.

### Corollary 4.2 -- observed birth is delayed source information

Suppose

\[
 A_n^{pr}(x,y)\quad\text{and}\quad\neg A_{n+1}^{pr}(x,y).
 \tag{PCG1.12}
\]

Then `not A_(n+1)^r(x,y)`. Thus an observed birth at step `n` is either a simultaneous source birth
or delayed exposure of a source distinction already present at some earlier horizon.

This corrects the overbroad slogan “observers only erase births.” They only delay or erase absolute
source information, but their coarser quotient may exhibit that information as a later relative
birth.

## 5. Sharp delay cell

Take three states `a,b,c`. Let `f(a)=a`, `f(b)=c`, `f(c)=c`, and let `g` be the identity. Let the
source reporter be the identity. Let the Boolean observer satisfy

\[
 p(a)=p(b)=0,\qquad p(c)=1.
 \tag{PCG1.13}
\]

The source distinguishes `a,b` at the empty word. The observer does not. After the one-letter word
`f`, it reports `0` on `a` and `1` on `b`. Hence

\[
 \neg A_1^{id}(a,b),\qquad
 A_1^p(a,b),\qquad
 \neg A_2^p(a,b).
 \tag{PCG1.14}
\]

This is observer-induced apparent genesis with an exact hidden-source certificate.

## 6. Completion-born coherent signature

Let source states be finite Boolean lists. Let the single context generator remove the head of a
list, and let the reporter return the current head, defaulting to `false` on the empty list. The
future signature of a list is therefore the list followed by an infinite tail of `false` values.

Let `T` be the all-`true` infinite signature.

### Theorem 6.1

1. for every finite horizon `n`, the list consisting of `n` copies of `true` agrees with `T` on all
   times `<n`;
2. no finite Boolean list has future signature `T`.

Thus `T` is coherent and finitely source-realizable at every horizon but not globally
source-realizable. In the product/prefix topology it lies in the closure of the source signature
image but outside the image.

### Proof

After fewer than `n` tail operations, the list of `n` true values still has a true head, proving
item 1. If a finite list has length `N`, after exactly `N` tail operations it is empty and the
reporter returns `false`, while `T(N)=true`. This proves item 2.

Every basic product neighbourhood of `T` constrains only finitely many coordinates; choose `n`
beyond their maximum and apply item 1. Therefore `T` belongs to the closure. QED.

## 7. Hostile loops and positive survivors

1. **New ultrametric geometry.** `[REDISCOVERED]` in automata/language and coalgebraic gauges.
   **Survivor:** exact coupling to law genesis, observer delay, and source-realization.
2. **A plateau can reopen.** `[FALSIFIED]` by Theorem 3.2. **Survivor:** reopening certifies a typed
   change outside fixed total grammar.
3. **Postobservation can create source information.** `[FALSIFIED]` by Theorem 4.1. **Survivor:**
   it can create only relative delayed birth, with earlier source separation.
4. **All finite realizations glue.** `[FALSIFIED]` by Theorem 6.1. **Survivor:** completion defect is
   non-surjectivity of the source-signature map onto coherent histories.
5. **Fixed grammar explains recursive open genesis.** `[FALSIFIED]` by plateau rigidity and finite
   ancestry. **Survivor:** open genesis must change grammar, admission, reporter, carrier, or pass
   to completion.

## 8. Parent and significance boundary

The mathematical parents are Myhill--Nerode/Moore refinement, syntactic congruence, symbolic
dynamics, Baire ultrametrics, behavioral metrics, and prodiscrete completion. The July 2026 paper
*Ultrametric Convergence of Guarded Automata* (arXiv:2607.19065) directly occupies distinguishing-word
ultrametrics and their regular-language completion. Coalgebraic generality is represented by
Baldan--Bonchi--Kerstan--König (arXiv:1712.07511), and generic partition refinement by
Wißmann--Dorsch--Milius--Schröder (arXiv:1806.05654).

The theorem is therefore a `[BRIDGE]`, not a priority claim for an isolated ultrametric result. Its
new corpus leverage is the exact no-reopening test and observer-delay correction for recursive law
genesis. It identifies what every late proof-route obstruction must spend: grammar, admission,
reporter, carrier, or completion change.

## 9. Exact scope

1. Contexts are total unary maps and words are finite.
2. Numerical ultrametric gauge uses binary scale only for convenience; the filtration is primary.
3. Infinite signatures carry the product/prefix topology.
4. No compactness of the source image is assumed.
5. No recursive rule generates a new context constructor here.
6. No positivity, HT, physical time, arithmetic source, RH endpoint, or proof-route datum appears.

## 10. Lean certification

Module `GaloisForLFunctions.HTGeometry.ConstitutiveProspectiveChallengeGeometry` certifies:

1. word depth and prospective agreement;
2. equivalence, nesting, context shift, and future-kernel intersection;
3. permanent plateau;
4. observer delay and injective preservation;
5. the three-state delayed-birth cell;
6. finite-list all-true finite realization and global nonrealization;
7. coordinatewise convergence of finite source signatures to the all-true history;
8. product-topology closure membership of that non-realized history; and
9. the numerical separation gauge `(PCG1.7)`: nonnegativity, symmetry, the exact zero relation
   `A_infinity`, and the ultrametric inequality;
10. one unconditional capstone. The filtration, plateau, observer-delay, finite/global realization gap, and
topological closure mechanism are certified without project axioms or route premises.

## Log

- 2026-08-10 -- paper proof closed after numeric-ultrametric novelty claim was killed by direct
  2026 literature collision.
- 2026-08-10 -- observer “only erases birth” slogan corrected to monotone first-separation delay.
- 2026-08-10 -- mechanism core and product-topology completion witness formalized in Lean.
- 2026-08-11 -- numerical separation gauge (PCG1.7) certified as a pseudoultrametric; card promoted to stage 3.
