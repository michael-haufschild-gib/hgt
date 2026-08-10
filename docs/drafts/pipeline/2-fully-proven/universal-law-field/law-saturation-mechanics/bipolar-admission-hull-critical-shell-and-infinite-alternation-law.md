# Bipolar admission hull, analytic critical shell, and infinite-alternation law

- **ID:** ULF-LSM-7
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL LAW-FIELD MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [BIPOLAR ADMISSION]
  [ANALYTIC CRITICAL SHELL] [COFINAL FINITE/GLOBAL SEPARATION]
  [EXACT HALF-GAP] [BRIDGE] [NOT RH] [LEAN CORE]

## 1. Mathematical delta

ULF-LSM-6 proves that executable operations can generate both unitization pressure and the exchange
reporter erased by joint strict execution.  ULF-GTM-3 proves that bounded continuous formation depth
commutes with compact Hausdorff completion.  This theorem closes the next missing mechanism:

> algebraic unitization and analytic admission are two different saturations.  Their difference is
> exactly the set of distinctions retained by the set quotient but erased by every continuous
> Hausdorff observer.

The theorem gives that difference a reporter-dual formula, proves an exact conflict criterion and
TV response, and constructs two source operations for which every finite truncation has an exact
continuous endpoint observer while the cofinal set quotient remains lossless and the global
continuous observer space collapses to constants.  The finite observers have a pointwise limit,
but the limit lies at exact uniform distance `1/2` from global analytic admission.

No RH route, zero, divisor, or endpoint normal form enters the construction.

## 2. Bipolar definitions

Let `X` be compact Hausdorff and let `R` be any binary relation on `X`.  Write `Eq(R)` for the least
set-theoretic equivalence relation containing `R`.

The continuous real reporter polar of `R` is

\[
 R^\perp
 =\{f\in C(X,\mathbb R): (x,y)\in R\Longrightarrow f(x)=f(y)\}.
\tag{BA.1}
\]

Its bipolar relation is

\[
 R^{\perp\perp}
 =\{(x,y)\in X^2: f(x)=f(y)\text{ for every }f\in R^\perp\}.
\tag{BA.2}
\]

Define the **analytic admission hull** and **analytic critical shell** by

\[
 \operatorname{Adm}(R)=R^{\perp\perp},
 \qquad
 \Sigma_{\rm an}(R)=\operatorname{Adm}(R)\setminus\operatorname{Eq}(R).
\tag{BA.3}
\]

The terminology is operational: `Eq(R)` is equality forced by finite algebraic unitization paths;
`Adm(R)` is equality forced by every admitted continuous scalar reporter.

## 3. Bipolar admission theorem

### Theorem 3.1 — least closed-equivalence hull

For every relation `R` on a compact Hausdorff space `X`:

1. `Adm(R)` is a closed equivalence relation containing `R`;
2. it is the least closed equivalence relation containing `R`;
3. the quotient map
   \[
     \pi_{\rm an}:X\longrightarrow X/\operatorname{Adm}(R)
   \]
   is universal among continuous maps from `X` to Hausdorff spaces that unitize `R`;
4. `Adm` is an extensive, monotone, idempotent closure operation on relations.

#### Proof

For every `f in R^perp`, its kernel relation

\[
 K_f=\{(x,y):f(x)=f(y)\}
\]

is an equivalence relation.  It is closed because it is the inverse image of the closed diagonal in
`R x R` under the continuous map `(x,y) mapsto (f(x),f(y))`.  Equation (BA.2) is the intersection
of all these kernels, hence is a closed equivalence relation.  Every `f in R^perp` is constant on
`R`, so `R subset Adm(R)`.

Let `E` be any closed equivalence relation containing `R`.  The quotient `X/E` is compact
Hausdorff.  Suppose `(x,y) notin E`.  Their quotient points are distinct.  Compact Hausdorff spaces
are normal, so Urysohn separation gives a continuous

\[
 h:X/E\longrightarrow[0,1]
\]

with `h([x])=0` and `h([y])=1`.  The composite with the quotient map belongs to `R^perp` and
separates `x,y`; therefore `(x,y) notin Adm(R)`.  Thus `Adm(R) subset E`, proving minimality.

If `q:X -> Y` is continuous, `Y` is Hausdorff, and `R subset ker q`, then `ker q` is a closed
equivalence relation containing `R`; minimality gives `Adm(R) subset ker q`.  The set-theoretic
factorization through `pi_an` is therefore well defined and unique, and quotient topology makes it
continuous.  This proves universality.

Extensivity and monotonicity follow directly from the least-hull characterization.  Since
`Adm(R)` is already a closed equivalence relation, applying the least-hull operation again changes
nothing.  This proves idempotence.  QED.

### Corollary 3.2 — reporter intersection law

For arbitrary relations `R,S`,

\[
 (R\cup S)^\perp=R^\perp\cap S^\perp,
\tag{BA.4}
\]

and

\[
 \operatorname{Adm}(R\cup S)
 =\operatorname{Adm}\bigl(\operatorname{Adm}(R)\cup
                            \operatorname{Adm}(S)\bigr).
\tag{BA.5}
\]

Consequently the join of two closed equivalence relations in the lattice of closed equivalences is
the analytic hull of their set-theoretic join.  A mixed admission term may appear even when each
primitive relation is already closed.

#### Proof

A function is constant on `R union S` exactly when it is constant on each relation, proving
(BA.4).  Both sides of (BA.5) are the least closed equivalence relation containing `R union S`, by
Theorem 3.1.  QED.

## 4. Exact conflict and reporter-loss theorem

Let `C subset X x X` be a declared distinction/conflict relation.  An observer is **lossless for
`C`** when it separates every pair in `C`.

### Theorem 4.1 — algebraic versus analytic realizability

1. A set-valued observer unitizing `R` and lossless for `C` exists iff
   \[
     C\cap\operatorname{Eq}(R)=\varnothing.
   \tag{BA.6}
   \]
2. A continuous Hausdorff-valued observer unitizing `R` and lossless for `C` exists iff
   \[
     C\cap\operatorname{Adm}(R)=\varnothing.
   \tag{BA.7}
   \]
3. Hence the admission-only obstruction is exactly
   \[
     C\cap\Sigma_{\rm an}(R).
   \tag{BA.8}
   \]

#### Proof

The set quotient `X -> X/Eq(R)` unitizes `R` and has kernel exactly `Eq(R)`, proving (BA.6).
The compact Hausdorff quotient `pi_an` has kernel exactly `Adm(R)`, proving sufficiency in
(BA.7).  Necessity follows from Theorem 3.1(3): every continuous Hausdorff observer unitizing `R`
has kernel containing `Adm(R)`.  Subtracting (BA.6) from (BA.7) gives (BA.8).  QED.

### Theorem 4.2 — exact Dirac total-variation response

Let `(x,y) in Sigma_an(R)`.  With

\[
 d_{\rm TV}(\mu,\nu)=\frac12\|\mu-\nu\|_1
\]

on finitely supported probabilities,

\[
 d_{\rm TV}(\delta_x,\delta_y)=1.
\tag{BA.9}
\]

For every continuous Hausdorff observer `q` unitizing `R`,

\[
 d_{\rm TV}(q_*\delta_x,q_*\delta_y)=0.
\tag{BA.10}
\]

#### Proof

Because `Eq(R)` contains the diagonal and `(x,y) notin Eq(R)`, the points are distinct; the two
Dirac masses have disjoint support, giving (BA.9).  Theorem 3.1 gives
`Adm(R) subset ker q`, hence `q(x)=q(y)`.  The pushforward Dirac masses are equal, proving
(BA.10).  QED.

## 5. Alternating-depth mechanism

Let `E,F` be closed equivalence relations on compact Hausdorff `X`.  Let `J_d(E,F)` contain pairs
connected by an `E/F` path of length at most `d`, and put

\[
 J(E,F)=\operatorname{Eq}(E\cup F)=\bigcup_{d<\infty}J_d(E,F).
\tag{BA.11}
\]

### Theorem 5.1 — bounded alternation is analytically safe

For every finite `d`, `J_d(E,F)` is closed.  If

\[
 (x,y)\in\overline{J(E,F)}\setminus J(E,F),
\]

then for every `d` and every neighbourhood of `(x,y)` small enough, there is a pair in that
neighbourhood whose minimal alternating path length is greater than `d`.

#### Proof

The relational composite of two closed relations on compact Hausdorff `X` is closed.  Indeed,

\[
 \{(x,z):\exists y,\ (x,y)\in A,\ (y,z)\in B\}
\]

is the projection to the first and third factors of a closed subset of compact `X^3`; the image is
compact, hence closed in Hausdorff `X^2`.  Every `J_d` is a finite union of such finite composites,
so it is closed.

Fix `d`.  Since `(x,y) notin J_d` and `J_d` is closed, some neighbourhood `W_d` of `(x,y)` misses
`J_d`.  Since `(x,y) in closure J`, every smaller neighbourhood inside `W_d` meets `J`; every such
meeting pair lies in `J setminus J_d`, so its minimal path length exceeds `d`.  QED.

This theorem is one-way.  The full hull `Adm(J)` can exceed `closure J` when ordinary closure is
not transitive.  Higher admission ranks require a transfinite closure/equivalence tower and remain
a Stage-1 problem.

## 6. Dependency-closed cofinal source model

### 6.1 Carrier and primitive formations

Let

\[
 \overline{\mathbb Z}=\mathbb Z\cup\{-\infty,+\infty\}
\]

with isolated integer points and the two tail topologies at the ends.  Equivalently it is the closed
subspace

\[
 \left\{\frac{n}{1+|n|}:n\in\mathbb Z\right\}\cup\{-1,1\}\subset[-1,1].
\]

Thus it is compact metrizable Hausdorff and `Z` is dense.

Define continuous idempotent unary formations `e,o` by

\[
 e(2k)=2k,\quad e(2k+1)=2k,
\tag{BA.12}
\]

\[
 o(2k-1)=2k,\quad o(2k)=2k,
\tag{BA.13}
\]

and let both fix the two ends.  Continuity at the ends follows because both maps change an integer
by at most one; idempotence is immediate.

Their source-generated unitization relations are the closed equivalences

\[
 E:\{2k,2k+1\}\text{ are classes},
 \qquad
 F:\{2k-1,2k\}\text{ are classes},
\tag{BA.14}
\]

with singleton end classes.  Closedness follows either from (BA.12)--(BA.13) and the explicit
classes, or directly: the only accumulation points of non-diagonal class pairs are the two diagonal
end pairs.

### 6.2 Joint algebraic and analytic laws

The set-theoretic join `J=Eq(E union F)` has exactly three classes:

\[
 \mathbb Z,\qquad\{-\infty\},\qquad\{+\infty\}.
\tag{BA.15}
\]

Hence the set observer

\[
 r(-\infty)=0,\qquad r(n)=\frac12\ (n\in\mathbb Z),\qquad r(+\infty)=1
\tag{BA.16}
\]

unitizes both formations and distinguishes the two ends.  But `Z x Z subset J` is dense in
`X x X`; therefore

\[
 \overline J=X^2,
 \qquad
 \operatorname{Adm}(J)=X^2.
\tag{BA.17}
\]

Every continuous Hausdorff observer unitizing `e,o` is constant.  The endpoint conflict belongs to
the analytic critical shell and its TV drops exactly from one to zero.

### 6.3 Uniform finite-stage realizability

For `N >= 0`, let `e_N,o_N` perform the collapses (BA.12)--(BA.13) only for `|k| <= N` and act as
the identity elsewhere.  They are continuous idempotents.  Their joint relation has one nontrivial
finite class

\[
 I_N=\{-2N-1,-2N,\ldots,2N,2N+1\}
\tag{BA.18}
\]

and all other classes are singletons.  It is closed.

Define `r_N:X -> [0,1]` by

\[
 r_N(-\infty)=0,\quad r_N(+\infty)=1,
\]

\[
 r_N(n)=
 \begin{cases}
 0,&n\le -2N-2,\\
 1/2,&-2N-1\le n\le 2N+1,\\
 1,&n\ge 2N+2.
 \end{cases}
\tag{BA.19}
\]

This map is continuous, unitizes both finite formations, and separates the endpoint conflict by the
full margin one.  Thus every finite problem is analytically realizable with the same compact target
and the same exact endpoint margin.

For every fixed integer `n`, eventually `n in I_N`, so

\[
 r_N(x)\longrightarrow r(x)
\tag{BA.20}
\]

pointwise on `X`, where `r` is the lossless set observer (BA.16).  The pointwise limit is
discontinuous at both ends.

### Theorem 6.1 — exact analytic half-gap and non-equicontinuity

Let `A_J` be the real vector space of continuous observers unitizing both limiting formations.  Then

\[
 A_J=\{\text{constant functions}\},
\tag{BA.21}
\]

the family `(r_N)` is not equicontinuous at either end, and

\[
 \boxed{
 \inf_{q\in A_J}\|r-q\|_\infty=\frac12.}
\tag{BA.22}
\]

#### Proof

Any `q in A_J` is constant on the joint integer class.  Its equalizer with that constant is closed
and contains dense `Z`, hence is all of `X`; this proves (BA.21).

If `(r_N)` were equicontinuous at `+infinity`, the tolerance `1/4` would have one common tail
neighbourhood on which every `r_N` stayed within `1/4` of `r_N(+infinity)=1`.  Choose an integer in
that tail and then choose `N` large enough that the integer lies in `I_N`; its value is `1/2`, a
contradiction.  The negative end is identical.

For a constant `c`,

\[
 \|r-c\|_\infty
 =\max\{|c|,|1/2-c|,|1-c|\}
 \ge\max\{|c|,|1-c|\}\ge1/2.
\]

Equality holds at `c=1/2`, proving (BA.22).  QED.

Finally, the pairs `(-m,m)` approach `(-infinity,+infinity)` and require exactly `2m` consecutive
alternating edges.  Hence the critical pair is reached only through unbounded alternating depth,
as predicted by Theorem 5.1.

### 6.4 Sharp one-ended specialization

The same finite/global admission mechanism already occurs on the smaller carrier

\[
 X_+=\mathbb N\cup\{\infty\},
\]

the one-point compactification of the discrete natural ray.  Define continuous idempotent
retractions by pairing

\[
 e_+:\{0,1\},\{2,3\},\ldots,
 \qquad
 o_+:\{0\},\{1,2\},\{3,4\},\ldots,
\tag{BA.23}
\]

and fixing `infinity`.  Their algebraic join has two classes, `N` and `{infinity}`.  Thus the set
reporter

\[
 r_+(n)=0,\qquad r_+(\infty)=1
\tag{BA.24}
\]

unitizes both operations and distinguishes the end.  Every continuous Hausdorff-valued jointly
unitizing observer is constant: adjacency makes it constant on `N`, and continuity at infinity
extends the same value to the end.  Hence the analytic admission relation is total.

For each `N`, the continuous reporter

\[
 r_{+,N}(n)=\mathbf 1_{n>N},\qquad r_{+,N}(\infty)=1
\tag{BA.25}
\]

unitizes both retractions throughout the aperture `{0,...,N}`, has exact endpoint margin one, and
converges pointwise to `r_+`.  The limit is discontinuous.  Moreover

\[
 \inf_{c\in\mathbb R}\|r_+-c\|_\infty=\frac12,
\tag{BA.26}
\]

because every constant has error at least the maximum of its errors at `0` and `infinity`, while
`c=1/2` has pointwise error exactly `1/2`.  This one-ended specialization is the formal capstone;
it is not a finite substitute for the cofinal mechanism.

## 7. Conjecture/failure/survivor ledger

### Loop A — closed primitive admissions have a closed join

**[FALSIFIED].**  `E,F` in (BA.14) are closed; their algebraic join is not.

**Positive survivor:** the admitted join is `Adm(E union F)`, and its mixed shell is dual to the
intersection of reporter algebras.

### Loop B — finite analytic realizability compactness-passes to the limit

**[FALSIFIED].**  Every `r_N` has exact margin one, yet no global continuous observer separates the
ends.

**Exact why:** the observer family is not equicontinuous.  Arzela--Ascoli compactness is unavailable;
pointwise convergence lands outside `C(X)`.

**Positive survivor:** (BA.22) is a nonzero quantitative admission gap, not a missing subsequence.

### Loop C — ordinary closure of the algebraic join is always the hull

**[FALSIFIED IN GENERAL].**  Closure of an equivalence relation need not remain transitive.

**Positive survivor:** the bipolar relation is the least closed-equivalence hull without any
metrizability or one-step-closure hypothesis.  First-shell depth divergence is retained exactly by
Theorem 5.1.

### Loop D — the field theorem is a new closed-relation lattice theorem

**[REDISCOVERED/BRIDGE].**  Closed-equivalence lattices, Hausdorff quotients, invariant-function
duality, and continuous coloring obstructions are occupied mathematics.

**Surviving field content:** one source-executable cofinal system simultaneously exhibits operation
provenance, finite exact realizability, algebraic global realizability, analytic global failure,
unbounded alternating depth, exact TV erasure, loss of equicontinuity, and the exact uniform half-gap.
This is a new-to-corpus mechanism theorem and closes Bipolar Target 3, not an external priority
claim.

## 8. Parent mathematics and priority boundary

The universal hull belongs to established topology and functional duality:

- closed equivalence relations on compact Hausdorff spaces and their quotients;
- Shilov/Gelfand duality between closed equivalences and suitable invariant subalgebras of `C(X)`;
- lattices of closed quasiorders/equivalence relations;
- de Vries duality and closed-relation allegories;
- continuous chromatic-number obstructions in topological dynamics.

Primary/current parents include:

- Abbadini--Bezhanishvili--Carai,
  [*A generalization of de Vries duality to closed relations between compact Hausdorff spaces*](https://arxiv.org/abs/2206.05711);
- Heunen--Lindenhovius, *Domains of commutative C*-subalgebras*, Lemma 4.3 (closed equivalences are
  dual to invariant continuous-function algebras);
- Lecomte,
  [*Continuous 2-colorings and topological dynamics*](https://arxiv.org/abs/2307.00851);
- Erne--Stege, *Lattices of Closed Quasiorders* (1996).

No novelty claim is made for these ingredients.  The exact HGT residue is their mechanism-level
coupling to endogenous formation and quantitative observer loss.

## 9. Scope and next gate

1. Compact Hausdorffness is used to turn closed equivalences into Hausdorff quotients and to
   separate quotient points by continuous real reporters.
2. The theorem concerns continuous Hausdorff admission.  Measurable, smooth, holomorphic,
   positive, bounded, and domain-restricted admissions have different bipolar hulls.
3. The two-ended model supplies an asymptotic reporter generated by completion of the formation
   history; it is not the finite schedule reporter of ULF-LSM-6.
4. The theorem does not prove that every RH route instantiates the same relation.
5. It closes the finite/cofinal analytic-admission gate, but not the field acceptance gate requiring
   one source to produce three structurally distinct formations and a cross-organ withheld
   consequence.
6. The next live conjecture is **doctrine-relative bipolarity**: replace `C(X,R)` by a declared
   admissible reporter doctrine and determine which laws of the hull survive, how hulls exchange,
   and whether positivity/differential/whole-space admissions yield nonisomorphic critical shells
   from one source.

## 10. Lean gate

Lean now certifies the theorem's mechanism core:

- `ConstitutiveAnalyticAdmissionHull.lean` constructs algebraic saturation followed by Hausdorff
  admission, proves universal factorization for every continuous Hausdorff-valued unitizing
  observer, and proves exact scalar bipolarity on compact Hausdorff sources;
- `ConstitutiveOneEndedAdmissionCriticalShell.lean` proves the continuous source retractions,
  algebraic finite-class propagation, total analytic admission, the surviving discontinuous set
  reporter, finite continuous reporters with exact margin one and pointwise stabilization, and the
  exact global half-gap.

The unconditional capstone is `oneEndedAdmissionCriticalShell`.  The paper's general
closed-equivalence least-hull reformulation, measure-theoretic Dirac-TV statement, two-ended model,
and bounded-alternation closure theorem remain paper-proved rather than Lean-certified.  They must
not be cited as formally proved until separately promoted.

## Log

- 2026-08-10 — closed-join and finite-to-global conjectures killed by the two-ended alternating
  chain.
- 2026-08-10 — bipolar hull, conflict criterion, TV response, depth divergence, cofinal model,
  equicontinuity failure, and exact half-gap closed on paper.
- 2026-08-10 — coordinate-free Hausdorff-admission bipolarity and one-ended cofinal critical shell
  certified in Lean; remaining paper-only clauses listed explicitly in Section 10.
