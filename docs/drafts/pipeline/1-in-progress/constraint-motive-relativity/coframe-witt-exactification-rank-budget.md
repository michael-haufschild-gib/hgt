# Coframe--Witt exactification rank budget

- **ID:** `cmr-coframe-witt-exactification-rank-budget`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE / PAPER-PROOF ATTACK
- **Status:** `[PAPER-PROVED LOCAL THEOREM] [FINITE-DUALITY PARENT ROUTINE]`
  `[INJECTIVE-REALIZATION NO-GO] [REGULAR-REDUCTION ESCAPE]`
  `[LIVE SOURCE-DAGGER CONSEQUENCE CONDITIONAL] [NO LEAN WRITTEN OR BUILT]`
- **Source:** `../nomological-geometry-and-dynamics/constraint-motive-relativity.md`;
  `../../2-fully-proven/constraint-relativity/prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law.md`;
  `../../4-publication-ready/euler-stokes-rank-port-inertia-law.md`.
- **Statement:** Exactifying `k` independent source laws creates a canonical hyperbolic
  law--observer double of Witt index `k`; any injective pairing-preserving realization in a target
  whose negative index plus radical rank is at most `r` satisfies `k<=r`. A boundary-isotropic
  chain realization obeys the same budget, and a form descending to homology obeys the sharper
  radical-only budget.

## Goal

Turn the corpus's apparent uncertainty between complete arithmetic coframe and one-port Stokes
geometry into a quantitative theorem. The result must not assume RH, a zero-line selector, or the
missing source-nullhomology. It constrains injective pairing-preserving common realizations. A
hostile counterexample shows that it does not constrain regular coisotropic quotients by itself;
topology/admission, not Witt rank alone, is load-bearing there.

## Exact theorem under attack

Let `C,E` be chain complexes of finite-dimensional complex vector spaces and let `f:C->E` be a
chain map. Fix degree `n`. Put `Z=Z_n(E)` and `B=B_n(E)`. Let `q` be a Hermitian form on `Z`. Let
`U subset Z_n(C)` be finite-dimensional, assume `U -> H_n(C)` and `f|U` are injective, and put

\[
 K=\{u\in U:[f(u)]=0\text{ in }H_n(E)\}.
\tag{1}
\]

There are two distinct chain-level conclusions.

### Boundary-isotropic variant

If

\[
 q(B,B)=0
\tag{2}
\]

and

\[
 \operatorname{ind}_{-}(q)+\dim\operatorname{rad}(q)\le r,
\tag{3}
\]

then

\[
 \boxed{\dim K\le r.}
\tag{4}
\]

### Homological variant

If the stronger condition

\[
 q(B,Z)=0
\tag{5}
\]

holds, then `B subset rad(q)` and

\[
 \boxed{\dim K\le \dim\operatorname{rad}(q).}
\tag{6}
\]

This is stronger than `(4)` and does not use the negative index.

### Cotangent anomaly double

Put `K_H=ker H_n(f)`. The already-proved relative-law observer-descent theorem identifies the
relative laws made exact by `f` with `K_H`, and scalar observers that fail to descend with
`K_H^*`. Forget complex scalars temporarily. Real part gives a canonical real-linear
identification between the complex dual `K_H^*` and the real dual of the underlying real vector
space `K_{H,R}`. Hence the real cotangent double

\[
 \mathbb H_{\mathbb R}(K_H)=K_{H,\mathbb R}\oplus K_{H,\mathbb R}^*
\tag{7}
\]

carries canonical symmetric and alternating forms

\[
 h((x,\alpha),(y,\beta))=\alpha(y)+\beta(x),
 \qquad
 \omega((x,\alpha),(y,\beta))=\alpha(y)-\beta(x).
\tag{8}
\]

The two summands are complementary Lagrangians for `omega` and complementary totally isotropic
subspaces for `h`; `h` has split real signature `(2 dim_C K_H,2 dim_C K_H)` and zero radical.
Equivalently one may use the standard hyperbolic Hermitian object
`K_H direct-sum K_H^sharp`, where `K_H^sharp` is the conjugate-linear dual. Thus any injective
isometry from this hyperbolic double to the underlying real symmetric form of a complex Hermitian
space `(V,q_V)` satisfies

\[
 \boxed{\dim K_H\le
 \operatorname{ind}_{-}(q_V)+\dim\operatorname{rad}(q_V).}
\tag{9}
\]

In the finite dualizable case evaluation also gives

\[
 \ker H_n(f)\cong\operatorname{coker}H^n(f)^{\vee}.
\tag{10}
\]

Consequently any source coframe perfect on `K` loses at least `dim K` independent directions from
the extendable coframe.

## Conjecture loops

### Loop A — kernel/cokernel duality is the new geometry

**Verdict:** `[REDISCOVERED]`. For finite-dimensional complexes, `(5)` is dual linear algebra:
`H^n(-)=H_n(-)^*`, and the dual of the cokernel of the transpose is the kernel. It is a required
typing law, not a new field.

**Positive survivor:** the dimension of killed source law is exactly the codimension of extendable
dual observers. This makes observer loss quantitative and supplies the dual half of `(4)`.

### Loop B — one negative Stokes port exactifies the prime coframe

**Attack:** if boundaries are mutually `q`-isotropic, every killed source vector maps into a
totally isotropic subspace. A Hermitian form with `ind_-+nullity<=r` has no totally isotropic
subspace of dimension greater than `r`. If boundaries are orthogonal to every cycle, they lie in
the radical and the sharper radical-only bound applies.

**Surviving claim:** theorems `(4)`, `(6)`, and `(9)`. They predict that the published one-port
Stokes form cannot be an injective pairing-preserving realization of two or more exactified prime
classes. They do not forbid a coisotropic quotient that deliberately removes conjugate pairs.

### Loop C — use `(4)` to prove RH

**Verdict:** `[FALSIFIED AS CIRCULAR]`. The theorem does not prove any prime class is killed. It
only constrains a comparison if source-nullhomology is independently constructed. Installing that
nullhomology remains RH-bearing.

**Positive survivor:** fixed finite-port, finite-index, coefficient-faithful exactification is
ruled out uniformly in prime cutoff only in the injective/isometric architecture. The theorem
forces a noninjective reduction, but does not decide whether that reduction is regular or singular.

### Loop D — Witt rank forces a singular/Tate transition

**Verdict:** `[FALSIFIED]`. Let `0 ne lambda in K^*` and put `I=ker lambda` inside the law half of
the hyperbolic space `H(K)=K direct-sum K^*`. Then

\[
 I^\perp=K\oplus\mathbb C\lambda,
 \qquad
 I^\perp/I\cong (K/I)\oplus\mathbb C\lambda\cong\mathbb H(\mathbb C).
\tag{11}
\]

This is an ordinary regular coisotropic reduction from arbitrarily large rank to one hyperbolic
port. One observer polarization is one-dimensional. Thus Witt rank does not force singularity.

**Positive survivor:** the same reduction behaves differently after source-selected completion.
For finite-support prime sequences, the augmentation kernel is dense in `ell^2` but closed of
codimension one in `ell^1`. Hence the meaningful higher invariant is the comparison between
`complete then reduce` and `reduce then complete`, not raw Witt index. This is attacked in the
PCCG field card.

## Proof

Let `R=rad(q)` and let `W=f(K) subset B`. Injectivity of `f|U` gives `dim W=dim K`.

Under `(2)`, `W` is totally isotropic. Pass to the nondegenerate Hermitian quotient `Z/R`, whose
signature is `(p,s)` with `s=ind_-(q)`. The image of `W` is totally isotropic. Projection to a
maximal negative subspace is injective on any totally isotropic subspace after quotienting its
intersection with `R`: a vector in the kernel would lie in the positive subspace and have zero
norm, hence vanish. Therefore

\[
 \dim W-\dim(W\cap R)\le s.
\]

Since `dim(W cap R)<=dim R`, this proves `(4)`. Under `(5)`, `W subset B subset R`, so injectivity
gives `dim K=dim W<=dim R`, proving `(6)`.

For `(8)`, both forms are nondegenerate by evaluation. Both coordinate summands pair to zero with
themselves and pair perfectly with one another. They are therefore complementary Lagrangians for
`omega` and maximal totally isotropic subspaces for `h`. Choosing a real basis `e_i` of
`K_{H,R}` and dual basis `epsilon_i`, the vectors `e_i+epsilon_i` and `e_i-epsilon_i` diagonalize
`h` with opposite signs. Hence its real signature is `(2k,2k)`, `k=dim_C K_H`. The underlying
real form of a Hermitian target has negative index and radical dimension twice their complex
values. An injective isometry sends the `2k`-dimensional real isotropic half into a totally
isotropic target subspace, so the real Witt bound, divided by two, proves `(9)`.
All claims are independent of RH. `[PROVED HERE, PENDING HOSTILE REVIEW]`

## Live arithmetic consequence

For a finite prime set `F`, the valuation coframe makes

\[
 U_F=\operatorname{span}\{[u_p]:p\in F\}
\]

have dimension `|F|`. If a proposed source-to-physical chain realization is injective on chosen
prime cycle representatives, kills all their homology classes, and its target boundaries are
isotropic for a form satisfying the published Stokes bound `ind_-+nullity<=1`, then `|F|<=1`.
If the form descends to homology and has radical zero, it cannot kill even one injected prime
class. Therefore no **injective isometric** realization of two prime directions can already be the
published one-port Stokes realization. A regular quotient can evade the bound, so a literal route
consequence additionally requires the topology and admissibility of that quotient.

This is an obstruction to a candidate comparison architecture, not an RH theorem and not proof
that the literal published Stokes form already satisfies `(1)` for the missing comparison.

## External-parent audit targets

- Witt decomposition and maximal totally isotropic dimension;
- duality between kernel and cokernel of transpose;
- Pontryagin-space boundary relations;
- relative Calabi--Yau/Lagrangian functors;
- anomaly inflow and finite-index boundary modes.

## Gates

- [x] 0 -> 1: exact source-pure statement, attack, and anti-circularity gate
- [x] paper proof written including maximal-isotropic bound and conditional prime corollary
- [x] hostile corpus audit across at least eight independent organs
- [x] external primary-source collision audit
- [ ] 1 -> 2: separate proved local theorem from falsified singularity inference, then copy exact
  theorem and counterexample to Stage 2
- [ ] promote only exact theorem; retain common-field interpretation in Stage 1
- [ ] no Lean until paper proof and hostile review close

## No-go closure

- **Exact killing theorem/mechanism:** Loop A is routine finite duality; Loop C would require the
  RH-bearing nullhomology premise.
- **Strongest positive survivor:** canonical hyperbolic cotangent anomaly double `(7)--(9)`,
  quantitative rank--inertia/coframe anomaly bounds `(4)` and `(6)`, and explicit regular
  coisotropic escape `(11)`.
- **New insight:** one-port Lorentz/Stokes geometry cannot be an injective isometric copy of the
  all-prime anomaly double, but finite-dimensional rank alone does not obstruct regular reduction.
  Source-selected completion can: reduction and completion need not commute.
- **Status:** local theorem and counterexample paper-proved; literal Stokes comparison conditional;
  no Lean written.

## Log

- 2026-08-09 — opened after CMR anti-regression audit; finite duality demoted to parent law and
  rank--inertia coupling selected as active claim.
- 2026-08-09 — separated boundary-isotropic and homological hypotheses, closed both Witt bounds,
  and identified exactification's canonical hyperbolic law--observer double. The finite double is
  parent geometry; its all-prime versus one-port incompatibility is the new cross-organ theorem
  under audit.
- 2026-08-09 — hostile literature audit killed the inference from large Witt index to singular
  reduction using the regular quotient `(11)`. Pivoted higher to the completion--reduction
  commutator, where the literal prime augmentation has different outcomes in `ell^1` and `ell^2`.
