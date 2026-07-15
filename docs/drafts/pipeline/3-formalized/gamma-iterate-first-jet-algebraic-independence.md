# Algebraic independence of the complete first-jet Gamma-iterate tower

- **ID:** `gamma-iterate-first-jet-algebraic-independence`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scientific status:** `[PROVEN IN LEAN] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The countable family

  \[
    z,\ \Gamma(z),\Gamma'(z),\
    \Gamma^{\circ2}(z),(\Gamma^{\circ2})'(z),\ldots
  \]

  is algebraically independent over `ℂ`.

## Goal

Prove the first genuinely joint differential layer beyond algebraic independence of the iterate
values.  Equivalently, every finite positive-depth prefix has differential transcendence visible
simultaneously in its value and first derivative.

## Factorial boundary and the decisive grading

Put `F_j=Γ^{∘j}`, `s_n=(-1)^(n+1)/n!`, and

\[
  g_n(x)=\Gamma(-n+s_nx).
\]

Then, locally away from zero,

\[
  g_n\to M=-1/x,
  \qquad g_n'\to M'=M^2,
\]

and for every `j ≥ 1`,

\[
  F_{j+1}(-n+s_nx)=F_j(g_n(x)),\qquad
  s_nF_{j+1}'(-n+s_nx)=F_j'(g_n(x))g_n'(x).
\]

The ungraded limiting evaluation has the single base-germ equation

\[
  R(Y_0,Y_1)=Y_1-Y_0^2.
\]

and its complete kernel is the principal ideal `(R)`.  However, `R` is inhomogeneous in raw
derivative degree: `Y₁` has derivative degree one while `Y₀²` has derivative degree zero.  Therefore
the boundary exponent map is injective on every fixed derivative-homogeneous slice.  Taking maximal
total derivative degree before the boundary limit removes the Riccati kernel completely.

## Transverse harmonic residue `[PROVEN IN LEAN]`

Put `a_n=s_nH_n`.  The exact pole factorization and the shifted digamma recurrence give, for every
fixed `x≠0`,

\[
  \frac{\Gamma(-n+s_nx)^{-1}+x}{a_n}\longrightarrow x^2,
  \qquad
  \frac{s_n\psi(-n+s_nx)+x^{-1}}{a_n}\longrightarrow1.
\]

Writing `h_n=Γ(-n+s_nx)^{-1}` gives the exact identity

\[
  g_n'-g_n^2=\frac{s_n\psi(-n+s_nx)h_n-1}{h_n^2}.
\]

Consequently

\[
  \frac{g_n'-g_n^2}{s_nH_n}\longrightarrow2M=-2/x.        \tag{1}
\]

The pole-germ residue is also exact:

\[
  \lim_{x\to0,\,x\ne0}x(g_n'-g_n^2)=-2s_n\psi(n+1),
  \qquad \frac{-2s_n\psi(n+1)}{s_nH_n}\to-2.
\]

Thus `(1)` is a canonical nonzero direction transverse to the complete first-jet boundary kernel,
not merely a formal Taylor prediction.

## Inductive dominant-symbol argument `[PROVEN IN LEAN]`

Given a finite polynomial relation, split it only by:

1. factorial derivative degree;
2. pole-index polynomial degree from the `z` coordinate;

After evaluation at `-n+s_nx`, multiplying every derivative by `s_n`, and dividing by the maximal
factorial and point scale, all lower derivative and point grades vanish.  The surviving polynomial
is derivative-homogeneous, so its boundary image is nonzero.  It gives a relation in

\[
  x,F_1(x),F_1'(x),\ldots,F_k(x),F_k'(x),
\]

contradicting the induction hypothesis.  The base case is Gamma's local differential rigidity at
jet order one.  The harmonic residue is a strictly finer transverse theorem, but it is not needed
for algebraic independence because the leading derivative symbol never enters the Riccati kernel.

## Lean formalization

`formal/GaloisForLFunctions/HTGeometry/GammaFactorialFirstJetBoundary.lean` defines the exact
Riccati defect of the Gamma zoom and proves
`tendsto_gammaFactorialFirstJetDefect_zero`.  Thus Lean verifies that the holomorphic first-jet
limit lands on `M'=M²`; the theorem uses convergence of derivatives, not an invalid differentiation
of a pointwise limit.

`GammaFactorialHarmonicResidue.lean` proves the exact pole-germ residue and its normalized nonzero
limit.  `GammaFactorialMovingHarmonicResidue.lean` proves the reciprocal-Gamma and scaled-digamma
first harmonic corrections and the moving theorem `(1)` for every `x≠0`.  Direct compilation,
individual Lake targets, and headline axiom audits pass; only `propext`, `Classical.choice`, and
`Quot.sound` occur.

`GammaFirstJetRiccatiKernel.lean` proves over every commutative coefficient ring that substitution
`Z↦W²` has kernel exactly the principal ideal `(Z-W²)`.  It also extracts the maximal boundary
multiplicity of every nonzero relation and a quotient with nonzero boundary substitution.  This
allows the coefficient ring to contain all earlier iterate jets and closes the principal-kernel
normal-form obligation.

`GammaIterationFirstJetBoundary.lean` proves coordinatewise convergence of the complete scaled
first-jet tail.  `GammaIterationFirstJetDominantBoundary.lean` proves injectivity of the boundary
map on fixed derivative degree and constructs the nonzero dominant tail polynomial.
`GammaIterationFirstJetDominantDescent.lean` proves the exact normalized relation and its finite
limit.  `GammaIterationFirstJetLocalIndependence.lean` supplies analytic propagation and the
depth-one base case.  `GammaIterationFirstJetAlgebraicIndependence.lean` proves the induction and
the countable capstone

`algebraicIndependent_gammaIterateInfiniteFirstJetFamily`.

Direct compilation and the individual module target pass.  The formal lint gate passes, and the
headline axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.  No full build
and no numerical computation were used.

## Novelty and significance gate

Exact searches found no theorem on algebraic independence of the joint first jets of Euler-Gamma
self-iterates.  The result would be the first infinite-rank differential shadow of the iterate
tower, strictly stronger than independence of values and separate hypertranscendence.  It remains
below the full differential-independence conjecture and is not by itself assessed as
Fields-Medal-level.

## Gates

- [x] 0 → 1 in-progress: exact statement, principal boundary kernel, transverse residue, and
  falsifier isolated
- [x] 1 → 2 fully-proven: dominant derivative-symbol descent complete
- [x] 2 → 3 formalized: countable capstone in Lean with targeted validation
- [ ] 3 → 4 publication-ready: specialist priority and proof audit complete

## Log

- 2026-07-15 — split from the full differential-independence card after identifying that the
  first-jet reciprocal kernel is principal and the harmonic Gamma deformation is transverse to it.
- 2026-07-15 — formalized the exact first-jet Riccati boundary collapse in
  `GammaFactorialFirstJetBoundary.lean`; direct compilation and its individual Lake target pass.
- 2026-07-15 — formalized the exact pole-germ residue in
  `GammaFactorialHarmonicResidue.lean` and the fixed-point moving harmonic limit
  `(g_n'-g_n^2)/(s_n H_n) → -2/x` in `GammaFactorialMovingHarmonicResidue.lean`; direct checks,
  narrow module builds, and axiom audits pass without a full build or numerical computation.
- 2026-07-15 — formalized the complete reciprocal first-jet kernel and maximal Riccati-multiplicity
  normal form over arbitrary commutative coefficient rings in `GammaFirstJetRiccatiKernel.lean`;
  direct compilation, its narrow target, and axiom audit pass.
- 2026-07-15 — discovered that the Riccati kernel is invisible to the maximal raw derivative symbol,
  replacing the four-grade harmonic valuation by a two-grade factorial/point descent.  Formalized
  the complete finite-depth induction and the countable first-jet algebraic-independence theorem;
  direct compilation, the single-module build, lint, and headline axiom audit pass.
