# Algebraic independence of the complete first-jet Gamma-iterate tower

- **ID:** `gamma-iterate-first-jet-algebraic-independence`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Scientific status:** `[CONJECTURE] [PAPER PROOF IN PROGRESS] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
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

## Factorial boundary and its exact kernel

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

Assuming first-jet independence through depth `k`, Möbius pullback makes the limiting evaluation
map injective except for the single base-germ equation

\[
  R(Y_0,Y_1)=Y_1-Y_0^2.
\]

Thus the entire failure of leading factorial descent is the principal ideal `(R)`.

## Transverse harmonic residue

The exact pole factorization gives the first subleading coefficient

\[
  \Gamma(-n+t)=\frac{r_n}{t}+r_n\psi(n+1)+O_n(t),
  \qquad r_n=(-1)^n/n!,
\]

and `r_n=-s_n`.  Since `ψ(n+1)=H_n-γ`, factorial decay gives
`s_n ψ(n+1)→0` while `|ψ(n+1)|→∞`.  The normalized germs therefore satisfy

\[
  \frac{g_n-M}{s_n\psi(n+1)}\to-1,
  \qquad
  \frac{g_n'-M'}{s_n\psi(n+1)}\to0,
\]

locally uniformly away from zero.  Consequently

\[
  \frac{g_n'-g_n^2}{s_n\psi(n+1)}\to2M=-2/x.              \tag{1}
\]

Equation `(1)` is transverse to the complete first-jet boundary kernel.

## Inductive valuation argument

Given a finite polynomial relation, split it by:

1. factorial derivative degree;
2. pole-index polynomial degree from the `z` coordinate;
3. multiplicity along the principal kernel `(R)`;
4. harmonic degree.

After evaluation at `-n+s_nx`, a slice of derivative deficit `d` and kernel multiplicity `m`
has factorial order `d+m`.  At fixed factorial order, polynomial powers of `n` dominate; at fixed
polynomial degree, the largest harmonic power dominates because `ψ(n+1)~log n`.  Dividing by the
lexicographically dominant scale and using `(1)` leaves a nonzero polynomial in

\[
  x,F_1(x),F_1'(x),\ldots,F_k(x),F_k'(x),
\]

contradicting the induction hypothesis.  The base case is Hölder hypertranscendence over `ℂ(z)`.

## Open proof obligations

- Prove the two locally uniform normalized limits preceding `(1)` from the exact reciprocal-Gamma
  product; pointwise Laurent coefficients alone do not give the required moving-pole uniformity.
- State and prove the finite lexicographic residue lemma without hiding cancellation between equal
  factorial and pole-index grades.
- Formalize the principal-kernel normal form for the first reciprocal jet.
- Attack the proof for a cancellation between different derivative deficits with equal total
  factorial order.  Such a cancellation that survives harmonic grading falsifies the argument.

## Lean foundation `[PARTIAL]`

`formal/GaloisForLFunctions/HTGeometry/GammaFactorialFirstJetBoundary.lean` defines the exact
Riccati defect of the Gamma zoom and proves
`tendsto_gammaFactorialFirstJetDefect_zero`.  Thus Lean verifies that the holomorphic first-jet
limit lands on `M'=M²`; the theorem uses convergence of derivatives, not an invalid differentiation
of a pointwise limit.  The harmonic normalization and transverse nonzero residue `(1)` remain open.

## Novelty and significance gate

Exact searches found no theorem on algebraic independence of the joint first jets of Euler-Gamma
self-iterates.  The result would be the first infinite-rank differential shadow of the iterate
tower, strictly stronger than independence of values and separate hypertranscendence.  It remains
below the full differential-independence conjecture and is not by itself assessed as
Fields-Medal-level.

## Gates

- [x] 0 → 1 in-progress: exact statement, principal boundary kernel, transverse residue, and
  falsifier isolated
- [ ] 1 → 2 fully-proven: uniform residue and lexicographic induction complete
- [ ] 2 → 3 formalized: countable capstone in Lean with targeted validation
- [ ] 3 → 4 publication-ready: specialist priority and proof audit complete

## Log

- 2026-07-15 — split from the full differential-independence card after identifying that the
  first-jet reciprocal kernel is principal and the harmonic Gamma deformation is transverse to it.
- 2026-07-15 — formalized the exact first-jet Riccati boundary collapse in
  `GammaFactorialFirstJetBoundary.lean`; direct compilation and its individual Lake target pass.
