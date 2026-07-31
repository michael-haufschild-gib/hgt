# Unitary-flow Riesz-eigenfunctional purity

- **ID:** `deninger-unitary-flow-riesz-eigenfunctional-purity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_UNITARY_FLOW_RIESZ_EIGENFUNCTIONAL_PURITY`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** a nonzero Hodge-bounded transpose eigenfunctional of
  the centered time-one unitary flow has unit-modulus eigencharacter;
  if that character is \(\exp(\rho-\tfrac12)\), then
  \(\operatorname{Re}\rho=\tfrac12\).

## Goal

Remove the unnecessary generator-domain hypothesis from the
RH-bearing spectral comparison.  Deninger's Hodge theory need only
make each order-zero Meyer evaluation functional bounded and nonzero
on the completed arithmetic cohomology.  Unitarity of one nonzero
flow time then forces the critical line.

## Theorem

Let \(H\) be a complex Hilbert space, let \(V:H\to H\) be unitary, and
let \(0\ne y\in H\).  Put
\[
  \ell_y(x)=\langle y,x\rangle .
\]
Suppose that for some \(c\in\mathbb C\)
\[
  \ell_y(Vx)=c\,\ell_y(x) \qquad (x\in H).                 \tag{1}
\]
Then \(|c|=1\).

Consequently, if
\[
  c=\exp(\rho-\tfrac12),                                  \tag{2}
\]
then
\[
  \operatorname{Re}\rho=\tfrac12.                         \tag{3}
\]

## Proof

`[PROVED HERE]`

Because \(V\) is a surjective isometry, precomposition by \(V\)
preserves the operator norm of every bounded functional:
\[
  \|\ell_y\circ V\|=\|\ell_y\|.
\]
Equation `(1)` also gives
\[
  \|\ell_y\circ V\|=|c|\,\|\ell_y\|.
\]
Riesz representation and \(y\ne0\) imply
\(\|\ell_y\|=\|y\|>0\).  Cancelling this positive factor proves
\(|c|=1\).

For completeness, the same cancellation can be made without operator
norms.  Apply `(1)` to \(V^{-1}y\):
\[
  \langle y,y\rangle
  =c\langle y,V^{-1}y\rangle
  =c\langle Vy,y\rangle.
\]
Taking the conjugate of `(1)` at \(y\) gives
\[
  \langle Vy,y\rangle
  =\bar c\langle y,y\rangle.
\]
Thus
\[
  \langle y,y\rangle
  =c\bar c\langle y,y\rangle.
\]
Since \(\langle y,y\rangle\ne0\), \(c\bar c=1\), hence \(|c|=1\).

Finally, `(2)` and the standard identity
\[
  |\exp z|=\exp(\operatorname{Re}z)
\]
give
\[
  1=|c|
   =\exp(\operatorname{Re}\rho-\tfrac12).
\]
Injectivity of the real exponential proves `(3)`.

## Deninger consequence

Assume the source-built positive Hodge completion
\(\mathcal H^1_{\mathrm{arith}}\) carries the centered time-one flow
\[
  V=\exp(\Theta-\tfrac12)
\]
as a unitary operator.  For a nontrivial zeta zero \(\rho\), suppose
Meyer's order-zero evaluation functional:

1. pulls back nontrivially to source arithmetic cohomology;
2. is bounded for the Hodge norm, with nonzero Riesz vector \(y_\rho\);
3. obeys the source-proved transpose character law
   \[
   \langle y_\rho,Vx\rangle
   =\exp(\rho-\tfrac12)\langle y_\rho,x\rangle .
   \]

The theorem forces \(\operatorname{Re}\rho=\tfrac12\).  This uses no
zero to construct the coefficient object, Hodge norm, cup product, or
flow.

Order-zero functionals suffice for RH.  Higher Mellin jets remain
necessary only for the stronger comparison of generalized blocks,
Jordan filtrations, and zero multiplicities.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and proof route
- [x] 1 → 2 fully-proven: complete proof with no open dependency
- [x] 2 → 3 formalized: Lean theorem and RH corollary build unconditionally
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-27 — Proved time-one unitary form.  This strictly weakens
  the earlier sufficient infinitesimal criterion: no membership of
  the Riesz vector in the closed generator domain is required.

## Unconditional Lean formalization

`formal/GaloisForLFunctions/RHTower/DeningerUnitaryFlowRieszPurity.lean`, wired into the
`RHTower` umbrella.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `norm_eq_one_of_unitary_transposeEigenfunctional` — the theorem: for `V : H ≃ₗᵢ[ℂ] H` and
  `y ≠ 0` with `⟪y, V x⟫ = c ⟪y, x⟫` for all `x`, one has `‖c‖ = 1`.  The proof is the card's
  second, norm-free route: evaluating `(1)` at `V⁻¹ y` and conjugating `(1)` at `y` gives
  `⟪y,y⟫ = c · conj c · ⟪y,y⟫`, and `⟪y,y⟫ ≠ 0` cancels.
- `re_eq_half_of_norm_exp_eq_one` — `(2) ⇒ (3)` via `‖exp z‖ = exp (Re z)` and injectivity of the
  real exponential.
- `re_eq_half_of_unitary_transposeEigenfunctional` — the two combined: a nonzero transpose
  eigenfunctional with centered exponential character `exp (ρ - 1/2)` forces `Re ρ = 1/2`.
- `riemannHypothesis_of_unitaryFlow_rieszEigenfunctional` — the Deninger consequence: realizing
  every nontrivial zeta zero by a nonzero Riesz vector satisfying the transpose character law
  yields mathlib's `RiemannHypothesis`.

The hypothesis is exactly a unitary time-one flow; no generator, no domain condition, and no
differentiability appears.  This is strictly weaker than the corpus's earlier infinitesimal
criterion `RHTower.deningerClosedWeightOne_rieszEigenfunctional_re_eq_half`
(`DeningerArithmeticRieszEigenfunctionalPurity.lean`), which additionally requires the Riesz
vector to lie in the closed domain of the generator — the exact hypothesis this card removes.
