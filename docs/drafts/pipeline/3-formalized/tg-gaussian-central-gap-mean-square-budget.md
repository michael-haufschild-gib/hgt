# TG — Mean-square form of the central Gaussian budget

- **ID:** TG-L2-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional equivalence)
- **Statement:** G(u) = P(e^{-u}) − C(e^{-u}) (central Gaussian gap in the log-damping variable). TFAE:
  (1) RH; (2) ∃K ∀U≥0: ∫₀^U G² ≤ K(U+1); (3) ∀ε>0 ∃K ∀U≥0: ∫₀^U G² ≤ K e^{εU}.
  Also: (∀τ>0: ∫₀^∞ |G| e^{-τu} < ∞) ⇒ RH.

## Proof
(1⇒2) Gaussian Cramér identity (TG-BOHR-4): Cesàro means of G² converge ⇒ linear growth.
(2⇒3) U+1 ≤ (1+ε⁻¹)e^{εU}.
(3⇒1) Unit-block Cauchy–Schwarz: ∫_k^{k+1}|G| ≤ √K e^{ε(k+1)/2}, geometric sum ⇒ |G|e^{-τu} ∈ L¹ for τ > ε/2;
then max(G,0) e^{-τu} ∈ L¹ and the one-sided Landau law `xi_ne_zero_of_gaussianPrimeExcess` (σ=½, a=0, B=0)
gives ξ ≠ 0 on Re z > ½.

## Lean
`RHTower/GaussianCentralGapMeanSquareBudget.lean` (235 lines), wired after GaussianWeightedGapExtremalParseval.
`integral_abs_sq_le_integral_sq_unit`, `integrableOn_abs_mul_exp_of_integral_sq_le`,
`exists_integral_le_mul_add_one_of_tendsto`, `riemannHypothesis_of_integrableOn_abs_gaussianCentralGapLog`,
`riemannHypothesis_tfae_gaussianCentralGapMeanSquare`. Axioms [propext, Classical.choice, Quot.sound].

## Reading
The TG budget only needs to be proved on average in L² with subexponential loss: e^{εU} slack against the
true linear growth. An off-line zero at Θ > ½ forces ∫₀^U G² ≳ e^{(Θ−½)U} (Parseval/Bessel at the
extremal line), so the L² gate is exactly the "no exponential L² growth" condition. Producer target:
a bilinear (large-sieve/Montgomery–Vaughan type) bound for Σ_{m,n} Λ(m)Λ(n)(mn)^{-1/2} K_U(m,n) with
subexponential loss.
