import Mathlib

/-!
# Source three-term Hodge purity

A positive flow-natural anti-linear Hodge operator on the middle cohomology of a source
three-term arithmetic complex forces every eigenvalue of the transverse flow to have real part
one half.

The mechanism is a two-line scalar cancellation.  Conjugate-linearity turns an eigenvector for
`λ` into an eigenvector for `conj λ` after applying the Hodge operator, and the weight-one law
for the cup–trace pairing evaluated on that pair gives `λ + conj λ = 1`.  Positivity is used
only to know that the pairing does not vanish on the pair.

Nothing here constructs the complex, the pairing, the Hodge operator, or the spectral
comparison; they are hypotheses.  The final corollary is the one-way implication: if every
nontrivial zeta zero is realized as an eigenvalue of the transverse flow, the Riemann hypothesis
follows.
-/

namespace RHTower

namespace DeningerArithmeticThreeTermHodge

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- Middle-degree Hodge data on a source three-term arithmetic complex: a transverse flow, a
cup–trace pairing of weight one, and a positive flow-natural anti-linear Hodge operator. -/
structure HodgeData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  /-- The transverse flow generator on middle cohomology. -/
  theta : H →ₗ[ℂ] H
  /-- The descended cup–trace pairing. -/
  cup : H →ₗ[ℂ] H →ₗ[ℂ] ℂ
  /-- The anti-linear Hodge operator. -/
  hodge : H →ₗ⋆[ℂ] H
  /-- Weight-one flow naturality of the pairing. -/
  weightOne : ∀ x y, cup (theta x) y + cup x (theta y) = cup x y
  /-- The Hodge operator is an almost complex structure. -/
  hodgeSq : ∀ x, hodge (hodge x) = -x
  /-- The Hodge operator commutes with the flow. -/
  commutes : ∀ x, theta (hodge x) = hodge (theta x)
  /-- Positivity of the associated hermitian form. -/
  positive : ∀ x : H, x ≠ 0 → 0 < (cup x (hodge x)).re

variable (D : HodgeData H)

/-- The Hodge operator carries a `λ`-eigenvector to a `conj λ`-eigenvector. -/
theorem theta_hodge_eigenvector {x : H} {lam : ℂ} (heig : D.theta x = lam • x) :
    D.theta (D.hodge x) = (starRingEnd ℂ) lam • D.hodge x := by
  rw [D.commutes, heig, map_smulₛₗ]

/-- The pairing does not annihilate a nonzero vector against its Hodge image. -/
theorem cup_hodge_ne_zero {x : H} (hx : x ≠ 0) : D.cup x (D.hodge x) ≠ 0 := by
  intro h
  have hpos := D.positive x hx
  rw [h] at hpos
  simp at hpos

/-- **Hodge purity.**  Every eigenvalue of the transverse flow has real part one half. -/
theorem theta_eigenvalue_re_eq_half {x : H} {lam : ℂ} (hx : x ≠ 0)
    (heig : D.theta x = lam • x) :
    lam.re = 1 / 2 := by
  have hBne : D.cup x (D.hodge x) ≠ 0 := cup_hodge_ne_zero D hx
  have hJeig := theta_hodge_eigenvector D heig
  have hw := D.weightOne x (D.hodge x)
  rw [heig, hJeig, map_smul, LinearMap.smul_apply, LinearMap.map_smul] at hw
  have hsum : lam + (starRingEnd ℂ) lam = 1 := by
    refine mul_right_cancel₀ hBne ?_
    rw [one_mul]
    linear_combination hw
  have htwo : ((2 * lam.re : ℝ) : ℂ) = 1 := by
    rw [← Complex.add_conj]
    exact hsum
  have h2 : (2 : ℝ) * lam.re = 1 := by exact_mod_cast htwo
  linarith

/-- Centered coordinate form: the eigenvalue is `1/2 + i z` for a real `z`. -/
theorem eigenvalue_eq_half_add_I_mul {x : H} {lam : ℂ} (hx : x ≠ 0)
    (heig : D.theta x = lam • x) :
    lam = 1 / 2 + Complex.I * (lam.im : ℂ) := by
  have hre := theta_eigenvalue_re_eq_half D hx heig
  apply Complex.ext <;> simp [hre]

/-- **One-way spectral comparison.**  If every nontrivial zero of the Riemann zeta function is
realized as an eigenvalue of the transverse flow on the middle cohomology of a source three-term
complex carrying positive flow-natural Hodge data, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_zetaZero_eigenvector
    (hspec : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
      ∃ x : H, x ≠ 0 ∧ D.theta x = s • x) :
    RiemannHypothesis := by
  intro s hs htriv hone
  obtain ⟨x, hx, heig⟩ := hspec s hs htriv hone
  exact theta_eigenvalue_re_eq_half D hx heig

end DeningerArithmeticThreeTermHodge

end RHTower
