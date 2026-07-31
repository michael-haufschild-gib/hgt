import Mathlib

/-!
# Unitary-flow Riesz-eigenfunctional purity

A nonzero Riesz vector whose functional is a transpose eigenfunctional of a unitary operator has
unit-modulus eigencharacter.  No generator, no domain condition, and no differentiability is
involved: the time-one flow alone suffices.

Applying the eigenfunctional law to the preimage of the Riesz vector and conjugating it at the
Riesz vector itself gives `⟪y, y⟫ = c · conj c · ⟪y, y⟫`, and `⟪y, y⟫ ≠ 0` cancels.  If the
character is the centered exponential `exp (ρ - 1/2)`, unit modulus is exactly
`Re ρ = 1/2`.

This strictly weakens the infinitesimal criterion of
`RHTower.deningerClosedWeightOne_rieszEigenfunctional_re_eq_half`, which additionally requires the
Riesz vector to lie in the closed domain of the generator.
-/

namespace RHTower

open Complex

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Unit-modulus eigencharacter.**  A nonzero transpose eigenfunctional of a unitary operator
has eigencharacter of modulus one. -/
theorem norm_eq_one_of_unitary_transposeEigenfunctional
    (V : H ≃ₗᵢ[ℂ] H) {y : H} (hy : y ≠ 0) {c : ℂ}
    (heigen : ∀ x : H, inner ℂ y (V x) = c * inner ℂ y x) :
    ‖c‖ = 1 := by
  have hyy : (inner ℂ y y : ℂ) ≠ 0 := inner_self_ne_zero.mpr hy
  -- evaluate the eigenfunctional law at the preimage of `y`
  have h1 : (inner ℂ y y : ℂ) = c * inner ℂ y (V.symm y) := by
    have h := heigen (V.symm y)
    rwa [V.apply_symm_apply] at h
  -- unitarity moves the inverse to the other side
  have h2 : (inner ℂ y (V.symm y) : ℂ) = inner ℂ (V y) y := by
    have h := V.inner_map_map y (V.symm y)
    rw [V.apply_symm_apply] at h
    exact h.symm
  -- conjugating the eigenfunctional law at `y`
  have h3 : (inner ℂ (V y) y : ℂ) = (starRingEnd ℂ) c * inner ℂ y y := by
    have h := heigen y
    have hc := congrArg (starRingEnd ℂ) h
    rw [inner_conj_symm, map_mul, inner_conj_symm] at hc
    exact hc
  have hkey : (inner ℂ y y : ℂ) = c * ((starRingEnd ℂ) c * inner ℂ y y) := by
    rw [h1, h2, h3]
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    refine mul_right_cancel₀ hyy ?_
    rw [one_mul]
    linear_combination -hkey
  have hnormSq : (Complex.normSq c : ℂ) = 1 := by
    rw [← Complex.mul_conj]
    exact hcc
  have hnormSq' : Complex.normSq c = 1 := by exact_mod_cast hnormSq
  have hsq : ‖c‖ ^ 2 = 1 := by
    rw [Complex.sq_norm]
    exact hnormSq'
  nlinarith [norm_nonneg c, hsq]

/-- Unit modulus of the centered exponential character is exactly the critical line. -/
theorem re_eq_half_of_norm_exp_eq_one {rho : ℂ} (h : ‖Complex.exp (rho - 1 / 2)‖ = 1) :
    rho.re = 1 / 2 := by
  rw [Complex.norm_exp] at h
  have h' : (rho - 1 / 2).re = 0 := by
    have := Real.exp_eq_one_iff (x := (rho - 1 / 2).re)
    exact this.mp h
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at h'
  linarith

/-- **Unitary-flow Riesz purity.**  A nonzero transpose eigenfunctional of a unitary operator with
centered exponential character forces the character exponent onto the critical line. -/
theorem re_eq_half_of_unitary_transposeEigenfunctional
    (V : H ≃ₗᵢ[ℂ] H) {y : H} (hy : y ≠ 0) {rho : ℂ}
    (heigen : ∀ x : H, inner ℂ y (V x) = Complex.exp (rho - 1 / 2) * inner ℂ y x) :
    rho.re = 1 / 2 :=
  re_eq_half_of_norm_exp_eq_one
    (norm_eq_one_of_unitary_transposeEigenfunctional V hy heigen)

/-- **One-way spectral comparison.**  If every nontrivial zero of the Riemann zeta function
supplies a nonzero Riesz vector whose functional is a transpose eigenfunctional of the centered
time-one unitary flow with character `exp (ρ - 1/2)`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_unitaryFlow_rieszEigenfunctional
    (V : H ≃ₗᵢ[ℂ] H)
    (hspec : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
      ∃ y : H, y ≠ 0 ∧
        ∀ x : H, inner ℂ y (V x) = Complex.exp (s - 1 / 2) * inner ℂ y x) :
    RiemannHypothesis := by
  intro s hs htriv hone
  obtain ⟨y, hy, heigen⟩ := hspec s hs htriv hone
  exact re_eq_half_of_unitary_transposeEigenfunctional V hy heigen

end

end RHTower
