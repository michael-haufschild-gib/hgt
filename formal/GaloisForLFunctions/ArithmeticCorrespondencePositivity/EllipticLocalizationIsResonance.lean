import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair

/-!
# Elliptic localization is resonance

B3.25 asks for a localizing carrier whose local symmetry at an off-line pair is not hyperbolic. On
real even tests the fibre at a point `ρ = σ + iγ` is `z = ĝ(ρ)` with local form `2 Re(z²)`, and the
symmetric dilation by a scale `a > 1` — a prime's Hecke operator for `a = p`, the archimedean flow
for real `a` — acts by the symbol `w_a = a^{ρ−½} + a^{½−ρ}` (P4). This file classifies the
correspondences that can be elliptic there.

* **Resonance** (`symHeckeSymbol_im_ne_zero_iff`, `sin_mul_log_eq_zero_iff`). At an off-line point
  the symbol of `a` is real iff `γ log a ∈ πℤ`, i.e. `a` lies in the discrete group
  `exp((π/γ)ℤ)`.
* **One non-resonant scale is blindness** (`eq_zero_of_nonresonant_scale`): if a carrier is closed
  under the symmetric dilation of a single scale with `γ log a ∉ πℤ` and its local form is
  nonnegative there, its fibre vanishes.
* **The archimedean flow is blind** (`eq_zero_of_archimedean_closed`): a carrier closed under the
  symmetric dilations of all scales `a > 1` is blind at every non-real off-line point; so is one
  closed under two primes (P4).
* **Resonant carriers have elliptic survivors** (`resonant_survivor`): if every closure scale is
  resonant, positivity asks only `Re z² ≥ 0`, and the fibre `z = 1` is nonzero, positive and not
  isotropic.

So within correspondence-closed carriers, elliptic localization at a non-real off-line point
happens exactly when every correspondence used lies in the resonant group `exp((π/γ)ℤ)` of that
point. This group contains at most one prime (P4), depends on the unknown height `γ`, and excludes
every continuous family. A carrier with elliptic localization must therefore be closed under
almost no multiplicative symmetry: its localization has to come from a non-multiplicative
operation.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- **Resonance**: at an off-line point the symbol of `a > 1` is non-real iff `γ log a ∉ πℤ`. -/
theorem symHeckeSymbol_im_ne_zero_iff {a : ℝ} (ha : 1 < a) {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) :
    (symHeckeSymbol a ρ).im ≠ 0 ↔ Real.sin (ρ.im * Real.log a) ≠ 0 := by
  rw [Ne, symHeckeSymbol_im_eq_zero_iff ha]
  tauto

/-- The resonant scales form the discrete group `exp((π/γ)ℤ)`. -/
theorem sin_mul_log_eq_zero_iff {γ : ℝ} (hγ : γ ≠ 0) {a : ℝ} :
    Real.sin (γ * Real.log a) = 0 ↔ ∃ k : ℤ, Real.log a = k * Real.pi / γ := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by field_simp; linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; field_simp⟩

/-- **One non-resonant scale forces blindness** of a real fibre at an off-line point. -/
theorem eq_zero_of_nonresonant_scale {a : ℝ} (ha : 1 < a) {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2)
    (hres : Real.sin (ρ.im * Real.log a) ≠ 0) {z : ℂ}
    (h : ∀ x y : ℝ, 0 ≤ localForm ((x + y * symHeckeSymbol a ρ) * z)
      (conj ((x + y * symHeckeSymbol a ρ) * z))) : z = 0 :=
  eq_zero_of_symCyclic_nonneg ((symHeckeSymbol_im_ne_zero_iff ha hρ).mpr hres) h

/-- A non-real point has a non-resonant scale: `a = exp(π/(2|γ|))` gives `γ log a = ±π/2`. -/
theorem exists_nonresonant_scale {γ : ℝ} (hγ : γ ≠ 0) :
    ∃ a : ℝ, 1 < a ∧ Real.sin (γ * Real.log a) ≠ 0 := by
  have hγa : 0 < |γ| := abs_pos.mpr hγ
  refine ⟨Real.exp (Real.pi / (2 * |γ|)), ?_, ?_⟩
  · exact Real.one_lt_exp_iff.mpr (by positivity)
  · rw [Real.log_exp]
    rcases lt_or_gt_of_ne hγ with h | h
    · rw [abs_of_neg h, show γ * (Real.pi / (2 * -γ)) = -(Real.pi / 2) by field_simp, Real.sin_neg,
        Real.sin_pi_div_two]
      norm_num
    · rw [abs_of_pos h, show γ * (Real.pi / (2 * γ)) = Real.pi / 2 by field_simp,
        Real.sin_pi_div_two]
      norm_num

/-- **The archimedean flow is blind**: a real fibre with nonnegative local form under the symmetric
dilations of every scale `a > 1` vanishes at each non-real off-line point. -/
theorem eq_zero_of_archimedean_closed {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) (hγ : ρ.im ≠ 0) {z : ℂ}
    (h : ∀ a : ℝ, 1 < a → ∀ x y : ℝ, 0 ≤ localForm ((x + y * symHeckeSymbol a ρ) * z)
      (conj ((x + y * symHeckeSymbol a ρ) * z))) : z = 0 := by
  obtain ⟨a, ha, hres⟩ := exists_nonresonant_scale hγ
  exact eq_zero_of_nonresonant_scale ha hρ hres (h a ha)

/-- **Resonant carriers have elliptic survivors**: if every scale in `S` is resonant at the
off-line point `ρ`, the fibre `z = 1` is positive under all of them and `2 Re(1²) = 2 > 0`. -/
theorem resonant_survivor {S : Set ℝ} (hS : ∀ a ∈ S, 1 < a) {ρ : ℂ}
    (hres : ∀ a ∈ S, Real.sin (ρ.im * Real.log a) = 0) :
    (∀ a ∈ S, ∀ x y : ℝ, 0 ≤ localForm ((x + y * symHeckeSymbol a ρ) * 1)
      (conj ((x + y * symHeckeSymbol a ρ) * 1))) ∧ 0 < localForm 1 (conj 1) := by
  refine ⟨fun a ha x y => ?_, ?_⟩
  · have hw : (symHeckeSymbol a ρ).im = 0 :=
      (symHeckeSymbol_im_eq_zero_iff (hS a ha) ρ).mpr (Or.inr (hres a ha))
    exact (symCyclic_nonneg_iff_of_im_eq_zero hw).mpr (by norm_num) x y
  · rw [localForm_conj]; norm_num

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
