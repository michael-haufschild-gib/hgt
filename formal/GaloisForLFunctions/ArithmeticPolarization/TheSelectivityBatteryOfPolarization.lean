import GaloisForLFunctions.ArithmeticPolarization.ThePolarizationLaw
import GaloisForLFunctions.ArithmeticPolarization.CouplingCollidesEvenly

/-!
# The selectivity battery of polarization

What the polarization mechanisms give on the fake curves.

* **The golden spectrum** `{φ, φ⁻¹}` (a real off-circle pair) and **the complex-fake spectrum**
  `{±2i, ±i/2}` (a complex quartet) are reflection-closed spectra (`goldenSpectrum`,
  `complexFakeSpectrum`). On both the Rosati form has a negative direction and the Frobenius does
  not preserve the collided form (`goldenSpectrum_fails`, `complexFakeSpectrum_fails`): neither
  form of the spectral model is a polarization with both properties.
* **Coupling hides even the real pair** (`golden_detDeg_neg_couple_nonneg`): the golden datum has
  the kernel count `deg(2 − F) = −1`, but every kernel count of every coupling of it is a modulus
  square. A coupling sees neither real pairs nor complex quartets by counting.
-/

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCastelnuovoSeveri ArithmeticCorrespondencePositivity

/-! ### The golden spectrum -/

theorem refl_ofReal {x : ℝ} : refl (x : ℂ) = ((x⁻¹ : ℝ) : ℂ) := by
  simp [refl, Complex.conj_ofReal]

/-- The golden spectrum `{φ, φ⁻¹}` with unit weights. -/
def goldenSpectrum : ReflSpectrum where
  S := {((Real.goldenRatio : ℝ) : ℂ), ((Real.goldenRatio⁻¹ : ℝ) : ℂ)}
  zero_not_mem := by
    simp [Real.goldenRatio_ne_zero]
  refl_mem β hβ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ ⊢
    rcases hβ with rfl | rfl
    · right; rw [refl_ofReal]
    · left; rw [refl_ofReal, inv_inv]
  m _ := 1
  m_pos _ _ := one_pos
  m_refl _ _ := rfl

theorem goldenSpectrum_not_unitary : ¬ ∀ β ∈ goldenSpectrum.S, ‖β‖ = 1 := by
  intro h
  have := h ((Real.goldenRatio : ℝ) : ℂ) (by simp [goldenSpectrum])
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.goldenRatio_pos] at this
  exact Real.one_lt_goldenRatio.ne' this

/-- **The golden spectrum fails both forms.** -/
theorem goldenSpectrum_fails :
    (¬ ∀ x : ℂ → ℂ, 0 ≤ (goldenSpectrum.rosatiForm x).re) ∧
      ¬ ∀ x : ℂ → ℂ, goldenSpectrum.collided (fun β => β * x β) = goldenSpectrum.collided x :=
  ⟨fun h => goldenSpectrum_not_unitary (goldenSpectrum.rosatiForm_nonneg_iff_unitary.mp h),
    fun h => goldenSpectrum_not_unitary (goldenSpectrum.collided_frob_invariant_iff_unitary.mp h)⟩

/-! ### The complex-fake spectrum -/

theorem refl_two_I : refl (2 * I) = I / 2 := by
  rw [refl]; refine inv_eq_of_mul_eq_one_right ?_
  rw [map_mul, Complex.conj_I, map_ofNat]; ring_nf; rw [Complex.I_sq]; ring

theorem refl_neg_two_I : refl (-(2 * I)) = -(I / 2) := by
  rw [refl]; refine inv_eq_of_mul_eq_one_right ?_
  rw [map_neg, map_mul, Complex.conj_I, map_ofNat]; ring_nf; rw [Complex.I_sq]; ring

theorem refl_I_div_two : refl (I / 2) = 2 * I := by
  rw [← refl_two_I, refl_refl]

theorem refl_neg_I_div_two : refl (-(I / 2)) = -(2 * I) := by
  rw [← refl_neg_two_I, refl_refl]

/-- The complex-fake spectrum `{2i, −2i, i/2, −i/2}` with unit weights. -/
def complexFakeSpectrum : ReflSpectrum where
  S := {2 * I, -(2 * I), I / 2, -(I / 2)}
  zero_not_mem := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      simpa using congrArg Complex.im h
  refl_mem β hβ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ ⊢
    rcases hβ with rfl | rfl | rfl | rfl
    · right; right; left; exact refl_two_I
    · right; right; right; exact refl_neg_two_I
    · left; exact refl_I_div_two
    · right; left; exact refl_neg_I_div_two
  m _ := 1
  m_pos _ _ := one_pos
  m_refl _ _ := rfl

theorem complexFakeSpectrum_not_unitary : ¬ ∀ β ∈ complexFakeSpectrum.S, ‖β‖ = 1 := by
  intro h
  have := h (2 * I) (by simp [complexFakeSpectrum])
  rw [norm_mul, Complex.norm_I, mul_one] at this
  norm_num at this

/-- **The complex-fake spectrum fails both forms.** -/
theorem complexFakeSpectrum_fails :
    (¬ ∀ x : ℂ → ℂ, 0 ≤ (complexFakeSpectrum.rosatiForm x).re) ∧
      ¬ ∀ x : ℂ → ℂ,
        complexFakeSpectrum.collided (fun β => β * x β) = complexFakeSpectrum.collided x :=
  ⟨fun h => complexFakeSpectrum_not_unitary
      (complexFakeSpectrum.rosatiForm_nonneg_iff_unitary.mp h),
    fun h => complexFakeSpectrum_not_unitary
      (complexFakeSpectrum.collided_frob_invariant_iff_unitary.mp h)⟩

/-! ### Coupling hides the real pair -/

/-- **Coupling hides even the real pair.** The golden datum has a negative kernel count, every
coupling of it has none. -/
theorem golden_detDeg_neg_couple_nonneg :
    detDeg goldenDatum (C 2 - X) = -1 ∧
      ∀ (θ : ℝ) (P : ℝ[X]), ∃ r : ℝ, 0 ≤ r ∧ detDeg (coupleDatum goldenDatum θ) P = r :=
  ⟨goldenDatum_detDeg_two_sub_X, couple_detDeg_nonneg goldenDatum⟩

end GaloisForLFunctions.ArithmeticPolarization
