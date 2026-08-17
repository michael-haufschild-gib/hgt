/-
# Sharp small-aperture birth of the indexed even prolate spectrum

The even moment synthesis is welded to the actual indexed Slepian block through
the exact rectangular Gram-square law.  This yields the sharp exponent
`4n + 1` for every indexed eigenvalue, including all multiplicities and zeros.
-/
import GaloisForLFunctions.HTGeometry.RectangularGramSpectrum
import GaloisForLFunctions.RHTower.ProlateSmallApertureEvenSynthesis

noncomputable section

open scoped Topology

namespace GaloisForLFunctions.RHTower

open ContinuousLinearMap MeasureTheory Filter
open _root_.RHTower

/-- The actual even moment synthesis is compact, as the operator-norm limit of its
finite-rank even Taylor heads. -/
theorem isCompactOperator_complexEvenApertureMomentSynthesis (c : ℝ) :
    IsCompactOperator (complexEvenApertureMomentSynthesis c) := by
  have hdouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop_of_monotone
      (fun a b hab => Nat.mul_le_mul_left 2 hab)
      (fun b => ⟨b, by omega⟩)
  have hlim : Tendsto
      (fun n : ℕ => complexEvenApertureMomentTaylorHead n c) atTop
      (𝓝 (complexEvenApertureMomentSynthesis c)) := by
    have h :=
      (hasSum_complexEvenApertureMomentSynthesis_coeff c).tendsto_sum_nat.comp hdouble
    change Tendsto
      ((fun k : ℕ => ∑ j ∈ Finset.range k,
          (c : ℂ) ^ j • evenApertureMomentPowerSynthesisCoeff j) ∘
        fun n : ℕ => 2 * n) atTop
      (𝓝 (complexEvenApertureMomentSynthesis c))
    exact h
  apply isClosed_setOf_isCompactOperator.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    (hasRectRankLE_complexEvenApertureMomentTaylorHead n c).isCompactOperator

/-- Exact indexed Gram transfer for the actual even prolate block. -/
theorem rectApproxNumber_complexEven_sq_eq_scaled_evenValue
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    rectApproxNumber (complexEvenApertureMomentSynthesis c) n ^ 2 =
      (2 * Real.pi / c) * complexUnitBandEvenValue c n := by
  rw [rectApproxNumber_sq_eq_approxNumber_adjoint_comp_self
      (complexEvenApertureMomentSynthesis c)
      (isCompactOperator_complexEvenApertureMomentSynthesis c) n,
    adjoint_comp_complexEvenApertureMomentSynthesis_eq_evenBlock hc.ne',
    approxNumber_smul]
  change _ = _ * approxNumber (complexUnitBandEvenBlock c) n
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (mul_pos (by norm_num) Real.pi_pos) hc)]

/-- Exact birth law reducing the indexed prolate value to the squared singular rung. -/
theorem complexUnitBandEvenValue_eq_c_mul_rectApproxNumber_sq
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    complexUnitBandEvenValue c n =
      (c / (2 * Real.pi)) *
        rectApproxNumber (complexEvenApertureMomentSynthesis c) n ^ 2 := by
  have h := rectApproxNumber_complexEven_sq_eq_scaled_evenValue hc n
  field_simp [hc.ne', Real.pi_ne_zero] at h ⊢
  nlinarith

/-- Every actual indexed even prolate eigenvalue is born at the sharp order
`c^(4n+1)` as the positive bandwidth tends to zero. -/
theorem exists_pos_eventually_complexUnitBandEvenValue_twoSided (n : ℕ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
        A * c ^ (4 * n + 1) ≤ complexUnitBandEvenValue c n ∧
          complexUnitBandEvenValue c n ≤ B * c ^ (4 * n + 1) := by
  obtain ⟨C, D, hC, hD, hbounds⟩ :=
    exists_pos_eventually_rectApproxNumber_complexEven_twoSided n
  let A : ℝ := C ^ 2 / (2 * Real.pi)
  let B : ℝ := D ^ 2 / (2 * Real.pi)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨A, B, hA, hB, ?_⟩
  have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (by
      intro c hc
      exact ne_of_gt hc)
  filter_upwards [hmono hbounds, self_mem_nhdsWithin]
    with c hcBounds hc
  have hcAbs : |c| = c := abs_of_pos hc
  rw [hcAbs] at hcBounds
  let s : ℝ := rectApproxNumber (complexEvenApertureMomentSynthesis c) n
  have hs0 : 0 ≤ s := rectApproxNumber_nonneg _ _
  have hlowSq : (C * c ^ (2 * n)) ^ 2 ≤ s ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hC.le (pow_nonneg hc.le _)) hcBounds.1 2
  have huppSq : s ^ 2 ≤ (D * c ^ (2 * n)) ^ 2 :=
    pow_le_pow_left₀ hs0 hcBounds.2 2
  have hpow : c ^ (4 * n + 1) = c * (c ^ (2 * n)) ^ 2 := by
    calc
      c ^ (4 * n + 1) = c ^ (1 + (2 * n) * 2) := by congr 1; omega
      _ = c ^ 1 * c ^ ((2 * n) * 2) := pow_add _ _ _
      _ = c * (c ^ (2 * n)) ^ 2 := by rw [pow_one, pow_mul]
  rw [complexUnitBandEvenValue_eq_c_mul_rectApproxNumber_sq hc n]
  change A * c ^ (4 * n + 1) ≤ (c / (2 * Real.pi)) * s ^ 2 ∧
    (c / (2 * Real.pi)) * s ^ 2 ≤ B * c ^ (4 * n + 1)
  constructor
  · calc
      A * c ^ (4 * n + 1) =
          (c / (2 * Real.pi)) * (C * c ^ (2 * n)) ^ 2 := by
        dsimp [A]
        rw [hpow]
        field_simp [Real.pi_ne_zero]
      _ ≤ (c / (2 * Real.pi)) * s ^ 2 :=
        mul_le_mul_of_nonneg_left hlowSq
          (div_nonneg hc.le (mul_nonneg (by norm_num) Real.pi_pos.le))
  · calc
      (c / (2 * Real.pi)) * s ^ 2 ≤
          (c / (2 * Real.pi)) * (D * c ^ (2 * n)) ^ 2 :=
        mul_le_mul_of_nonneg_left huppSq
          (div_nonneg hc.le (mul_nonneg (by norm_num) Real.pi_pos.le))
      _ = B * c ^ (4 * n + 1) := by
        dsimp [B]
        rw [hpow]
        field_simp [Real.pi_ne_zero]

end GaloisForLFunctions.RHTower
