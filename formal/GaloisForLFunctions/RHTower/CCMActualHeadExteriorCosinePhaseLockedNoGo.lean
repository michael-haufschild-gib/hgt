import GaloisForLFunctions.RHTower.CCMActualHeadExteriorCosineSuperoscillation
import GaloisForLFunctions.RHTower.DigammaVerticalGrowthBound

/-!
# Phase-locked obstruction for exterior CCM superoscillation gauges

The canonical constant-mode downshifting packet has an exact phase-locked subsequence.  At
`H = 8πa`, `δ = 4πa`, and `x = N / (4a)`, its signed cosine gauge is `(-3)^N`.  The corrected
CCM symbol has only logarithmic vertical growth, so a sufficiently large odd packet gives a
strictly negative corrected representative, despite both constituent measures being supported
outside the physical two-aperture diameter.

This is deliberately a no-go for this canonical packet family only.  It does not exclude an
arbitrary finite exterior signed gauge, whose construction remains the live signed-current
problem.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Exact phase locking of the canonical constant-mode exterior cosine packet. -/
theorem phaseLockedCosinePacket {a : ℝ} (ha : a ≠ 0) (N : ℕ) :
    exteriorSuperoscillationCosineSum (4 * a) (2 * a) 2
        (Real.pi * (N : ℝ) / (2 * a)) N = (-3 : ℝ) ^ N := by
  cases N with
  | zero => norm_num [exteriorSuperoscillationCosineSum,
      exteriorSuperoscillationCoefficient, exteriorSuperoscillationFrequency]
  | succ N =>
    let n : ℕ := N + 1
    rw [exteriorSuperoscillationCosineSum_eq_re]
    unfold exteriorSuperoscillationPacket
    have houter :
        Complex.exp (((4 * a * (Real.pi * (n : ℝ) / (2 * a)) : ℝ) : ℂ) * Complex.I) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (n : ℤ) using 1
      push_cast
      field_simp [ha]
      ring_nf
    have hinner :
        Complex.exp (((((-(2 * a) * (Real.pi * (n : ℝ) / (2 * a)) : ℝ) : ℂ) *
          Complex.I) / (n : ℂ))) = -1 := by
      have hn : (n : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero N
      let z : ℂ := ((-(2 * a) * (Real.pi * (n : ℝ) / (2 * a)) : ℝ) : ℂ)
      change Complex.exp (z * Complex.I / (n : ℂ)) = -1
      have harg :
          z * Complex.I / (n : ℂ) = -(Real.pi : ℂ) * Complex.I := by
        dsimp only [z]
        push_cast
        field_simp [ha, hn]
      rw [harg]
      have hminus : -(Real.pi : ℂ) * Complex.I = -((Real.pi : ℂ) * Complex.I) := by ring
      rw [hminus, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    dsimp [n] at houter hinner
    rw [houter, hinner]
    norm_num
    have hthree : (-3 : ℂ) = ((-3 : ℝ) : ℂ) := by norm_num
    rw [hthree, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The corrected CCM symbol has an unconditional logarithmic vertical envelope. -/
theorem ccmCorrectedSymbol_logUpper (a xi : ℝ) :
    correctedCCMSymbol a xi ≤
      digammaVerticalGrowthConst (1 / 4) + Real.log (2 + |xi / 2|) +
        ccmPolarPrimeUniformBudget a := by
  rw [correctedCCMSymbol_eq_ccmCorrectedSymbol]
  have hdigabs := abs_re_digamma_vertical_le (c := (1 / 4 : ℝ)) (by norm_num) (xi / 2)
  have hdig :
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((xi / 2 : ℝ) : ℂ) * Complex.I)).re ≤
        digammaVerticalGrowthConst (1 / 4) + Real.log (2 + |xi / 2|) :=
    (le_abs_self _).trans hdigabs
  have hquarter : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
  rw [hquarter] at hdig
  have harch : GaloisForLFunctions.RHTower.ccmArchSymbol xi ≤
      digammaVerticalGrowthConst (1 / 4) + Real.log (2 + |xi / 2|) := by
    unfold GaloisForLFunctions.RHTower.ccmArchSymbol
    have hpi : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (by nlinarith [Real.one_le_pi_div_two])
    exact (sub_le_self _ hpi).trans hdig
  have hprimeabs := abs_ccmPrimeCutoffSum_le_finitePrimeCosineMass a xi
  have hprime : -2 * GaloisForLFunctions.RHTower.ccmPrimeCutoffSum a xi ≤
      2 * ccmFinitePrimeCosineMass a := by
    have hlow := neg_le_of_abs_le hprimeabs
    linarith
  have hpolarabs := GaloisForLFunctions.RHTower.abs_ccmPolarMultiplier_le a xi
  have hpolar : GaloisForLFunctions.RHTower.ccmPolarMultiplier a xi ≤
      8 * |Real.sinh a| + 4 * Real.cosh a :=
    le_trans (le_abs_self _) hpolarabs
  unfold GaloisForLFunctions.RHTower.ccmCorrectedSymbol ccmPolarPrimeUniformBudget
  linarith

/-- Every affine sequence is negligible compared with `3^n`. -/
theorem tendsto_affine_div_three_pow (C B : ℝ) :
    Tendsto (fun n : ℕ => (C + B * (n : ℝ)) / (3 : ℝ) ^ n) atTop (𝓝 0) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdecay : Tendsto (fun x : ℝ => Real.exp (-Real.log 3 * x)) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_const_mul_atTop_of_pos hlog3).2 tendsto_id)).congr' ?_
    filter_upwards with x
    simp only [Function.comp_apply]
    congr 1
    simp
  have hlinear : Tendsto (fun x : ℝ => x * Real.exp (-Real.log 3 * x)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log 3) hlog3 using 1
    ext x
    rw [Real.rpow_one]
  have hscale : Tendsto (fun x : ℝ => (C + B * x) * Real.exp (-Real.log 3 * x))
      atTop (𝓝 0) := by
    have hsum := (hdecay.const_mul C).add (hlinear.const_mul B)
    convert hsum using 1
    · ext x
      ring
    · norm_num
  have hnat := hscale.comp tendsto_natCast_atTop_atTop
  refine hnat.congr' (Filter.Eventually.of_forall fun n => ?_)
  change (C + B * (n : ℝ)) * Real.exp (-Real.log 3 * (n : ℝ)) =
    (C + B * (n : ℝ)) / (3 : ℝ) ^ n
  have hpow : (3 : ℝ) ^ n = Real.exp (Real.log 3 * (n : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [hpow, div_eq_mul_inv, ← Real.exp_neg]
  congr 1
  ring

/-- The logarithmically bounded corrected CCM symbol is eventually smaller than `3^n`. -/
theorem eventually_phaseLockedSymbol_lt_three_pow (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      correctedCCMSymbol a (Real.pi * (n : ℝ) / (2 * a)) < (3 : ℝ) ^ n := by
  let C : ℝ := digammaVerticalGrowthConst (1 / 4) + ccmPolarPrimeUniformBudget a + 2
  let B : ℝ := |Real.pi / (4 * a)|
  have hbound : ∀ n : ℕ,
      correctedCCMSymbol a (Real.pi * (n : ℝ) / (2 * a)) ≤ C + B * (n : ℝ) := by
    intro n
    have hbase := ccmCorrectedSymbol_logUpper a (Real.pi * (n : ℝ) / (2 * a))
    have harg : Real.pi * (n : ℝ) / (2 * a) / 2 =
        (Real.pi / (4 * a)) * (n : ℝ) := by
      field_simp [ha.ne']
      ring
    have habs : |Real.pi * (n : ℝ) / (2 * a) / 2| = B * (n : ℝ) := by
      dsimp only [B]
      rw [harg, abs_mul]
      rw [abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
    have hlog : Real.log (2 + |Real.pi * (n : ℝ) / (2 * a) / 2|) ≤
        2 + B * (n : ℝ) := by
      rw [habs]
      have hpos : 0 < 2 + B * (n : ℝ) := by
        dsimp only [B]
        positivity
      have hraw := Real.log_le_sub_one_of_pos hpos
      linarith
    linarith [hbase, hlog]
  have hratio := tendsto_affine_div_three_pow C B
  filter_upwards [hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  have hpowpos : 0 < (3 : ℝ) ^ n := pow_pos (by norm_num) _
  have hlinear : C + B * (n : ℝ) < (3 : ℝ) ^ n := by
    rw [div_lt_iff₀ hpowpos] at hn
    simpa using hn
  exact (hbound n).trans_lt hlinear

/--
For every physical aperture, an exterior-admissible canonical constant-mode packet has a
strictly negative corrected representative at some odd order.  This rules out this phase-locked
superoscillatory repair, but not arbitrary exterior signed measures.
-/
theorem exists_phaseLockedExteriorPacket_negative
    (a : SuzukiPositiveAperture) :
    ∃ N : ℕ, Odd N ∧
      (∀ᵐ h : ℝ ∂exteriorSuperoscillationPositiveMeasure
        (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 N, 2 * a.1 ≤ h) ∧
      (∀ᵐ h : ℝ ∂exteriorSuperoscillationNegativeMeasure
        (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 N, 2 * a.1 ≤ h) ∧
      ccmCorrectedExteriorMeasureGaugeRepresentative a
        (exteriorSuperoscillationPositiveMeasure
          (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 N)
        (exteriorSuperoscillationNegativeMeasure
          (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2 N)
        ((N : ℝ) / (4 * a.1)) < 0 := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    (eventually_phaseLockedSymbol_lt_three_pow a.1 a.property)
  refine ⟨2 * M + 1, odd_two_mul_add_one M, ?_, ?_, ?_⟩
  · apply ae_exteriorSuperoscillationPositiveMeasure_two_aperture_le a
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos))
        (le_of_lt a.property)
    · calc
        4 * Real.pi * a.1 =
            8 * Real.pi * a.1 - 4 * Real.pi * a.1 := by ring
        _ ≤ 8 * Real.pi * a.1 - 4 * Real.pi * a.1 := le_rfl
  · apply ae_exteriorSuperoscillationNegativeMeasure_two_aperture_le a
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos))
        (le_of_lt a.property)
    · calc
        4 * Real.pi * a.1 =
            8 * Real.pi * a.1 - 4 * Real.pi * a.1 := by ring
        _ ≤ 8 * Real.pi * a.1 - 4 * Real.pi * a.1 := le_rfl
  · have hlt := hM (2 * M + 1) (by omega)
    have hphase :
        exteriorSuperoscillationCosineSum
          (8 * Real.pi * a.1) (4 * Real.pi * a.1) 2
          (((2 * M + 1 : ℕ) : ℝ) / (4 * a.1)) (2 * M + 1) =
          (-3 : ℝ) ^ (2 * M + 1) := by
      have hne : 2 * Real.pi * a.1 ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) a.property.ne'
      convert phaseLockedCosinePacket (a := 2 * Real.pi * a.1) hne (2 * M + 1) using 1
      all_goals
        field_simp [a.property.ne', Real.pi_ne_zero]
        ring
    have hxi : 2 * Real.pi * (((2 * M + 1 : ℕ) : ℝ) / (4 * a.1)) =
        Real.pi * ((2 * M + 1 : ℕ) : ℝ) / (2 * a.1) := by
      field_simp [a.property.ne', Real.pi_ne_zero]
      ring
    rw [correctedExteriorSuperoscillationRepresentative_eq, hxi, hphase]
    have hnegpow : (-3 : ℝ) ^ (2 * M + 1) = -(3 : ℝ) ^ (2 * M + 1) := by
      simpa using (odd_two_mul_add_one M).neg_pow (3 : ℝ)
    rw [hnegpow]
    linarith

end RHTower
