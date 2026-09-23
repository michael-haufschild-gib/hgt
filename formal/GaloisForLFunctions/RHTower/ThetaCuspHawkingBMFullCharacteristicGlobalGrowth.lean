import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMeanGrowth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceCircleGrowth
import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# Global growth of the literal full characteristic current

The direct normal face differentiates the actual full circle mean through
`deriv / sinh`.  The quotient is regular at the characteristic edge because
the literal circle mean is even; it is controlled at large radius by the
strict growth theorem for that same mean.  No response channel is replaced by
a source or modal proxy.

Proof-chain role:
`literal direct normal face -> full characteristic current majorant ->
normal derivative interchange -> corrected-future cap coefficient -> HB B2`.
-/

namespace RHTower.D4BMFullAngularCurrent

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMFullAngularCircle
open D4BMNativeCircle
open D4BMFullAngularGrowth
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The actual native circle mean has the same strict exponent as the full
circle.  Its fixed log-height cost is absorbed once in the constant; no
sign restriction on that original coordinate is used. -/
theorem nativeMean_strict_growth (q : XiZeroCopy) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 ≤ d →
      ‖mean q d X k‖ ≤ C * Real.exp (strictGrowthExponent q * d) := by
  obtain ⟨A, hA, hmean⟩ := mean_global_growth q
  let C := A * Real.exp (sourceGrowthExponent q * |k|)
  have hC : 0 ≤ C := mul_nonneg hA (Real.exp_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro d hd
  have hsource : sourceGrowthExponent q ≤ strictGrowthExponent q :=
    (strictGrowthExponent_bounds q).1.le
  have htail := hmean d X k hd
  calc
    ‖mean q d X k‖ ≤ A * Real.exp (sourceGrowthExponent q * (d + |k|)) := htail
    _ = C * Real.exp (sourceGrowthExponent q * d) := by
      dsimp only [C]
      rw [mul_assoc, ← Real.exp_add,
        show sourceGrowthExponent q * |k| + sourceGrowthExponent q * d =
          sourceGrowthExponent q * (d + |k|) from by ring]
    _ ≤ C * Real.exp (strictGrowthExponent q * d) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsource hd)) hC

/-- The actual full circular characteristic quotient has the strict rate of
the constructed full response.  The proof keeps its two indispensable pieces
separate: exact edge regularity from radial parity, and the noncompact
strict-growth tail. -/
theorem angularMean_sinh_ratio_strict_growth (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d →
      ‖deriv (fun r => angularMean q branch r X k) d / (Real.sinh d : ℂ)‖ ≤
        C * Real.exp (strictGrowthExponent q * d) := by
  let M : ℝ → ℂ := fun d => angularMean q branch d X k
  have hM : ContDiff ℝ ∞ M := angularMean_smooth q branch X k
  have hM1 := (contDiff_infty_iff_deriv.mp hM).2
  have hM2 := (contDiff_infty_iff_deriv.mp hM1).2
  have hzero : deriv M 0 = 0 := by
    simpa only [M] using (angularMean_radial_oddJets_zero q branch X k).1
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hM2.continuous.continuousOn
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hsmall_deriv (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
      ‖deriv M d‖ ≤ A0 * d := by
    have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le (C := A0)
      (fun u _ => hM1.differentiable (by simp) u)
      (fun u hu => (hA u hu).trans (le_max_left _ _))
      (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
      (show d ∈ Icc 0 1 by exact ⟨hd0, hd1⟩)
    rw [hzero] at h
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hd0] using h
  obtain ⟨B, hB, htail⟩ := angularMean_strict_growth q branch X k
  have hstrict0 : 0 ≤ strictGrowthExponent q := by
    have hsource := (sourceGrowthExponent_bounds q).1
    have hstrict := (strictGrowthExponent_bounds q).1
    linarith
  have hsinhone : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
  let C := A0 + B / Real.sinh 1
  have hC : 0 ≤ C := add_nonneg hA0 (div_nonneg hB hsinhone.le)
  refine ⟨C, hC, ?_⟩
  intro d hd
  by_cases hd1 : d ≤ 1
  · have hderiv := hsmall_deriv d hd.le hd1
    have hsinh : 0 < Real.sinh d := Real.sinh_pos_iff.mpr hd
    have hlinear : d ≤ Real.sinh d := Real.self_le_sinh_iff.mpr hd.le
    have hquot : ‖deriv M d / (Real.sinh d : ℂ)‖ ≤ A0 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsinh]
      calc
        ‖deriv M d‖ / Real.sinh d ≤ (A0 * d) / Real.sinh d :=
          div_le_div_of_nonneg_right hderiv hsinh.le
        _ ≤ A0 := (div_le_iff₀ hsinh).mpr
          (mul_le_mul_of_nonneg_left hlinear hA0)
    have hexp : 1 ≤ Real.exp (strictGrowthExponent q * d) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hstrict0 hd.le)
    calc
      ‖deriv M d / (Real.sinh d : ℂ)‖ ≤ A0 := hquot
      _ ≤ A0 * Real.exp (strictGrowthExponent q * d) := le_mul_of_one_le_right hA0 hexp
      _ ≤ C * Real.exp (strictGrowthExponent q * d) := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (div_nonneg hB hsinhone.le)) (Real.exp_pos _).le
  · have hdlarge : 1 ≤ d := (lt_of_not_ge hd1).le
    have hsinh : Real.sinh 1 ≤ Real.sinh d := (Real.sinh_le_sinh).mpr hdlarge
    have hderiv : ‖deriv M d‖ ≤ B * Real.exp (strictGrowthExponent q * d) :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans (htail d hd.le)
    have hquot : ‖deriv M d / (Real.sinh d : ℂ)‖ ≤
        (B / Real.sinh 1) * Real.exp (strictGrowthExponent q * d) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
        (Real.sinh_pos_iff.mpr (lt_of_lt_of_le (by norm_num) hdlarge))]
      calc
        ‖deriv M d‖ / Real.sinh d ≤ ‖deriv M d‖ / Real.sinh 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) hsinhone hsinh
        _ ≤ (B * Real.exp (strictGrowthExponent q * d)) / Real.sinh 1 :=
          div_le_div_of_nonneg_right hderiv hsinhone.le
        _ = (B / Real.sinh 1) * Real.exp (strictGrowthExponent q * d) := by ring
    calc
      ‖deriv M d / (Real.sinh d : ℂ)‖ ≤
          (B / Real.sinh 1) * Real.exp (strictGrowthExponent q * d) := hquot
      _ ≤ C * Real.exp (strictGrowthExponent q * d) := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hA0) (Real.exp_pos _).le

end
end RHTower.D4BMFullAngularCurrent
