import GaloisForLFunctions.ArithmeticPositiveDuality.TheExtensionsOfAnAtomicArchimedeanCorrelation
import GaloisForLFunctions.ArithmeticPositiveDuality.WeilsCorrelationCarriesNoSuccessor

/-!
# The extensions of Weil's correlation are indexed by the critical zeros

By P13 a positive-definite `φ` on `Aff(ℚ)` restricting to Weil's spline correlation on the
dilations exists iff RH holds. This file describes all of them.

**Theorem** (`weil_extension_classification`, unconditional). If `φ` is positive definite on
`Aff(ℚ)` and `φ(x ↦ ux) = ratCorr(u)` for `u > 0`, then RH holds, Weil's correlation is the
characteristic function of the atomic measure `ν_W = Σ_γ w_γ δ_{−γ}` over the critical ordinates
`γ`, `w_γ = μ_Λ{γ}|B̂(γ)|²` (`weilMeasure`, `weilMeasure_real_singleton_neg`), and there are
constants `0 ≤ α_x ≤ ν_W{x}` with
`φ(x ↦ ux + b) = Σ_x α_x u^{ix}` (sum over the atoms of `ν_W`) for all `u > 0`, `b ≠ 0`.

So an extension of Weil's correlation to the affine group carries exactly one parameter per
critical zero, `α_{−γ} ∈ [0, w_γ]`, and nothing else: the non-commutative carrier adds a box
of parameters indexed by the zeros and no new constraint on them.
-/

open Complex MeasureTheory Filter Topology Finset
open scoped InnerProductSpace ComplexConjugate
open RHTower RHTower.WeilSpectral
open RHTower.WeilConditional (criticalOrdinates)

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

variable (hW : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- Weil's spectral measure `Σ_γ w_γ δ_{−γ}` over the critical ordinates. -/
def weilMeasure : Measure ℝ :=
  Measure.sum fun x : criticalOrdinates => ENNReal.ofReal (weilWeight hW x) • Measure.dirac (-(x : ℝ))

theorem summable_ofReal_weilWeight :
    Summable fun x : criticalOrdinates => (ENNReal.ofReal (weilWeight hW x)).toReal := by
  (summable_weilWeight hW).congr fun x => (ENNReal.toReal_ofReal (weilWeight_nonneg hW x)).symm

instance : IsFiniteMeasure (weilMeasure hW) := by
  refine ⟨?_⟩
  rw [weilMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (weilWeight_nonneg hW) (summable_weilWeight hW)]
  exact ENNReal.ofReal_lt_top

/-- Weil's correlation is the characteristic function of `ν_W`. -/
theorem ratCorr_eq_integral_weilMeasure (u : posUnits) :
    ratCorr u = ∫ x, archChar x ((u : ℚˣ) : ℚ) ∂weilMeasure hW := by
  rw [weilMeasure, integral_sum_dirac_eq_tsum (f := fun x : ℝ => archChar x ((u : ℚˣ) : ℚ))
    (fun _ => ENNReal.ofReal_ne_top) ?_, ratCorr_eq_tsum hW u]
  · refine tsum_congr fun x => ?_
    rw [ENNReal.toReal_ofReal (weilWeight_nonneg hW x), Complex.real_smul]
  · simpa [norm_archChar] using summable_ofReal_weilWeight hW

theorem weilMeasure_singleton_ge (x : criticalOrdinates) :
    ENNReal.ofReal (weilWeight hW x) ≤ weilMeasure hW {-(x : ℝ)} := by
  have h := Measure.le_sum (fun x : criticalOrdinates =>
    ENNReal.ofReal (weilWeight hW x) • Measure.dirac (-(x : ℝ))) x
  refine le_trans ?_ (Measure.le_iff'.1 h {-(x : ℝ)})
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), smul_eq_mul, mul_one]

/-- The atoms of `ν_W` are the negated critical ordinates, with weights `w_γ`. -/
theorem weilMeasure_real_singleton_neg (x : criticalOrdinates) :
    (weilMeasure hW).real {-(x : ℝ)} = weilWeight hW x := by
  rw [measureReal_def, weilMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  rw [tsum_eq_single x fun y hyx => by
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply, Set.indicator_of_notMem (fun h => hyx (Subtype.ext (neg_injective
      (Set.mem_singleton_iff.mp h)))), mul_zero]]
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (weilWeight_nonneg hW x)]

/-- `ν_W` is purely atomic. -/
theorem weilMeasure_nonatomic_null : weilMeasure hW {x | weilMeasure hW {x} = 0} = 0 := by
  have hB : MeasurableSet {x : ℝ | weilMeasure hW {x} = 0} := by
    have hA : {x : ℝ | 0 < weilMeasure hW {x}}.Countable :=
      Measure.countable_meas_pos_of_disjoint_iUnion (As := fun x : ℝ => ({x} : Set ℝ))
        (fun x => measurableSet_singleton x) (fun x y hxy => Set.disjoint_singleton.mpr hxy)
    have : {x : ℝ | weilMeasure hW {x} = 0} = {x : ℝ | 0 < weilMeasure hW {x}}ᶜ := by
      ext x; simp [pos_iff_ne_zero]
    rw [this]
    exact hA.measurableSet.compl
  rw [weilMeasure, Measure.sum_apply _ hB]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  by_cases hx : weilWeight hW x = 0
  · rw [hx, ENNReal.ofReal_zero, zero_mul]
  · have hnot : -(x : ℝ) ∉ {y : ℝ | weilMeasure hW {y} = 0} := by
      intro hmem
      have h1 := weilMeasure_singleton_ge hW x
      rw [show weilMeasure hW {-(x : ℝ)} = 0 from hmem, nonpos_iff_eq_zero,
        ENNReal.ofReal_eq_zero] at h1
      exact hx (le_antisymm h1 (weilWeight_nonneg hW x))
    rw [Measure.dirac_apply, Set.indicator_of_notMem hnot, mul_zero]

/-- **The extensions of Weil's correlation are indexed by the critical zeros.** -/
theorem weil_extension_classification {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hdil : ∀ u : posUnits, φ (dilation (u : ℚˣ)) = ratCorr u) :
    ∃ hW : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      ∃ α : ℝ → ℝ, (∀ x, 0 ≤ α x ∧ α x ≤ (weilMeasure hW).real {x}) ∧
        ∀ u : ℚˣ, 0 < (u : ℚ) → ∀ b : ℚ, b ≠ 0 →
          HasSum (fun x : {x : ℝ // 0 < weilMeasure hW {x}} => (α x : ℂ) * archChar x u)
            (φ (translation b * dilation u)) := by
  have hRH : RiemannHypothesis := riemannHypothesis_iff_exists_affine_posDef.mpr ⟨φ, hφ, hdil⟩
  have hW := weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
  have hν : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ x, archChar x u ∂weilMeasure hW :=
    fun u hu => by
      rw [show dilation u = dilation ((⟨u, hu⟩ : posUnits) : ℚˣ) from rfl, hdil,
        ratCorr_eq_integral_weilMeasure hW]
  exact ⟨hW, atomAlpha hφ, fun x => ⟨atomAlpha_nonneg hφ hν x, atomAlpha_le hφ hν x⟩,
    fun u hu b hb => hasSum_affine_of_atomic hφ hν (weilMeasure_nonatomic_null hW) hu hb⟩

end GaloisForLFunctions.ArithmeticPositiveDuality
