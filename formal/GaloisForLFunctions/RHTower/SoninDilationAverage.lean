import GaloisForLFunctions.RHTower.SoninExtendedDilation
import GaloisForLFunctions.RHTower.SoninDilationContinuity

/-!
# Multiplicative smoothing of a vector of `L²(ℝ)`

For a continuous compactly supported weight `k` on the logarithmic scale put

`dilationAverage k f = ∫_ℝ k(x) · U_{e^x} f dx`   (a Bochner integral in `L²`),

where `U_v` is the normalized dilation.  The average inherits every closed linear condition that
each dilate satisfies, its distance to `(∫k)·f` is controlled by the modulus of strong continuity of
the dilation group, and a continuous linear functional passes through the integral.  These are the
three facts behind Burnol's Theorem 4.9.

## Main results

* `dilationAverage`
* `dilationAverage_mem_orthogonal`, `dilationAverage_mem_evenSubspace`
* `norm_dilationAverage_sub_smul_le`
* `apply_dilationAverage`
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

/-- Multiplicative smoothing: the average of the dilates `U_{e^x} f` against a weight `k`. -/
def dilationAverage (k : ℝ → ℝ) (f : SoninL2) : SoninL2 :=
  ∫ x : ℝ, (k x : ℂ) • rayDilate (Real.exp x) f

theorem continuous_dilationOrbit (f : SoninL2) :
    Continuous fun x : ℝ => rayDilate (Real.exp x) f :=
  (continuousOn_rayDilate f).comp_continuous Real.continuous_exp (fun x => Real.exp_pos x)

theorem continuous_weightedOrbit {k : ℝ → ℝ} (hk : Continuous k) (f : SoninL2) :
    Continuous fun x : ℝ => (k x : ℂ) • rayDilate (Real.exp x) f :=
  (Complex.continuous_ofReal.comp hk).smul (continuous_dilationOrbit f)

theorem hasCompactSupport_weightedOrbit {k : ℝ → ℝ} (hk : HasCompactSupport k) (f : SoninL2) :
    HasCompactSupport fun x : ℝ => (k x : ℂ) • rayDilate (Real.exp x) f := by
  refine HasCompactSupport.intro hk ?_
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport hx]
  simp

theorem integrable_weightedOrbit {k : ℝ → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    (f : SoninL2) : Integrable (fun x : ℝ => (k x : ℂ) • rayDilate (Real.exp x) f) volume :=
  (continuous_weightedOrbit hk f).integrable_of_hasCompactSupport
    (hasCompactSupport_weightedOrbit hks f)

/-- **The average inherits every orthogonality condition of the dilates.** -/
theorem dilationAverage_mem_orthogonal {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {f : SoninL2} {S : Submodule ℂ SoninL2}
    (h : ∀ x : ℝ, k x ≠ 0 → rayDilate (Real.exp x) f ∈ Sᗮ) :
    dilationAverage k f ∈ Sᗮ := by
  intro v hv
  rw [dilationAverage, ← integral_inner (integrable_weightedOrbit hk hks f) v]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  show inner ℂ v ((k x : ℂ) • rayDilate (Real.exp x) f) = 0
  by_cases hx : k x = 0
  · simp [hx]
  · rw [inner_smul_right, h x hx v hv, mul_zero]

theorem dilationAverage_mem_evenSubspace {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {f : SoninL2} (hf : f ∈ evenSubspace) :
    dilationAverage k f ∈ evenSubspace := by
  rw [mem_evenSubspace_iff, dilationAverage,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_weightedOrbit hk hks f)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show l2Reflection ((k x : ℂ) • rayDilate (Real.exp x) f)
      = (k x : ℂ) • rayDilate (Real.exp x) f
  rw [ContinuousLinearMap.map_smul]
  congr 1
  rw [rayDilate_of_pos (Real.exp_pos x), l2Reflection_dilation,
    (mem_evenSubspace_iff f).1 hf]

/-- **A continuous linear functional passes through the average.** -/
theorem apply_dilationAverage {k : ℝ → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    (f : SoninL2) (Φ : SoninL2 →L[ℂ] ℂ) :
    Φ (dilationAverage k f) = ∫ x : ℝ, (k x : ℂ) * Φ (rayDilate (Real.exp x) f) := by
  rw [dilationAverage, ← ContinuousLinearMap.integral_comp_comm _
    (integrable_weightedOrbit hk hks f)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show Φ ((k x : ℂ) • rayDilate (Real.exp x) f) = (k x : ℂ) * Φ (rayDilate (Real.exp x) f)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

theorem integral_smul_self (k : ℝ → ℝ) (f : SoninL2) :
    (∫ x : ℝ, (k x : ℂ) • f) = ((∫ x : ℝ, k x : ℝ) : ℂ) • f := by
  rw [integral_smul_const, integral_complex_ofReal]

/-- **The smoothing moves a vector by at most the modulus of continuity of the dilation group.** -/
theorem norm_dilationAverage_sub_smul_le {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) (f : SoninL2) {δ M : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ x : ℝ, δ ≤ |x| → k x = 0)
    (hM : ∀ x : ℝ, |x| ≤ δ → ‖rayDilate (Real.exp x) f - f‖ ≤ M) :
    ‖dilationAverage k f - ((∫ x : ℝ, k x : ℝ) : ℂ) • f‖ ≤ (∫ x : ℝ, |k x|) * M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp [le_of_lt hδ]))
  have hint1 := integrable_weightedOrbit hk hks f
  have hint2 : Integrable (fun x : ℝ => (k x : ℂ) • f) volume := by
    refine ((Complex.continuous_ofReal.comp hk).smul continuous_const).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hks ?_
    intro x hx
    show (k x : ℂ) • f = 0
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  have hdiff : dilationAverage k f - ((∫ x : ℝ, k x : ℝ) : ℂ) • f
      = ∫ x : ℝ, (k x : ℂ) • (rayDilate (Real.exp x) f - f) := by
    rw [dilationAverage, ← integral_smul_self k f, ← integral_sub hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (k x : ℂ) • rayDilate (Real.exp x) f - (k x : ℂ) • f
        = (k x : ℂ) • (rayDilate (Real.exp x) f - f)
    rw [smul_sub]
  have hbound : ∀ x : ℝ, ‖(k x : ℂ) • (rayDilate (Real.exp x) f - f)‖ ≤ |k x| * M := by
    intro x
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rcases le_or_gt |x| δ with hx | hx
    · exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)
    · rw [hsupp x (le_of_lt hx)]
      simp
  have hintdiff : Integrable (fun x : ℝ => (k x : ℂ) • (rayDilate (Real.exp x) f - f)) volume := by
    have := hint1.sub hint2
    refine this.congr (Eventually.of_forall fun x => ?_)
    show (k x : ℂ) • rayDilate (Real.exp x) f - (k x : ℂ) • f
        = (k x : ℂ) • (rayDilate (Real.exp x) f - f)
    rw [smul_sub]
  have hintabs : Integrable (fun x : ℝ => |k x| * M) volume := by
    refine (hk.abs.mul continuous_const).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hks ?_
    intro x hx
    show |k x| * M = 0
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  rw [hdiff]
  calc ‖∫ x : ℝ, (k x : ℂ) • (rayDilate (Real.exp x) f - f)‖
      ≤ ∫ x : ℝ, ‖(k x : ℂ) • (rayDilate (Real.exp x) f - f)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, |k x| * M :=
        integral_mono hintdiff.norm hintabs hbound
    _ = (∫ x : ℝ, |k x|) * M := integral_mul_const _ _

end RHTower

end
