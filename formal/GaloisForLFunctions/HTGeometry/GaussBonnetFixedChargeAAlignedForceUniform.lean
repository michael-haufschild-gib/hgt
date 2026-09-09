import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAAlignedForceRationalFamily

/-!
# Uniform cancellation of the aligned Gibbs force correction

The exact correction is a jointly continuous rational family near its
critical coefficient state on the full compact phase interval. Its
critical value is identically zero. Compactness therefore proves that
the entire first correction of the actual aligned force vanishes
uniformly, including both endpoints.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAAlignedForceRationalFamily_continuousOn (w φ : ℝ) :
    ContinuousOn (fun p : EGBAlignedForceState × Icc (-1 : ℝ) 1 =>
      egbFixedChargeAAlignedForceRationalFamily w φ p.1 p.2)
      ({s : EGBAlignedForceState | |s.1.1| < 1 / 2 ∧ |s.2.2.1| < 1 / 2 ∧ 0 < s.2.2.2.2} ×ˢ univ) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hd : |p.1.1.1| < 1 / 2 := hp.1.1
  have hc : |p.1.2.2.1| < 1 / 2 := hp.1.2.1
  have hq : 0 < p.1.2.2.2.2 := hp.1.2.2
  have ht : |(p.2 : ℝ)| ≤ 1 := abs_le.mpr p.2.property
  have hct : |p.1.2.2.1 * (p.2 : ℝ)| < 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hc)
  have hplus : 0 < 1 + p.1.2.2.1 * (p.2 : ℝ) := by linarith [(abs_lt.mp hct).1]
  let y : EGBAlignedForceState × Icc (-1 : ℝ) 1 → ℝ :=
    fun z => ((z.2 : ℝ) + z.1.2.2.1) / (1 + z.1.2.2.1 * (z.2 : ℝ))
  let j : EGBAlignedForceState × Icc (-1 : ℝ) 1 → ℝ :=
    fun z => (1 - z.1.2.2.1 ^ 2) / (1 + z.1.2.2.1 * (z.2 : ℝ)) ^ 2
  let y₁ : EGBAlignedForceState × Icc (-1 : ℝ) 1 → ℝ :=
    fun z => z.1.2.1 * (1 - (z.2 : ℝ) ^ 2) / (1 + z.1.2.2.1 * (z.2 : ℝ))
  let j₁ : EGBAlignedForceState × Icc (-1 : ℝ) 1 → ℝ :=
    fun z => -z.1.2.1 * (2 * (z.2 : ℝ) + z.1.2.2.1 * (1 + (z.2 : ℝ) ^ 2)) /
      (1 + z.1.2.2.1 * (z.2 : ℝ)) ^ 2
  have hY : ContinuousAt y p := by dsimp [y]; fun_prop (disch := positivity)
  have hJ : ContinuousAt j p := by dsimp [j]; fun_prop (disch := positivity)
  have hY₁ : ContinuousAt y₁ p := by dsimp [y₁]; fun_prop (disch := positivity)
  have hJ₁ : ContinuousAt j₁ p := by dsimp [j₁]; fun_prop (disch := positivity)
  have hy : -1 ≤ y p ∧ y p ≤ 1 := by
    have hc' := abs_lt.mp hc
    have ht' := abs_le.mp ht
    dsimp [y]
    constructor
    · apply (le_div_iff₀ hplus).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + p.1.2.2.1) (by linarith : 0 ≤ 1 + (p.2 : ℝ))]
    · apply (div_le_iff₀ hplus).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p.1.2.2.1) (by linarith : 0 ≤ 1 - (p.2 : ℝ))]
  have hdy : |p.1.1.1 * y p| < 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr hy) (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hd)
  have hinner : 0 < 1 + p.1.1.1 * y p := by linarith [(abs_lt.mp hdy).1]
  have hR : ContinuousAt (fun z : EGBAlignedForceState × Icc (-1 : ℝ) 1 =>
      egbFixedChargeAGibbsOddRationalFamily w φ z.1.1 (y z)) p := by
    dsimp [egbFixedChargeAGibbsOddRationalFamily]
    fun_prop (disch := positivity)
  have hB := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  change ContinuousAt (fun z =>
    (egbFixedChargeAGibbsOddRationalFamily w φ z.1.1 (y z) * j z +
      4 * egbFixedChargeAGibbsBarrierCoefficient w φ * y₁ z * (y z ^ 2 + y z * (z.2 : ℝ) + (z.2 : ℝ) ^ 2 - 1) * j z +
      egbFixedChargeAGibbsLeadingKernel w φ z.2 * j₁ z -
      egbFixedChargeAGibbsLeadingKernel w φ z.2 / egbFixedChargeAGibbsBarrierCoefficient w φ * z.1.2.2.2.1) / z.1.2.2.2.2) p
  unfold egbFixedChargeAGibbsLeadingKernel
  fun_prop (disch := positivity)

theorem egbFixedChargeAAlignedForceRationalFamily_uniform_limit (w φ : ℝ) :
    TendstoUniformly (fun s (t : Icc (-1 : ℝ) 1) => egbFixedChargeAAlignedForceRationalFamily w φ s t)
      (fun t => egbFixedChargeAAlignedForceRationalFamily w φ (egbFixedChargeAAlignedForceCriticalState w φ) t)
      (𝓝 (egbFixedChargeAAlignedForceCriticalState w φ)) := by
  have hU : {s : EGBAlignedForceState | |s.1.1| < 1 / 2 ∧ |s.2.2.1| < 1 / 2 ∧ 0 < s.2.2.2.2} ∈
      𝓝 (egbFixedChargeAAlignedForceCriticalState w φ) := by
    have ho : IsOpen {s : EGBAlignedForceState | |s.1.1| < 1 / 2 ∧ |s.2.2.1| < 1 / 2 ∧ 0 < s.2.2.2.2} := by
      exact (isOpen_lt (show Continuous (fun s : EGBAlignedForceState => |s.1.1|) by fun_prop) continuous_const).inter
        ((isOpen_lt (show Continuous (fun s : EGBAlignedForceState => |s.2.2.1|) by fun_prop) continuous_const).inter
          (isOpen_lt continuous_const (show Continuous (fun s : EGBAlignedForceState => s.2.2.2.2) by fun_prop)))
    apply ho.mem_nhds
    dsimp [egbFixedChargeAAlignedForceCriticalState, egbFixedChargeAGibbsOddCriticalState]
    norm_num only [abs_zero]
    exact ⟨trivial, trivial, egbFixedChargeAGibbsBarrierCoefficient_pos w φ⟩
  exact (egbFixedChargeAAlignedForceRationalFamily_continuousOn w φ).tendstoUniformly hU

theorem egbFixedChargeAPeakNormalizedGibbsForce_uniform_first_zero_limit (w φ l : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAPeakNormalizedGibbsForce w φ τ l ψ + 4 * sin ψ * cos ψ ^ 3) /
      egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAAlignedForceRationalFamily_uniform_limit w φ)) ε hε
  filter_upwards [(egbFixedChargeAAlignedForceState_critical_limit w φ l).eventually he] with τ hτ
  intro ψ
  let t : Icc (-1 : ℝ) 1 := ⟨sin ψ, neg_one_le_sin ψ, sin_le_one ψ⟩
  have h := hτ t
  rw [egbFixedChargeAAlignedForceRationalFamily_critical] at h
  simp only [Real.dist_eq, zero_sub, abs_neg] at h ⊢
  rw [egbFixedChargeAPeakNormalizedGibbsForce_correction_formula, abs_mul]
  have hc : |cos ψ| ≤ 1 := abs_le.mpr ⟨neg_one_le_cos ψ, cos_le_one ψ⟩
  calc
    _ ≤ |egbFixedChargeAAlignedForceRationalFamily w φ (egbFixedChargeAAlignedForceState w φ τ l) (sin ψ)| * 1 :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ < ε := by simpa only [mul_one, t] using h

end GaloisForLFunctions.HTGeometry
