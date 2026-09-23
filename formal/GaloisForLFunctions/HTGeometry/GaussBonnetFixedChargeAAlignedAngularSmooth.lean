import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakGibbsC1Profile

/-!
# Joint smoothness of the aligned angular force correction

The open rational parameter domain contains every actual physical
state. The angular correction is jointly smooth there at every real
angle, with no endpoint exclusions or critical-state restriction.
-/
noncomputable section
open Real Filter Set
open scoped Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAAlignedSmoothDomain : Set EGBAlignedForceState :=
  {s | |s.1.1| < 1 ∧ |s.2.2.1| < 1 ∧ 0 < s.2.2.2.2}

def egbFixedChargeAAlignedAngularCorrection (w φ : ℝ) (p : EGBAlignedForceState) (ψ : ℝ) : ℝ :=
  egbFixedChargeAAlignedForceRationalFamily w φ p (sin ψ) * cos ψ

theorem egbFixedChargeAAlignedSmoothDomain_isOpen : IsOpen egbFixedChargeAAlignedSmoothDomain := by
  exact (isOpen_lt (show Continuous (fun s : EGBAlignedForceState => |s.1.1|) by fun_prop) continuous_const).inter
    ((isOpen_lt (show Continuous (fun s : EGBAlignedForceState => |s.2.2.1|) by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const (show Continuous (fun s : EGBAlignedForceState => s.2.2.2.2) by fun_prop)))

theorem egbFixedChargeAAlignedForceState_mem_smoothDomain (w φ τ l : ℝ) :
    egbFixedChargeAAlignedForceState w φ τ l ∈ egbFixedChargeAAlignedSmoothDomain := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hc := egbFixedChargeAMiddleGapCoordinate_bounds τ φ
  change |egbCoexistenceASymmetricRatio τ| < 1 ∧ |egbFixedChargeAMiddleGapCoordinate τ φ| < 1 ∧
    0 < egbFixedChargeAGibbsBarrierScale w φ τ l
  exact ⟨abs_lt.mpr ⟨by linarith, hd.2⟩, abs_lt.mpr hc, egbFixedChargeAGibbsBarrierScale_pos w φ τ l⟩

theorem egbFixedChargeAAlignedForceCriticalState_mem_smoothDomain (w φ : ℝ) :
    egbFixedChargeAAlignedForceCriticalState w φ ∈ egbFixedChargeAAlignedSmoothDomain := by
  change |(0 : ℝ)| < 1 ∧ |(0 : ℝ)| < 1 ∧ 0 < egbFixedChargeAGibbsBarrierCoefficient w φ
  exact ⟨by norm_num, by norm_num, egbFixedChargeAGibbsBarrierCoefficient_pos w φ⟩

theorem egbFixedChargeAAlignedAngularCorrection_critical (w φ ψ : ℝ) :
    egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceCriticalState w φ) ψ = 0 := by
  unfold egbFixedChargeAAlignedAngularCorrection
  rw [egbFixedChargeAAlignedForceRationalFamily_critical, zero_mul]

theorem egbFixedChargeAAlignedAngularCorrection_contDiffOn (w φ : ℝ) :
    ContDiffOn ℝ ∞ (fun p : EGBAlignedForceState × ℝ => egbFixedChargeAAlignedAngularCorrection w φ p.1 p.2)
      (egbFixedChargeAAlignedSmoothDomain ×ˢ univ) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hd : |p.1.1.1| < 1 := hp.1.1
  have hc : |p.1.2.2.1| < 1 := hp.1.2.1
  have hq : 0 < p.1.2.2.2.2 := hp.1.2.2
  have ht : |(sin p.2)| ≤ 1 := abs_le.mpr ⟨neg_one_le_sin p.2, sin_le_one p.2⟩
  have hct : |p.1.2.2.1 * (sin p.2)| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hc)
  have hplus : 0 < 1 + p.1.2.2.1 * (sin p.2) := by linarith [(abs_lt.mp hct).1]
  let y : EGBAlignedForceState × ℝ → ℝ :=
    fun z => ((sin z.2) + z.1.2.2.1) / (1 + z.1.2.2.1 * (sin z.2))
  let j : EGBAlignedForceState × ℝ → ℝ :=
    fun z => (1 - z.1.2.2.1 ^ (2 : ℕ)) / (1 + z.1.2.2.1 * (sin z.2)) ^ (2 : ℕ)
  let y₁ : EGBAlignedForceState × ℝ → ℝ :=
    fun z => z.1.2.1 * (1 - (sin z.2) ^ (2 : ℕ)) / (1 + z.1.2.2.1 * (sin z.2))
  let j₁ : EGBAlignedForceState × ℝ → ℝ :=
    fun z => -z.1.2.1 * (2 * (sin z.2) + z.1.2.2.1 * (1 + (sin z.2) ^ (2 : ℕ))) /
      (1 + z.1.2.2.1 * (sin z.2)) ^ (2 : ℕ)
  have hY : ContDiffAt ℝ ∞ y p := by dsimp [y]; fun_prop (disch := positivity)
  have hJ : ContDiffAt ℝ ∞ j p := by dsimp [j]; fun_prop (disch := positivity)
  have hY₁ : ContDiffAt ℝ ∞ y₁ p := by dsimp [y₁]; fun_prop (disch := positivity)
  have hJ₁ : ContDiffAt ℝ ∞ j₁ p := by dsimp [j₁]; fun_prop (disch := positivity)
  have hy : -1 ≤ y p ∧ y p ≤ 1 := by
    have hc' := abs_lt.mp hc
    have ht' := abs_le.mp ht
    dsimp [y]
    constructor
    · apply (le_div_iff₀ hplus).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + p.1.2.2.1) (by linarith : 0 ≤ 1 + (sin p.2))]
    · apply (div_le_iff₀ hplus).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p.1.2.2.1) (by linarith : 0 ≤ 1 - (sin p.2))]
  have hdy : |p.1.1.1 * y p| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr hy) (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hd)
  have hinner : 0 < 1 + p.1.1.1 * y p := by linarith [(abs_lt.mp hdy).1]
  have hR : ContDiffAt ℝ ∞ (fun z : EGBAlignedForceState × ℝ =>
      egbFixedChargeAGibbsOddRationalFamily w φ z.1.1 (y z)) p := by
    dsimp [egbFixedChargeAGibbsOddRationalFamily]
    fun_prop (disch := positivity)
  have hB := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  change ContDiffAt ℝ ∞ (fun z =>
    (egbFixedChargeAGibbsOddRationalFamily w φ z.1.1 (y z) * j z +
      4 * egbFixedChargeAGibbsBarrierCoefficient w φ * y₁ z * (y z ^ (2 : ℕ) + y z * (sin z.2) + (sin z.2) ^ (2 : ℕ) - 1) * j z +
      egbFixedChargeAGibbsLeadingKernel w φ (sin z.2) * j₁ z -
      egbFixedChargeAGibbsLeadingKernel w φ (sin z.2) / egbFixedChargeAGibbsBarrierCoefficient w φ * z.1.2.2.2.1) / z.1.2.2.2.2 * cos z.2) p
  unfold egbFixedChargeAGibbsLeadingKernel
  fun_prop (disch := positivity)

end GaloisForLFunctions.HTGeometry
