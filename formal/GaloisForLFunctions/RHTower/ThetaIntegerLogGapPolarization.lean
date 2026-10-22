import GaloisForLFunctions.RHTower.CCM.CCMIntegerLogGapCrossBound
import GaloisForLFunctions.RHTower.CCM.CCMThetaModulusObstruction

/-!
# Decay of the full Weil polarization across complete integer-log gaps

The physical interaction estimate transfers through the exact theta ground
coordinates. Consequently the difference between the full energies of the sum
and difference of two profiles decays per unit physical mass when their entire
supporting-ball difference interval avoids every integer logarithm.

This estimates the same cross pairing that drives the previously constructed
arithmetic phase oscillator. It does not establish either quadratic's sign.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem support_ccmThetaSourceOfCompactRealProfile
    (a : SuzukiPositiveAperture) (phi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Ioo (-a.1) a.1) :
    Function.support (ccmThetaSourceOfCompactRealProfile a phi hc hs) =
      Function.support phi := by
  ext x
  simp only [Function.mem_support, ccmThetaSourceOfCompactRealProfile_apply,
    mul_ne_zero_iff, Complex.ofReal_ne_zero]
  exact ⟨And.right, fun hx =>
    ⟨(show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x).ne', hx⟩⟩

theorem thetaGroundNormSq_compactReal_eq_physical
    (a : SuzukiPositiveAperture) (phi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Ioo (-a.1) a.1) :
    thetaGroundNormSq (thetaComplexify phi) =
      ‖ccmArchimedeanFormEmbedding a
        (ccmThetaSourceOfCompactRealProfile a phi hc hs).toCCMFormVector‖ ^ 2 := by
  rw [← ccmThetaGroundProfile_ofCompactRealProfile a phi hc hs]
  exact thetaGroundNormSq_ccmProfile_eq_physical _

theorem thetaGammaPolarGroundCrossPairing_eq_ccm_screw
    (a : SuzukiPositiveAperture) (phi psi : 𝓢(ℝ, ℝ))
    (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    (hps : tsupport phi ⊆ Ioo (-a.1) a.1) (hqs : tsupport psi ⊆ Ioo (-a.1) a.1)
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y) :
    thetaGammaPolarGroundCrossPairing phi psi =
      screwRegularForm
        (fun x => (ccmThetaSourceOfCompactRealProfile a phi hpc hps x).re)
        (fun x => (ccmThetaSourceOfCompactRealProfile a psi hqc hqs x).re) := by
  unfold thetaGammaPolarGroundCrossPairing screwRegularForm
  apply integral_congr_ae
  filter_upwards with p
  simp only [ccmThetaSourceOfCompactRealProfile_apply, ← Complex.ofReal_mul, Complex.ofReal_re]
  by_cases hp : phi p.2 = 0
  · simp only [hp, mul_zero, zero_mul]
  by_cases hq : psi p.1 = 0
  · simp only [hq, mul_zero]
  rw [thetaGammaPolarScalingKernel_eq_screw (hsep p.1 hq p.2 hp)]
  ring

/-- The positive cross-coupling mechanism has an exponentially decreasing mass-normalized
budget when the whole supporting difference interval avoids the complete integer log mesh. -/
theorem abs_thetaGammaPolarGroundCrossPairing_integerLogGap_le
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hgap : screwSignThreshold ≤ c₂ - c₁ - 2 * r)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉
      Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r)) :
    |thetaGammaPolarGroundCrossPairing phi psi| ≤
      Real.exp (1 / 2) / 4 * Real.exp (-(c₂ - c₁ - 2 * r) / 2) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  obtain ⟨A, hA, hbound⟩ := (hpc.union hqc).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inl hx))
  have hqs : tsupport psi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inr hx))
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    linarith [hx'.1, hy'.2, screwSignThreshold_pos]
  rw [thetaGammaPolarGroundCrossPairing_eq_ccm_screw a phi psi hpc hqc hps hqs hsep,
    thetaGroundNormSq_compactReal_eq_physical a phi hpc hps,
    thetaGroundNormSq_compactReal_eq_physical a psi hqc hqs]
  exact abs_screwRegularForm_ccm_integerLogGap_le _ _ hr
    (by rwa [support_ccmThetaSourceOfCompactRealProfile])
    (by rwa [support_ccmThetaSourceOfCompactRealProfile]) hgap hfree

/-- A quantitative comparison of the two *full* arithmetic quadratics, with all prime,
Gamma, and polar channels retained by the exact polarization identity. -/
theorem abs_thetaRealArithmeticQuadratic_integerLogGap_difference_le
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hgap : screwSignThreshold ≤ c₂ - c₁ - 2 * r)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉
      Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r)) :
    |thetaRealArithmeticQuadratic (phi + psi) - thetaRealArithmeticQuadratic (phi - psi)| ≤
      Real.exp (1 / 2) * Real.exp (-(c₂ - c₁ - 2 * r) / 2) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  have hpair : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      x - y ∈ Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r) := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y :=
    fun x hx y hy => screwSignThreshold_pos.trans_le hgap |>.trans (hpair x hx y hy).1
  have hatom : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n := by
    intro x hx y hy n hn he
    exact hfree n hn (he ▸ hpair x hx y hy)
  rw [thetaRealArithmeticQuadratic_disjoint_polarization phi psi hsep hatom,
    abs_mul, abs_of_pos (show (0 : ℝ) < 4 by positivity)]
  have h := abs_thetaGammaPolarGroundCrossPairing_integerLogGap_le
    phi psi hpc hqc hr hp hq hgap hfree
  linarith only [h]

end RHTower
