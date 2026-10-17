import GaloisForLFunctions.HTGeometry.BurnolWeightedShiftStrongContinuity
import GaloisForLFunctions.HTGeometry.BurnolComplexLaplaceFeature
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Algebra.Group.ForwardDiff

/-! Literal positive Burnol packets and their finite-difference readout. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexOrder NNReal

namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

instance burnolL2IsOrderedModule : IsOrderedModule ℝ BurnolHalfLineL2 := by
  apply IsOrderedModule.of_smul_nonneg
  intro a ha f hf
  apply (Lp.coeFn_nonneg _).mp
  have hf' := (Lp.coeFn_nonneg f).mpr hf
  filter_upwards [Lp.coeFn_smul a f, hf'] with t hc ht
  rw [hc, Pi.smul_apply]
  exact smul_nonneg ha ht

theorem burnolWeightedShift_nonneg (h : ℝ≥0) {f : BurnolHalfLineL2}
    (hf : 0 ≤ f) : 0 ≤ burnolWeightedShift h f := by
  apply (Lp.coeFn_nonneg _).mp
  have hp := (quasiMeasurePreserving_add_right_Ioi h.coe_nonneg).ae
    ((Lp.coeFn_nonneg f).mpr hf)
  filter_upwards [burnolWeightedShift_coeFn h f, hp,
    ae_restrict_mem measurableSet_Ioi] with t he ht hpos
  rw [he]
  exact mul_nonneg (Complex.zero_le_real.mpr (div_nonneg hpos.le
    (add_nonneg hpos.le h.coe_nonneg))) ht

/-- Recursion realizes the actual positive packet `t exp(-lambda*t)(1-exp(-delta*t))^n`. -/
def burnolPositivePacket (δ : ℝ≥0) : ℕ → Ioi (0 : ℝ) → BurnolHalfLineL2
  | 0, lam => burnolRateFeature lam lam.2
  | n + 1, lam => burnolPositivePacket δ n lam -
      burnolPositivePacket δ n ⟨lam + δ, add_pos_of_pos_of_nonneg lam.2 δ.coe_nonneg⟩

theorem burnolPositivePacket_ae (δ : ℝ≥0) (n : ℕ) (lam : Ioi (0 : ℝ)) :
    (burnolPositivePacket δ n lam : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => ((t * Real.exp (-(lam * t)) * (1 - Real.exp (-(δ * t)))^n : ℝ) : ℂ) := by
  induction n generalizing lam with
  | zero => simpa [burnolPositivePacket] using burnolRateFeature_ae lam lam.2
  | succ n ih =>
    let lam' : Ioi (0 : ℝ) := ⟨lam + δ, add_pos_of_pos_of_nonneg lam.2 δ.coe_nonneg⟩
    filter_upwards [Lp.coeFn_sub (burnolPositivePacket δ n lam)
      (burnolPositivePacket δ n lam'), ih lam, ih lam'] with t hs h1 h2
    change ((burnolPositivePacket δ n lam - burnolPositivePacket δ n lam' : BurnolHalfLineL2) : ℝ → ℂ) t = _
    rw [hs, Pi.sub_apply, h1, h2]
    change ((t * Real.exp (-(lam * t)) * (1 - Real.exp (-(δ * t)))^n : ℝ) : ℂ) -
      ((t * Real.exp (-((lam + δ) * t)) * (1 - Real.exp (-(δ * t)))^n : ℝ) : ℂ) = _
    rw [show -(((lam : ℝ) + (δ : ℝ)) * t) = -(lam * t) + -(δ * t) by ring, Real.exp_add]
    push_cast
    ring

theorem burnolPositivePacket_nonneg (δ : ℝ≥0) (n : ℕ) (lam : Ioi (0 : ℝ)) :
    0 ≤ burnolPositivePacket δ n lam := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [burnolPositivePacket_ae δ n lam, ae_restrict_mem measurableSet_Ioi]
    with t he ht
  change (0 : ℂ) ≤ _
  rw [he, Complex.zero_le_real]
  exact mul_nonneg (mul_nonneg ht.le (Real.exp_pos _).le)
    (pow_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg δ.coe_nonneg ht.le)))) _)

/-- Polynomial in `exp(-delta*t)` obtained after dividing an output by its positive envelope. -/
def burnolPacketCoefficient (φ : ℝ → ℂ) (δ : ℝ) : ℕ → ℝ → ℝ → ℂ
  | 0, lam, _ => φ lam
  | n + 1, lam, t => burnolPacketCoefficient φ δ n lam t -
      (Real.exp (-(δ * t)) : ℂ) * burnolPacketCoefficient φ δ n (lam + δ) t

theorem continuous_burnolPacketCoefficient (φ : ℝ → ℂ) (δ lam : ℝ) (n : ℕ) :
    Continuous (burnolPacketCoefficient φ δ n lam) := by
  induction n generalizing lam with
  | zero => exact continuous_const
  | succ n ih => exact (ih lam).sub (by
      exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).mul (ih (lam + δ)))

theorem burnolPacketCoefficient_zero_re (φ : ℝ → ℂ) (δ lam : ℝ) (n : ℕ) :
    (burnolPacketCoefficient φ δ n lam 0).re =
      (-1 : ℝ)^n * (fwdDiff δ)^[n] (fun x => (φ x).re) lam := by
  induction n generalizing lam with
  | zero => simp [burnolPacketCoefficient]
  | succ n ih =>
    simp only [burnolPacketCoefficient, mul_zero, neg_zero, Real.exp_zero,
      Complex.ofReal_one, one_mul, Complex.sub_re, ih,
      Function.iterate_succ_apply', fwdDiff, pow_succ]
    ring

theorem burnolPositivePacket_image_ae
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (φ : ℝ → ℂ)
    (hφ : ∀ (lam : ℝ) (hlam : 0 < lam), T (burnolRateFeature lam hlam) = φ lam • burnolRateFeature lam hlam)
    (δ : ℝ≥0) (n : ℕ) (lam : Ioi (0 : ℝ)) :
    (T (burnolPositivePacket δ n lam) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => (t * Real.exp (-(lam * t)) : ℂ) * burnolPacketCoefficient φ δ n lam t := by
  induction n generalizing lam with
  | zero =>
    simp only [burnolPositivePacket, burnolPacketCoefficient, hφ]
    filter_upwards [Lp.coeFn_smul (φ lam) (burnolRateFeature lam lam.2),
      burnolRateFeature_ae lam lam.2] with t hs he
    rw [hs, Pi.smul_apply, he]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  | succ n ih =>
    let lam' : Ioi (0 : ℝ) := ⟨lam + δ, add_pos_of_pos_of_nonneg lam.2 δ.coe_nonneg⟩
    change (T (burnolPositivePacket δ n lam - burnolPositivePacket δ n lam') : ℝ → ℂ) =ᵐ[_] _
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (T (burnolPositivePacket δ n lam))
      (T (burnolPositivePacket δ n lam')), ih lam, ih lam'] with t hs h1 h2
    rw [hs, Pi.sub_apply, h1, h2]
    change (t * Real.exp (-(lam * t)) : ℂ) * burnolPacketCoefficient φ δ n lam t -
      (t * Real.exp (-((lam + δ) * t)) : ℂ) * burnolPacketCoefficient φ δ n (lam + δ) t = _
    rw [show -(((lam : ℝ) + (δ : ℝ)) * t) = -(lam * t) + -(δ * t) by ring, Real.exp_add]
    simp only [burnolPacketCoefficient, Complex.ofReal_mul]
    ring

private theorem nonneg_at_zero_of_continuous_ae {F : ℝ → ℂ} (hF : Continuous F)
    (h : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ F t) : 0 ≤ F 0 := by
  have he : F =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => ((max (0 : ℝ) (F t).re : ℝ) : ℂ)) := by
    filter_upwards [h] with t ht
    obtain ⟨hr, hi⟩ := Complex.le_def.mp ht
    apply Complex.ext
    · exact (max_eq_right (show (0 : ℝ) ≤ (F t).re from hr)).symm
    · simpa only [Complex.ofReal_im, Complex.zero_im] using hi.symm
  have hall := Measure.eqOn_open_of_ae_eq he isOpen_Ioi hF.continuousOn
    (Complex.continuous_ofReal.comp (continuous_const.max (Complex.continuous_re.comp hF))).continuousOn
  apply ge_of_tendsto (x := 𝓝[>] (0 : ℝ))
    (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [hall ht, Complex.zero_le_real]
  exact le_max_left _ _

/-- Positivity of a single literal packet exposes the alternating difference at its rate. -/
theorem burnolPacketCoefficient_zero_nonneg
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (φ : ℝ → ℂ)
    (hφ : ∀ (lam : ℝ) (hlam : 0 < lam), T (burnolRateFeature lam hlam) =
      φ lam • burnolRateFeature lam hlam)
    (δ : ℝ≥0) (n : ℕ) (lam : Ioi (0 : ℝ))
    (hp : 0 ≤ T (burnolPositivePacket δ n lam)) :
    0 ≤ burnolPacketCoefficient φ δ n lam 0 := by
  apply nonneg_at_zero_of_continuous_ae (continuous_burnolPacketCoefficient φ δ lam n)
  filter_upwards [burnolPositivePacket_image_ae T φ hφ δ n lam,
    (Lp.coeFn_nonneg _).mpr hp, ae_restrict_mem measurableSet_Ioi] with t he ht htpos
  change (0 : ℂ) ≤ _ at ht
  rw [he] at ht
  have hw : 0 < t * Real.exp (-(lam * t)) := mul_pos htpos (Real.exp_pos _)
  have hh := Complex.le_def.mp ht
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.zero_im] at hh
  apply Complex.le_def.mpr
  constructor
  · exact nonneg_of_mul_nonneg_right hh.1 hw
  · exact ((mul_eq_zero.mp hh.2.symm).resolve_left hw.ne').symm

end GaloisForLFunctions.HTGeometry
