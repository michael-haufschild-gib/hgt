import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringCore
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# Recovery of scattering charge from the finite-energy core

At every nonreal strip zeta zero the actual scattering-subtracted field obeys
`a * fieldCore w a → -scatteringCoefficient w`. The coefficient is nonzero
by the zeta functional equation, so the weighted square energy is strictly
positive. This is a statement about the canonical field itself.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringCore
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringCharge

/-- Below real part one, the outgoing coefficient cannot vanish. -/
theorem scatteringCoefficient_ne_zero {w : ℂ} (hw : w.re < 1) (him : 0 < w.im) :
    scatteringCoefficient w ≠ 0 :=
  div_ne_zero (_root_.RHTower.reflectedCompletedLambda_sub_one_ne_zero hw him.ne')
    (_root_.RHTower.Gammaℝ_ne_zero_of_im_ne_zero him.ne')

/-- Multiplication by height still leaves the normalized Fourier tail decaying to zero. -/
theorem scaledTail_tendsto_zero {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun a : ℝ => (a : ℂ)*normalizedTail w a) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun a : ℝ => tailCoefficient w*a^(-(w.re/2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by linarith only [hw] : 0 < w.re/2)).const_mul (tailCoefficient w)
  refine squeeze_zero' (Eventually.of_forall (fun a => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hp : a*a^(-w.re/2-1)=a^(-(w.re/2)) := by
    calc
      _ = a^(1 : ℝ)*a^(-w.re/2-1) := by rw [Real.rpow_one]
      _ = a^(1+(-w.re/2-1)) := (Real.rpow_add ha0 _ _).symm
      _ = _ := by congr 1; ring
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha0]
  calc
    _ ≤ a*(tailCoefficient w*a^(-w.re/2-1)) :=
      mul_le_mul_of_nonneg_left (normalizedTail_norm_le ha) ha0.le
    _ = tailCoefficient w*(a*a^(-w.re/2-1)) := by ring
    _ = _ := by rw [hp]

private theorem scaled_core_eq {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    (hz : riemannZeta w = 0) {a : ℝ} (ha : 0 < a) :
    (a : ℂ)*fieldCore w a=(a : ℂ)*normalizedTail w a-scatteringCoefficient w := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [fieldCore_eq_tail hw him ha,hz,zero_mul,sub_zero,Complex.cpow_neg_one]
  field_simp

/-- The canonical finite-energy field retains the exact outgoing scattering charge. -/
theorem core_charge_limit {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    (hz : riemannZeta w = 0) :
    Tendsto (fun a : ℝ => (a : ℂ)*fieldCore w a) atTop (𝓝 (-scatteringCoefficient w)) := by
  have h := (scaledTail_tendsto_zero hw).sub_const (scatteringCoefficient w)
  simp only [zero_sub] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (scaled_core_eq hw him hz ha).symm

/-- At a strip zeta zero, the canonical finite-energy field is eventually nowhere zero. -/
theorem core_eventually_ne_zero {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) :
    ∀ᶠ a : ℝ in atTop, fieldCore w a ≠ 0 := by
  have hn : -scatteringCoefficient w ≠ 0 := neg_ne_zero.mpr (scatteringCoefficient_ne_zero hw1 him)
  have h := (core_charge_limit hw him hz).eventually_ne hn
  filter_upwards [h] with a ha
  exact fun he => ha (by rw [he,mul_zero])

/-- The actual weighted square energy is strictly positive at every strip zeta zero. -/
theorem weighted_energy_pos {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) :
    0 < ∫ a in Ioi (0 : ℝ), a^(w.re-1)*‖fieldCore w a‖^2 := by
  have hnn : ∀ᵐ a : ℝ ∂volume.restrict (Ioi 0), 0 ≤ a^(w.re-1)*‖fieldCore w a‖^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (sq_nonneg _)
  rw [integral_pos_iff_support_of_nonneg_ae hnn
    (weighted_energy_integrable hw (by linarith only [hw1]) him)]
  obtain ⟨A,hA⟩ := eventually_atTop.mp (core_eventually_ne_zero hw hw1 him hz)
  let B : ℝ := max A 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hsub : Ioo B (B+1) ⊆ Function.support (fun a : ℝ => a^(w.re-1)*‖fieldCore w a‖^2) := by
    intro a ha
    have ha0 : 0 < a := hB.trans ha.1
    have hfa := hA a ((le_max_left A 1).trans ha.1.le)
    exact mul_ne_zero (Real.rpow_pos_of_pos ha0 _).ne' (pow_ne_zero 2 (norm_ne_zero_iff.mpr hfa))
  have hval : (volume.restrict (Ioi (0 : ℝ))) (Ioo B (B+1))=1 := by
    have hsub0 : Ioo B (B+1) ⊆ Ioi (0 : ℝ) := fun a ha => hB.trans ha.1
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr hsub0,Real.volume_Ioo]
    norm_num
  have hm := measure_mono (μ := volume.restrict (Ioi (0 : ℝ))) hsub
  rw [hval] at hm
  exact lt_of_lt_of_le zero_lt_one hm

#print axioms scatteringCoefficient_ne_zero
#print axioms scaledTail_tendsto_zero
#print axioms core_charge_limit
#print axioms core_eventually_ne_zero
#print axioms weighted_energy_pos

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringCharge
