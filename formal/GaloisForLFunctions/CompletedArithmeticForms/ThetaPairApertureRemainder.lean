import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairCenterTailReassembly
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailRepresentation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorqueArchLaplace

/-!
# Aperture-weighted truncation of the full theta-pair sum

The ordinary-pair truncation error decays exponentially in the center
cutoff. Integrating against the exact aperture weight gives a remainder
uniform in frequency, with an explicit factor vanishing linearly with
the aperture.
-/

open MeasureTheory Set Complex Filter
open scoped BigOperators
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower
noncomputable section

private theorem weight_exp_three_eq (a r : ℝ) :
    thetaCuspCenterTailWeight a r * Real.exp (-3 * r) =
      (1 / 2 : ℝ) * ((a * r + 1) * Real.exp (a * r) * Real.exp (-3 * r) +
        (a * r + (-1)) * Real.exp ((-a) * r) * Real.exp (-3 * r)) := by
  unfold thetaCuspCenterTailWeight
  rw [Real.sinh_eq, Real.cosh_eq, show -(a * r) = (-a) * r by ring]
  ring

/-- The exponential majorant is integrable with the exact aperture weight. -/
theorem integrableOn_thetaCenterWeight_exp_three {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    IntegrableOn (fun r : ℝ => thetaCuspCenterTailWeight a r * Real.exp (-3 * r)) (Ioi 0) := by
  have hplus := integrableOn_affineExp (a := a) (b := 1) (c := a) (σ := 3)
    (by linarith only [ha])
  have hminus := integrableOn_affineExp (a := a) (b := -1) (c := -a) (σ := 3)
    (by linarith only [ha0])
  exact Integrable.congr ((hplus.add hminus).const_mul (1 / 2 : ℝ))
    (Filter.Eventually.of_forall fun r => (weight_exp_three_eq a r).symm)

/-- The exact aperture dependence of the integrable exponential majorant. -/
theorem integral_thetaCenterWeight_exp_three {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    (∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r * Real.exp (-3 * r)) =
      18 * a / (9 - a ^ 2) ^ 2 := by
  have hp : a < 3 := by linarith only [ha]
  have hm : -a < 3 := by linarith only [ha0]
  have hplus := integrableOn_affineExp (a := a) (b := 1) hp
  have hminus := integrableOn_affineExp (a := a) (b := -1) hm
  simp_rw [weight_exp_three_eq]
  rw [integral_const_mul, integral_add hplus hminus,
    integral_affineExp hp, integral_affineExp hm]
  simp only [sub_neg_eq_add]
  have hd1 : 3 - a ≠ 0 := (sub_pos.mpr hp).ne'
  have hd2 : 3 + a ≠ 0 := (show 0 < 3 + a by linarith only [ha0]).ne'
  have hd : 9 - a ^ 2 ≠ 0 := by
    rw [show 9 - a ^ 2 = (3 - a) * (3 + a) by ring]
    exact mul_ne_zero hd1 hd2
  field_simp [hd1, hd2, hd]
  ring

private theorem exp_pairScale_decay {r k : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k) :
    Real.exp (-(Real.pi * Real.exp r * k)) ≤
      Real.exp (-(Real.pi * k)) * Real.exp (-3 * r) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hpk : 3 ≤ Real.pi * k :=
    Real.pi_gt_three.le.trans (le_mul_of_one_le_right Real.pi_pos.le hk)
  have hx := mul_le_mul_of_nonneg_left (Real.add_one_le_exp r)
    (mul_nonneg Real.pi_pos.le hk0)
  have hy := mul_le_mul_of_nonneg_right hpk hr
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith only [hx, hy])

/-- Each ordinary pair retains exponential center decay before aperture integration. -/
theorem abs_thetaPairCenterTailSpectrum_center_decay {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    |thetaPairCenterTailSpectrum n m r b| ≤
      (4 * besselFirstAtomTailCost 0 * Real.exp (-(Real.pi * ((n : ℝ) * m)))) *
        Real.exp (-3 * r) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnm : (1 : ℝ) ≤ (n : ℝ) * m :=
    hnR.trans (le_mul_of_one_le_right (by positivity) hmR)
  have h := mul_le_mul_of_nonneg_left (exp_pairScale_decay hr hnm)
    (show 0 ≤ 4 * besselFirstAtomTailCost 0 from
      mul_nonneg (by norm_num) (besselFirstAtomTailCost_nonneg 0))
  have hb := abs_thetaPairCenterTailSpectrum_uniform_le hn hm hr b
  apply hb.trans
  simpa only [mul_assoc] using h

private theorem one_sub_exp_neg_pi_pos : 0 < 1 - Real.exp (-Real.pi) :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos))

/-- A single exponential in the center controls the whole rectangular truncation error. -/
theorem thetaPairCenterTailSum_remainder_center_decay {r : ℝ} (hr : 0 ≤ r)
    (b : ℝ) (M : ℕ) :
    |thetaPairCenterTailSum r b - ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
      thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b| ≤
      (8 * besselFirstAtomTailCost 0 * Real.exp (-Real.pi * ((M : ℝ) + 1)) /
        (1 - Real.exp (-Real.pi)) ^ 2) * Real.exp (-3 * r) := by
  have hC := besselFirstAtomTailCost_nonneg 0
  have hq : Real.pi ≤ Real.pi * Real.exp r :=
    le_mul_of_one_le_right Real.pi_pos.le (Real.one_le_exp hr)
  have hd : 1 - Real.exp (-Real.pi) ≤ 1 - Real.exp (-(Real.pi * Real.exp r)) :=
    sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hq)) 1
  have hd2 : (1 - Real.exp (-Real.pi)) ^ 2 ≤
      (1 - Real.exp (-(Real.pi * Real.exp r))) ^ 2 :=
    pow_le_pow_left₀ one_sub_exp_neg_pi_pos.le hd 2
  have he := exp_pairScale_decay hr
    (show (1 : ℝ) ≤ (M : ℝ) + 1 by exact le_add_of_nonneg_left (Nat.cast_nonneg M))
  calc
    _ ≤ 8 * besselFirstAtomTailCost 0 *
        Real.exp (-(Real.pi * Real.exp r) * ((M : ℝ) + 1)) /
        (1 - Real.exp (-(Real.pi * Real.exp r))) ^ 2 :=
      thetaPairCenterTailSum_remainder_le hr b M
    _ ≤ 8 * besselFirstAtomTailCost 0 *
        Real.exp (-(Real.pi * Real.exp r) * ((M : ℝ) + 1)) /
        (1 - Real.exp (-Real.pi)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos one_sub_exp_neg_pi_pos) hd2
    _ ≤ 8 * besselFirstAtomTailCost 0 *
        (Real.exp (-(Real.pi * ((M : ℝ) + 1))) * Real.exp (-3 * r)) /
        (1 - Real.exp (-Real.pi)) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hC)
      simpa only [neg_mul] using he
    _ = _ := by simp only [neg_mul]; ring

/-- Ordinary-pair tails are measurable functions of the center cutoff. -/
theorem stronglyMeasurable_thetaPairCenterTailSpectrum (n m : ℕ) (b : ℝ) :
    StronglyMeasurable (fun r => thetaPairCenterTailSpectrum n m r b) := by
  let K : ℝ × ℝ → ℂ := fun p =>
    (thetaCuspSourceTerm (p.1 / 2 + p.2) n *
      thetaCuspSourceTerm (p.1 / 2 - p.2) m : ℂ) * thetaWignerDifferencePhase b p.2
  have hK : Continuous K := by
    unfold K thetaCuspSourceTerm thetaCuspSeed thetaWignerDifferencePhase
    fun_prop
  have hC := hK.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  let g : ℝ → ℝ := fun s => (thetaCuspSourcePairWigner n m (s / 2) b).re
  have hg : StronglyMeasurable g := by
    simpa only [g, K, thetaCuspSourcePairWigner] using
      Complex.continuous_re.comp_stronglyMeasurable hC
  have ht := (hg.comp_measurable (measurable_fst.add measurable_snd)).integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))
  have he : (fun r => thetaPairCenterTailSpectrum n m r b) =
      fun r => ∫ t in Ioi (0 : ℝ), g (r + t) := by
    funext r
    have h := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right g r r
    rw [sub_self] at h
    change (∫ s in Ioi r, g s) = _
    apply h.symm.trans
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change g (t + r) = g (r + t)
    rw [add_comm t r]
  rw [he]
  exact ht

private theorem stronglyMeasurable_pairTailSum (b : ℝ) :
    StronglyMeasurable (fun r => thetaPairCenterTailSum r b) := by
  exact (Measurable.tsum (fun p : ℕ × ℕ =>
    (stronglyMeasurable_thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) b).measurable)).stronglyMeasurable

private theorem integrableOn_weight_mul_of_exp_bound {a B : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    {f : ℝ → ℝ} (hf : StronglyMeasurable f)
    (hb : ∀ r : ℝ, 0 ≤ r → |f r| ≤ B * Real.exp (-3 * r)) :
    IntegrableOn (fun r => thetaCuspCenterTailWeight a r * f r) (Ioi 0) := by
  have hw : Continuous (thetaCuspCenterTailWeight a) := by
    unfold thetaCuspCenterTailWeight
    fun_prop
  apply ((integrableOn_thetaCenterWeight_exp_three ha0 ha).const_mul B).mono'
    (hw.stronglyMeasurable.mul hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hwr := thetaCuspCenterTailWeight_nonneg ha0 hr.le
  change ‖thetaCuspCenterTailWeight a r * f r‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwr]
  calc
    _ ≤ thetaCuspCenterTailWeight a r * (B * Real.exp (-3 * r)) :=
      mul_le_mul_of_nonneg_left (hb r hr.le) hwr
    _ = _ := by ring

/-- Every ordinary-pair tail can be integrated against the complete aperture weight. -/
theorem integrableOn_weight_mul_thetaPairCenterTailSpectrum {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    IntegrableOn (fun r => thetaCuspCenterTailWeight a r * thetaPairCenterTailSpectrum n m r b)
      (Ioi 0) :=
  integrableOn_weight_mul_of_exp_bound ha0 ha
    (stronglyMeasurable_thetaPairCenterTailSpectrum n m b)
    (fun _ hr => abs_thetaPairCenterTailSpectrum_center_decay hn hm hr b)

/-- The complete ordinary-pair sum has an absolutely integrable aperture weight. -/
theorem integrableOn_weight_mul_thetaPairCenterTailSum {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) (b : ℝ) :
    IntegrableOn (fun r => thetaCuspCenterTailWeight a r * thetaPairCenterTailSum r b) (Ioi 0) := by
  apply integrableOn_weight_mul_of_exp_bound ha0 ha (stronglyMeasurable_pairTailSum b)
    (B := 8 * besselFirstAtomTailCost 0 * Real.exp (-Real.pi) /
      (1 - Real.exp (-Real.pi)) ^ 2)
  intro r hr
  simpa using thetaPairCenterTailSum_remainder_center_decay hr b 0

/-- One ordinary-pair Fourier tail with the exact aperture weight retained. -/
def thetaPairApertureSpectrum (n m : ℕ) (a b : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r * thetaPairCenterTailSpectrum n m r b

/-- The literal full-source Fourier tail integrated against the aperture weight. -/
def thetaFullApertureTail (a b : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r *
    (∫ s in Ioi r, (thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re)

/-- The aperture-weighted full source has an explicit truncation error uniform in frequency. -/
theorem thetaFullApertureTail_remainder_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (b : ℝ) (M : ℕ) :
    |thetaFullApertureTail a b - ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
      thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b| ≤
      144 * a * besselFirstAtomTailCost 0 * Real.exp (-Real.pi * ((M : ℝ) + 1)) /
        ((9 - a ^ 2) ^ 2 * (1 - Real.exp (-Real.pi)) ^ 2) := by
  let S := Finset.range M ×ˢ Finset.range M
  let D := 8 * besselFirstAtomTailCost 0 * Real.exp (-Real.pi * ((M : ℝ) + 1)) /
    (1 - Real.exp (-Real.pi)) ^ 2
  have hfull := integrableOn_weight_mul_thetaPairCenterTailSum ha0 ha b
  have hp (p : ℕ × ℕ) : IntegrableOn (fun r => thetaCuspCenterTailWeight a r *
      thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b) (Ioi 0) :=
    integrableOn_weight_mul_thetaPairCenterTailSpectrum (Nat.succ_pos _) (Nat.succ_pos _) ha0 ha b
  have hhead : IntegrableOn (fun r => ∑ p ∈ S, thetaCuspCenterTailWeight a r *
      thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b) (Ioi 0) :=
    integrable_finsetSum S (fun p _ => hp p)
  have he : thetaFullApertureTail a b - ∑ p ∈ S,
      thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b =
      ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r * thetaPairCenterTailSum r b -
        ∑ p ∈ S, thetaCuspCenterTailWeight a r *
          thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b := by
    unfold thetaFullApertureTail thetaPairApertureSpectrum
    simp_rw [← thetaPairCenterTailSum_eq_fullSource]
    rw [integral_sub hfull hhead, integral_finsetSum S (fun p _ => hp p)]
  change |thetaFullApertureTail a b - ∑ p ∈ S,
    thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b| ≤ _
  rw [he]
  have hmajor := (integrableOn_thetaCenterWeight_exp_three ha0 ha).const_mul D
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), ‖thetaCuspCenterTailWeight a r * thetaPairCenterTailSum r b -
        ∑ p ∈ S, thetaCuspCenterTailWeight a r *
          thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
          (fun r : ℝ => thetaCuspCenterTailWeight a r * thetaPairCenterTailSum r b -
            ∑ p ∈ S, thetaCuspCenterTailWeight a r *
              thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b))
    _ ≤ ∫ r in Ioi (0 : ℝ), D * (thetaCuspCenterTailWeight a r * Real.exp (-3 * r)) := by
      apply integral_mono_ae (hfull.sub hhead).norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hw := thetaCuspCenterTailWeight_nonneg ha0 hr.le
      change ‖thetaCuspCenterTailWeight a r * thetaPairCenterTailSum r b -
        ∑ p ∈ S, thetaCuspCenterTailWeight a r *
          thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b‖ ≤ _
      rw [Real.norm_eq_abs, ← Finset.mul_sum, ← mul_sub, abs_mul, abs_of_nonneg hw]
      have h := mul_le_mul_of_nonneg_left
        (thetaPairCenterTailSum_remainder_center_decay hr.le b M) hw
      calc
        _ ≤ thetaCuspCenterTailWeight a r * (D * Real.exp (-3 * r)) := h
        _ = _ := by ring
    _ = D * (18 * a / (9 - a ^ 2) ^ 2) := by
      rw [integral_const_mul, integral_thetaCenterWeight_exp_three ha0 ha]
    _ = _ := by
      dsimp only [D]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem integral_Ioi_pos_of_pos {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (hpos : ∀ r, 0 < r → 0 < f r) :
    0 < ∫ r in Ioi (0 : ℝ), f r := by
  have hn : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ f r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hpos r hr).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn hf]
  have hs : Function.support f ∩ Ioi (0 : ℝ) = Ioi 0 := by
    ext r
    exact ⟨fun h => h.2, fun h => ⟨(hpos r h).ne', h⟩⟩
  rw [hs, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- A nonzero aperture preserves the exact log-ratio cosine sign of each pair. -/
theorem thetaPairApertureSpectrum_nonneg_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (b : ℝ) :
    0 ≤ thetaPairApertureSpectrum n m a b ↔
      0 ≤ Real.cos (b * (Real.log n - Real.log m)) := by
  constructor
  · intro h
    by_contra hc
    have hcneg : Real.cos (b * (Real.log n - Real.log m)) < 0 := lt_of_not_ge hc
    have hint := (integrableOn_weight_mul_thetaPairCenterTailSpectrum hn hm ha0.le ha b).neg
    have hp := integral_Ioi_pos_of_pos hint (fun r hr => by
      have hw := thetaCuspCenterTailWeight_pos ha0 hr
      have hT : thetaPairCenterTailSpectrum n m r b < 0 := by
        rw [thetaPairCenterTailSpectrum_eq hn hm hr.le]
        exact mul_neg_of_neg_of_pos hcneg (thetaPairCenterTailAmplitude_pos hn hm hr.le b)
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hw hT))
    simp only [Pi.neg_apply, integral_neg] at hp
    exact (not_lt_of_ge h) (neg_pos.mp hp)
  · intro hc
    apply setIntegral_nonneg measurableSet_Ioi
    intro r hr
    exact mul_nonneg (thetaCuspCenterTailWeight_nonneg ha0.le hr.le)
      ((thetaPairCenterTailSpectrum_nonneg_iff hn hm hr.le b).mpr hc)

/-- Every diagonal pair remains strictly positive after aperture integration. -/
theorem thetaPairApertureSpectrum_diagonal_pos {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (b : ℝ) :
    0 < thetaPairApertureSpectrum n n a b := by
  exact integral_Ioi_pos_of_pos
    (integrableOn_weight_mul_thetaPairCenterTailSpectrum hn hn ha0.le ha b)
    (fun r hr => mul_pos (thetaCuspCenterTailWeight_pos ha0 hr)
      (thetaPairCenterTailSpectrum_diagonal_pos hn hr.le b))

/-- Aperture integration does not remove an unequal pair's negative frequency. -/
theorem thetaPairApertureSpectrum_unequal_neg {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hne : n ≠ m) {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    thetaPairApertureSpectrum n m a (Real.pi / (Real.log n - Real.log m)) < 0 := by
  have hp := integral_Ioi_pos_of_pos
    (integrableOn_weight_mul_thetaPairCenterTailSpectrum hn hm ha0.le ha _).neg
    (fun r hr => neg_pos.mpr (mul_neg_of_pos_of_neg
      (thetaCuspCenterTailWeight_pos ha0 hr)
      (thetaPairCenterTailSpectrum_unequal_neg hn hm hne hr.le)))
  simp only [Pi.neg_apply, integral_neg] at hp
  exact neg_pos.mp hp

/-- Strict positivity of a weighted pair is exactly positivity of its log-ratio cosine. -/
theorem thetaPairApertureSpectrum_pos_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (b : ℝ) :
    0 < thetaPairApertureSpectrum n m a b ↔
      0 < Real.cos (b * (Real.log n - Real.log m)) := by
  constructor
  · intro hp
    by_contra hc
    have hcnonpos := le_of_not_gt hc
    have hnonpos : thetaPairApertureSpectrum n m a b ≤ 0 := by
      apply setIntegral_nonpos measurableSet_Ioi
      intro r hr
      rw [thetaPairCenterTailSpectrum_eq hn hm hr.le]
      exact mul_nonpos_of_nonneg_of_nonpos
        (thetaCuspCenterTailWeight_nonneg ha0.le hr.le)
        (mul_nonpos_of_nonpos_of_nonneg hcnonpos
          (thetaPairCenterTailAmplitude_pos hn hm hr.le b).le)
    exact (not_lt_of_ge hnonpos) hp
  · intro hc
    apply integral_Ioi_pos_of_pos
      (integrableOn_weight_mul_thetaPairCenterTailSpectrum hn hm ha0.le ha b)
    intro r hr
    rw [thetaPairCenterTailSpectrum_eq hn hm hr.le]
    exact mul_pos (thetaCuspCenterTailWeight_pos ha0 hr)
      (mul_pos hc (thetaPairCenterTailAmplitude_pos hn hm hr.le b))

end
end GaloisForLFunctions.CompletedArithmeticForms
