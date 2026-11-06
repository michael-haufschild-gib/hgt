import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairGaussianRemainder
import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomRadialProfile

/-!
# Gaussian coercivity of finite theta-pair heads

Each finite ordinary-pair current head vanishes at high frequency.
Gaussian Hankel completeness converts this decay into the absence of
a positive lower margin uniform over every finite rank.
-/

open MeasureTheory Set Complex Filter Polynomial
open scoped BigOperators ENNReal Topology FourierTransform SchwartzMap
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower
noncomputable section

private theorem pairScale_two_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) : 2 ≤ Real.pi * n * m * Real.exp r := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 := le_mul_of_one_le_right Real.pi_pos.le hnR
  have h2 := le_mul_of_one_le_right (show 0 ≤ Real.pi * n by positivity) hmR
  have h3 := le_mul_of_one_le_right (show 0 ≤ Real.pi * n * m by positivity)
    (Real.one_le_exp hr)
  linarith only [Real.pi_gt_three, h1, h2, h3]

private theorem besselTail_eq_schwartz_fourier {q : ℝ} (hq : 2 ≤ q) (b : ℝ) :
    besselFirstAtomTailDensity (b / 2) q =
      (SchwartzMap.fourierTransformCLM ℂ (firstAtomRadialTailSchwartz q hq)
        (-b / Real.pi)).re := by
  have h := fourier_firstAtomRadialTail_re hq (-b / Real.pi)
  have he : -Real.pi * (-b / Real.pi) / 2 = b / 2 := by
    field_simp [Real.pi_ne_zero]
  simpa only [he, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe] using h.symm

private theorem continuous_besselTail_frequency {q : ℝ} (hq : 2 ≤ q) :
    Continuous (fun b : ℝ => besselFirstAtomTailDensity (b / 2) q) := by
  simp_rw [besselTail_eq_schwartz_fourier hq]
  exact Complex.continuous_re.comp
    ((SchwartzMap.fourierTransformCLM ℂ (firstAtomRadialTailSchwartz q hq)).continuous.comp
      (continuous_id.neg.div_const Real.pi))

private theorem tendsto_besselTail_frequency {q : ℝ} (hq : 2 ≤ q) :
    Tendsto (fun b : ℝ => besselFirstAtomTailDensity (b / 2) q) atTop (𝓝 0) := by
  let f := SchwartzMap.fourierTransformCLM ℂ (firstAtomRadialTailSchwartz q hq)
  have hs : Tendsto (fun b : ℝ => -b / Real.pi) atTop atBot := by
    have h := Filter.Tendsto.atTop_mul_const_of_neg'
      (neg_neg_of_pos (inv_pos.mpr Real.pi_pos))
      (tendsto_id : Tendsto (fun b : ℝ => b) atTop atTop)
    simpa only [div_eq_mul_inv, neg_mul, mul_neg, id_eq] using h
  have h := Complex.continuous_re.tendsto (0 : ℂ) |>.comp
    (f.tendsto_cocompact.comp (hs.mono_right atBot_le_cocompact))
  simpa only [Function.comp_def, Complex.zero_re, f, ← besselTail_eq_schwartz_fourier hq] using h

private theorem continuous_pairTail_frequency {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) : Continuous (thetaPairCenterTailSpectrum n m r) := by
  have he : thetaPairCenterTailSpectrum n m r = fun b =>
      Real.cos (b * (Real.log n - Real.log m)) *
        (4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) *
          besselFirstAtomTailDensity (b / 2) (Real.pi * n * m * Real.exp r)) :=
    funext (thetaPairCenterTailSpectrum_eq hn hm hr)
  rw [he]
  exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).mul
    (continuous_const.mul (continuous_besselTail_frequency (pairScale_two_le hn hm hr)))

private theorem tendsto_pairTail_frequency {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (thetaPairCenterTailSpectrum n m r) atTop (𝓝 0) := by
  have hA : Tendsto (thetaPairCenterTailAmplitude n m r) atTop (𝓝 0) := by
    change Tendsto (fun b : ℝ => 4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) *
      besselFirstAtomTailDensity (b / 2) (Real.pi * n * m * Real.exp r)) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_besselTail_frequency (pairScale_two_le hn hm hr)).const_mul
        (4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)))
  have hbound (b : ℝ) : ‖thetaPairCenterTailSpectrum n m r b‖ ≤
      ‖thetaPairCenterTailAmplitude n m r b‖ := by
    rw [thetaPairCenterTailSpectrum_eq hn hm hr, norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  exact squeeze_zero_norm hbound (by simpa only [norm_zero] using hA.norm)

/-- Each aperture pair is continuous in frequency and vanishes at positive infinity. -/
theorem thetaPairApertureSpectrum_continuous_and_decay {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaPairApertureSpectrum n m a) ∧
      Tendsto (thetaPairApertureSpectrum n m a) atTop (𝓝 0) := by
  let B := 4 * besselFirstAtomTailCost 0 * Real.exp (-(Real.pi * ((n : ℝ) * m)))
  let bound : ℝ → ℝ := fun r => B * (thetaCuspCenterTailWeight a r * Real.exp (-3 * r))
  let F : ℝ → ℝ → ℝ := fun b r =>
    thetaCuspCenterTailWeight a r * thetaPairCenterTailSpectrum n m r b
  have hmeas (b : ℝ) : AEStronglyMeasurable (F b) (volume.restrict (Ioi 0)) :=
    (integrableOn_weight_mul_thetaPairCenterTailSpectrum hn hm ha0 ha b).aestronglyMeasurable
  have hbound (b : ℝ) : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ‖F b r‖ ≤ bound r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hw := thetaCuspCenterTailWeight_nonneg ha0 hr.le
    dsimp only [F, bound]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ thetaCuspCenterTailWeight a r * (B * Real.exp (-3 * r)) :=
        mul_le_mul_of_nonneg_left (abs_thetaPairCenterTailSpectrum_center_decay hn hm hr.le b) hw
      _ = _ := by ring
  have hi : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_thetaCenterWeight_exp_three ha0 ha).const_mul B
  constructor
  · change Continuous (fun b : ℝ => ∫ r in Ioi (0 : ℝ), F b r)
    apply continuous_of_dominated hmeas hbound hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact continuous_const.mul (continuous_pairTail_frequency hn hm hr.le)
  · change Tendsto (fun b : ℝ => ∫ r in Ioi (0 : ℝ), F b r) atTop (𝓝 0)
    have hlim : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
        Tendsto (fun b => F b r) atTop (𝓝 0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simpa only [F, mul_zero] using
        (tendsto_pairTail_frequency hn hm hr.le).const_mul (thetaCuspCenterTailWeight a r)
    have h := tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (F := F) (f := fun _ => (0 : ℝ)) bound
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hi hlim
    simpa only [integral_zero] using h

/-- Every finite ordinary-pair head is continuous and vanishes at high frequency. -/
theorem thetaPairApertureCurrentHead_continuous_and_decay {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (M : ℕ) :
    Continuous (thetaPairApertureCurrentHead M a) ∧
      Tendsto (thetaPairApertureCurrentHead M a) atTop (𝓝 0) := by
  have hp (p : ℕ × ℕ) := thetaPairApertureSpectrum_continuous_and_decay
    (Nat.succ_pos p.1) (Nat.succ_pos p.2) ha0 ha
  constructor
  · exact continuous_const.mul (continuous_finsetSum _ (fun p _ => (hp p).1))
  · change Tendsto (fun b : ℝ => 2 * ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
      thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b) atTop (𝓝 0)
    have h := tendsto_finsetSum (Finset.range M ×ˢ Finset.range M)
      (fun p _ => (hp p).2)
    simpa only [Finset.sum_const_zero, mul_zero] using h.const_mul 2

private theorem head_memLp {a tau : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (M : ℕ) :
    MemLp (thetaPairApertureCurrentHead M a) ∞ (gaussianWindowMeasure tau) := by
  have hA : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  let J := thetaCuspCenterMixedFourierCurrent a hA
  have hJ := thetaCuspCenterMixedFourierCurrent_memLp_top tau a hA
  have hd : MemLp (fun b => J b - thetaPairApertureCurrentHead M a b)
      ∞ (gaussianWindowMeasure tau) := by
    apply memLp_top_of_bound
      ((continuous_thetaCuspCenterMixedFourierCurrent a hA).sub
        (thetaPairApertureCurrentHead_continuous_and_decay ha0 ha M).1).aestronglyMeasurable
      (thetaPairCurrentRemainderBound a M)
    filter_upwards with b
    change ‖J b - thetaPairApertureCurrentHead M a b‖ ≤ _
    rw [Real.norm_eq_abs]
    exact thetaCuspCenterMixedFourierCurrent_pair_remainder_le ha0 ha b M
  have he : thetaPairApertureCurrentHead M a =
      J - (fun b => J b - thetaPairApertureCurrentHead M a b) := by
    funext b
    change _ = J b - (J b - _)
    ring
  rw [he]
  exact hJ.sub hd

/-- The one-atom Gaussian Hankel sections are strictly positive at every finite rank. -/
theorem thetaPairApertureCurrentHead_one_gaussian_posDef {a tau : ℝ}
    (ha0 : 0 < a) (ha : a < 1 / 2) (htau : 0 < tau) (N : ℕ) :
    (_root_.HTGeometry.momentHankelMatrix
      (weightedMoment (gaussianWindowMeasure tau) (thetaPairApertureCurrentHead 1 a)) N).PosDef := by
  have hp (b : ℝ) : 0 < thetaPairApertureCurrentHead 1 a b := by
    simpa [thetaPairApertureCurrentHead, Finset.range_one] using
      mul_pos (show (0 : ℝ) < 2 by norm_num)
        (thetaPairApertureSpectrum_diagonal_pos (show 0 < 1 by decide) ha0 ha b)
  exact gaussianWindow_momentHankelMatrix_posDef_of_nonneg htau
    (thetaPairApertureCurrentHead_continuous_and_decay ha0.le ha 1).1
    (fun b => (hp b).le) (head_memLp ha0.le ha 1) (hp 0) N

private theorem gaussian_hankel_floor_iff {tau : ℝ} (htau : 0 < tau)
    (f : ℝ → ℝ) (hf : Continuous f) (hfb : MemLp f ∞ (gaussianWindowMeasure tau)) (c : ℝ) :
    (∀ (N : ℕ) (v : Fin N → ℝ),
      c * (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (fun _ => 1) (i.val + j.val)) ≤
      ∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) f (i.val + j.val)) ↔
      ∀ b : ℝ, c ≤ f b := by
  letI := gaussianWindowMeasure_finite htau
  have hmu := gaussianWindowMeasure_hasEntireExponentialMoments htau
  have hc : MemLp (fun _ : ℝ => c) ∞ (gaussianWindowMeasure tau) := memLp_const c
  have hm (k : ℕ) : weightedMoment (gaussianWindowMeasure tau) (fun b => f b - c) k =
      weightedMoment (gaussianWindowMeasure tau) f k -
        c * weightedMoment (gaussianWindowMeasure tau) (fun _ => 1) k := by
    have hi := integrable_monomial_mul_of_entireExponentialMoments hmu f hfb k
    have hj := integrable_monomial_mul_of_entireExponentialMoments hmu (fun _ => c) hc k
    unfold weightedMoment
    simp_rw [mul_sub]
    rw [integral_sub hi hj, integral_mul_const]
    simp only [mul_one]
    ring
  have hs (N : ℕ) (v : Fin N → ℝ) :
      (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (fun b => f b - c) (i.val + j.val)) =
      (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) f (i.val + j.val)) -
      c * (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (fun _ => 1) (i.val + j.val)) := by
    simp_rw [hm, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hiff := completeHankelCone_weightedMoment_iff hmu (fun b => f b - c)
    (hf.sub continuous_const) (hfb.sub hc)
  constructor
  · intro h b
    have hcone : CompleteHankelCone (weightedMoment (gaussianWindowMeasure tau)
        (fun b => f b - c)) := by
      intro N v
      rw [hs]
      exact sub_nonneg.mpr (h N v)
    exact sub_nonneg.mp (hiff.mp hcone b)
  · intro h N v
    have hcone := hiff.mpr (fun b => sub_nonneg.mpr (h b))
    have hh := hcone N v
    rw [hs] at hh
    exact sub_nonneg.mp hh

/-- The all-rank Gaussian margins of a finite theta head are exactly its pointwise lower bounds. -/
theorem thetaPairApertureCurrentHead_gaussian_floor_iff {a tau : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (htau : 0 < tau) (M : ℕ) (c : ℝ) :
    (∀ (N : ℕ) (v : Fin N → ℝ),
      c * (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (fun _ => 1) (i.val + j.val)) ≤
      ∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (thetaPairApertureCurrentHead M a)
          (i.val + j.val)) ↔
      ∀ b : ℝ, c ≤ thetaPairApertureCurrentHead M a b :=
  gaussian_hankel_floor_iff htau _
    (thetaPairApertureCurrentHead_continuous_and_decay ha0 ha M).1 (head_memLp ha0 ha M) c

/-- No fixed theta-pair head has a positive Gaussian lower margin simultaneously at all ranks. -/
theorem thetaPairApertureCurrentHead_no_uniform_gaussian_floor {a tau c : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (htau : 0 < tau) (hc : 0 < c) (M : ℕ) :
    ∃ (N : ℕ) (v : Fin N → ℝ),
      (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (thetaPairApertureCurrentHead M a)
          (i.val + j.val)) <
      c * (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (fun _ => 1) (i.val + j.val)) := by
  by_contra h
  push Not at h
  have hlim := (thetaPairApertureCurrentHead_continuous_and_decay ha0 ha M).2
  have hpoint := (thetaPairApertureCurrentHead_gaussian_floor_iff ha0 ha htau M c).mp h
  obtain ⟨b, hb⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
  exact (not_lt_of_ge (hpoint b)) hb

/-- At positive aperture the explicit uniform truncation cost is strictly positive. -/
theorem thetaPairCurrentRemainderBound_pos {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (M : ℕ) : 0 < thetaPairCurrentRemainderBound a M := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hp := besselFirstAtomTailDensity_pos
    (show 1 + Real.sqrt 2 < (4 : ℝ) by linarith only [hsqrt]) 0
  have hb := abs_besselFirstAtomTailDensity_le (show (1 : ℝ) ≤ 4 by norm_num) 0
  have hCprod : 0 < besselFirstAtomTailCost 0 * Real.exp (-4) :=
    hp.trans_le ((le_abs_self _).trans hb)
  have hC : 0 < besselFirstAtomTailCost 0 := by
    by_contra h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt h) (Real.exp_pos (-4)).le)) hCprod
  have hden : 0 < 9 - a ^ 2 := by
    nlinarith only [mul_pos ha0 (sub_pos.mpr ha), ha]
  have hex : 0 < 1 - Real.exp (-Real.pi) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos))
  unfold thetaPairCurrentRemainderBound
  positivity

/-- A fixed head never dominates its own positive uniform error at every Gaussian Hankel rank. -/
theorem thetaPairApertureCurrentHead_cannot_pay_uniform_remainder {a tau : ℝ}
    (ha0 : 0 < a) (ha : a < 1 / 2) (htau : 0 < tau) (M : ℕ) :
    ∃ (N : ℕ) (v : Fin N → ℝ),
      (∑ i : Fin N, ∑ j : Fin N, v i * v j *
        weightedMoment (gaussianWindowMeasure tau) (thetaPairApertureCurrentHead M a)
          (i.val + j.val)) <
      thetaPairCurrentRemainderBound a M *
        (∑ i : Fin N, ∑ j : Fin N, v i * v j *
          weightedMoment (gaussianWindowMeasure tau) (fun _ => 1) (i.val + j.val)) :=
  thetaPairApertureCurrentHead_no_uniform_gaussian_floor ha0.le ha htau
    (thetaPairCurrentRemainderBound_pos ha0 ha M) M

end
end GaloisForLFunctions.CompletedArithmeticForms
