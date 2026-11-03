import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisHeckePrimeThreeEigenvalue
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWindowCuspTransport

/-!
# Finite cusp energy survives every arithmetic Hecke word

A window lift may lose compact support after one or two Hecke steps. Its decay survives:
every determinant-two or determinant-three branch preserves the weight `(1+a)^(-2 Re s)`.
Thus all finite words in the actual source operators have finite upper Haar square energy
and finite dyadic cusp energy when `Re s>0`, at every window aperture.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Positive branch numerators and denominators add to at least the original weight. -/
private theorem branch_decay {s : ℂ} (hs : 0 ≤ s.re) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x > 0, ‖f x‖ ≤ C * (1 + x) ^ (-(2 * s.re)))
    {a u v : ℝ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v) (huv : 1 + a ≤ u + v) :
    ‖(v : ℂ) ^ (-(2 * s)) * f (u / v)‖ ≤ C * (1 + a) ^ (-(2 * s.re)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hre : (-(2 * s)).re = -(2 * s.re) := by simp
  rw [hre]
  calc
    v ^ (-(2 * s.re)) * ‖f (u / v)‖ ≤
        v ^ (-(2 * s.re)) * (C * (1 + u / v) ^ (-(2 * s.re))) :=
      mul_le_mul_of_nonneg_left (hf _ (div_pos hu hv)) (Real.rpow_pos_of_pos hv _).le
    _ = C * (u + v) ^ (-(2 * s.re)) := by
      have hm : v ^ (-(2 * s.re)) * (1 + u / v) ^ (-(2 * s.re)) =
          (u + v) ^ (-(2 * s.re)) := by
        rw [← Real.mul_rpow hv.le (by positivity)]
        congr 1
        field_simp [hv.ne']
        ring
      calc
        _ = C * (v ^ (-(2 * s.re)) * (1 + u / v) ^ (-(2 * s.re))) := by ring
        _ = _ := by rw [hm]
    _ ≤ C * (1 + a) ^ (-(2 * s.re)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) huv (by linarith)) hC

/-- The four source branches preserve weighted decay, with norm bound four. -/
theorem lewisHeckeT2_decay_bound {s : ℂ} (hs : 0 ≤ s.re) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x > 0, ‖f x‖ ≤ C * (1 + x) ^ (-(2 * s.re)))
    {a : ℝ} (ha : 0 < a) :
    ‖lewisHeckeT2 s f a‖ ≤ (4 * C) * (1 + a) ^ (-(2 * s.re)) := by
  have b0 := branch_decay hs hC hf ha (show 0 < 2 * a by positivity)
    (by norm_num : (0 : ℝ) < 1) (show 1 + a ≤ 2 * a + 1 by linarith)
  simp only [Complex.ofReal_one, one_cpow, one_mul, div_one] at b0
  have b1 := branch_decay hs hC hf ha ha
    (by norm_num : (0 : ℝ) < 2) (show 1 + a ≤ a + 2 by linarith)
  have b2 := branch_decay hs hC hf ha (show 0 < a + 1 by linarith)
    (by norm_num : (0 : ℝ) < 2) (show 1 + a ≤ (a + 1) + 2 by linarith)
  have b3 := branch_decay hs hC hf ha (show 0 < 2 * a by positivity)
    (show 0 < a + 1 by linarith) (show 1 + a ≤ 2 * a + (a + 1) by linarith)
  simp only [Complex.ofReal_ofNat] at b1 b2
  unfold lewisHeckeT2
  exact (norm_add_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add b0 b1)) b2)) b3).trans (by ring_nf; rfl))

/-- The seven source branches preserve weighted decay, with norm bound seven. -/
theorem lewisHeckeT3_decay_bound {s : ℂ} (hs : 0 ≤ s.re) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x > 0, ‖f x‖ ≤ C * (1 + x) ^ (-(2 * s.re)))
    {a : ℝ} (ha : 0 < a) :
    ‖lewisHeckeT3 s f a‖ ≤ (7 * C) * (1 + a) ^ (-(2 * s.re)) := by
  have b0 := branch_decay hs hC hf ha (show 0 < 3 * a by positivity)
    (by norm_num : (0 : ℝ) < 1) (show 1 + a ≤ 3 * a + 1 by linarith)
  simp only [Complex.ofReal_one, one_cpow, one_mul, div_one] at b0
  have b1 := branch_decay hs hC hf ha ha
    (by norm_num : (0 : ℝ) < 3) (show 1 + a ≤ a + 3 by linarith)
  have b2 := branch_decay hs hC hf ha (show 0 < a + 1 by linarith)
    (by norm_num : (0 : ℝ) < 3) (show 1 + a ≤ (a + 1) + 3 by linarith)
  have b3 := branch_decay hs hC hf ha (show 0 < 3 * a by positivity)
    (show 0 < a + 1 by linarith) (show 1 + a ≤ 3 * a + (a + 1) by linarith)
  have b4 := branch_decay hs hC hf ha (show 0 < a + 2 by linarith)
    (by norm_num : (0 : ℝ) < 3) (show 1 + a ≤ (a + 2) + 3 by linarith)
  have b5 := branch_decay hs hC hf ha (show 0 < 3 * a by positivity)
    (show 0 < 2 * a + 1 by linarith) (show 1 + a ≤ 3 * a + (2 * a + 1) by linarith)
  have b6 := branch_decay hs hC hf ha (show 0 < 2 * a + 1 by linarith)
    (show 0 < a + 2 by linarith) (show 1 + a ≤ (2 * a + 1) + (a + 2) by linarith)
  simp only [Complex.ofReal_ofNat] at b1 b2 b4
  have d01 := (norm_add_le _ _).trans (add_le_add b0 b1)
  have d23 := (norm_add_le _ _).trans (add_le_add b2 b3)
  have d45 := (norm_add_le _ _).trans (add_le_add b4 b5)
  have d0123 := (norm_add_le _ _).trans (add_le_add d01 d23)
  have d456 := (norm_add_le _ _).trans (add_le_add d45 b6)
  exact ((norm_add_le _ _).trans (add_le_add d0123 d456)).trans (by ring_nf; rfl)

private theorem window_zero_at_zero {A : ℝ} {H : ℝ → ℝ} (hc : Continuous H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) : H 0 = 0 := by
  have hseq : ∀ n : ℕ, H (1 / ((n : ℝ) + 1)) = 0 := by
    intro n
    apply hv
    intro hm
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hm.2]
  have htend1 : Tendsto (fun n : ℕ => H (1 / ((n : ℝ) + 1))) atTop (𝓝 (H 0)) :=
    (hc.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat)
  have htend0 : Tendsto (fun n : ℕ => H (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    rw [show (fun n : ℕ => H (1 / ((n : ℝ) + 1))) = fun _ : ℕ => (0 : ℝ) from funext hseq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique htend1 htend0

private theorem continuous_windowLogLift {A : ℝ} {H : ℝ → ℝ} (hc : Continuous H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    Continuous (windowLogLift s H) := by
  have hH0 : H 0 = 0 := window_zero_at_zero hc hv
  let f_pos : ℝ → ℂ := fun u => ((Real.exp (-((s.re - 1 / 4) * u)) * H (-u) : ℝ) : ℂ)
  let f_neg : ℝ → ℂ := fun u =>
    Complex.exp (-((2 * s - 1 / 2) * (u : ℂ))) *
      ((Real.exp ((s.re - 1 / 4) * u) * H u : ℝ) : ℂ)
  have hc_pos : Continuous f_pos := by
    dsimp [f_pos]; fun_prop
  have hc_neg : Continuous f_neg := by
    dsimp [f_neg]; fun_prop
  have hf_pos0 : f_pos 0 = 0 := by simp [f_pos, hH0]
  have hf_neg0 : f_neg 0 = 0 := by simp [f_neg, hH0]
  rw [continuous_iff_continuousAt]
  intro u₀
  rcases lt_trichotomy u₀ 0 with hlt | rfl | hgt
  · refine hc_neg.continuousAt.congr ?_
    filter_upwards [isOpen_Iio.mem_nhds hlt] with u hu
    have hnot : ¬ (0 < u) := not_lt.mpr (le_of_lt hu)
    simp [windowLogLift, f_neg, show u < 0 from hu, hnot]
  · rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.continuousAt_iff.mp hc_pos.continuousAt ε hε
    obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.continuousAt_iff.mp hc_neg.continuousAt ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun u hu => ?_⟩
    have hz0 : windowLogLift s H 0 = 0 := by simp [windowLogLift]
    rw [hz0]
    rcases lt_trichotomy u 0 with hlt | rfl | hgt
    · have hnot : ¬ (0 < u) := not_lt.mpr hlt.le
      have heq : windowLogLift s H u = f_neg u := by simp [windowLogLift, f_neg, hlt, hnot]
      rw [heq, ← hf_neg0]
      exact hb₂ (lt_of_lt_of_le hu (min_le_right _ _))
    · simp [windowLogLift, hε]
    · have heq : windowLogLift s H u = f_pos u := by simp [windowLogLift, f_pos, hgt]
      rw [heq, ← hf_pos0]
      exact hb₁ (lt_of_lt_of_le hu (min_le_left _ _))
  · refine hc_pos.continuousAt.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hgt] with u hu
    simp [windowLogLift, f_pos, show 0 < u from hu]

private theorem windowLogLift_eq_zero_of_notMem {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) {u : ℝ} (hu : u ∉ Icc (-A) A) :
    windowLogLift s H u = 0 := by
  unfold windowLogLift
  rcases lt_trichotomy u 0 with hlt | rfl | hgt
  · simp [hlt, not_lt.mpr hlt.le, hv u (fun hm => hu ⟨hm.1, hm.2.trans hA⟩)]
  · simp
  · simp [hgt, hv (-u) (fun hm => hu ⟨by linarith [hm.2, hA], by linarith [hm.1]⟩)]

private theorem continuousOn_windowPeriodLift {A : ℝ} {H : ℝ → ℝ}
    (hc : Continuous H) (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    ContinuousOn (windowPeriodLift s H) (Ioi 0) := by
  have hF := continuous_windowLogLift hc hv s
  intro a ha
  have ha0 : 0 < a := ha
  have hsum : a + a⁻¹ ≠ 0 := (add_pos ha0 (inv_pos.mpr ha0)).ne'
  have c1 : ContinuousAt (fun x : ℝ => (x + x⁻¹) ^ (3 : ℝ)) a :=
    (continuousAt_id.add (continuousAt_inv₀ ha0.ne')).rpow continuousAt_const (Or.inl hsum)
  have c2 : ContinuousAt (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) a :=
    continuousAt_id.rpow continuousAt_const (Or.inl ha0.ne')
  have c3 : ContinuousAt (fun x : ℝ => windowLogLift s H (Real.log x)) a :=
    ContinuousAt.comp hF.continuousAt (Real.continuousAt_log ha0.ne')
  have c12 := Complex.continuous_ofReal.continuousAt.comp (c1.mul c2)
  exact (c12.mul c3).continuousWithinAt

private theorem windowPeriodLift_zero_outside {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) {a : ℝ} (ha : 0 < a)
    (hna : a ∉ Icc (Real.exp (-A)) (Real.exp A)) : windowPeriodLift s H a = 0 := by
  have hlog : Real.log a ∉ Icc (-A) A := by
    intro h
    apply hna
    constructor
    · calc
        Real.exp (-A) ≤ Real.exp (Real.log a) := Real.exp_le_exp.mpr h.1
        _ = a := Real.exp_log ha
    · calc
        a = Real.exp (Real.log a) := (Real.exp_log ha).symm
        _ ≤ Real.exp A := Real.exp_le_exp.mpr h.2
  have hz := windowLogLift_eq_zero_of_notMem hA hv s hlog
  simp only [windowPeriodLift, logPeriodInverse, hz, mul_zero]

private theorem compact_positive_decay_bound {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0))
    {l u : ℝ} (hl : 0 < l) (hz : ∀ a > 0, a ∉ Icc l u → f a = 0) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0, ‖f a‖ ≤ C * (1 + a) ^ (-r) := by
  have hcont : ContinuousOn (fun a : ℝ => (1 + a) ^ r * ‖f a‖) (Icc l u) := by
    intro a ha
    have ha0 : 0 < a := hl.trans_le ha.1
    have hp : ContinuousAt (fun x : ℝ => (1 + x) ^ r) a :=
      (continuousAt_const.add continuousAt_id).rpow continuousAt_const
        (Or.inl (show 1 + a ≠ 0 by linarith))
    exact (hp.mul (hf.continuousAt (isOpen_Ioi.mem_nhds ha0)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc l u)).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, fun a ha => ?_⟩
  have hp : 0 < 1 + a := by linarith
  by_cases hm : a ∈ Icc l u
  · have hh : (1 + a) ^ r * ‖f a‖ ≤ max B 0 := by
      have hb := hB a hm
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hp _).le
        (norm_nonneg _))] at hb
      exact hb.trans (le_max_left _ _)
    have hh' := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hp (-r)).le
    rw [← mul_assoc, ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero, one_mul] at hh'
    simpa only [mul_comm] using hh'
  · rw [hz a ha hm, norm_zero]
    exact mul_nonneg (le_max_right _ _) (Real.rpow_pos_of_pos hp _).le

/-- Every window lift starts in the decaying cusp carrier, at every aperture. -/
theorem windowPeriodLift_decay_bound {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.IsWindowTest A H) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖windowPeriodLift s H a‖ ≤ C * (1 + a) ^ (-(2 * s.re)) := by
  exact compact_positive_decay_bound (continuousOn_windowPeriodLift hH.contDiff.continuous hH.vanish s)
    (Real.exp_pos (-A)) (fun a ha hna => windowPeriodLift_zero_outside hA hH.vanish s ha hna) _

/-- The two source correspondences whose cone identities have been established. -/
inductive LewisHeckePrime where
  | two
  | three

/-- An ordered finite composition of the actual source operators. -/
def lewisHeckeWord (s : ℂ) : List LewisHeckePrime → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | LewisHeckePrime.two :: w, f => lewisHeckeT2 s (lewisHeckeWord s w f)
  | LewisHeckePrime.three :: w, f => lewisHeckeT3 s (lewisHeckeWord s w f)

/-- Ordered compositions of both source correspondences preserve the decaying carrier. -/
theorem lewisHeckeWord_decay_bound {s : ℂ} (hs : 0 ≤ s.re) {f : ℝ → ℂ}
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0, ‖f a‖ ≤ C * (1 + a) ^ (-(2 * s.re)))
    (w : List LewisHeckePrime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0, ‖lewisHeckeWord s w f a‖ ≤ C * (1 + a) ^ (-(2 * s.re)) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    obtain ⟨C, hC, hc⟩ := ih
    cases p with
    | two => exact ⟨4 * C, by positivity, fun a ha => lewisHeckeT2_decay_bound hs hC hc ha⟩
    | three => exact ⟨7 * C, by positivity, fun a ha => lewisHeckeT3_decay_bound hs hC hc ha⟩

private theorem measurable_heckeWord (s : ℂ) {f : ℝ → ℂ} (hf : Measurable f)
    (w : List LewisHeckePrime) : Measurable (lewisHeckeWord s w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    cases p with
    | two =>
      change Measurable (fun a => lewisHeckeT2 s (lewisHeckeWord s w f) a)
      unfold lewisHeckeT2
      fun_prop
    | three =>
      change Measurable (fun a => lewisHeckeT3 s (lewisHeckeWord s w f) a)
      unfold lewisHeckeT3
      fun_prop

private theorem measurable_windowPeriodLift {A : ℝ} {H : ℝ → ℝ}
    (hc : Continuous H) (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    Measurable (windowPeriodLift s H) := by
  have hF := (continuous_windowLogLift hc hv s).measurable
  unfold windowPeriodLift logPeriodInverse
  fun_prop

private theorem haar_square_integrable_of_decay {f : ℝ → ℂ} (hf : Measurable f)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hb : ∀ a > 0, ‖f a‖ ≤ C * (1 + a) ^ (-r)) :
    IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioi 1) := by
  have hmajor : IntegrableOn (fun a : ℝ => C ^ 2 * a ^ (-2 * r - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -2 * r - 1 < -1) zero_lt_one).const_mul _
  have hm : AEStronglyMeasurable (fun a : ℝ => ‖f a‖ ^ 2 / a) (volume.restrict (Ioi 1)) := by
    exact ((hf.norm.pow_const 2).div measurable_id).aestronglyMeasurable
  apply hmajor.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hn : ‖f a‖ ≤ C * a ^ (-r) := (hb a ha0).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha0 (by linarith) (by linarith)) hC)
  have hp : (a ^ (-r)) ^ 2 / a = a ^ (-2 * r - 1) := by
    rw [← Real.rpow_natCast (a ^ (-r)) 2, ← Real.rpow_mul ha0.le,
      div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add ha0]
    congr 1
    norm_num
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha0.le)]
  calc
    ‖f a‖ ^ 2 / a ≤ (C * a ^ (-r)) ^ 2 / a :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) ha0.le
    _ = C ^ 2 * a ^ (-2 * r - 1) := by rw [mul_pow, mul_div_assoc, hp]

private theorem dyadicCuspExtractor_decay {s : ℂ} (hs : 0 ≤ s.re) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ a > 0, ‖f a‖ ≤ C * (1 + a) ^ (-(2 * s.re))) :
    ∀ a > 0, ‖dyadicCuspExtractor s f a‖ ≤
      (C + ‖(2 : ℂ) ^ (1 - 2 * s)‖ * C) * (1 + a) ^ (-(2 * s.re)) := by
  intro a ha
  have hdouble : ‖f (2 * a)‖ ≤ C * (1 + a) ^ (-(2 * s.re)) :=
    (hf _ (by positivity)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)) hC)
  have hsingle := mul_le_mul_of_nonneg_left (hf a ha) (norm_nonneg ((2 : ℂ) ^ (1 - 2 * s)))
  unfold dyadicCuspExtractor
  calc
    _ ≤ ‖f (2 * a)‖ + ‖(2 : ℂ) ^ (1 - 2 * s) * f a‖ := norm_sub_le _ _
    _ ≤ C * (1 + a) ^ (-(2 * s.re)) +
        ‖(2 : ℂ) ^ (1 - 2 * s)‖ * (C * (1 + a) ^ (-(2 * s.re))) := by
      rw [norm_mul]
      exact add_le_add hdouble hsingle
    _ = _ := by ring

/-- Compact admission may fail, but every finite arithmetic word retains decaying cusp tails. -/
theorem lewisHeckeWord_windowPeriodLift_decay {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.IsWindowTest A H)
    {s : ℂ} (hs : 0 ≤ s.re) (w : List LewisHeckePrime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖lewisHeckeWord s w (windowPeriodLift s H) a‖ ≤ C * (1 + a) ^ (-(2 * s.re)) :=
  lewisHeckeWord_decay_bound hs (windowPeriodLift_decay_bound hA hH s) w

/-- Every measurable member of the decay carrier retains finite upper Haar square energy
and finite dyadic cusp energy under all finite words. -/
theorem lewisHeckeWord_finite_cusp_energy {s : ℂ} (hs : 0 < s.re) {f : ℝ → ℂ}
    (hf : Measurable f)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0, ‖f a‖ ≤ C * (1 + a) ^ (-(2 * s.re)))
    (w : List LewisHeckePrime) :
    IntegrableOn (fun a : ℝ => ‖lewisHeckeWord s w f a‖ ^ 2 / a) (Ioi 1) ∧
      IntegrableOn (fun a : ℝ => ‖dyadicCuspExtractor s (lewisHeckeWord s w f) a‖ ^ 2 / a)
        (Ioi 1) := by
  obtain ⟨C, hC, hbound⟩ := lewisHeckeWord_decay_bound hs.le hb w
  have hm := measurable_heckeWord s hf w
  refine ⟨haar_square_integrable_of_decay hm (by linarith : 0 < 2 * s.re) hC hbound, ?_⟩
  have hmd : Measurable (dyadicCuspExtractor s (lewisHeckeWord s w f)) := by
    unfold dyadicCuspExtractor
    fun_prop
  exact haar_square_integrable_of_decay hmd (by linarith : 0 < 2 * s.re)
    (by positivity) (dyadicCuspExtractor_decay hs.le hC hbound)

/-- All finite source Hecke words on a window lift have finite upper Haar square energy and
finite dyadic cusp energy. There is no aperture restriction or resonance premise. -/
theorem lewisHeckeWord_windowPeriodLift_finite_cusp_energy {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.IsWindowTest A H)
    {s : ℂ} (hs : 0 < s.re) (w : List LewisHeckePrime) :
    IntegrableOn (fun a : ℝ => ‖lewisHeckeWord s w (windowPeriodLift s H) a‖ ^ 2 / a) (Ioi 1) ∧
      IntegrableOn (fun a : ℝ =>
        ‖dyadicCuspExtractor s (lewisHeckeWord s w (windowPeriodLift s H)) a‖ ^ 2 / a) (Ioi 1) :=
  lewisHeckeWord_finite_cusp_energy hs
    (measurable_windowPeriodLift hH.contDiff.continuous hH.vanish s)
    (windowPeriodLift_decay_bound hA hH s) w

#print axioms lewisHeckeWord_windowPeriodLift_decay
#print axioms lewisHeckeWord_windowPeriodLift_finite_cusp_energy

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
