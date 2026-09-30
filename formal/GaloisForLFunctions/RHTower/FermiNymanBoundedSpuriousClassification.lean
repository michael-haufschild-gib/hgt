import GaloisForLFunctions.RHTower.FermiNymanCorrelationKernel

/-!
# Complete arithmetic classification of bounded Fermi witnesses

For every continuous dyadically self-similar function, pairing with the literal alternating
fractional-part generator at scale `a ≥ 1` is exactly `-1/a` times its logarithmic mean on
`[1/2,1]`. Half-dilation cancels the lower fractional-part integrals; on the remaining upper
interval the fractional part equals its reciprocal argument. This proof uses finite-interval
identities, not a zeta divisor or a spectral completeness premise.

Consequently the actual bounded witnesses are exactly the continuous self-similar functions
with zero fundamental logarithmic mean. Combined with the correlation-kernel theorem, this
classifies the entire intrinsic zero-jet kernel by the literal source itself.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin
noncomputable section
namespace RHTower

/-- Logarithmic mean on the dyadic fundamental interval. -/
def dyadicLogMean (w : ℝ → ℂ) : ℂ :=
  ∫ t in Ioc (1 / 2 : ℝ) 1, (t : ℂ)⁻¹ * w t

theorem dyadicLogMean_conj (w : ℝ → ℂ) :
    dyadicLogMean (fun t => (starRingEnd ℂ) (w t)) = (starRingEnd ℂ) (dyadicLogMean w) := by
  unfold dyadicLogMean
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  simp

theorem nymanGen_half (a t : ℝ) : nymanGen (2 * a) (t / 2) = nymanGen a t := by
  have h : (2 * a) * (t / 2) = a * t := by ring
  simp only [nymanGen, h]

theorem integrableOn_nymanGen_mul_of_bounded {w : ℝ → ℂ}
    (hc : ContinuousOn w (Ioc (0 : ℝ) 1)) {M : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M) (a : ℝ) :
    IntegrableOn (fun t => nymanGen a t * w t) (Ioc (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound (μ := volume) (s := Ioc (0 : ℝ) 1)
    measure_Ioc_lt_top
    ((measurable_nymanGen a).aestronglyMeasurable.mul
      (hc.aestronglyMeasurable measurableSet_Ioc)) M
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
    change ‖nymanGen a t * w t‖ ≤ M
    rw [norm_mul]
    calc
      ‖nymanGen a t‖ * ‖w t‖ ≤ 1 * ‖w t‖ :=
        mul_le_mul_of_nonneg_right (norm_nymanGen_le a t) (norm_nonneg _)
      _ ≤ M := by simpa using hb t ht

/-- Every source scale reads the same fundamental logarithmic mean. -/
theorem integral_fermiNymanGen_mul_of_dyadicSelfSimilar {w : ℝ → ℂ}
    (hc : ContinuousOn w (Ioc (0 : ℝ) 1))
    (hs : ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t) {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in Ioc (0 : ℝ) 1, fermiNymanGen a t * w t) =
      -((a : ℂ)⁻¹) * dyadicLogMean w := by
  obtain ⟨M, hM⟩ := bounded_of_continuous_dyadicSelfSimilar hc hs
  have hint := integrableOn_nymanGen_mul_of_bounded hc hM (2 * a)
  have hlow : IntegrableOn (fun t => nymanGen (2 * a) t * w t)
      (Ioc (0 : ℝ) (1 / 2)) := hint.mono_set (by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (by norm_num)⟩)
  have hupp : IntegrableOn (fun t => nymanGen (2 * a) t * w t)
      (Ioc (1 / 2 : ℝ) 1) := hint.mono_set (by
    intro t ht
    exact ⟨lt_trans (by norm_num) ht.1, ht.2⟩)
  have hsplit := setIntegral_union (s := Ioc (0 : ℝ) (1 / 2))
    (t := Ioc (1 / 2 : ℝ) 1)
    (Set.disjoint_left.mpr fun t ht hu => (not_lt_of_ge ht.2) hu.1)
    measurableSet_Ioc hlow hupp
  rw [Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)] at hsplit
  have hcomp : (∫ t in Ioc (0 : ℝ) 1, nymanGen a t * w t) =
      (2 : ℂ) * ∫ t in Ioc (0 : ℝ) (1 / 2), nymanGen (2 * a) t * w t := by
    have h := integral_Ioc_comp_half (fun t => nymanGen (2 * a) t * w t)
    rw [real_smul, Complex.ofReal_ofNat] at h
    calc
      _ = ∫ t in Ioc (0 : ℝ) 1, nymanGen (2 * a) (t / 2) * w (t / 2) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change nymanGen a t * w t = nymanGen (2 * a) (t / 2) * w (t / 2)
        rw [nymanGen_half, hs t ht]
      _ = _ := h
  have ha0 : 0 < a := by linarith
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
  have hup : (∫ t in Ioc (1 / 2 : ℝ) 1, nymanGen (2 * a) t * w t) =
      (2 * (a : ℂ))⁻¹ * dyadicLogMean w := by
    rw [dyadicLogMean, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht.1
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hden : 1 < 2 * a * t := by
      nlinarith [ht.1, mul_nonneg (sub_nonneg.mpr ha) ht0.le]
    change nymanGen (2 * a) t * w t = (2 * (a : ℂ))⁻¹ * ((t : ℂ)⁻¹ * w t)
    rw [nymanGen, Int.fract_eq_self.mpr
      ⟨by positivity, (div_lt_one (by positivity)).mpr hden⟩]
    push_cast
    field_simp [haC, htC]
  have hdist : (fun t => fermiNymanGen a t * w t) =
      fun t => nymanGen a t * w t - (2 : ℂ) * (nymanGen (2 * a) t * w t) := by
    funext t
    unfold fermiNymanGen
    ring
  rw [hdist, integral_sub (integrableOn_nymanGen_mul_of_bounded hc hM a)
    (hint.const_mul 2), integral_const_mul, hcomp, hsplit, hup]
  field_simp [haC]
  ring

/-- Continuous dyadic profiles with zero fundamental logarithmic mean. -/
def dyadicLogMeanZeroSet : Set (ℝ → ℂ) :=
  {w | ContinuousOn w (Ioc (0 : ℝ) 1) ∧
    (∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t) ∧ dyadicLogMean w = 0}

/-- Complete literal source classification of the bounded spurious class. -/
theorem boundedFermiWitnessSet_eq_dyadicLogMeanZeroSet :
    boundedFermiWitnessSet = dyadicLogMeanZeroSet := by
  ext w
  constructor
  · rintro ⟨hw, M, hM⟩
    have hs : ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t :=
      fun t ht => hw.selfSimilar_of_bounded hM ht
    refine ⟨hw.1, hs, ?_⟩
    have hconj : ∀ t ∈ Ioc (0 : ℝ) 1,
        (starRingEnd ℂ) (w (t / 2)) = (starRingEnd ℂ) (w t) :=
      fun t ht => congrArg (starRingEnd ℂ) (hs t ht)
    have h := integral_fermiNymanGen_mul_of_dyadicSelfSimilar
      (w := fun t => (starRingEnd ℂ) (w t))
      (Complex.continuous_conj.comp_continuousOn hw.1) hconj (a := 1) le_rfl
    have hmean : dyadicLogMean (fun t => (starRingEnd ℂ) (w t)) = 0 := by
      simpa using h.symm.trans (hw.2.2 1 le_rfl)
    have h' := congrArg (starRingEnd ℂ) hmean
    simpa [dyadicLogMean_conj] using h'
  · rintro ⟨hc, hs, hmean⟩
    obtain ⟨M, hM⟩ := bounded_of_continuous_dyadicSelfSimilar hc hs
    have hM0 : 0 ≤ M := le_trans (norm_nonneg (w 1)) (hM 1 ⟨one_pos, le_rfl⟩)
    refine ⟨⟨hc, ?_, ?_⟩, M, hM⟩
    · apply IntegrableOn.of_bound (μ := volume) (s := Ioc (0 : ℝ) 1)
        measure_Ioc_lt_top (((hc.aestronglyMeasurable measurableSet_Ioc).norm).pow 2) (M ^ 2)
      exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        change ‖(‖w t‖ ^ 2 : ℝ)‖ ≤ M ^ 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hM t ht))
          (add_nonneg hM0 (norm_nonneg (w t)))]
    · intro a ha
      have hconj : ∀ t ∈ Ioc (0 : ℝ) 1,
          (starRingEnd ℂ) (w (t / 2)) = (starRingEnd ℂ) (w t) :=
        fun t ht => congrArg (starRingEnd ℂ) (hs t ht)
      have hpair := integral_fermiNymanGen_mul_of_dyadicSelfSimilar
        (w := fun t => (starRingEnd ℂ) (w t))
        (Complex.continuous_conj.comp_continuousOn hc) hconj ha
      exact hpair.trans (by rw [dyadicLogMean_conj, hmean, map_zero, mul_zero])

/-- The analytic divisor coordinates forget exactly this source-classified dyadic profile space. -/
theorem fermiMultiplicityJetKernelSet_eq_dyadicLogMeanZeroSet :
    fermiMultiplicityJetKernelSet = dyadicLogMeanZeroSet :=
  fermiMultiplicityJetKernelSet_eq_boundedFermiWitnessSet.trans
    boundedFermiWitnessSet_eq_dyadicLogMeanZeroSet

end RHTower
