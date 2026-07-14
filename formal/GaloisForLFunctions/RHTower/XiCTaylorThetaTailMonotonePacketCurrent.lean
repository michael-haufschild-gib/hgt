import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPacketRecombination
import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhasePotentialSeam

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

lemma norm_spectralTranslationPhase_eq_exp_neg_mul_im
    (t : ℝ) (z : ℂ) :
    ‖spectralTranslationPhase t z‖ = Real.exp (-t * z.im) := by
  unfold spectralTranslationPhase
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

lemma mul_exp_neg_le_one_sub_exp_neg_div
    {t y : ℝ} (ht : 0 ≤ t) (hy : 0 < y) :
    t * Real.exp (-t * y) ≤
      (1 - Real.exp (-t * y)) / y := by
  have hv : 0 ≤ t * y := mul_nonneg ht hy.le
  have hexp := Real.add_one_le_exp (t * y)
  have hpos : 0 < Real.exp (-t * y) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hexp hpos.le
  have hinv : Real.exp (t * y) * Real.exp (-t * y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hcore : t * y * Real.exp (-t * y) ≤
      1 - Real.exp (-t * y) := by
    rw [add_mul, hinv] at hmul
    linarith
  apply (le_div_iff₀ hy).2
  nlinarith

def positiveTailCompletion (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    (h t : ℂ) * (1 - spectralTranslationPhase t z)

def positiveTailCompletionDerivative (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)

def criticalLogPhaseTranslatedDensityProfileDerivative
    (L : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    Real.exp (-((j : ℝ) * L) / 2) *
      (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) 1 (t + (j : ℝ) * L))

theorem hasDerivAt_criticalLogPhaseTranslatedDensityProfile
    (L : ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (criticalLogPhaseTranslatedDensityProfile L N)
      (criticalLogPhaseTranslatedDensityProfileDerivative L N t) t := by
  unfold criticalLogPhaseTranslatedDensityProfile
    criticalLogPhaseTranslatedDensityProfileDerivative
  convert HasDerivAt.sum (u := Finset.range N)
    (A := fun j (x : ℝ) => Real.exp (-((j : ℝ) * L) / 2) *
      thetaCuspTailSecondDensityAtom 1 (x + (j : ℝ) * L))
    (A' := fun j => Real.exp (-((j : ℝ) * L) / 2) *
      (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) 1 (t + (j : ℝ) * L)))
    (fun j _hj => by
      convert ((hasDerivAt_thetaCuspTailSecondDensityAtom 1
        (t + (j : ℝ) * L)).comp t
          ((hasDerivAt_id t).add_const ((j : ℝ) * L))).const_mul
            (Real.exp (-((j : ℝ) * L) / 2)) using 1 <;> ring)
  simp only [Finset.sum_apply]

theorem neg_criticalLogPhaseTranslatedDensityProfileDerivative_nonneg
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ -criticalLogPhaseTranslatedDensityProfileDerivative L N t := by
  rw [neg_nonneg]
  unfold criticalLogPhaseTranslatedDensityProfileDerivative
  apply Finset.sum_nonpos
  intro j _hj
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    (thetaCuspTailSecondDensityAtom_deriv_neg Nat.zero_lt_one
      (add_nonneg ht (mul_nonneg (Nat.cast_nonneg j) hL))).le

private theorem integrableOn_shiftedDensityAtomOneDerivative
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ =>
      4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) 1 (t + a)) (Ioi 0) := by
  let f : ℝ → ℝ := fun u =>
    4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 3) 1 u
  have hf : IntegrableOn f (Ioi 0) := by
    exact (integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos
      (thetaCuspTailDerivativePolynomial 3) Nat.zero_lt_one).const_mul 4
  have hfa : IntegrableOn f (Ioi a) := hf.mono_set (Ioi_subset_Ioi ha)
  have hcomp :=
    ((measurePreserving_add_right (volume : Measure ℝ) a).integrableOn_comp_preimage
      (measurableEmbedding_addRight a)).mpr hfa
  have hpre : (fun x : ℝ => x + a) ⁻¹' Ioi a = Ioi 0 := by
    ext x
    simp
  rw [hpre] at hcomp
  exact hcomp

private theorem integrableOn_mul_shiftedDensityAtomOneDerivative
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => t *
      (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) 1 (t + a))) (Ioi 0) := by
  let f : ℝ → ℝ := fun u =>
    4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 3) 1 u
  have hbase : IntegrableOn (fun u : ℝ =>
      4 * (u ^ 1 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) 1 u)) (Ioi 0) :=
    (integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
      1 (thetaCuspTailDerivativePolynomial 3) Nat.zero_lt_one).const_mul 4
  have huf : IntegrableOn (fun u : ℝ => u * f u) (Ioi 0) := by
    apply hbase.congr_fun _ measurableSet_Ioi
    intro u _hu
    dsimp only [f]
    simp only [pow_one]
    ring
  have hufa : IntegrableOn (fun u : ℝ => u * f u) (Ioi a) :=
    huf.mono_set (Ioi_subset_Ioi ha)
  have hcompMoment :=
    ((measurePreserving_add_right (volume : Measure ℝ) a).integrableOn_comp_preimage
      (measurableEmbedding_addRight a)).mpr hufa
  have hpre : (fun x : ℝ => x + a) ⁻¹' Ioi a = Ioi 0 := by
    ext x
    simp
  rw [hpre] at hcompMoment
  have hcompBase := integrableOn_shiftedDensityAtomOneDerivative ha
  have hcomb := hcompMoment.sub (hcompBase.const_mul a)
  apply hcomb.congr_fun _ measurableSet_Ioi
  intro t _ht
  change (t + a) * (4 * thetaCuspPolynomialAtom
      (thetaCuspTailDerivativePolynomial 3) 1 (t + a)) -
      a * (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) 1 (t + a)) =
    t * (4 * thetaCuspPolynomialAtom
      (thetaCuspTailDerivativePolynomial 3) 1 (t + a))
  ring

private theorem integrableOn_shiftedDensityAtomOne
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ =>
      thetaCuspTailSecondDensityAtom 1 (t + a)) (Ioi 0) := by
  let f : ℝ → ℝ := thetaCuspTailSecondDensityAtom 1
  have hf : IntegrableOn f (Ioi 0) := by
    unfold f thetaCuspTailSecondDensityAtom
    exact (integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos
      (thetaCuspTailDerivativePolynomial 2) Nat.zero_lt_one).const_mul 4
  have hfa : IntegrableOn f (Ioi a) := hf.mono_set (Ioi_subset_Ioi ha)
  have hcomp :=
    ((measurePreserving_add_right (volume : Measure ℝ) a).integrableOn_comp_preimage
      (measurableEmbedding_addRight a)).mpr hfa
  have hpre : (fun x : ℝ => x + a) ⁻¹' Ioi a = Ioi 0 := by
    ext x
    simp
  rw [hpre] at hcomp
  exact hcomp

private theorem integrableOn_mul_shiftedDensityAtomOne
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => t *
      thetaCuspTailSecondDensityAtom 1 (t + a)) (Ioi 0) := by
  let f : ℝ → ℝ := thetaCuspTailSecondDensityAtom 1
  have hbase : IntegrableOn (fun u : ℝ =>
      4 * (u ^ 1 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 2) 1 u)) (Ioi 0) :=
    (integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
      1 (thetaCuspTailDerivativePolynomial 2) Nat.zero_lt_one).const_mul 4
  have huf : IntegrableOn (fun u : ℝ => u * f u) (Ioi 0) := by
    apply hbase.congr_fun _ measurableSet_Ioi
    intro u _hu
    unfold f thetaCuspTailSecondDensityAtom
    simp only [pow_one]
    ring
  have hufa : IntegrableOn (fun u : ℝ => u * f u) (Ioi a) :=
    huf.mono_set (Ioi_subset_Ioi ha)
  have hcompMoment :=
    ((measurePreserving_add_right (volume : Measure ℝ) a).integrableOn_comp_preimage
      (measurableEmbedding_addRight a)).mpr hufa
  have hpre : (fun x : ℝ => x + a) ⁻¹' Ioi a = Ioi 0 := by
    ext x
    simp
  rw [hpre] at hcompMoment
  have hcompBase := integrableOn_shiftedDensityAtomOne ha
  have hcomb := hcompMoment.sub (hcompBase.const_mul a)
  apply hcomb.congr_fun _ measurableSet_Ioi
  intro t _ht
  change (t + a) * thetaCuspTailSecondDensityAtom 1 (t + a) -
      a * thetaCuspTailSecondDensityAtom 1 (t + a) =
    t * thetaCuspTailSecondDensityAtom 1 (t + a)
  ring

theorem integrableOn_criticalLogPhaseTranslatedDensityProfile
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    IntegrableOn (criticalLogPhaseTranslatedDensityProfile L N) (Ioi 0) := by
  unfold criticalLogPhaseTranslatedDensityProfile
  exact MeasureTheory.integrable_finset_sum _ fun j _hj =>
    (integrableOn_shiftedDensityAtomOne
      (mul_nonneg (Nat.cast_nonneg j) hL)).const_mul
        (Real.exp (-((j : ℝ) * L) / 2))

theorem integrableOn_mul_criticalLogPhaseTranslatedDensityProfile
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    IntegrableOn (fun t : ℝ => t *
      criticalLogPhaseTranslatedDensityProfile L N t) (Ioi 0) := by
  unfold criticalLogPhaseTranslatedDensityProfile
  rw [show (fun t : ℝ => t *
      ∑ j ∈ Finset.range N,
        Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)) =
      fun t : ℝ => ∑ j ∈ Finset.range N,
        Real.exp (-((j : ℝ) * L) / 2) *
          (t * thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)) by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  exact MeasureTheory.integrable_finset_sum _ fun j _hj =>
    (integrableOn_mul_shiftedDensityAtomOne
      (mul_nonneg (Nat.cast_nonneg j) hL)).const_mul
        (Real.exp (-((j : ℝ) * L) / 2))

theorem integrableOn_criticalLogPhaseTranslatedDensityProfileDerivative
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    IntegrableOn (criticalLogPhaseTranslatedDensityProfileDerivative L N) (Ioi 0) := by
  unfold criticalLogPhaseTranslatedDensityProfileDerivative
  exact MeasureTheory.integrable_finset_sum _ fun j _hj =>
    (integrableOn_shiftedDensityAtomOneDerivative
      (mul_nonneg (Nat.cast_nonneg j) hL)).const_mul
        (Real.exp (-((j : ℝ) * L) / 2))

theorem integrableOn_mul_criticalLogPhaseTranslatedDensityProfileDerivative
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    IntegrableOn (fun t : ℝ => t *
      criticalLogPhaseTranslatedDensityProfileDerivative L N t) (Ioi 0) := by
  unfold criticalLogPhaseTranslatedDensityProfileDerivative
  rw [show (fun t : ℝ => t *
      ∑ j ∈ Finset.range N,
        Real.exp (-((j : ℝ) * L) / 2) *
          (4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 3) 1 (t + (j : ℝ) * L))) =
      fun t : ℝ => ∑ j ∈ Finset.range N,
        Real.exp (-((j : ℝ) * L) / 2) *
          (t * (4 * thetaCuspPolynomialAtom
            (thetaCuspTailDerivativePolynomial 3) 1 (t + (j : ℝ) * L))) by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  exact MeasureTheory.integrable_finset_sum _ fun j _hj =>
    (integrableOn_mul_shiftedDensityAtomOneDerivative
      (mul_nonneg (Nat.cast_nonneg j) hL)).const_mul
        (Real.exp (-((j : ℝ) * L) / 2))

theorem tendsto_criticalLogPhaseTranslatedDensityProfile_atTop_zero
    (L : ℝ) (N : ℕ) :
    Tendsto (criticalLogPhaseTranslatedDensityProfile L N) atTop (nhds 0) := by
  unfold criticalLogPhaseTranslatedDensityProfile
  have hsum := tendsto_finset_sum (Finset.range N) (fun j _hj =>
    ((thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      (thetaCuspTailDerivativePolynomial 2) Nat.zero_lt_one).comp
        (tendsto_atTop_add_const_right atTop ((j : ℝ) * L) tendsto_id)).const_mul
          (4 * Real.exp (-((j : ℝ) * L) / 2)))
  convert hsum using 1
  · funext t
    apply Finset.sum_congr rfl
    intro j _hj
    unfold thetaCuspTailSecondDensityAtom
    simp only [Function.comp_apply, id_eq, add_comm]
    ring
  · simp

theorem tendsto_mul_criticalLogPhaseTranslatedDensityProfile_atTop_zero
    (L : ℝ) (N : ℕ) :
    Tendsto (fun t : ℝ => t * criticalLogPhaseTranslatedDensityProfile L N t)
      atTop (nhds 0) := by
  unfold criticalLogPhaseTranslatedDensityProfile
  rw [show (fun t : ℝ => t *
      ∑ j ∈ Finset.range N,
        Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)) =
      fun t : ℝ => ∑ j ∈ Finset.range N,
        Real.exp (-((j : ℝ) * L) / 2) *
          (t * thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)) by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  have hterm : ∀ j ∈ Finset.range N, Tendsto (fun t : ℝ =>
      Real.exp (-((j : ℝ) * L) / 2) *
        (t * thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)))
      atTop (nhds 0) := by
    intro j _hj
    let a : ℝ := (j : ℝ) * L
    have hshift0 : Tendsto (fun t : ℝ =>
        (t + a) * thetaCuspTailSecondDensityAtom 1 (t + a))
        atTop (nhds 0) := by
      have h := (pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        1 (thetaCuspTailDerivativePolynomial 2) Nat.zero_lt_one).comp
          (tendsto_atTop_add_const_right atTop a tendsto_id)
      convert h.const_mul 4 using 1 <;>
        simp [Function.comp_apply, id_eq, pow_one,
          thetaCuspTailSecondDensityAtom, mul_comm, mul_left_comm, mul_assoc]
    have hbase0 : Tendsto (fun t : ℝ =>
        thetaCuspTailSecondDensityAtom 1 (t + a)) atTop (nhds 0) := by
      have h := (thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        (thetaCuspTailDerivativePolynomial 2) Nat.zero_lt_one).comp
          (tendsto_atTop_add_const_right atTop a tendsto_id)
      convert h.const_mul 4 using 1 <;>
        simp [Function.comp_apply, id_eq,
          thetaCuspTailSecondDensityAtom, mul_comm, mul_left_comm, mul_assoc]
    have hdiff := hshift0.sub (hbase0.const_mul a)
    have ht : Tendsto (fun t : ℝ =>
        t * thetaCuspTailSecondDensityAtom 1 (t + a)) atTop (nhds 0) := by
      convert hdiff using 1
      · funext t
        ring
      · simp
    simpa only [a, mul_zero] using
      ht.const_mul (Real.exp (-((j : ℝ) * L) / 2))
  simpa using tendsto_finset_sum (Finset.range N) hterm

theorem integrableOn_neg_profileDerivative_mul_one_sub_phase
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun t : ℝ =>
      ((-criticalLogPhaseTranslatedDensityProfileDerivative L N t : ℝ) : ℂ) *
        (1 - spectralTranslationPhase t z)) (Ioi 0) := by
  let h : ℝ → ℝ := fun t =>
    -criticalLogPhaseTranslatedDensityProfileDerivative L N t
  have hhReal : IntegrableOn h (Ioi 0) :=
    (integrableOn_criticalLogPhaseTranslatedDensityProfileDerivative hL N).neg
  have hh : Integrable (fun t => (h t : ℂ)) (volume.restrict (Ioi 0)) :=
    hhReal.ofReal
  have hmajor : Integrable (fun t => (2 : ℂ) * (h t : ℂ))
      (volume.restrict (Ioi 0)) := hh.const_mul 2
  apply Integrable.mono hmajor
  · have hphase : Continuous (fun t : ℝ =>
        1 - spectralTranslationPhase t z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact hh.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hhnon := neg_criticalLogPhaseTranslatedDensityProfileDerivative_nonneg
      hL N ht.le
    have hp := norm_spectralTranslationPhase_le_one ht.le hz
    dsimp only [h]
    rw [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hhnon]
    calc
      h t * ‖1 - spectralTranslationPhase t z‖ ≤ h t * 2 := by
        apply mul_le_mul_of_nonneg_left _ hhnon
        calc
          ‖1 - spectralTranslationPhase t z‖ ≤
              ‖(1 : ℂ)‖ + ‖spectralTranslationPhase t z‖ := norm_sub_le _ _
          _ ≤ 2 := by norm_num; linarith
      _ = ‖(2 : ℂ) * (h t : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
        rw [abs_of_nonneg hhnon]
        ring

theorem integrableOn_neg_profileDerivative_mul_phaseDerivative
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun t : ℝ =>
      ((-criticalLogPhaseTranslatedDensityProfileDerivative L N t : ℝ) : ℂ) *
        (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0) := by
  let h : ℝ → ℝ := fun t =>
    -criticalLogPhaseTranslatedDensityProfileDerivative L N t
  have hthReal : IntegrableOn (fun t : ℝ => t * h t) (Ioi 0) := by
    have hneg :=
      (integrableOn_mul_criticalLogPhaseTranslatedDensityProfileDerivative hL N).neg
    apply hneg.congr_fun _ measurableSet_Ioi
    intro t _ht
    dsimp only [h]
    simp only [Pi.neg_apply]
    ring
  have hth : Integrable (fun t => ((t * h t : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := hthReal.ofReal
  apply Integrable.mono hth
  · have hhReal : IntegrableOn h (Ioi 0) :=
      (integrableOn_criticalLogPhaseTranslatedDensityProfileDerivative hL N).neg
    have hh : Integrable (fun t => (h t : ℂ)) (volume.restrict (Ioi 0)) :=
      hhReal.ofReal
    have hphase : Continuous (fun t : ℝ =>
        -((t : ℂ) * I) * spectralTranslationPhase t z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact hh.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hhnon := neg_criticalLogPhaseTranslatedDensityProfileDerivative_nonneg
      hL N ht.le
    have hp := norm_spectralTranslationPhase_le_one ht.le hz
    dsimp only [h]
    rw [norm_mul, norm_mul, norm_neg, norm_mul]
    have ht0 : 0 ≤ t := le_of_lt ht
    have hh0 : 0 ≤ h t := by simpa only [h] using hhnon
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg hhnon, abs_of_nonneg ht0]
    calc
      h t * (t * ‖spectralTranslationPhase t z‖) =
          (t * h t) * ‖spectralTranslationPhase t z‖ := by ring
      _ ≤ (t * h t) * 1 :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg ht0 hh0)
      _ = ‖((t * h t : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg ht0 hh0)]
        ring
      _ = |t * -criticalLogPhaseTranslatedDensityProfileDerivative L N t| := by
        simp only [h, Complex.norm_real, Real.norm_eq_abs]

lemma integrableOn_ofReal_mul_spectralTranslationPhase
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun t : ℝ => (f t : ℂ) * spectralTranslationPhase t z) (Ioi 0) := by
  have hfC : Integrable (fun t => (f t : ℂ)) (volume.restrict (Ioi 0)) :=
    hf.ofReal
  apply Integrable.mono hfC
  · have hphase : Continuous (fun t : ℝ => spectralTranslationPhase t z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact hfC.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_spectralTranslationPhase_le_one ht.le hz)

theorem positiveTailCompletion_neg_profileDerivative_eq
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    positiveTailCompletion
        (fun t => -criticalLogPhaseTranslatedDensityProfileDerivative L N t) z =
      -I * z *
        (∫ t : ℝ in Ioi 0,
          (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
            spectralTranslationPhase t z) := by
  let g : ℝ → ℝ := criticalLogPhaseTranslatedDensityProfile L N
  let g' : ℝ → ℝ := criticalLogPhaseTranslatedDensityProfileDerivative L N
  let p : ℝ → ℂ := fun t => spectralTranslationPhase t z
  let p' : ℝ → ℂ := fun t => I * z * spectralTranslationPhase t z
  have hg (t : ℝ) : HasDerivAt g (g' t) t :=
    hasDerivAt_criticalLogPhaseTranslatedDensityProfile L N t
  have hp (t : ℝ) : HasDerivAt p (p' t) t := by
    exact hasDerivAt_spectralTranslationPhase_source z t
  have hg'int : IntegrableOn g' (Ioi 0) :=
    integrableOn_criticalLogPhaseTranslatedDensityProfileDerivative hL N
  have hgint : IntegrableOn g (Ioi 0) :=
    integrableOn_criticalLogPhaseTranslatedDensityProfile hL N
  have hp_mul_g' : IntegrableOn (p * fun t => (g' t : ℂ)) (Ioi 0) := by
    have h := integrableOn_ofReal_mul_spectralTranslationPhase hg'int hz
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, p]
    ring
  have hp'_mul_g : IntegrableOn (p' * fun t => (g t : ℂ)) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ =>
        (I * z) * ((g t : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
      (integrableOn_ofReal_mul_spectralTranslationPhase hgint hz).const_mul
        (I * z)
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, p']
    ring
  have hgzero : Tendsto (fun t : ℝ => (g t : ℂ)) (𝓝[>] 0) (nhds (g 0 : ℂ)) := by
    exact ((hg 0).ofReal_comp.continuousAt.tendsto.mono_left inf_le_left)
  have hgtop : Tendsto (fun t : ℝ => (g t : ℂ)) atTop (nhds 0) := by
    simpa using (tendsto_criticalLogPhaseTranslatedDensityProfile_atTop_zero L N).ofReal
  have hmass := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (g 0 : ℂ)) (b' := (0 : ℂ))
    (u := fun _ : ℝ => (1 : ℂ)) (u' := fun _ : ℝ => 0)
    (v := fun t : ℝ => (g t : ℂ)) (v' := fun t : ℝ => (g' t : ℂ))
    (fun t _ht => hasDerivAt_const t 1)
    (fun t _ht => (hg t).ofReal_comp)
    (by
      change IntegrableOn (fun t : ℝ => (1 : ℂ) * (g' t : ℂ)) (Ioi 0)
      simpa using hg'int.ofReal)
    (by
      have hzero : IntegrableOn (fun _t : ℝ => (0 : ℂ)) (Ioi 0) :=
        integrableOn_zero
      apply hzero.congr_fun _ measurableSet_Ioi
      intro t _ht
      simp only [Pi.mul_apply, zero_mul])
    (by
      change Tendsto (fun t : ℝ => (1 : ℂ) * (g t : ℂ))
        (𝓝[>] 0) (nhds (g 0 : ℂ))
      simpa using hgzero)
    (by
      change Tendsto (fun t : ℝ => (1 : ℂ) * (g t : ℂ)) atTop (nhds 0)
      simpa using hgtop)
  have hmass' : (∫ t : ℝ in Ioi 0, (g' t : ℂ)) = -(g 0 : ℂ) := by
    simpa only [one_mul, zero_mul, integral_zero, sub_zero, zero_sub] using hmass
  have hpgtop : Tendsto (fun t : ℝ => p t * (g t : ℂ)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
      (by simpa using hgtop.norm)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [norm_mul]
    have hpNorm : ‖p t‖ ≤ 1 := by
      simpa only [p] using norm_spectralTranslationPhase_le_one ht hz
    calc
      ‖p t‖ * ‖(g t : ℂ)‖ ≤ 1 * ‖(g t : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hpNorm (norm_nonneg _)
      _ = ‖(g t : ℂ)‖ := by ring
      _ = |g t| := by simp only [Complex.norm_real, Real.norm_eq_abs]
  have hpgzero : Tendsto (fun t : ℝ => p t * (g t : ℂ))
      (𝓝[>] 0) (nhds (g 0 : ℂ)) := by
    have h := (hp 0).continuousAt.mul (hg 0).ofReal_comp.continuousAt
    simpa [p, spectralTranslationPhase] using h.tendsto.mono_left inf_le_left
  have hphase := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (g 0 : ℂ)) (b' := (0 : ℂ))
    (u := p) (u' := p')
    (v := fun t : ℝ => (g t : ℂ)) (v' := fun t : ℝ => (g' t : ℂ))
    (fun t _ht => hp t) (fun t _ht => (hg t).ofReal_comp)
    hp_mul_g' hp'_mul_g hpgzero hpgtop
  have hphase' :
      (∫ t : ℝ in Ioi 0, (g' t : ℂ) * p t) =
        -(g 0 : ℂ) - (I * z) *
          (∫ t : ℝ in Ioi 0, (g t : ℂ) * p t) := by
    rw [show (fun t : ℝ => (g' t : ℂ) * p t) = p * fun t => (g' t : ℂ) by
      funext t; simp only [Pi.mul_apply]; ring]
    rw [show (fun t : ℝ => p' t * (g t : ℂ)) =
        fun t => (I * z) * ((g t : ℂ) * p t) by
      funext t; simp only [p']; ring,
      integral_const_mul] at hphase
    simpa only [zero_sub] using hphase
  unfold positiveTailCompletion
  rw [show (fun t : ℝ =>
      ((-criticalLogPhaseTranslatedDensityProfileDerivative L N t : ℝ) : ℂ) *
        (1 - spectralTranslationPhase t z)) =
      fun t => -(g' t : ℂ) + (g' t : ℂ) * p t by
    funext t
    dsimp only [g', p]
    push_cast
    ring]
  rw [integral_add]
  · rw [integral_neg, hmass', hphase']
    dsimp only [g, p]
    ring
  · exact hg'int.ofReal.neg
  · exact hp_mul_g'.congr_fun (fun t _ht => by simp only [Pi.mul_apply]; ring)
      measurableSet_Ioi

theorem positiveTailCompletionDerivative_neg_profileDerivative_eq
    {L : ℝ} (hL : 0 ≤ L) (N : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    positiveTailCompletionDerivative
        (fun t => -criticalLogPhaseTranslatedDensityProfileDerivative L N t) z =
      -I *
        ((∫ t : ℝ in Ioi 0,
            (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
              spectralTranslationPhase t z) +
          z * (∫ t : ℝ in Ioi 0,
            (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
              ((t : ℂ) * I * spectralTranslationPhase t z))) := by
  let g : ℝ → ℝ := criticalLogPhaseTranslatedDensityProfile L N
  let g' : ℝ → ℝ := criticalLogPhaseTranslatedDensityProfileDerivative L N
  let q : ℝ → ℂ := fun t =>
    -((t : ℂ) * I) * spectralTranslationPhase t z
  let q' : ℝ → ℂ := fun t =>
    -I * spectralTranslationPhase t z +
      (t : ℂ) * z * spectralTranslationPhase t z
  have hg (t : ℝ) : HasDerivAt g (g' t) t :=
    hasDerivAt_criticalLogPhaseTranslatedDensityProfile L N t
  have hq (t : ℝ) : HasDerivAt q (q' t) t := by
    have hlin : HasDerivAt (fun u : ℝ => -((u : ℂ) * I)) (-I) t := by
      convert ((Complex.ofRealCLM.hasDerivAt.mul_const I).neg) using 1
      simp [Complex.ofRealCLM_apply]
    have hp := hasDerivAt_spectralTranslationPhase_source z t
    convert hlin.mul hp using 1
    dsimp only [q, q']
    ring_nf
    rw [I_sq]
    ring
  have hg'int : IntegrableOn g' (Ioi 0) :=
    integrableOn_criticalLogPhaseTranslatedDensityProfileDerivative hL N
  have ht_g'int : IntegrableOn (fun t : ℝ => t * g' t) (Ioi 0) :=
    integrableOn_mul_criticalLogPhaseTranslatedDensityProfileDerivative hL N
  have hgint : IntegrableOn g (Ioi 0) :=
    integrableOn_criticalLogPhaseTranslatedDensityProfile hL N
  have ht_gint : IntegrableOn (fun t : ℝ => t * g t) (Ioi 0) :=
    integrableOn_mul_criticalLogPhaseTranslatedDensityProfile hL N
  have hq_mul_g' : IntegrableOn (q * fun t => (g' t : ℂ)) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ =>
        (-I) * (((t * g' t : ℝ) : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
      (integrableOn_ofReal_mul_spectralTranslationPhase ht_g'int hz).const_mul (-I)
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, q]
    push_cast
    ring
  have hq'_mul_g : IntegrableOn (q' * fun t => (g t : ℂ)) (Ioi 0) := by
    have h0 := (integrableOn_ofReal_mul_spectralTranslationPhase hgint hz).const_mul (-I)
    have h1 := (integrableOn_ofReal_mul_spectralTranslationPhase ht_gint hz).const_mul z
    have h : IntegrableOn (fun t : ℝ =>
        (-I) * ((g t : ℂ) * spectralTranslationPhase t z) +
          z * (((t * g t : ℝ) : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
      h0.add h1
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, q']
    push_cast
    ring
  have hqgzero : Tendsto (fun t : ℝ => q t * (g t : ℂ))
      (𝓝[>] 0) (nhds 0) := by
    have hcont := (hq 0).continuousAt.mul (hg 0).ofReal_comp.continuousAt
    convert hcont.tendsto.mono_left inf_le_left using 1 <;>
      simp [Pi.mul_apply, q, spectralTranslationPhase]
  have hqgtop : Tendsto (fun t : ℝ => q t * (g t : ℂ)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto (fun t : ℝ => ((t * g t : ℝ) : ℂ)) atTop (nhds 0) := by
      simpa only [g] using
        (tendsto_mul_criticalLogPhaseTranslatedDensityProfile_atTop_zero L N).ofReal
    have hmajorNorm : Tendsto (fun t : ℝ => ‖((t * g t : ℝ) : ℂ)‖)
        atTop (nhds 0) := by
      simpa using hmajor.norm
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
      hmajorNorm
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    dsimp only [q]
    rw [norm_mul, norm_mul, norm_neg, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, norm_I,
      one_mul]
    have hp := norm_spectralTranslationPhase_le_one ht hz
    calc
      t * 1 * ‖spectralTranslationPhase t z‖ * |g t| ≤
          t * 1 * 1 * |g t| := by gcongr
      _ = ‖((t * g t : ℝ) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg ht, mul_one]
      _ = |t * g t| := by simp only [Complex.norm_real, Real.norm_eq_abs]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℂ)) (b' := (0 : ℂ))
    (u := q) (u' := q')
    (v := fun t : ℝ => (g t : ℂ)) (v' := fun t : ℝ => (g' t : ℂ))
    (fun t _ht => hq t) (fun t _ht => (hg t).ofReal_comp)
    hq_mul_g' hq'_mul_g hqgzero hqgtop
  have hqintegral :
      (∫ t : ℝ in Ioi 0, (g' t : ℂ) * q t) =
        I * (∫ t : ℝ in Ioi 0, (g t : ℂ) * spectralTranslationPhase t z) -
          z * (∫ t : ℝ in Ioi 0,
            (g t : ℂ) * ((t : ℂ) * spectralTranslationPhase t z)) := by
    rw [show (fun t : ℝ => (g' t : ℂ) * q t) = q * fun t => (g' t : ℂ) by
      funext t; simp only [Pi.mul_apply]; ring]
    rw [show (fun t : ℝ => q' t * (g t : ℂ)) =
        fun t => (-I) * ((g t : ℂ) * spectralTranslationPhase t z) +
          z * ((g t : ℂ) * ((t : ℂ) * spectralTranslationPhase t z)) by
      funext t
      simp only [q']
      push_cast
      ring,
      integral_add, integral_const_mul, integral_const_mul] at hibp
    · calc
        _ = 0 - 0 -
            ((-I) * (∫ t : ℝ in Ioi 0,
                (g t : ℂ) * spectralTranslationPhase t z) +
              z * (∫ t : ℝ in Ioi 0,
                (g t : ℂ) * ((t : ℂ) * spectralTranslationPhase t z))) := hibp
        _ = _ := by ring
    · exact (integrableOn_ofReal_mul_spectralTranslationPhase hgint hz).const_mul (-I)
    · have h : IntegrableOn (fun t : ℝ =>
          z * (((t * g t : ℝ) : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
        (integrableOn_ofReal_mul_spectralTranslationPhase ht_gint hz).const_mul z
      apply h.congr_fun _ measurableSet_Ioi
      intro t _ht
      push_cast
      ring
  unfold positiveTailCompletionDerivative
  rw [show (fun t : ℝ =>
      ((-criticalLogPhaseTranslatedDensityProfileDerivative L N t : ℝ) : ℂ) *
        (-((t : ℂ) * I) * spectralTranslationPhase t z)) =
      fun t => -(g' t : ℂ) * q t by
    funext t
    dsimp only [g', q]
    push_cast
    ring,
    show (fun t => -(g' t : ℂ) * q t) = fun t => -((g' t : ℂ) * q t) by
      funext t; ring,
    integral_neg, hqintegral]
  dsimp only [g]
  rw [show (fun t : ℝ =>
      (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
        ((t : ℂ) * I * spectralTranslationPhase t z)) =
      fun t => I *
        ((criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
          ((t : ℂ) * spectralTranslationPhase t z)) by
    funext t; ring,
    integral_const_mul]
  ring_nf
  rw [I_sq]
  ring

lemma norm_positiveTailCompletionDerivative_integrand_le_re_div
    {h : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hht : 0 ≤ h t)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)‖ ≤
      (((h t : ℂ) * (1 - spectralTranslationPhase t z)).re) / z.im := by
  have hscalar := mul_exp_neg_le_one_sub_exp_neg_div ht hz
  have hphaseRe : (spectralTranslationPhase t z).re ≤
      Real.exp (-t * z.im) := by
    calc
      (spectralTranslationPhase t z).re ≤
          ‖spectralTranslationPhase t z‖ := Complex.re_le_norm _
      _ = Real.exp (-t * z.im) :=
        norm_spectralTranslationPhase_eq_exp_neg_mul_im t z
  have hcomp :
      (1 - Real.exp (-t * z.im)) / z.im ≤
        (1 - (spectralTranslationPhase t z).re) / z.im := by
    exact (div_le_div_iff_of_pos_right hz).2 (by linarith)
  calc
    ‖(h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)‖ =
        h t * (t * Real.exp (-t * z.im)) := by
      rw [norm_mul, norm_mul, norm_neg, norm_mul,
        norm_spectralTranslationPhase_eq_exp_neg_mul_im]
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_I]
      rw [abs_of_nonneg hht, abs_of_nonneg ht]
      ring
    _ ≤ h t * ((1 - Real.exp (-t * z.im)) / z.im) := by
      gcongr
    _ ≤ h t * ((1 - (spectralTranslationPhase t z).re) / z.im) := by
      gcongr
    _ = (((h t : ℂ) * (1 - spectralTranslationPhase t z)).re) / z.im := by
      simp [Complex.mul_re]
      ring

theorem norm_positiveTailCompletionDerivative_le_re_div
    {h : ℝ → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hh : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ h t)
    (hcompletion : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0))
    (hderivative : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0)) :
    ‖positiveTailCompletionDerivative h z‖ ≤
      (positiveTailCompletion h z).re / z.im := by
  let f : ℝ → ℂ := fun t =>
    (h t : ℂ) * (1 - spectralTranslationPhase t z)
  let f' : ℝ → ℂ := fun t =>
    (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)
  have hf : Integrable f (volume.restrict (Ioi 0)) := hcompletion
  have hf' : Integrable f' (volume.restrict (Ioi 0)) := hderivative
  have hmajor : Integrable (fun t => (f t).re / z.im)
      (volume.restrict (Ioi 0)) := hf.re.div_const z.im
  calc
    ‖positiveTailCompletionDerivative h z‖ =
        ‖∫ t : ℝ in Ioi 0, f' t‖ := rfl
    _ ≤ ∫ t : ℝ in Ioi 0, ‖f' t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 0, (f t).re / z.im := by
      apply MeasureTheory.integral_mono_ae hf'.norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_positiveTailCompletionDerivative_integrand_le_re_div
        ht.le (hh t ht) hz
    _ = (positiveTailCompletion h z).re / z.im := by
      rw [MeasureTheory.integral_div]
      have hre :
          (∫ t : ℝ in Ioi 0, (f t).re) =
            (∫ t : ℝ in Ioi 0, f t).re :=
        integral_re (μ := volume.restrict (Ioi 0)) hf
      calc
        (∫ t : ℝ in Ioi 0, (f t).re) / z.im =
            (∫ t : ℝ in Ioi 0, f t).re / z.im := by rw [hre]
        _ = (positiveTailCompletion h z).re / z.im := rfl

/-- The completion contraction controls the full derivative norm, not merely one orientation of
the current.  This stronger form is what is needed after a bounded cosine rotates an opposite-phase
Hermitian cross. -/
theorem norm_derivative_le_two_div_im_of_completion_contraction
    {F D G G' z : ℂ} (hz : 0 < z.im)
    (hG : G = -I * z * F)
    (hG' : G' = -I * (F + z * D))
    (hcontract : ‖G'‖ ≤ ‖G‖ / z.im) :
    ‖D‖ ≤ (2 / z.im) * ‖F‖ := by
  have hzNorm : z.im ≤ ‖z‖ := by
    simpa only [abs_of_pos hz] using Complex.abs_im_le_norm z
  have hzNormPos : 0 < ‖z‖ := lt_of_lt_of_le hz hzNorm
  have hGnorm : ‖G‖ = ‖z‖ * ‖F‖ := by
    rw [hG, norm_mul, norm_mul]
    norm_num
  have hzd : z * D = I * G' - F := by
    rw [hG']
    ring_nf
    rw [I_sq]
    ring
  have htri : ‖z‖ * ‖D‖ ≤ ‖G'‖ + ‖F‖ := by
    rw [← norm_mul, hzd]
    calc
      ‖I * G' - F‖ ≤ ‖I * G'‖ + ‖F‖ := norm_sub_le _ _
      _ = ‖G'‖ + ‖F‖ := by simp
  have hc : ‖G'‖ ≤ (‖z‖ / z.im) * ‖F‖ := by
    rw [hGnorm] at hcontract
    calc
      ‖G'‖ ≤ (‖z‖ * ‖F‖) / z.im := hcontract
      _ = (‖z‖ / z.im) * ‖F‖ := by ring
  have hdiv : ‖D‖ ≤ ‖F‖ / z.im + ‖F‖ / ‖z‖ := by
    have hmul : ‖z‖ * ‖D‖ ≤
        ‖z‖ * (‖F‖ / z.im + ‖F‖ / ‖z‖) := by
      calc
        ‖z‖ * ‖D‖ ≤ ‖G'‖ + ‖F‖ := htri
        _ ≤ (‖z‖ / z.im) * ‖F‖ + ‖F‖ := by gcongr
        _ = ‖z‖ * (‖F‖ / z.im + ‖F‖ / ‖z‖) := by
          field_simp [ne_of_gt hzNormPos, ne_of_gt hz]
          <;> ring
    exact (mul_le_mul_iff_of_pos_left hzNormPos).mp hmul
  calc
    ‖D‖ ≤ ‖F‖ / z.im + ‖F‖ / ‖z‖ := hdiv
    _ ≤ ‖F‖ / z.im + ‖F‖ / z.im := by gcongr
    _ = (2 / z.im) * ‖F‖ := by ring

theorem abs_orientedCurrent_le_two_div_im_of_completion_contraction
    {F D G G' z : ℂ} (hz : 0 < z.im)
    (hG : G = -I * z * F)
    (hG' : G' = -I * (F + z * D))
    (hcontract : ‖G'‖ ≤ ‖G‖ / z.im) :
    |(D * (starRingEnd ℂ) F).im| ≤
      (2 / z.im) * Complex.normSq F := by
  have hD := norm_derivative_le_two_div_im_of_completion_contraction
    hz hG hG' hcontract
  calc
    |(D * (starRingEnd ℂ) F).im| ≤ ‖D * (starRingEnd ℂ) F‖ :=
      Complex.abs_im_le_norm _
    _ = ‖D‖ * ‖F‖ := by simp
    _ ≤ ((2 / z.im) * ‖F‖) * ‖F‖ := by gcongr
    _ = (2 / z.im) * Complex.normSq F := by
      rw [Complex.normSq_eq_norm_sq]
      ring

theorem orientedCurrent_le_two_div_im_of_completion_contraction
    {F D G G' z : ℂ} (hz : 0 < z.im)
    (hG : G = -I * z * F)
    (hG' : G' = -I * (F + z * D))
    (hcontract : ‖G'‖ ≤ ‖G‖ / z.im) :
    (D * (starRingEnd ℂ) F).im ≤
      (2 / z.im) * Complex.normSq F := by
  have hzNorm : z.im ≤ ‖z‖ := by
    simpa only [abs_of_pos hz] using Complex.abs_im_le_norm z
  have hzNormPos : 0 < ‖z‖ := lt_of_lt_of_le hz hzNorm
  have hGnorm : ‖G‖ = ‖z‖ * ‖F‖ := by
    rw [hG, norm_mul, norm_mul]
    norm_num
  have hzd : z * D = I * G' - F := by
    rw [hG']
    ring_nf
    rw [I_sq]
    ring
  have hDnorm : ‖D‖ ≤ (2 / z.im) * ‖F‖ := by
    have htri : ‖z‖ * ‖D‖ ≤ ‖G'‖ + ‖F‖ := by
      rw [← norm_mul, hzd]
      calc
        ‖I * G' - F‖ ≤ ‖I * G'‖ + ‖F‖ := norm_sub_le _ _
        _ = ‖G'‖ + ‖F‖ := by simp
    have hc : ‖G'‖ ≤ (‖z‖ / z.im) * ‖F‖ := by
      rw [hGnorm] at hcontract
      calc
        ‖G'‖ ≤ (‖z‖ * ‖F‖) / z.im := hcontract
        _ = (‖z‖ / z.im) * ‖F‖ := by ring
    have hdiv : ‖D‖ ≤ ‖F‖ / z.im + ‖F‖ / ‖z‖ := by
      have hmul : ‖z‖ * ‖D‖ ≤
          ‖z‖ * (‖F‖ / z.im + ‖F‖ / ‖z‖) := by
        calc
          ‖z‖ * ‖D‖ ≤ ‖G'‖ + ‖F‖ := htri
          _ ≤ (‖z‖ / z.im) * ‖F‖ + ‖F‖ := by gcongr
          _ = ‖z‖ * (‖F‖ / z.im + ‖F‖ / ‖z‖) := by
            field_simp [ne_of_gt hzNormPos, ne_of_gt hz]
            <;> ring
      exact (mul_le_mul_iff_of_pos_left hzNormPos).mp hmul
    calc
      ‖D‖ ≤ ‖F‖ / z.im + ‖F‖ / ‖z‖ := hdiv
      _ ≤ ‖F‖ / z.im + ‖F‖ / z.im := by
        gcongr
      _ = (2 / z.im) * ‖F‖ := by ring
  calc
    (D * (starRingEnd ℂ) F).im ≤ ‖D * (starRingEnd ℂ) F‖ :=
      Complex.im_le_norm _
    _ = ‖D‖ * ‖F‖ := by simp
    _ ≤ ((2 / z.im) * ‖F‖) * ‖F‖ := by
      gcongr
    _ = (2 / z.im) * Complex.normSq F := by
      rw [Complex.normSq_eq_norm_sq]
      ring

theorem orientedCurrent_le_two_div_im_of_positiveTailCompletion
    {h : ℝ → ℝ} {F D z : ℂ} (hz : 0 < z.im)
    (hh : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ h t)
    (hcompletionInt : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0))
    (hderivativeInt : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0))
    (hcompletion : positiveTailCompletion h z = -I * z * F)
    (hcompletionDerivative :
      positiveTailCompletionDerivative h z = -I * (F + z * D)) :
    (D * (starRingEnd ℂ) F).im ≤
      (2 / z.im) * Complex.normSq F := by
  apply orientedCurrent_le_two_div_im_of_completion_contraction hz
    hcompletion hcompletionDerivative
  calc
    ‖positiveTailCompletionDerivative h z‖ ≤
        (positiveTailCompletion h z).re / z.im :=
      norm_positiveTailCompletionDerivative_le_re_div hz hh
        hcompletionInt hderivativeInt
    _ ≤ ‖positiveTailCompletion h z‖ / z.im := by
      exact (div_le_div_iff_of_pos_right hz).2 (Complex.re_le_norm _)

theorem abs_orientedCurrent_le_two_div_im_of_positiveTailCompletion
    {h : ℝ → ℝ} {F D z : ℂ} (hz : 0 < z.im)
    (hh : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ h t)
    (hcompletionInt : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0))
    (hderivativeInt : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0))
    (hcompletion : positiveTailCompletion h z = -I * z * F)
    (hcompletionDerivative :
      positiveTailCompletionDerivative h z = -I * (F + z * D)) :
    |(D * (starRingEnd ℂ) F).im| ≤
      (2 / z.im) * Complex.normSq F := by
  apply abs_orientedCurrent_le_two_div_im_of_completion_contraction hz
    hcompletion hcompletionDerivative
  calc
    ‖positiveTailCompletionDerivative h z‖ ≤
        (positiveTailCompletion h z).re / z.im :=
      norm_positiveTailCompletionDerivative_le_re_div hz hh
        hcompletionInt hderivativeInt
    _ ≤ ‖positiveTailCompletion h z‖ / z.im := by
      exact (div_le_div_iff_of_pos_right hz).2 (Complex.re_le_norm _)

/-- A complete finite critical translate packet has a uniform half-plane upper current budget.
All off-diagonal Hermitian currents between its Abel blocks are retained in the norm of the final
recombined packet value. -/
theorem criticalLogPhase_tail_packetCurrent_le_two_div_im
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 < z.im) (N : ℕ) :
    (((∑ j ∈ Finset.range N,
        (criticalLogPhaseCoefficient L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z +
          criticalLogPhaseCoefficientDerivative L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z))) *
      (starRingEnd ℂ)
        (∑ j ∈ Finset.range N,
          criticalLogPhaseCoefficient L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)).im ≤
      (2 / z.im) *
        Complex.normSq
          (∑ j ∈ Finset.range N,
            criticalLogPhaseCoefficient L j z *
              thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z) := by
  rw [criticalLogPhase_tail_packetCurrent_eq_translatedProfile hL hz.le N,
    criticalLogPhase_tail_packet_eq_translatedProfile hL hz.le N]
  let h : ℝ → ℝ := fun t =>
    -criticalLogPhaseTranslatedDensityProfileDerivative L N t
  apply orientedCurrent_le_two_div_im_of_positiveTailCompletion
    (h := h) hz
  · intro t ht
    exact neg_criticalLogPhaseTranslatedDensityProfileDerivative_nonneg hL N ht.le
  · simpa only [h] using
      integrableOn_neg_profileDerivative_mul_one_sub_phase hL N hz.le
  · simpa only [h] using
      integrableOn_neg_profileDerivative_mul_phaseDerivative hL N hz.le
  · simpa only [h] using positiveTailCompletion_neg_profileDerivative_eq hL N hz.le
  · simpa only [h] using
      positiveTailCompletionDerivative_neg_profileDerivative_eq hL N hz.le

/-- Absolute form of the complete packet budget.  It is stable under the signed cosine rotation
created by pairing the two reflected logarithmic phase channels. -/
theorem abs_criticalLogPhase_tail_packetCurrent_le_two_div_im
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 < z.im) (N : ℕ) :
    |(((∑ j ∈ Finset.range N,
        (criticalLogPhaseCoefficient L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z +
          criticalLogPhaseCoefficientDerivative L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z))) *
      (starRingEnd ℂ)
        (∑ j ∈ Finset.range N,
          criticalLogPhaseCoefficient L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)).im| ≤
      (2 / z.im) *
        Complex.normSq
          (∑ j ∈ Finset.range N,
            criticalLogPhaseCoefficient L j z *
              thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z) := by
  rw [criticalLogPhase_tail_packetCurrent_eq_translatedProfile hL hz.le N,
    criticalLogPhase_tail_packet_eq_translatedProfile hL hz.le N]
  let h : ℝ → ℝ := fun t =>
    -criticalLogPhaseTranslatedDensityProfileDerivative L N t
  apply abs_orientedCurrent_le_two_div_im_of_positiveTailCompletion
    (h := h) hz
  · intro t ht
    exact neg_criticalLogPhaseTranslatedDensityProfileDerivative_nonneg hL N ht.le
  · simpa only [h] using
      integrableOn_neg_profileDerivative_mul_one_sub_phase hL N hz.le
  · simpa only [h] using
      integrableOn_neg_profileDerivative_mul_phaseDerivative hL N hz.le
  · simpa only [h] using positiveTailCompletion_neg_profileDerivative_eq hL N hz.le
  · simpa only [h] using
      positiveTailCompletionDerivative_neg_profileDerivative_eq hL N hz.le

end

end RHTower
