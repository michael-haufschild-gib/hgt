import GaloisForLFunctions.RHTower.ThetaArithmeticWeightedAdmission
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exact two-tail density ratio of the theta weighted translation scale

The literal change-of-variable density has one Gaussian coefficient at
each cusp. Its envelope ratio has a positive finite limit, including the
zero Gaussian coefficient where the remaining linear exponent matters.
-/

open Filter Topology Set

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-- The literal squared-norm density after translating the input variable. -/
def thetaTranslationDensityRatio (q q' a y : ℝ) : ℝ :=
  thetaCuspFullSource (y-a) ^ (-q') / thetaCuspFullSource y ^ (-q)

theorem thetaTranslationDensityRatio_pos (q q' a y : ℝ) :
    0 < thetaTranslationDensityRatio q q' a y :=
  div_pos (Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all _) _)
    (Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all _) _)

theorem continuous_thetaTranslationDensityRatio (q q' a : ℝ) :
    Continuous (thetaTranslationDensityRatio q q' a) := by
  have hsource := contDiff_thetaCuspFullSource.continuous
  exact ((hsource.comp (continuous_id.sub continuous_const)).rpow_const
    fun y => Or.inl (thetaCuspFullSource_pos_all (y-a)).ne').div
      (hsource.rpow_const fun y => Or.inl (thetaCuspFullSource_pos_all y).ne')
      (fun y => (Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all y) _).ne')

theorem thetaTranslationDensityRatio_neg (q q' a y : ℝ) :
    thetaTranslationDensityRatio q q' a (-y) = thetaTranslationDensityRatio q q' (-a) y := by
  unfold thetaTranslationDensityRatio
  rw [show -y-a = -(y- -a) by ring, thetaCuspFullSource_neg, thetaCuspFullSource_neg]

theorem thetaTranslationDensityRatio_zero (q q' y : ℝ) :
    thetaTranslationDensityRatio q q' 0 y = thetaCuspFullSource y ^ (q-q') := by
  unfold thetaTranslationDensityRatio
  rw [sub_zero, ← Real.rpow_sub (thetaCuspFullSource_pos_all y)]
  congr 1
  ring

/-- The exact positive-cusp envelope ratio. -/
def thetaTranslationDensityModel (q q' a y : ℝ) : ℝ :=
  thetaEnvelope (y-a) ^ (-q') / thetaEnvelope y ^ (-q)

theorem thetaTranslationDensityModel_pos (q q' a y : ℝ) :
    0 < thetaTranslationDensityModel q q' a y :=
  div_pos (Real.rpow_pos_of_pos (thetaEnvelope_pos _) _)
    (Real.rpow_pos_of_pos (thetaEnvelope_pos _) _)

private theorem envelope_eq_exp (y : ℝ) :
    thetaEnvelope y = Real.exp (9*y/2-Real.pi*Real.exp (2*y)) := by
  rw [thetaEnvelope, ← Real.exp_add]
  congr 1
  ring

theorem thetaTranslationDensityModel_eq_exp (q q' a y : ℝ) :
    thetaTranslationDensityModel q q' a y =
      Real.exp (9*(q-q')*y/2 + 9*q'*a/2 +
        Real.pi*(q'*Real.exp (-2*a)-q)*Real.exp (2*y)) := by
  have hs : Real.exp (2*(y-a)) = Real.exp (-2*a)*Real.exp (2*y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [thetaTranslationDensityModel, envelope_eq_exp, envelope_eq_exp,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_sub]
  congr 1
  rw [hs]
  ring

private theorem thetaTranslationDensityModel_fun (q q' a : ℝ) :
    thetaTranslationDensityModel q q' a = fun y =>
      Real.exp ((9*(q-q')/2)*y + 9*q'*a/2 +
        Real.pi*(q'*Real.exp (-2*a)-q)*Real.exp (2*y)) := by
  funext y
  rw [thetaTranslationDensityModel_eq_exp]
  congr 1
  ring

/-- The actual source contributes the exact positive power of its first-atom constant. -/
theorem thetaTranslationDensityRatio_div_model_tendsto (q q' a : ℝ) :
    Tendsto (fun y => thetaTranslationDensityRatio q q' a y /
      thetaTranslationDensityModel q q' a y) atTop (𝓝 ((4*Real.pi^2)^(q-q'))) := by
  have hC : 0 < 4*Real.pi^2 := by positivity
  have hshift : Tendsto (fun y : ℝ => y-a) atTop atTop := by
    change Tendsto (fun y : ℝ => y + -a) atTop atTop
    exact tendsto_atTop_add_const_right atTop (-a) (tendsto_id (α := ℝ))
  have h1 := (Real.continuousAt_rpow_const (4*Real.pi^2) (-q')
    (Or.inl hC.ne')).tendsto.comp (thetaCuspFullSource_div_envelope_tendsto.comp hshift)
  have h2 := (Real.continuousAt_rpow_const (4*Real.pi^2) (-q)
    (Or.inl hC.ne')).tendsto.comp thetaCuspFullSource_div_envelope_tendsto
  have h := h1.div h2 (Real.rpow_pos_of_pos hC (-q)).ne'
  have hvalue : (4*Real.pi^2)^(-q')/(4*Real.pi^2)^(-q) = (4*Real.pi^2)^(q-q') := by
    rw [← Real.rpow_sub hC]
    congr 1
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards with y
  change (thetaCuspFullSource (y-a)/thetaEnvelope (y-a))^(-q') /
    (thetaCuspFullSource y/thetaEnvelope y)^(-q) = _
  rw [Real.div_rpow (thetaCuspFullSource_pos_all (y-a)).le (thetaEnvelope_pos (y-a)).le,
    Real.div_rpow (thetaCuspFullSource_pos_all y).le (thetaEnvelope_pos y).le]
  dsimp only [thetaTranslationDensityRatio, thetaTranslationDensityModel]
  field_simp [(Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all y) (-q)).ne',
    (Real.rpow_pos_of_pos (thetaEnvelope_pos (y-a)) (-q')).ne',
    (Real.rpow_pos_of_pos (thetaEnvelope_pos y) (-q)).ne']

private theorem linear_double_exp_ratio (b c d : ℝ) :
    Tendsto (fun y : ℝ => (b*y+c+d*Real.exp (2*y))/Real.exp (2*y)) atTop (𝓝 d) := by
  have h1 : Tendsto (fun y : ℝ => y/Real.exp (2*y)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, div_eq_mul_inv, ← Real.exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 2 (by norm_num)
  have h0 : Tendsto (fun y : ℝ => 1/Real.exp (2*y)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, div_eq_mul_inv, ← Real.exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 2 (by norm_num)
  have h := ((h1.const_mul b).add (h0.const_mul c)).add_const d
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards with y
  field_simp [Real.exp_ne_zero (2*y)]

private theorem tendsto_double_exp_linear_zero (b c d : ℝ) (hd : d < 0) :
    Tendsto (fun y : ℝ => Real.exp (b*y+c+d*Real.exp (2*y))) atTop (𝓝 0) := by
  have he : Tendsto (fun y : ℝ => Real.exp (2*y)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have hscale : Tendsto (fun y : ℝ => (d/2)*Real.exp (2*y)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : d/2 < 0)).mpr he
  have hb : ∀ᶠ y : ℝ in atTop, b*y+c+d*Real.exp (2*y) ≤ (d/2)*Real.exp (2*y) := by
    filter_upwards [(linear_double_exp_ratio b c d).eventually
      (Iio_mem_nhds (by linarith : d < d/2))] with y hy
    exact ((div_lt_iff₀ (Real.exp_pos _)).mp hy).le
  exact Real.tendsto_exp_atBot.comp (tendsto_atBot_mono' atTop hb hscale)

private theorem tendsto_double_exp_linear_atTop (b c d : ℝ) (hd : 0 < d) :
    Tendsto (fun y : ℝ => Real.exp (b*y+c+d*Real.exp (2*y))) atTop atTop := by
  have he : Tendsto (fun y : ℝ => Real.exp (2*y)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have hscale := he.const_mul_atTop (by linarith : 0 < d/2)
  have hb : ∀ᶠ y : ℝ in atTop, (d/2)*Real.exp (2*y) ≤ b*y+c+d*Real.exp (2*y) := by
    filter_upwards [(linear_double_exp_ratio b c d).eventually
      (Ioi_mem_nhds (by linarith : d/2 < d))] with y hy
    exact ((lt_div_iff₀ (Real.exp_pos _)).mp hy).le
  exact Real.tendsto_exp_atTop.comp (tendsto_atTop_mono' atTop hb hscale)

theorem thetaTranslationDensityRatio_tendsto_zero_atTop
    (q q' a : ℝ) (hmargin : q'*Real.exp (-2*a) < q) :
    Tendsto (thetaTranslationDensityRatio q q' a) atTop (𝓝 0) := by
  have hm : Tendsto (thetaTranslationDensityModel q q' a) atTop (𝓝 0) := by
    rw [thetaTranslationDensityModel_fun]
    exact tendsto_double_exp_linear_zero _ _ _ (mul_neg_of_pos_of_neg Real.pi_pos (by linarith))
  have h := (thetaTranslationDensityRatio_div_model_tendsto q q' a).mul hm
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with y
  exact div_mul_cancel₀ _ (thetaTranslationDensityModel_pos q q' a y).ne'

theorem thetaTranslationDensityRatio_tendsto_atTop_of_strict
    (q q' a : ℝ) (hmargin : q < q'*Real.exp (-2*a)) :
    Tendsto (thetaTranslationDensityRatio q q' a) atTop atTop := by
  have hm : Tendsto (thetaTranslationDensityModel q q' a) atTop atTop := by
    rw [thetaTranslationDensityModel_fun]
    exact tendsto_double_exp_linear_atTop _ _ _ (mul_pos Real.pi_pos (by linarith))
  let L := (4*Real.pi^2)^(q-q')
  have hL : 0 < L := Real.rpow_pos_of_pos (by positivity) _
  have hbound : ∀ᶠ y : ℝ in atTop,
      (L/2)*thetaTranslationDensityModel q q' a y ≤ thetaTranslationDensityRatio q q' a y := by
    filter_upwards [(thetaTranslationDensityRatio_div_model_tendsto q q' a).eventually
      (Ioi_mem_nhds (by dsimp [L]; linarith : L/2 < L))] with y hy
    exact ((lt_div_iff₀ (thetaTranslationDensityModel_pos q q' a y)).mp hy).le
  exact tendsto_atTop_mono' atTop hbound (hm.const_mul_atTop (by linarith : 0 < L/2))

theorem thetaTranslationDensityRatio_tendsto_atTop_of_equal
    (q q' a : ℝ) (hequal : q'*Real.exp (-2*a) = q) (hlinear : q' < q) :
    Tendsto (thetaTranslationDensityRatio q q' a) atTop atTop := by
  have hm : Tendsto (thetaTranslationDensityModel q q' a) atTop atTop := by
    rw [thetaTranslationDensityModel_fun]
    simp only [hequal, sub_self, mul_zero, zero_mul, add_zero]
    apply Real.tendsto_exp_atTop.comp
    have hlin : 0 < 9*(q-q')/2 := by linarith
    exact tendsto_atTop_add_const_right atTop (9*q'*a/2) (tendsto_id.const_mul_atTop hlin)
  let L := (4*Real.pi^2)^(q-q')
  have hL : 0 < L := Real.rpow_pos_of_pos (by positivity) _
  have hbound : ∀ᶠ y : ℝ in atTop,
      (L/2)*thetaTranslationDensityModel q q' a y ≤ thetaTranslationDensityRatio q q' a y := by
    filter_upwards [(thetaTranslationDensityRatio_div_model_tendsto q q' a).eventually
      (Ioi_mem_nhds (by dsimp [L]; linarith : L/2 < L))] with y hy
    exact ((lt_div_iff₀ (thetaTranslationDensityModel_pos q q' a y)).mp hy).le
  exact tendsto_atTop_mono' atTop hbound (hm.const_mul_atTop (by linarith : 0 < L/2))

theorem thetaTranslationDensityRatio_tendsto_zero_atBot
    (q q' a : ℝ) (hmargin : q'*Real.exp (2*a) < q) :
    Tendsto (thetaTranslationDensityRatio q q' a) atBot (𝓝 0) := by
  have hm : q'*Real.exp (-2*(-a)) < q := by
    simpa only [mul_neg, neg_mul, neg_neg] using hmargin
  have h := (thetaTranslationDensityRatio_tendsto_zero_atTop q q' (-a) hm).comp
    (tendsto_neg_atBot_atTop (G := ℝ))
  apply h.congr'
  filter_upwards with y
  change thetaTranslationDensityRatio q q' (-a) (-y) = _
  rw [thetaTranslationDensityRatio_neg, neg_neg]

private theorem continuous_bddAbove_of_zero_tails {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Tendsto f atTop (𝓝 0)) (hn : Tendsto f atBot (𝓝 0)) : BddAbove (range f) := by
  obtain ⟨P, hP⟩ := eventually_atTop.mp (hp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨N, hN⟩ := eventually_atBot.mp (hn.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := N) (b := P)).bddAbove_image hf.continuousOn
  refine ⟨max 1 C, ?_⟩
  rintro _ ⟨y, rfl⟩
  by_cases hny : y ≤ N
  · exact (hN y hny).le.trans (le_max_left _ _)
  · by_cases hpy : P ≤ y
    · exact (hP y hpy).le.trans (le_max_left _ _)
    · exact (hC ⟨y, ⟨(lt_of_not_ge hny).le, (lt_of_not_ge hpy).le⟩, rfl⟩).trans
        (le_max_right _ _)

private theorem not_bddAbove_of_tendsto_atTop {f : ℝ → ℝ} (hf : Tendsto f atTop atTop) :
    ¬ BddAbove (range f) := by
  rintro ⟨C, hC⟩
  obtain ⟨y, hy⟩ := (hf.eventually (eventually_ge_atTop (C+1))).exists
  have hu := hC (mem_range_self y)
  linarith

theorem thetaTranslationDensityRatio_bddAbove_neg_iff (q q' a : ℝ) :
    BddAbove (range (thetaTranslationDensityRatio q q' a)) ↔
      BddAbove (range (thetaTranslationDensityRatio q q' (-a))) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := hC (mem_range_self (-y))
    rwa [thetaTranslationDensityRatio_neg] at h
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := hC (mem_range_self (-y))
    rwa [thetaTranslationDensityRatio_neg, neg_neg] at h

theorem thetaTranslationDensityRatio_strict_threshold_iff (q q' a : ℝ) :
    q' < q*Real.exp (-2*|a|) ↔ q'*Real.exp (2*|a|) < q := by
  have he : Real.exp (-2*|a|)*Real.exp (2*|a|) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  constructor
  · intro h
    have hm := mul_lt_mul_of_pos_right h (Real.exp_pos (2*|a|))
    simpa only [mul_assoc, he, mul_one] using hm
  · intro h
    have hm := mul_lt_mul_of_pos_right h (Real.exp_pos (-2*|a|))
    have her : Real.exp (2*|a|)*Real.exp (-2*|a|) = 1 := by rwa [mul_comm]
    simpa only [mul_assoc, her, mul_one] using hm

/-- Strict Gaussian slack at both cusps gives a globally bounded literal ratio. -/
theorem thetaTranslationDensityRatio_bddAbove_of_strict
    (q q' a : ℝ) (hq' : 0 < q') (hmargin : q' < q*Real.exp (-2*|a|)) :
    BddAbove (range (thetaTranslationDensityRatio q q' a)) := by
  have hd := (thetaTranslationDensityRatio_strict_threshold_iff q q' a).mp hmargin
  have hp : q'*Real.exp (-2*a) < q := by
    apply lt_of_le_of_lt _ hd
    apply mul_le_mul_of_nonneg_left _ hq'.le
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs a]
  have hn : q'*Real.exp (2*a) < q := by
    apply lt_of_le_of_lt _ hd
    apply mul_le_mul_of_nonneg_left _ hq'.le
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self a]
  exact continuous_bddAbove_of_zero_tails (continuous_thetaTranslationDensityRatio q q' a)
    (thetaTranslationDensityRatio_tendsto_zero_atTop q q' a hp)
    (thetaTranslationDensityRatio_tendsto_zero_atBot q q' a hn)

/-- At equality the dangerous tail retains a positive linear exponent for every nonzero shift. -/
theorem thetaTranslationDensityRatio_not_bddAbove
    (q q' a : ℝ) (hq' : 0 < q') (ha : a ≠ 0)
    (hmargin : q*Real.exp (-2*|a|) ≤ q') :
    ¬ BddAbove (range (thetaTranslationDensityRatio q q' a)) := by
  intro hbounded
  have hnormalized : BddAbove (range (thetaTranslationDensityRatio q q' (-|a|))) := by
    by_cases hneg : a ≤ 0
    · simpa only [abs_of_nonpos hneg, neg_neg] using hbounded
    · simpa only [abs_of_pos (lt_of_not_ge hneg)] using
        (thetaTranslationDensityRatio_bddAbove_neg_iff q q' a).mp hbounded
  have he : Real.exp (-2*|a|)*Real.exp (2*|a|) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hd : q ≤ q'*Real.exp (2*|a|) := by
    have hm := mul_le_mul_of_nonneg_right hmargin (Real.exp_pos (2*|a|)).le
    simpa only [mul_assoc, he, mul_one] using hm
  have hout : Tendsto (thetaTranslationDensityRatio q q' (-|a|)) atTop atTop := by
    rcases lt_or_eq_of_le hd with hstrict | hequal
    · apply thetaTranslationDensityRatio_tendsto_atTop_of_strict
      simpa only [mul_neg, neg_mul, neg_neg] using hstrict
    · apply thetaTranslationDensityRatio_tendsto_atTop_of_equal
      · simpa only [mul_neg, neg_mul, neg_neg] using hequal.symm
      · have hb := Real.one_lt_exp_iff.mpr (by
          linarith [abs_pos.mpr ha] : 0 < 2*|a|)
        nlinarith
  exact not_bddAbove_of_tendsto_atTop hout hnormalized

theorem thetaTranslationDensityRatio_bddAbove_zero_iff (q q' : ℝ) :
    BddAbove (range (thetaTranslationDensityRatio q q' 0)) ↔ q' ≤ q := by
  constructor
  · intro hbounded
    by_contra hle
    have hstrict : q < q'*Real.exp (-2*0) := by simpa using lt_of_not_ge hle
    exact not_bddAbove_of_tendsto_atTop
      (thetaTranslationDensityRatio_tendsto_atTop_of_strict q q' 0 hstrict) hbounded
  · intro hle
    rcases lt_or_eq_of_le hle with hstrict | rfl
    · apply continuous_bddAbove_of_zero_tails (continuous_thetaTranslationDensityRatio q q' 0)
      · apply thetaTranslationDensityRatio_tendsto_zero_atTop
        simpa using hstrict
      · apply thetaTranslationDensityRatio_tendsto_zero_atBot
        simpa using hstrict
    · refine ⟨1, ?_⟩
      rintro _ ⟨y, rfl⟩
      simp only [thetaTranslationDensityRatio_zero, sub_self, Real.rpow_zero, le_refl]

/-- The exact strict transport boundary of every nonzero real shift. -/
theorem thetaTranslationDensityRatio_bddAbove_iff_of_ne_zero
    (q q' a : ℝ) (hq' : 0 < q') (ha : a ≠ 0) :
    BddAbove (range (thetaTranslationDensityRatio q q' a)) ↔ q' < q*Real.exp (-2*|a|) := by
  constructor
  · intro hbounded
    by_contra hmargin
    exact thetaTranslationDensityRatio_not_bddAbove q q' a hq' ha (le_of_not_gt hmargin) hbounded
  · exact thetaTranslationDensityRatio_bddAbove_of_strict q q' a hq'

/-- Complete scalar transport classification, with its distinct zero-shift endpoint. -/
theorem thetaTranslationDensityRatio_bddAbove_iff (q q' a : ℝ) (hq' : 0 < q') :
    BddAbove (range (thetaTranslationDensityRatio q q' a)) ↔
      (a = 0 ∧ q' ≤ q) ∨ (a ≠ 0 ∧ q' < q*Real.exp (-2*|a|)) := by
  by_cases ha : a = 0
  · subst a
    simpa using thetaTranslationDensityRatio_bddAbove_zero_iff q q'
  · simpa [ha] using
      thetaTranslationDensityRatio_bddAbove_iff_of_ne_zero q q' a hq' ha

end

end RHTower
