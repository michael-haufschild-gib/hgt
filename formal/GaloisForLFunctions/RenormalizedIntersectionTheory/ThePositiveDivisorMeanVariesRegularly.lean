import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanAtRealLogarithmicHorizons

/-!
# Regular growth of the positive divisor mean

The relative renewal error controls the logarithmic derivative of the integrated
positive mean. Right-derivative comparison then turns this control into scale ratios.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- A first fixed-error comparison bounds the logarithmic derivative away from zero
and infinity. -/
theorem eventually_positive_divisor_polarMoment_comparison (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∀ᶠ u : ℝ in atTop,
      2 * realPolarMoment (signDivisorCount (primeSetFlip P)) u ≤
        u * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u ∧
      u * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u ≤
        4 * realPolarMoment (signDivisorCount (primeSetFlip P)) u := by
  obtain ⟨C, hC⟩ := exists_abs_real_positive_divisor_renewal_equation_le P hP
    (by norm_num : (0 : ℝ) < 1 / 2)
  let D := max C 0
  filter_upwards [eventually_ge_atTop (max 1 (8 * D))] with u hu
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hDu : D ≤ u / 8 := by have := (le_max_right _ _).trans hu; linarith only [this]
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u
  let J := realPolarMoment (signDivisorCount (primeSetFlip P)) u
  have hG : 0 ≤ G := zero_le_one.trans
    (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hu0.le)
  have hJ : 0 ≤ J := hu0.le.trans (le_realPolarMoment_signDivisorCount
    (primeSetFlip_isSignGauge P) hu0.le)
  have herror : |u * G - 3 * J| ≤ 1 / 2 * J + C * G := hC u hu0.le
  have hCD := mul_le_mul_of_nonneg_right (le_max_left C 0) hG
  change C * G ≤ D * G at hCD
  have hscale := mul_le_mul_of_nonneg_right hDu hG
  have hlow := (abs_le.mp herror).1
  have hupp := (abs_le.mp herror).2
  change 2 * J ≤ u * G ∧ u * G ≤ 4 * J
  constructor <;> nlinarith only [hlow, hupp, hCD, hscale, hJ]

/-- The integrated positive divisor mean has logarithmic derivative asymptotic to `3/u`. -/
theorem tendsto_positive_divisor_logarithmic_derivative (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    Tendsto (fun u : ℝ =>
      u * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u /
        realPolarMoment (signDivisorCount (primeSetFlip P)) u) atTop (𝓝 3) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨C, hC⟩ := exists_abs_real_positive_divisor_renewal_equation_le P hP (half_pos hδ)
  filter_upwards [eventually_positive_divisor_polarMoment_comparison P hP,
    eventually_ge_atTop (max 1 (16 * |C| / δ))] with u hcomp hu
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u
  let J := realPolarMoment (signDivisorCount (primeSetFlip P)) u
  have hG : 0 ≤ G := zero_le_one.trans
    (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hu0.le)
  have hJ : 0 < J := hu0.trans_le (le_realPolarMoment_signDivisorCount
    (primeSetFlip_isSignGauge P) hu0.le)
  have hscale : 16 * |C| ≤ δ * u := by
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hu)
    nlinarith only [h]
  have hupper : u * G ≤ 4 * J := hcomp.2
  have hCG : C * G ≤ |C| * G := mul_le_mul_of_nonneg_right (le_abs_self C) hG
  have hsmall : |C| * G ≤ δ / 4 * J := by
    have h1 := mul_le_mul_of_nonneg_left hupper (abs_nonneg C)
    have h2 := mul_le_mul_of_nonneg_right hscale hJ.le
    have hh : u * (|C| * G) ≤ u * (δ / 4 * J) := by nlinarith only [h1, h2]
    exact le_of_mul_le_mul_left hh hu0
  have herror : |u * G - 3 * J| ≤ δ / 2 * J + C * G := hC u hu0.le
  have herror' : |u * G - 3 * J| ≤ (3 * δ / 4) * J := by
    nlinarith only [herror, hCG, hsmall]
  have heq : u * G / J - 3 = (u * G - 3 * J) / J := by field_simp [hJ.ne']
  change dist (u * G / J) 3 < δ
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hJ]
  exact ((div_le_iff₀ hJ).mpr herror').trans_lt (by linarith only [hδ])

private theorem positive_divisor_log_increment_bounds (P : Set ℕ) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hr : ∀ t ∈ Set.Ico a b,
      3 - ε ≤ t * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) t /
        realPolarMoment (signDivisorCount (primeSetFlip P)) t ∧
      t * realLogHarmonicSum (signDivisorCount (primeSetFlip P)) t /
        realPolarMoment (signDivisorCount (primeSetFlip P)) t ≤ 3 + ε) :
    (3 - ε) * (Real.log b - Real.log a) ≤
      Real.log (realPolarMoment (signDivisorCount (primeSetFlip P)) b) -
        Real.log (realPolarMoment (signDivisorCount (primeSetFlip P)) a) ∧
    Real.log (realPolarMoment (signDivisorCount (primeSetFlip P)) b) -
        Real.log (realPolarMoment (signDivisorCount (primeSetFlip P)) a) ≤
      (3 + ε) * (Real.log b - Real.log a) := by
  let J := realPolarMoment (signDivisorCount (primeSetFlip P))
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P))
  let F : ℝ → ℝ := fun t => Real.log (J t) - Real.log (J a)
  let B : ℝ → ℝ → ℝ := fun r t => r * (Real.log t - Real.log a)
  have hJpos : ∀ t, a ≤ t → 0 < J t := fun t ht =>
    (ha.trans_le ht).trans_le (le_realPolarMoment_signDivisorCount
      (primeSetFlip_isSignGauge P) (ha.trans_le ht).le)
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    intro t ht
    exact (((Real.continuousAt_log (hJpos t ht.1).ne').comp
      (continuous_realPolarMoment _).continuousAt).sub continuousAt_const).continuousWithinAt
  have hFder : ∀ t ∈ Set.Ico a b, HasDerivWithinAt F (G t / J t) (Set.Ici t) t :=
    fun t ht => ((hasDerivWithinAt_realPolarMoment _ t).log (hJpos t ht.1).ne').sub_const _
  have hBcont : ∀ r, ContinuousOn (B r) (Set.Icc a b) := by
    intro r t ht
    exact (((Real.continuousAt_log (ha.trans_le ht.1).ne').sub
      continuousAt_const).const_mul r).continuousWithinAt
  have hBder : ∀ r t, t ∈ Set.Ico a b →
      HasDerivWithinAt (B r) (r / t) (Set.Ici t) t := by
    intro r t ht
    simpa only [B, div_eq_mul_inv] using
      (((Real.hasDerivAt_log (ha.trans_le ht.1).ne').sub_const (Real.log a)).const_mul r).hasDerivWithinAt
  have hlo : ∀ t ∈ Set.Ico a b, (3 - ε) / t ≤ G t / J t := by
    intro t ht
    apply (div_le_iff₀ (ha.trans_le ht.1)).mpr
    calc
      _ ≤ t * G t / J t := (hr t ht).1
      _ = _ := by ring
  have hup : ∀ t ∈ Set.Ico a b, G t / J t ≤ (3 + ε) / t := by
    intro t ht
    apply (le_div_iff₀ (ha.trans_le ht.1)).mpr
    calc
      _ = t * G t / J t := by ring
      _ ≤ _ := (hr t ht).2
  have hleft := image_le_of_deriv_right_le_deriv_boundary (hBcont (3 - ε))
    (hBder (3 - ε)) (show B (3 - ε) a ≤ F a by simp [B, F]) hFcont hFder hlo
    (Set.right_mem_Icc.mpr hab)
  have hright := image_le_of_deriv_right_le_deriv_boundary hFcont hFder
    (show F a ≤ B (3 + ε) a by simp [B, F]) (hBcont (3 + ε)) (hBder (3 + ε)) hup
    (Set.right_mem_Icc.mpr hab)
  exact ⟨hleft, hright⟩

/-- The logarithmic derivative limit gives uniform power comparisons on every sufficiently
large interval of logarithmic horizons. -/
theorem exists_positive_divisor_log_scaling_bounds (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ a b : ℝ, U ≤ a → a ≤ b →
      (3 - ε) * Real.log (b / a) ≤
        Real.log (realPolarMoment (signDivisorCount (primeSetFlip P)) b /
          realPolarMoment (signDivisorCount (primeSetFlip P)) a) ∧
      Real.log (realPolarMoment (signDivisorCount (primeSetFlip P)) b /
          realPolarMoment (signDivisorCount (primeSetFlip P)) a) ≤
        (3 + ε) * Real.log (b / a) := by
  have hlim := tendsto_positive_divisor_logarithmic_derivative P hP
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hlim) ε hε)
  refine ⟨max 1 U₀, le_max_left _ _, fun a b ha hab => ?_⟩
  have ha0 : 0 < a := zero_lt_one.trans_le ((le_max_left _ _).trans ha)
  have hb0 := ha0.trans_le hab
  have hJa : 0 < realPolarMoment (signDivisorCount (primeSetFlip P)) a :=
    ha0.trans_le (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) ha0.le)
  have hJb : 0 < realPolarMoment (signDivisorCount (primeSetFlip P)) b :=
    hb0.trans_le (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hb0.le)
  rw [Real.log_div hb0.ne' ha0.ne', Real.log_div hJb.ne' hJa.ne']
  apply positive_divisor_log_increment_bounds P ha0 hab
  intro t ht
  have h := hU₀ t (((le_max_right _ _).trans ha).trans ht.1)
  rw [Real.dist_eq] at h
  have hb := abs_lt.mp h
  constructor <;> linarith only [hb.1, hb.2]

/-- The logarithm of the integrated mean has an asymptotically cubic scale ratio. -/
theorem tendsto_log_positive_divisor_polarMoment_ratio (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.log
      (realPolarMoment (signDivisorCount (primeSetFlip P)) (c * u) /
        realPolarMoment (signDivisorCount (primeSetFlip P)) u))
      atTop (𝓝 (3 * Real.log c)) := by
  let J := realPolarMoment (signDivisorCount (primeSetFlip P))
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let ε := δ / (1 + |Real.log c|)
  have hden : 0 < 1 + |Real.log c| := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hsmall : ε * |Real.log c| < δ := by
    have heq : ε * (1 + |Real.log c|) = δ := div_mul_cancel₀ δ hden.ne'
    nlinarith only [heq, hε]
  obtain ⟨U, hU1, hU⟩ := exists_positive_divisor_log_scaling_bounds P hP hε
  filter_upwards [eventually_ge_atTop (max U (U / c))] with u hu
  have huU := (le_max_left _ _).trans hu
  have hcuU : U ≤ c * u := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hu)
    simpa only [mul_comm] using h
  have hu0 : 0 < u := zero_lt_one.trans_le (hU1.trans huU)
  have hcu0 := mul_pos hc hu0
  have hJu : 0 < J u := hu0.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hu0.le)
  have hJcu : 0 < J (c * u) := hcu0.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hcu0.le)
  have hratio : c * u / u = c := mul_div_cancel_right₀ c hu0.ne'
  have hbound : |Real.log (J (c * u) / J u) - 3 * Real.log c| ≤
      ε * |Real.log c| := by
    rcases le_total u (c * u) with huc | hcu
    · have h := hU u (c * u) huU huc
      rw [hratio] at h
      have hc1 : 1 ≤ c := by nlinarith only [huc, hu0]
      rw [abs_of_nonneg (Real.log_nonneg hc1)]
      apply abs_le.mpr
      constructor <;> nlinarith only [h.1, h.2]
    · have h := hU (c * u) u hcuU hcu
      have hc1 : c ≤ 1 := by nlinarith only [hcu, hu0]
      have hlog : Real.log (u / (c * u)) = -Real.log c := by
        rw [Real.log_div hu0.ne' hcu0.ne', Real.log_mul hc.ne' hu0.ne']
        ring
      have hswap : Real.log (J u / J (c * u)) = -Real.log (J (c * u) / J u) := by
        rw [Real.log_div hJu.ne' hJcu.ne', Real.log_div hJcu.ne' hJu.ne']
        ring
      change (3 - ε) * Real.log (u / (c * u)) ≤ Real.log (J u / J (c * u)) ∧
        Real.log (J u / J (c * u)) ≤ (3 + ε) * Real.log (u / (c * u)) at h
      rw [hlog, hswap] at h
      rw [abs_of_nonpos (Real.log_nonpos hc.le hc1)]
      apply abs_le.mpr
      constructor <;> nlinarith only [h.1, h.2]
  rw [Real.dist_eq]
  exact hbound.trans_lt hsmall

/-- The integrated positive divisor mean is regularly varying with index three. -/
theorem tendsto_positive_divisor_polarMoment_ratio (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ =>
      realPolarMoment (signDivisorCount (primeSetFlip P)) (c * u) /
        realPolarMoment (signDivisorCount (primeSetFlip P)) u) atTop (𝓝 (c ^ 3)) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_log_positive_divisor_polarMoment_ratio P hP hc)
  have hexp : Real.exp (3 * Real.log c) = c ^ 3 := by
    rw [show 3 * Real.log c = Real.log c + Real.log c + Real.log c by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hc]
    ring
  rw [hexp] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hJu := hu.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  have hJcu := (mul_pos hc hu).trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) (mul_pos hc hu).le)
  exact Real.exp_log (div_pos hJcu hJu)

/-- The positive harmonic divisor mean is regularly varying with index two. -/
theorem tendsto_positive_divisor_harmonicMean_ratio (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ =>
      realLogHarmonicSum (signDivisorCount (primeSetFlip P)) (c * u) /
        realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u) atTop (𝓝 (c ^ 2)) := by
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P))
  let J := realPolarMoment (signDivisorCount (primeSetFlip P))
  let R : ℝ → ℝ := fun u => u * G u / J u
  have hscale : Tendsto (fun u : ℝ => c * u) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b / c)] with u hu
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hu
  have hR : Tendsto R atTop (𝓝 3) := tendsto_positive_divisor_logarithmic_derivative P hP
  have hJ := tendsto_positive_divisor_polarMoment_ratio P hP hc
  have h := (((hR.comp hscale).div hR (by norm_num)).mul hJ).div_const c
  have hvalue : ((3 : ℝ) / 3 * c ^ 3) / c = c ^ 2 := by
    field_simp [hc.ne']
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hJu := hu.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  have hJcu := (mul_pos hc hu).trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) (mul_pos hc hu).le)
  have hGu : 0 < G u := zero_lt_one.trans_le
    (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  change ((c * u * G (c * u) / J (c * u)) / (u * G u / J u)) *
    (J (c * u) / J u) / c = G (c * u) / G u
  change 0 < J u at hJu
  change 0 < J (c * u) at hJcu
  field_simp [hc.ne', hu.ne', hJu.ne', hJcu.ne', hGu.ne']

/-- A uniform comparison over all smaller large horizons controls the signed renewal
convolution; fixed-scale regular variation alone would not give this estimate. -/
theorem exists_positive_divisor_harmonicMean_uniform_comparison (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ v u : ℝ, U ≤ v → v ≤ u →
      realLogHarmonicSum (signDivisorCount (primeSetFlip P)) v / v ≤
        2 * (realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u / u) := by
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P))
  let J := realPolarMoment (signDivisorCount (primeSetFlip P))
  obtain ⟨U₁, hU₁1, hU₁⟩ := exists_positive_divisor_log_scaling_bounds P hP
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp
    (eventually_positive_divisor_polarMoment_comparison P hP)
  refine ⟨max U₁ U₂, hU₁1.trans (le_max_left _ _), fun v u hvU hvu => ?_⟩
  have hv1 := hU₁1.trans ((le_max_left _ _).trans hvU)
  have hv : 0 < v := zero_lt_one.trans_le hv1
  have hu := hv.trans_le hvu
  have hJv : 0 < J v := hv.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hv.le)
  have hJu : 0 < J u := hu.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  have hlog := (hU₁ v u ((le_max_left _ _).trans hvU) hvu).1
  have hpow : (u / v) ^ 2 ≤ J u / J v := by
    have h := Real.exp_le_exp.mpr hlog
    change Real.exp ((3 - 1) * Real.log (u / v)) ≤ Real.exp (Real.log (J u / J v)) at h
    rw [Real.exp_log (div_pos hJu hJv),
      show (3 - 1) * Real.log (u / v) = Real.log (u / v) + Real.log (u / v) by ring,
      Real.exp_add, Real.exp_log (div_pos hu hv)] at h
    simpa only [pow_two] using h
  rw [div_pow] at hpow
  have hclear := (div_le_div_iff₀ (show 0 < v ^ 2 by positivity) hJv).mp hpow
  have hcompv := (hU₂ v ((le_max_right _ _).trans hvU)).2
  have hcompu := (hU₂ u (((le_max_right _ _).trans hvU).trans hvu)).1
  change v * G v ≤ 4 * J v at hcompv
  change 2 * J u ≤ u * G u at hcompu
  have h₁ := mul_le_mul_of_nonneg_left hcompv (sq_nonneg u)
  have h₂ := mul_le_mul_of_nonneg_right hcompu (sq_nonneg v)
  have hprod : (u * v) * (u * G v) ≤ (u * v) * (2 * v * G u) := by
    nlinarith only [h₁, h₂, hclear]
  have hcancel := le_of_mul_le_mul_left hprod (mul_pos hu hv)
  change G v / v ≤ 2 * (G u / u)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hv hu).mpr
  nlinarith only [hcancel]

/-- Every power below the quadratic index gives an eventual lower bound, even when
the prime logarithmic density tends to zero arbitrarily slowly. -/
theorem exists_positive_divisor_harmonicMean_rpow_lower (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {α : ℝ} (hα : α < 2) :
    ∃ A U : ℝ, 0 < A ∧ 1 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      A * u ^ α ≤ realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u := by
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P))
  let J := realPolarMoment (signDivisorCount (primeSetFlip P))
  obtain ⟨U₁, hU₁1, hU₁⟩ := exists_positive_divisor_log_scaling_bounds P hP
    (sub_pos.mpr hα)
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp
    (eventually_positive_divisor_polarMoment_comparison P hP)
  let U := max U₁ U₂
  have hU1 : 1 ≤ U := hU₁1.trans (le_max_left _ _)
  have hU0 : 0 < U := zero_lt_one.trans_le hU1
  have hJU : 0 < J U := hU0.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hU0.le)
  have hden : 0 < U ^ (1 + α) := Real.rpow_pos_of_pos hU0 _
  refine ⟨2 * J U / U ^ (1 + α), U, by positivity, hU1, fun u huU => ?_⟩
  have hu := hU0.trans_le huU
  have hJu : 0 < J u := hu.trans_le
    (le_realPolarMoment_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  have hlog := (hU₁ U u (le_max_left _ _) huU).1
  have hpower : (u / U) ^ (1 + α) ≤ J u / J U := by
    rw [Real.rpow_def_of_pos (div_pos hu hU0)]
    calc
      _ ≤ Real.exp (Real.log (J u / J U)) := Real.exp_le_exp.mpr
        (by nlinarith only [hlog])
      _ = _ := Real.exp_log (div_pos hJu hJU)
  rw [Real.div_rpow hu.le hU0.le] at hpower
  have hclear := (div_le_div_iff₀ hden hJU).mp hpower
  rw [Real.rpow_add hu, Real.rpow_one] at hclear
  have hcomp := (hU₂ u ((le_max_right _ _).trans huU)).1
  change 2 * J u ≤ u * G u at hcomp
  have hweighted := mul_le_mul_of_nonneg_right hcomp hden.le
  change (2 * J U / U ^ (1 + α)) * u ^ α ≤ G u
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have hprod : u * (2 * J U * u ^ α) ≤ u * (G u * U ^ (1 + α)) := by
    nlinarith only [hclear, hweighted]
  exact le_of_mul_le_mul_left hprod hu

/-- The positive mean dominates every strictly subquadratic power. -/
theorem tendsto_positive_divisor_harmonicMean_div_rpow_atTop (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {α : ℝ} (hα : α < 2) :
    Tendsto (fun u : ℝ =>
      realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u / u ^ α) atTop atTop := by
  let β := (α + 2) / 2
  have hβ : β < 2 := by dsimp only [β]; linarith only [hα]
  have hdiff : 0 < β - α := by dsimp only [β]; linarith only [hα]
  obtain ⟨A, U, hA, hU1, hbound⟩ := exists_positive_divisor_harmonicMean_rpow_lower P hP hβ
  have hlim : Tendsto (fun u : ℝ => A * u ^ (β - α)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hA (tendsto_rpow_atTop hdiff)
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(tendsto_atTop.mp hlim) b, eventually_ge_atTop U] with u hb huU
  have hu : 0 < u := zero_lt_one.trans_le (hU1.trans huU)
  calc
    b ≤ A * u ^ (β - α) := hb
    _ = A * u ^ β / u ^ α := by rw [Real.rpow_sub hu]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (hbound u huU) (Real.rpow_nonneg hu.le _)

end GaloisForLFunctions.RenormalizedIntersectionTheory

