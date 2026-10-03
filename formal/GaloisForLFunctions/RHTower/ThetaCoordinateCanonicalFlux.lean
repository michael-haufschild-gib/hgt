import GaloisForLFunctions.RHTower.ThetaCoordinateCanonicalGlobal
import GaloisForLFunctions.RHTower.ThetaTailConfluentCoordinateJets

/-! The canonical sign transfers through a finite primitive with vanishing flux.
Only raw Schwartz products are integrated; no quotient-current integrability is assumed. -/

noncomputable section
open Set Filter Topology MeasureTheory
namespace RHTower.ThetaCoordinate
open ThetaConfluent

local notation "k" => thetaCuspFullSource
local notation "k₁" => deriv thetaCuspFullSource
local notation "k₂" => deriv (deriv thetaCuspFullSource)
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
private abbrev s := thetaCuspSchwartzReal
private abbrev d := SchwartzMap.derivCLM ℝ ℝ s
private abbrev dd := SchwartzMap.derivCLM ℝ ℝ d

private theorem first_eq (t : ℝ) : k₁ t = -p t*k t := by
  have h : iteratedDeriv 1 thetaCuspLogSource t = k₁ t/k t := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all t).ne']

private theorem second_eq (t : ℝ) : k₂ t = (p t^2-c t)*k t := by
  have he : k₁ = fun t => -p t*k t := funext first_eq
  have h := (((hasDerivAt_thetaCuspLogDecaySlope t).neg).mul (s.hasDerivAt t)).deriv
  change deriv (fun t => -p t*k t) t = -c t*k t+ -p t*k₁ t at h
  rw [← he, first_eq] at h
  rw [h]
  ring

private theorem p_zero : p 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

private theorem p_strictMono : StrictMonoOn p (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t _; exact (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt.continuousWithinAt
  · intro t _
    rw [(hasDerivAt_thetaCuspLogDecaySlope t).deriv]
    exact thetaCuspLogCurvature_pos t

private theorem p_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ p t := by
  have h := p_strictMono.monotoneOn (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  rwa [p_zero] at h

private theorem p_pos {t : ℝ} (ht : 0 < t) : 0 < p t := by
  have h := p_strictMono (show (0:ℝ) ∈ Ici 0 by simp) ht.le ht
  rwa [p_zero] at h

private theorem sum_pos {t y : ℝ} (ht : 0 ≤ t) (hy : 0 < y) :
    0 < p t+p (t+y) := add_pos_of_nonneg_of_pos (p_nonneg ht) (p_pos (by linarith))

/-- Positive normalized product of the actual source. -/
def sourceProductWeight (t y : ℝ) : ℝ := k t*k (t+y)/(k 0*k y)

theorem sourceProductWeight_pos (t y : ℝ) : 0 < sourceProductWeight t y :=
  div_pos (mul_pos (thetaCuspFullSource_pos_all t) (thetaCuspFullSource_pos_all (t+y)))
    (mul_pos (thetaCuspFullSource_pos_all 0) (thetaCuspFullSource_pos_all y))

/-- Raw numerator of the normalized canonical moment. -/
def canonicalRawMoment (t y : ℝ) : ℝ :=
  (t+y)*k₁ t*k (t+y)-t*k t*k₁ (t+y)

private def rawMomentDerivative (t y : ℝ) : ℝ :=
  k₁ t*k (t+y)+(t+y)*k₁ t*k₁ (t+y)-t*k t*k₂ (t+y)

/-- Parameter derivative after the literal source normalization. -/
def canonicalRawDerivative (t y : ℝ) : ℝ :=
  (rawMomentDerivative t y-(1/y+k₁ y/k y)*canonicalRawMoment t y)/(y*k 0*k y)

theorem canonicalRawMoment_eq {y : ℝ} (hy : 0 < y) (t : ℝ) :
    canonicalRawMoment t y/(y*k 0*k y) = canonicalMoment t y*sourceProductWeight t y := by
  unfold canonicalRawMoment canonicalMoment sourceProductWeight
  rw [first_eq, first_eq]
  field_simp [hy.ne', (thetaCuspFullSource_pos_all 0).ne', (thetaCuspFullSource_pos_all y).ne']
  ring

private def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) : weighted f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private theorem rawMoment_expansion (y : ℝ) :
    (fun t => canonicalRawMoment t y) = fun t =>
      weighted d t*s (y+t)+y*(d t*s (y+t))-weighted s t*d (y+t) := by
  funext t
  simp only [weighted_apply]
  change (t+y)*k₁ t*k (t+y)-t*k t*k₁ (t+y) =
    t*k₁ t*k (y+t)+y*(k₁ t*k (y+t))-t*k t*k₁ (y+t)
  rw [add_comm y t]
  ring

private theorem rawDerivative_expansion (y : ℝ) :
    (fun t => rawMomentDerivative t y) = fun t =>
      d t*s (y+t)+weighted d t*d (y+t)+y*(d t*d (y+t))-weighted s t*dd (y+t) := by
  funext t
  simp only [weighted_apply]
  change k₁ t*k (t+y)+(t+y)*k₁ t*k₁ (t+y)-t*k t*k₂ (t+y) =
    k₁ t*k (y+t)+t*k₁ t*k₁ (y+t)+y*(k₁ t*k₁ (y+t))-t*k t*k₂ (y+t)
  rw [add_comm y t]
  ring

theorem canonicalRawMoment_integrable (y : ℝ) : Integrable (fun t => canonicalRawMoment t y) := by
  rw [rawMoment_expansion]
  exact ((schwartzCorrelation_integrable (weighted d) s y).add
    ((schwartzCorrelation_integrable d s y).const_mul y)).sub
      (schwartzCorrelation_integrable (weighted s) d y)

theorem canonicalRawDerivative_integrable (y : ℝ) :
    Integrable (fun t => canonicalRawDerivative t y) := by
  have hD : Integrable (fun t => rawMomentDerivative t y) := by
    rw [rawDerivative_expansion]
    exact (((schwartzCorrelation_integrable d s y).add
      (schwartzCorrelation_integrable (weighted d) d y)).add
        ((schwartzCorrelation_integrable d d y).const_mul y)).sub
          (schwartzCorrelation_integrable (weighted s) dd y)
  exact (hD.sub ((canonicalRawMoment_integrable y).const_mul (1/y+k₁ y/k y))).div_const _

/-- Shifted Schwartz products vanish at the upper integration endpoint. -/
theorem schwartzShiftedProduct_limit (f g : SchwartzMap ℝ ℝ) (y : ℝ) :
    Tendsto (fun t => f t*g (y+t)) atTop (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => y+t) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b-y)] with t ht
    linarith
  convert! (f.tendsto_cocompact.mono_left atTop_le_cocompact).mul
    ((g.tendsto_cocompact.mono_left atTop_le_cocompact).comp hs) using 1
  simp only [mul_zero]

theorem canonicalRawMoment_limit (y : ℝ) :
    Tendsto (fun t => canonicalRawMoment t y) atTop (𝓝 0) := by
  rw [rawMoment_expansion]
  simpa only [mul_zero, zero_add, sub_zero] using
    ((schwartzShiftedProduct_limit (weighted d) s y).add
      ((schwartzShiftedProduct_limit d s y).const_mul y)).sub
        (schwartzShiftedProduct_limit (weighted s) d y)

/-- The exact canonical speed is bounded along the entire nonnegative integration ray. -/
theorem canonicalSpeed_mem_Ico {t y : ℝ} (ht : 0 ≤ t) (hy : 0 < y) :
    canonicalSpeed t y ∈ Ico (0:ℝ) 1 := by
  have hz : 0 ≤ t+y := by linarith
  have hb : p y ≤ p (t+y) := p_strictMono.monotoneOn hy.le hz (by linarith)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hb) (sum_pos ht hy).le
  · change (p (t+y)-p y)/(p t+p (t+y)) < 1
    apply (div_lt_iff₀ (sum_pos ht hy)).mpr
    have hp := p_nonneg ht
    have hpy := p_pos hy
    linarith

/-- Flux removed from the finite primitive before taking its infinite endpoint. -/
def canonicalFlux (t y : ℝ) : ℝ :=
  canonicalSpeed t y*(canonicalRawMoment t y/(y*k 0*k y))

theorem canonicalFlux_zero (y : ℝ) : canonicalFlux 0 y = 0 := by
  simp only [canonicalFlux, canonicalSpeed, zero_add, sub_self, zero_div, zero_mul]

theorem canonicalFlux_limit {y : ℝ} (hy : 0 < y) :
    Tendsto (fun t => canonicalFlux t y) atTop (𝓝 0) := by
  have hM : Tendsto (fun t => canonicalRawMoment t y/(y*k 0*k y)) atTop (𝓝 0) := by
    simpa only [zero_div] using (canonicalRawMoment_limit y).div_const (y*k 0*k y)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg (canonicalFlux t y))) ?_
    (by simpa only [norm_zero] using hM.norm)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  have hSpeed := canonicalSpeed_mem_Ico ht hy
  rw [canonicalFlux, norm_mul, Real.norm_of_nonneg hSpeed.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hSpeed.2.le

private theorem moment_left_deriv (t y : ℝ) :
    HasDerivAt (fun s => canonicalMoment s y)
      (((p (t+y)-p t)+t*(c (t+y)-c t))/y-c t) t := by
  have hp := hasDerivAt_thetaCuspLogDecaySlope t
  have hz := (hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp t
    ((hasDerivAt_id t).add_const y)
  convert! ((((hasDerivAt_id t).mul (hz.sub hp)).div_const y).sub hp) using 1
  dsimp
  ring

private theorem moment_right_deriv (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (canonicalMoment t)
      ((t*c (t+y)*y-t*(p (t+y)-p t))/y^2) y := by
  have hz := (hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp y
    ((hasDerivAt_id y).const_add t)
  convert! ((((hz.sub_const (p t)).const_mul t).div (hasDerivAt_id y) hy.ne').sub_const
    (p t)) using 1
  dsimp
  ring

private theorem speed_left_deriv {t y : ℝ} (ht : 0 ≤ t) (hy : 0 < y) :
    HasDerivAt (fun s => canonicalSpeed s y)
      ((c (t+y)*(p t+p (t+y))-(p (t+y)-p y)*(c t+c (t+y)))/
        (p t+p (t+y))^2) t := by
  have hp := hasDerivAt_thetaCuspLogDecaySlope t
  have hz := (hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp t
    ((hasDerivAt_id t).add_const y)
  convert! ((hz.sub_const (p y)).div (hp.add hz) (sum_pos ht hy).ne') using 1
  dsimp
  ring

private theorem weight_left_deriv (t y : ℝ) :
    HasDerivAt (fun u => sourceProductWeight u y)
      (-(p t+p (t+y))*sourceProductWeight t y) t := by
  have hz := (s.hasDerivAt (t+y)).comp t ((hasDerivAt_id t).add_const y)
  convert! ((s.hasDerivAt t).mul hz).div_const (k 0*k y) using 1
  change -(p t+p (t+y))*(k t*k (t+y)/(k 0*k y)) =
    (k₁ t*k (t+y)+k t*(k₁ (t+y)*1))/(k 0*k y)
  rw [first_eq, first_eq]
  ring

/-- Raw Schwartz derivative equals the exact normalized source transport density. -/
theorem canonicalRawDerivative_eq_transport (t : ℝ) {y : ℝ} (hy : 0 < y) :
    canonicalRawDerivative t y =
      (deriv (canonicalMoment t) y-(p (t+y)-p y)*canonicalMoment t y)*
        sourceProductWeight t y := by
  rw [(moment_right_deriv t hy).deriv]
  unfold canonicalRawDerivative rawMomentDerivative canonicalRawMoment
    canonicalMoment sourceProductWeight
  rw [first_eq t, first_eq (t+y), first_eq y, second_eq (t+y)]
  field_simp [hy.ne', (thetaCuspFullSource_pos_all 0).ne', (thetaCuspFullSource_pos_all y).ne']
  ring

/-- Exact divergence identity on the actual source, including the speed derivative. -/
theorem canonicalFlux_hasDerivAt {t y : ℝ} (ht : 0 ≤ t) (hy : 0 < y) :
    HasDerivAt (fun s => canonicalFlux s y)
      (canonicalRawDerivative t y-canonicalCurrent t y*sourceProductWeight t y) t := by
  have he : (fun u => canonicalFlux u y) =
      fun u => canonicalSpeed u y*(canonicalMoment u y*sourceProductWeight u y) := by
    funext u
    exact congrArg (fun z => canonicalSpeed u y*z) (canonicalRawMoment_eq hy u)
  rw [he]
  have hC := (moment_left_deriv t y).differentiableAt.hasDerivAt
  have hSpeed := (speed_left_deriv ht hy).differentiableAt.hasDerivAt
  have hcancel : canonicalSpeed t y*(p t+p (t+y)) = p (t+y)-p y := by
    unfold canonicalSpeed
    field_simp [(sum_pos ht hy).ne']
  convert! hSpeed.mul (hC.mul (weight_left_deriv t y)) using 1
  rw [canonicalRawDerivative_eq_transport t hy, canonicalCurrent, ← hcancel]
  dsimp
  ring

private theorem rawDerivative_continuous (y : ℝ) :
    Continuous (fun t => canonicalRawDerivative t y) := by
  have h0 : Continuous k := s.continuous
  have h1 : Continuous k₁ := d.continuous
  have h2 : Continuous k₂ := dd.continuous
  unfold canonicalRawDerivative rawMomentDerivative canonicalRawMoment
  fun_prop

private def cumulativeTransport (y b : ℝ) : ℝ :=
  (∫ t in 0..b, canonicalRawDerivative t y)-canonicalFlux b y

private theorem cumulativeTransport_hasDerivAt {y b : ℝ} (hy : 0 < y) (hb : 0 ≤ b) :
    HasDerivAt (cumulativeTransport y) (canonicalCurrent b y*sourceProductWeight b y) b := by
  convert! (intervalIntegral.integral_hasDerivAt_right
    (canonicalRawDerivative_integrable y).intervalIntegrable
    ((rawDerivative_continuous y).stronglyMeasurableAtFilter volume (𝓝 b))
    (rawDerivative_continuous y).continuousAt).sub (canonicalFlux_hasDerivAt hb hy) using 1
  ring

private theorem cumulativeTransport_zero (y : ℝ) : cumulativeTransport y 0 = 0 := by
  simp only [cumulativeTransport, intervalIntegral.integral_same, canonicalFlux_zero, sub_self]

private theorem cumulativeTransport_strictAnti {y : ℝ} (hy : 0 < y) :
    StrictAntiOn (cumulativeTransport y) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro t ht; exact (cumulativeTransport_hasDerivAt hy ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [(cumulativeTransport_hasDerivAt hy ht0.le).deriv]
    exact mul_neg_of_neg_of_pos (canonicalCurrent_neg ht0 hy) (sourceProductWeight_pos t y)

/-- The actual normalized mixed-row derivative density has strictly negative integral. -/
theorem integral_canonicalRawDerivative_neg {y : ℝ} (hy : 0 < y) :
    (∫ t in Ioi 0, canonicalRawDerivative t y) < 0 := by
  have hl : Tendsto (cumulativeTransport y) atTop
      (𝓝 (∫ t in Ioi 0, canonicalRawDerivative t y)) := by
    have h := (intervalIntegral_tendsto_integral_Ioi 0
      (canonicalRawDerivative_integrable y).integrableOn tendsto_id).sub (canonicalFlux_limit hy)
    change Tendsto (fun b => (∫ t in 0..b, canonicalRawDerivative t y)-canonicalFlux b y)
      atTop (𝓝 (∫ t in Ioi 0, canonicalRawDerivative t y))
    simpa only [id_eq, sub_zero] using h
  have hneg : cumulativeTransport y 1 < 0 := by
    have h := cumulativeTransport_strictAnti hy (show (0:ℝ) ∈ Ici 0 by simp)
      (show (1:ℝ) ∈ Ici 0 by norm_num) (by norm_num : (0:ℝ) < 1)
    rwa [cumulativeTransport_zero] at h
  have hle : (∫ t in Ioi 0, canonicalRawDerivative t y) ≤ cumulativeTransport y 1 := by
    apply le_of_tendsto hl
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    exact (cumulativeTransport_strictAnti hy).antitoneOn (by norm_num)
      (show t ∈ Ici 0 by change 0 ≤ t; linarith) ht
  exact hle.trans_lt hneg

end RHTower.ThetaCoordinate
