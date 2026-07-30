import GaloisForLFunctions.RHTower.SuzukiCriticalTwoFlankGeometry

open Set MeasureTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-!
# Critical apex-vacuum capacity no-go

An explicit atomless source obeys the same sharp width-two cumulative capacity band as the
Mangoldt log-Haar transport, but its mass compression on the rising flank creates quadrature
excess proportional to the moving Suzuki apex.  The reflected-polar and Gamma reserve is uniformly
bounded, so capacity-band information—even with an untouched decreasing flank—cannot produce the
completed-lag inequality.
-/

def suzukiCriticalApexVacuumCumulative (c t : ℝ) : ℝ :=
  if t ≤ c - 2 then t
  else if t ≤ c - 1 / 4 then c - 2
  else if t ≤ c then c - 2 + 8 * (t - (c - 1 / 4))
  else t

theorem suzukiCriticalApexVacuumCumulative_monotone (c : ℝ) :
    Monotone (suzukiCriticalApexVacuumCumulative c) := by
  intro x y hxy
  simp only [suzukiCriticalApexVacuumCumulative]
  split_ifs <;> linarith

theorem suzukiCriticalApexVacuumCumulative_band
    {c t : ℝ} :
    t - 2 ≤ suzukiCriticalApexVacuumCumulative c t ∧
      suzukiCriticalApexVacuumCumulative c t ≤ t := by
  simp only [suzukiCriticalApexVacuumCumulative]
  split_ifs <;> constructor <;> linarith

/-- Atomless source obtained by evacuating `(c-2,c)` and placing its mass with density eight on
the final quarter-unit before `c`. -/
def suzukiCriticalApexVacuumMeasure (c : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 (c - 2)) +
      ((8 : ENNReal) • volume.restrict (Ioc (c - 1 / 4) c))) +
    volume.restrict (Ioi c)

instance suzukiCriticalApexVacuumMeasure_noAtoms (c : ℝ) :
    NullSingletonClass (suzukiCriticalApexVacuumMeasure c) := by
  refine ⟨fun x => ?_⟩
  simp [suzukiCriticalApexVacuumMeasure, Measure.add_apply, Measure.smul_apply]

theorem suzukiCriticalApexVacuumMeasure_Ioc
    {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t) :
    (suzukiCriticalApexVacuumMeasure c (Ioc 0 t)).toReal =
      suzukiCriticalApexVacuumCumulative c t := by
  have hc0 : 0 ≤ c := by linarith
  have hc2 : 0 ≤ c - 2 := by linarith
  have hc14 : 0 ≤ c - 1 / 4 := by linarith
  rw [suzukiCriticalApexVacuumMeasure, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
    Measure.restrict_apply measurableSet_Ioc,
    Measure.restrict_apply measurableSet_Ioc]
  simp only [Set.Ioc_inter_Ioc, Set.Ioc_inter_Ioi, Real.volume_Ioc,
    max_self, max_eq_right hc14, max_eq_right hc0, smul_eq_mul]
  simp only [suzukiCriticalApexVacuumCumulative]
  split_ifs with h1 h2 h3
  · have ht14 : t ≤ c - 1 / 4 := by linarith
    have htc : t ≤ c := by linarith
    rw [min_eq_left h1, min_eq_left htc]
    have hncluster : ENNReal.ofReal (t - (c - 1 / 4)) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    have hnright : ENNReal.ofReal (t - c) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    rw [hncluster, hnright]
    simp [ENNReal.toReal_ofReal ht]
  · have h2low : c - 2 ≤ t := by linarith
    have htc : t ≤ c := by linarith
    rw [min_eq_right h2low, min_eq_left htc]
    have hncluster : ENNReal.ofReal (t - (c - 1 / 4)) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    have hnright : ENNReal.ofReal (t - c) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    rw [hncluster, hnright]
    simp [ENNReal.toReal_ofReal hc2]
  · have h1low : c - 2 ≤ t := by linarith
    have h2low : c - 1 / 4 ≤ t := by linarith
    have hcluster0 : 0 ≤ t - (c - 1 / 4) := by linarith
    rw [min_eq_right h1low, min_eq_left h3]
    have hnright : ENNReal.ofReal (t - c) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    rw [hnright, ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
    simp [ENNReal.toReal_ofReal hc2]
    all_goals nlinarith
  · have h1low : c - 2 ≤ t := by linarith
    have h2low : c - 1 / 4 ≤ t := by linarith
    have hclow : c ≤ t := by linarith
    have hright0 : 0 ≤ t - c := by linarith
    have hquarter0 : 0 ≤ c - (c - 1 / 4) := by norm_num
    rw [min_eq_right h1low, min_eq_right hclow]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
    simp [ENNReal.toReal_ofReal hc2, ENNReal.toReal_ofReal hright0]
    ring

def suzukiCriticalApexVacuumQuadrature
    (Phi : ℝ → ℝ) (c : ℝ) : ℝ :=
  (∫ t : ℝ in Ioi 0, Phi t) - (∫ t : ℝ in (c - 2)..c, Phi t) +
    8 * ∫ t : ℝ in (c - 1 / 4)..c, Phi t

theorem suzukiCriticalApexVacuumQuadrature_sub_continuum
    (Phi : ℝ → ℝ) (c : ℝ) :
    suzukiCriticalApexVacuumQuadrature Phi c -
        (∫ t : ℝ in Ioi 0, Phi t) =
      8 * (∫ t : ℝ in (c - 1 / 4)..c, Phi t) -
        ∫ t : ℝ in (c - 2)..c, Phi t := by
  rw [suzukiCriticalApexVacuumQuadrature]
  ring

theorem integral_suzukiCriticalApexVacuumMeasure_eq_quadrature
    {Phi : ℝ → ℝ} (hPhi : Integrable Phi) {c : ℝ} (hc : 2 ≤ c) :
    (∫ t : ℝ, Phi t ∂suzukiCriticalApexVacuumMeasure c) =
      suzukiCriticalApexVacuumQuadrature Phi c := by
  have hleft : Integrable Phi (volume.restrict (Ioc 0 (c - 2))) := hPhi.restrict
  have hcluster0 : Integrable Phi (volume.restrict (Ioc (c - 1 / 4) c)) := hPhi.restrict
  have hcluster : Integrable Phi
      ((8 : ENNReal) • volume.restrict (Ioc (c - 1 / 4) c)) :=
    hcluster0.smul_measure (by norm_num)
  have hright : Integrable Phi (volume.restrict (Ioi c)) := hPhi.restrict
  have h0c2 : IntervalIntegrable Phi volume 0 (c - 2) := hPhi.intervalIntegrable
  have hc2c : IntervalIntegrable Phi volume (c - 2) c := hPhi.intervalIntegrable
  have h0c : IntervalIntegrable Phi volume 0 c := hPhi.intervalIntegrable
  have hIoi0 : IntegrableOn Phi (Ioi 0) := hPhi.integrableOn
  have hIoic : IntegrableOn Phi (Ioi c) := hPhi.integrableOn
  have hadj := intervalIntegral.integral_add_adjacent_intervals h0c2 hc2c
  have htail := intervalIntegral.integral_interval_add_Ioi hIoi0 hIoic
  rw [suzukiCriticalApexVacuumMeasure,
    MeasureTheory.integral_add_measure (hleft.add_measure hcluster) hright,
    MeasureTheory.integral_add_measure hleft hcluster,
    MeasureTheory.integral_smul_measure]
  norm_num only [ENNReal.toReal_ofNat, smul_eq_mul]
  change (∫ t : ℝ in Ioc 0 (c - 2), Phi t) +
      8 * (∫ t : ℝ in Ioc (c - 1 / 4) c, Phi t) +
        (∫ t : ℝ in Ioi c, Phi t) = _
  rw [← intervalIntegral.integral_of_le (by linarith : 0 ≤ c - 2),
    ← intervalIntegral.integral_of_le (by linarith : c - 1 / 4 ≤ c),
    suzukiCriticalApexVacuumQuadrature]
  linarith

private theorem criticalTiltedTent_left_one_integral_le :
    (∫ x : ℝ in (-1 : ℝ)..0, tiltedTentFullProfile (1 / 2) 2 x) ≤ 7 / 8 := by
  let Phi : ℝ → ℝ := tiltedTentFullProfile (1 / 2) 2
  have hPhi : Continuous Phi := by
    dsimp only [Phi]
    unfold tiltedTentFullProfile
    fun_prop
  have hleft : (∫ x : ℝ in (-1 : ℝ)..(-1 / 2), Phi x) ≤
      ∫ _x : ℝ in (-1 : ℝ)..(-1 / 2), (3 / 4 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
        (hPhi.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro x hx
    dsimp [Phi, tiltedTentFullProfile]
    rw [abs_of_nonpos (by linarith [hx.2])]
    have he : Real.exp ((1 / 2 : ℝ) * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [hx.2])
    have hlin0 : 0 ≤ 1 + x / 2 := by linarith [hx.1]
    have hlin : 1 + x / 2 ≤ 3 / 4 := by linarith [hx.2]
    calc
      Real.exp ((1 / 2 : ℝ) * x) * (1 - -x / 2) =
          Real.exp ((1 / 2 : ℝ) * x) * (1 + x / 2) := by ring
      _ ≤ 1 * (1 + x / 2) := mul_le_mul_of_nonneg_right he hlin0
      _ ≤ 3 / 4 := by linarith
  have hright : (∫ x : ℝ in (-1 / 2 : ℝ)..0, Phi x) ≤
      ∫ _x : ℝ in (-1 / 2 : ℝ)..0, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
        (hPhi.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro x hx
    dsimp [Phi, tiltedTentFullProfile]
    rw [abs_of_nonpos (by linarith [hx.2])]
    have he : Real.exp ((1 / 2 : ℝ) * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [hx.2])
    have hlin0 : 0 ≤ 1 + x / 2 := by linarith [hx.1]
    have hlin : 1 + x / 2 ≤ 1 := by linarith [hx.2]
    calc
      Real.exp ((1 / 2 : ℝ) * x) * (1 - -x / 2) =
          Real.exp ((1 / 2 : ℝ) * x) * (1 + x / 2) := by ring
      _ ≤ 1 * (1 + x / 2) := mul_le_mul_of_nonneg_right he hlin0
      _ ≤ 1 := by linarith
  rw [show (∫ x : ℝ in (-1 : ℝ)..0, Phi x) =
      (∫ x : ℝ in (-1 : ℝ)..(-1 / 2), Phi x) +
        ∫ x : ℝ in (-1 / 2 : ℝ)..0, Phi x by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (hPhi.intervalIntegrable _ _) (hPhi.intervalIntegrable _ _)]
  calc
    _ ≤ (∫ _x : ℝ in (-1 : ℝ)..(-1 / 2), (3 / 4 : ℝ)) +
        ∫ _x : ℝ in (-1 / 2 : ℝ)..0, (1 : ℝ) := add_le_add hleft hright
    _ = 7 / 8 := by norm_num

private theorem criticalTiltedTent_last_eighth_integral_ge :
    225 / 2048 ≤
      ∫ x : ℝ in (-1 / 8 : ℝ)..0, tiltedTentFullProfile (1 / 2) 2 x := by
  let Phi : ℝ → ℝ := tiltedTentFullProfile (1 / 2) 2
  have hPhi : Continuous Phi := by
    dsimp only [Phi]
    unfold tiltedTentFullProfile
    fun_prop
  have hmono : (∫ _x : ℝ in (-1 / 8 : ℝ)..0, (225 / 256 : ℝ)) ≤
      ∫ x : ℝ in (-1 / 8 : ℝ)..0, Phi x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
        (continuous_const.intervalIntegrable _ _) (hPhi.intervalIntegrable _ _)
    intro x hx
    dsimp [Phi, tiltedTentFullProfile]
    rw [abs_of_nonpos (by linarith [hx.2])]
    have hlin : (15 / 16 : ℝ) ≤ 1 + x / 2 := by linarith [hx.1]
    have hlin0 : 0 ≤ 1 + x / 2 := by linarith [hx.1]
    have hexp : 1 + x / 2 ≤ Real.exp ((1 / 2 : ℝ) * x) := by
      convert Real.add_one_le_exp ((1 / 2 : ℝ) * x) using 1
      all_goals ring
    calc
      (225 / 256 : ℝ) = (15 / 16 : ℝ) ^ 2 := by norm_num
      _ ≤ (1 + x / 2) ^ 2 := by nlinarith
      _ ≤ Real.exp ((1 / 2 : ℝ) * x) * (1 + x / 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hexp hlin0]
      _ = Real.exp ((1 / 2 : ℝ) * x) * (1 - -x / 2) := by ring
  convert hmono using 1
  all_goals norm_num

private theorem integrable_suzukiCriticalPositiveArchChannel (a : ℝ) :
    Integrable (suzukiRectangularPositiveArchSampleChannel 2 a) := by
  let H : ℝ → ℂ := rectangularPolarHalfAutocorrelation 2 a
  have hH : Integrable H := integrable_rectangularPolarHalfAutocorrelation 2 a
  have hcomp : Integrable (fun t : ℝ => H (t / 2)) :=
    hH.comp_div (by norm_num : (2 : ℝ) ≠ 0)
  apply hcomp.re.congr
  filter_upwards with t
  dsimp [H]
  rw [suzukiRectangularPositiveArchSampleChannel,
    rectangularPolarHalfAutocorrelation]
  rw [show Complex.exp ((((t / 2 : ℝ) : ℂ)) / 2) =
      (Real.exp (t / 4) : ℂ) by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

private theorem suzukiCriticalApexVacuum_gap_integral
    {a : ℝ} (ha : 3 ≤ a) :
    (∫ t : ℝ in (suzukiCriticalMovingApexLag a - 2)..
        suzukiCriticalMovingApexLag a,
        suzukiRectangularPositiveArchSampleChannel 2 a t) =
      2 * suzukiCriticalMovingApexHeight a *
        ∫ x : ℝ in (-1 : ℝ)..0, tiltedTentFullProfile (1 / 2) 2 x := by
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (suzukiRectangularPositiveArchSampleChannel 2 a) (a := (-1 : ℝ)) (b := 0)
      2 (suzukiCriticalMovingApexLag a)
  have hinside : (∫ x : ℝ in (-1 : ℝ)..0,
      suzukiRectangularPositiveArchSampleChannel 2 a
        (suzukiCriticalMovingApexLag a + 2 * x)) =
      ∫ x : ℝ in (-1 : ℝ)..0,
        suzukiCriticalMovingApexHeight a * tiltedTentFullProfile (1 / 2) 2 x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    exact suzukiCriticalPositiveArchChannel_eq_apex_mul_tiltedTent ha
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hinside, intervalIntegral.integral_const_mul] at hchange
  norm_num [smul_eq_mul] at hchange ⊢
  convert hchange.symm using 1
  all_goals ring

private theorem suzukiCriticalApexVacuum_cluster_integral
    {a : ℝ} (ha : 3 ≤ a) :
    (∫ t : ℝ in (suzukiCriticalMovingApexLag a - 1 / 4)..
        suzukiCriticalMovingApexLag a,
        suzukiRectangularPositiveArchSampleChannel 2 a t) =
      2 * suzukiCriticalMovingApexHeight a *
        ∫ x : ℝ in (-1 / 8 : ℝ)..0, tiltedTentFullProfile (1 / 2) 2 x := by
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (suzukiRectangularPositiveArchSampleChannel 2 a) (a := (-1 / 8 : ℝ)) (b := 0)
      2 (suzukiCriticalMovingApexLag a)
  have hinside : (∫ x : ℝ in (-1 / 8 : ℝ)..0,
      suzukiRectangularPositiveArchSampleChannel 2 a
        (suzukiCriticalMovingApexLag a + 2 * x)) =
      ∫ x : ℝ in (-1 / 8 : ℝ)..0,
        suzukiCriticalMovingApexHeight a * tiltedTentFullProfile (1 / 2) 2 x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 / 8 : ℝ) ≤ 0)] at hx
    exact suzukiCriticalPositiveArchChannel_eq_apex_mul_tiltedTent ha
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hinside, intervalIntegral.integral_const_mul] at hchange
  norm_num [smul_eq_mul] at hchange ⊢
  convert hchange.symm using 1
  all_goals ring

theorem suzukiCriticalApexVacuumQuadrature_excess_ge
    {a : ℝ} (ha : 3 ≤ a) :
    suzukiCriticalMovingApexHeight a / 128 ≤
      suzukiCriticalApexVacuumQuadrature
          (suzukiRectangularPositiveArchSampleChannel 2 a)
          (suzukiCriticalMovingApexLag a) -
        ∫ t : ℝ in Ioi 0, suzukiRectangularPositiveArchSampleChannel 2 a t := by
  rw [suzukiCriticalApexVacuumQuadrature_sub_continuum,
    suzukiCriticalApexVacuum_gap_integral ha,
    suzukiCriticalApexVacuum_cluster_integral ha]
  have hH : 0 < suzukiCriticalMovingApexHeight a := by
    rw [suzukiCriticalMovingApexHeight]
    positivity
  have hgap := mul_le_mul_of_nonneg_left criticalTiltedTent_left_one_integral_le hH.le
  have hcluster := mul_le_mul_of_nonneg_left criticalTiltedTent_last_eighth_integral_ge hH.le
  nlinarith

def suzukiCriticalReflectedArchChannel (a t : ℝ) : ℝ :=
  Real.exp (-t / 4) * rectangularTwoEdgeAutocorrelation 2 a (t / 2)

private theorem integrable_suzukiCriticalReflectedArchChannel (a : ℝ) :
    Integrable (suzukiCriticalReflectedArchChannel a) := by
  let H : ℝ → ℂ := rectangularPolarHalfAutocorrelation 2 a
  have hH : Integrable H := integrable_rectangularPolarHalfAutocorrelation 2 a
  have hcomp : Integrable (fun t : ℝ => H (-(t / 2))) := by
    convert hH.comp_mul_left' (by norm_num : (-1 / 2 : ℝ) ≠ 0) using 1
    funext t
    congr 1
    ring
  apply hcomp.re.congr
  filter_upwards with t
  dsimp [H]
  rw [suzukiCriticalReflectedArchChannel,
    rectangularPolarHalfAutocorrelation, rectangularTwoEdgeAutocorrelation_neg]
  rw [show Complex.exp (((-(t / 2) : ℝ) : ℂ) / 2) =
      (Real.exp (-t / 4) : ℂ) by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem integral_suzukiCriticalReflectedArchChannel_le_sixteen
    {a : ℝ} (ha : 2 ≤ a) :
    (∫ t : ℝ in Ioi 0, suzukiCriticalReflectedArchChannel a t) ≤ 16 := by
  have href : IntegrableOn (suzukiCriticalReflectedArchChannel a) (Ioi 0) :=
    (integrable_suzukiCriticalReflectedArchChannel a).integrableOn
  have hmaj : IntegrableOn (fun t : ℝ => 4 * Real.exp ((-1 / 4 : ℝ) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 4 : ℝ) < 0) 0).const_mul 4
  have hle : ∀ t : ℝ, t ∈ Ioi 0 →
      suzukiCriticalReflectedArchChannel a t ≤ 4 * Real.exp ((-1 / 4 : ℝ) * t) := by
    intro t ht
    change 0 < t at ht
    rw [suzukiCriticalReflectedArchChannel]
    have hC := rectangularTwoEdgeAutocorrelation_le_zeroLag
      (L := (2 : ℝ)) (a := a) (h := t / 2) (by norm_num) ha (by linarith)
    rw [rectangularTwoEdgeAutocorrelation_zero (by norm_num) ha] at hC
    norm_num at hC
    have he : 0 ≤ Real.exp (-t / 4) := (Real.exp_pos _).le
    calc
      Real.exp (-t / 4) * rectangularTwoEdgeAutocorrelation 2 a (t / 2) ≤
          Real.exp (-t / 4) * 4 := mul_le_mul_of_nonneg_left hC he
      _ = 4 * Real.exp ((-1 / 4 : ℝ) * t) := by
        rw [show -t / 4 = (-1 / 4 : ℝ) * t by ring]
        ring
  have hae : suzukiCriticalReflectedArchChannel a ≤ᵐ[volume.restrict (Ioi 0)]
      fun t : ℝ => 4 * Real.exp ((-1 / 4 : ℝ) * t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hle t ht
  have hint := MeasureTheory.integral_mono_ae href hmaj hae
  rw [MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (by norm_num : (-1 / 4 : ℝ) < 0) 0] at hint
  norm_num at hint ⊢
  exact hint

def suzukiCriticalCompletedReserve (a : ℝ) : ℝ :=
  (∫ t : ℝ in Ioi 0, suzukiCriticalReflectedArchChannel a t) +
    rectangularGammaPolarCorrection 2 a

def suzukiCriticalCompletedReserveBound : ℝ :=
  16 + rectangularGammaPolarUniformBound 2

theorem suzukiCriticalCompletedReserve_le
    {a : ℝ} (ha : 3 ≤ a) :
    suzukiCriticalCompletedReserve a ≤ suzukiCriticalCompletedReserveBound := by
  have href := integral_suzukiCriticalReflectedArchChannel_le_sixteen (by linarith : 2 ≤ a)
  have hgamma := abs_rectangularGammaPolarCorrection_le_uniformBound
    (L := (2 : ℝ)) (a := a) (by norm_num) (by linarith)
  rw [suzukiCriticalCompletedReserve, suzukiCriticalCompletedReserveBound]
  nlinarith [le_abs_self (rectangularGammaPolarCorrection 2 a)]

private theorem suzukiCriticalCompletedLagMass_eq_sample_add_charge_add_reserve
    {a : ℝ} (ha : 3 ≤ a) :
    (∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel 2 a t) =
      (∫ t : ℝ in Ioi 0, suzukiRectangularPositiveArchSampleChannel 2 a t) +
        (Real.eulerMascheroniConstant + Real.log Real.pi) * 4 +
          suzukiCriticalCompletedReserve a := by
  have hA : IntegrableOn (suzukiRectangularPositiveArchSampleChannel 2 a) (Ioi 0) :=
    (integrable_suzukiCriticalPositiveArchChannel a).integrableOn
  have hR : IntegrableOn (suzukiCriticalReflectedArchChannel a) (Ioi 0) :=
    (integrable_suzukiCriticalReflectedArchChannel a).integrableOn
  have hG := integrableOn_rectangularGammaCancellationKernel (L := (2 : ℝ))
    (a := a) (by norm_num) (by linarith)
  have hfun : (fun t : ℝ => suzukiRectangularCompletedArchLagKernel 2 a t) =
      fun t : ℝ => suzukiRectangularPositiveArchSampleChannel 2 a t +
        suzukiCriticalReflectedArchChannel a t +
          rectangularGammaCancellationKernel 2 a t := by
    funext t
    rw [suzukiRectangularCompletedArchLagKernel, suzukiRectangularPolarLagKernel,
      suzukiRectangularPositiveArchSampleChannel, suzukiCriticalReflectedArchChannel,
      Real.cosh_eq]
    ring
  rw [hfun]
  have hadd1 : (∫ t : ℝ in Ioi 0,
      (suzukiRectangularPositiveArchSampleChannel 2 a t +
        suzukiCriticalReflectedArchChannel a t) +
          rectangularGammaCancellationKernel 2 a t) =
      (∫ t : ℝ in Ioi 0,
        suzukiRectangularPositiveArchSampleChannel 2 a t +
          suzukiCriticalReflectedArchChannel a t) +
        ∫ t : ℝ in Ioi 0, rectangularGammaCancellationKernel 2 a t := by
    exact MeasureTheory.integral_add (hA.add hR) hG
  have hadd2 : (∫ t : ℝ in Ioi 0,
      suzukiRectangularPositiveArchSampleChannel 2 a t +
        suzukiCriticalReflectedArchChannel a t) =
      (∫ t : ℝ in Ioi 0, suzukiRectangularPositiveArchSampleChannel 2 a t) +
        ∫ t : ℝ in Ioi 0, suzukiCriticalReflectedArchChannel a t := by
    exact MeasureTheory.integral_add hA hR
  rw [hadd1, hadd2, suzukiCriticalCompletedReserve,
    rectangularGammaPolarCorrection]
  ring

theorem exists_suzukiCriticalApexVacuum_completedLag_violation :
    ∃ a : ℝ, 3 ≤ a ∧
      (∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel 2 a t) <
        suzukiCriticalApexVacuumQuadrature
            (suzukiRectangularPositiveArchSampleChannel 2 a)
            (suzukiCriticalMovingApexLag a) +
          (Real.eulerMascheroniConstant + Real.log Real.pi) * 4 := by
  let B := suzukiCriticalCompletedReserveBound
  let a := 64 * B + 3
  have hB : 0 ≤ B := by
    dsimp [B, suzukiCriticalCompletedReserveBound]
    have hgamma := rectangularGammaPolarUniformBound_nonneg (L := (2 : ℝ)) (by norm_num)
    linarith
  have ha : 3 ≤ a := by dsimp [a]; nlinarith
  have hheight : B < suzukiCriticalMovingApexHeight a / 128 := by
    rw [suzukiCriticalMovingApexHeight]
    have hexp := Real.add_one_le_exp (a - 1)
    dsimp [a]
    nlinarith
  have hexcess := suzukiCriticalApexVacuumQuadrature_excess_ge ha
  have hreserve := suzukiCriticalCompletedReserve_le ha
  have hmass := suzukiCriticalCompletedLagMass_eq_sample_add_charge_add_reserve ha
  refine ⟨a, ha, ?_⟩
  rw [hmass]
  nlinarith

/-- **Capacity-only Suzuki no-go.**  An explicit atomless source satisfies the sharp width-two
cumulative band at every positive lag, agrees with capacity one outside one rising-flank gap, yet
violates completed-lag domination at a cofinal critical apex. -/
theorem exists_atomless_capacityBand_suzukiCompletedLag_violation :
    ∃ a : ℝ, 3 ≤ a ∧
      (∀ t : ℝ, 0 ≤ t →
        t - 2 ≤ (suzukiCriticalApexVacuumMeasure
          (suzukiCriticalMovingApexLag a) (Ioc 0 t)).toReal ∧
        (suzukiCriticalApexVacuumMeasure
          (suzukiCriticalMovingApexLag a) (Ioc 0 t)).toReal ≤ t) ∧
      (∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel 2 a t) <
        (∫ t : ℝ, suzukiRectangularPositiveArchSampleChannel 2 a t
          ∂suzukiCriticalApexVacuumMeasure (suzukiCriticalMovingApexLag a)) +
          (Real.eulerMascheroniConstant + Real.log Real.pi) * 4 := by
  rcases exists_suzukiCriticalApexVacuum_completedLag_violation with ⟨a, ha, hviol⟩
  have hc : 2 ≤ suzukiCriticalMovingApexLag a := by
    rw [suzukiCriticalMovingApexLag]
    linarith
  have hquad := integral_suzukiCriticalApexVacuumMeasure_eq_quadrature
    (integrable_suzukiCriticalPositiveArchChannel a) hc
  refine ⟨a, ha, ?_, ?_⟩
  · intro t ht
    rw [suzukiCriticalApexVacuumMeasure_Ioc hc ht]
    exact suzukiCriticalApexVacuumCumulative_band
  · rw [hquad]
    exact hviol

end RHTower
