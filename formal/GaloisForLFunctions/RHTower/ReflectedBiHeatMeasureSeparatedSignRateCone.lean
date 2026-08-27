import GaloisForLFunctions.RHTower.ReflectedBiHeatCountableSeparatedSignRateCone

/-!
# Reflected bi-heat measure-separated sign rate cone

The separated-sign RBH classification survives from finite and countable packets
to arbitrary nonzero finite positive Borel measures on rate space. Pointwise
separation `0 < r < kappa` almost everywhere on the negative packet and
`kappa ≤ r` on the positive packet is enough: no uniform low-rate gap and no
atomicity are required.

Finite low mass and all positive high hyperbolic moments give the exact cone:
the continuum reporter has only its forced wall zero iff its first wall moment
is nonnegative. The proof uses dominated Bochner integrals at both wall and
infinity, strict positive-measure separator comparison, and local uniform
convergence. Continuum real-power aperture factorization yields RH receivers.

`[NEW] [CONTINUUM INCOMMENSURATE] [EXACT SIGN CONE] [LEAN-PROVED]`
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

def reflectedBiHeatMeasureSeparatedSignReporter
    (P Q : Measure ℝ) (t : ℝ) : ℝ :=
  -(∫ r, Real.sinh (r * t) ∂P) + ∫ r, Real.sinh (r * t) ∂Q

def reflectedBiHeatMeasureSeparatedSignWallDerivative
    (P Q : Measure ℝ) : ℝ :=
  (∫ r, r ∂Q) - ∫ r, r ∂P

theorem integrable_reflectedBiHeatMeasureLowTerm
    (P : Measure ℝ) [IsFiniteMeasure P] {kappa t : ℝ}
    (ht : 0 < t) (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa) :
    Integrable (fun r => Real.sinh (r * t)) P := by
  refine (integrable_const (Real.sinh (kappa * t))).mono'
    (by fun_prop) ?_
  filter_upwards [hP] with r hr
  rw [Real.norm_eq_abs, abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos hr.1 ht))]
  exact Real.sinh_le_sinh.mpr
    (mul_le_mul_of_nonneg_right hr.2.le ht.le)

theorem integrable_reflectedBiHeatMeasureLowMoment
    (P : Measure ℝ) [IsFiniteMeasure P] {kappa : ℝ}
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa) :
    Integrable (fun r : ℝ => r) P := by
  refine (integrable_const kappa).mono' (by fun_prop) ?_
  filter_upwards [hP] with r hr
  rw [Real.norm_eq_abs, abs_of_pos hr.1]
  exact hr.2.le

theorem integrable_reflectedBiHeatMeasureHighMoment
    (Q : Measure ℝ) {kappa : ℝ}
    (hkappa : 0 < kappa) (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q) :
    Integrable (fun r : ℝ => r) Q := by
  refine (hhigh 1 one_pos).mono' (by fun_prop) ?_
  filter_upwards [hQ] with r hr
  have hrpos : 0 < r := hkappa.trans_le hr
  rw [Real.norm_eq_abs, abs_of_pos hrpos]
  simpa using (self_lt_sinh hrpos).le

theorem tendsto_reflectedBiHeatMeasureLowIntegral_div_self_nhdsGT_zero
    (P : Measure ℝ) [IsFiniteMeasure P] {kappa : ℝ}
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa) :
    Tendsto
      (fun t : ℝ => ∫ r, Real.sinh (r * t) / t ∂P)
      (𝓝[>] 0) (𝓝 (∫ r, r ∂P)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => Real.sinh kappa) ?_ ?_ (integrable_const _) ?_
  · filter_upwards with t
    fun_prop
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds one_pos)] with t ht ht1
    filter_upwards [hP] with r hr
    have hterm : 0 ≤ Real.sinh (r * t) / t :=
      div_nonneg (Real.sinh_pos_iff.mpr (mul_pos hr.1 ht)).le ht.le
    rw [Real.norm_eq_abs, abs_of_nonneg hterm]
    exact (sinh_rate_mul_div_self_le_sinh_rate hr.1 ht ht1.le).trans
      (Real.sinh_le_sinh.mpr hr.2.le)
  · filter_upwards [hP] with r hr
    exact tendsto_sinh_rate_mul_div_self_nhdsGT_zero hr.1

theorem tendsto_reflectedBiHeatMeasureHighIntegral_div_self_nhdsGT_zero
    (Q : Measure ℝ) {kappa : ℝ}
    (hkappa : 0 < kappa) (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q) :
    Tendsto
      (fun t : ℝ => ∫ r, Real.sinh (r * t) / t ∂Q)
      (𝓝[>] 0) (𝓝 (∫ r, r ∂Q)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun r => Real.sinh r) ?_ ?_ (by simpa using hhigh 1 one_pos) ?_
  · filter_upwards with t
    fun_prop
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds one_pos)] with t ht ht1
    filter_upwards [hQ] with r hr
    have hrpos : 0 < r := hkappa.trans_le hr
    have hterm : 0 ≤ Real.sinh (r * t) / t :=
      div_nonneg (Real.sinh_pos_iff.mpr (mul_pos hrpos ht)).le ht.le
    rw [Real.norm_eq_abs, abs_of_nonneg hterm]
    exact sinh_rate_mul_div_self_le_sinh_rate hrpos ht ht1.le
  · filter_upwards [hQ] with r hr
    exact tendsto_sinh_rate_mul_div_self_nhdsGT_zero (hkappa.trans_le hr)

theorem tendsto_reflectedBiHeatMeasureSeparatedSignReporter_div_self_nhdsGT_zero
    (P Q : Measure ℝ) [IsFiniteMeasure P] {kappa : ℝ}
    (hkappa : 0 < kappa)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q) :
    Tendsto
      (fun t : ℝ => reflectedBiHeatMeasureSeparatedSignReporter P Q t / t)
      (𝓝[>] 0) (𝓝 (reflectedBiHeatMeasureSeparatedSignWallDerivative P Q)) := by
  have hlow := tendsto_reflectedBiHeatMeasureLowIntegral_div_self_nhdsGT_zero P hP
  have hhi := tendsto_reflectedBiHeatMeasureHighIntegral_div_self_nhdsGT_zero
    Q hkappa hQ hhigh
  have hlim := hlow.neg.add hhi
  have heq :
      (fun t : ℝ => -(∫ r, Real.sinh (r * t) / t ∂P) +
        ∫ r, Real.sinh (r * t) / t ∂Q) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => reflectedBiHeatMeasureSeparatedSignReporter P Q t / t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [reflectedBiHeatMeasureSeparatedSignReporter]
    have hlowDiv : (∫ r, Real.sinh (r * t) ∂P) / t =
        ∫ r, Real.sinh (r * t) / t ∂P := by
      rw [div_eq_mul_inv, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with r
      ring
    have hhighDiv : (∫ r, Real.sinh (r * t) ∂Q) / t =
        ∫ r, Real.sinh (r * t) / t ∂Q := by
      rw [div_eq_mul_inv, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with r
      ring
    rw [add_div, neg_div, hlowDiv, hhighDiv]
  have hlim' := hlim.congr' heq
  rw [reflectedBiHeatMeasureSeparatedSignWallDerivative]
  simpa only [sub_eq_add_neg, add_comm] using hlim'

theorem reflectedBiHeatMeasureSeparatedSignReporter_pos
    (P Q : Measure ℝ) [IsFiniteMeasure P] {kappa t : ℝ}
    (hkappa : 0 < kappa) (ht : 0 < t) (hPne : P ≠ 0)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q)
    (hderiv : 0 ≤ reflectedBiHeatMeasureSeparatedSignWallDerivative P Q) :
    0 < reflectedBiHeatMeasureSeparatedSignReporter P Q t := by
  let G : ℝ := Real.sinh (kappa * t) / (kappa * t)
  have hkt : 0 < kappa * t := mul_pos hkappa ht
  have hG : 0 < G := div_pos (Real.sinh_pos_iff.mpr hkt) hkt
  have hlowInt := integrable_reflectedBiHeatMeasureLowTerm P ht hP
  have hlowMoment := integrable_reflectedBiHeatMeasureLowMoment P hP
  have hhighMoment := integrable_reflectedBiHeatMeasureHighMoment Q hkappa hQ hhigh
  have hhighInt := hhigh t ht
  have hlowScaledInt : Integrable (fun r : ℝ => r * t * G) P :=
    (hlowMoment.mul_const t).mul_const G
  have hhighScaledInt : Integrable (fun r : ℝ => r * t * G) Q :=
    (hhighMoment.mul_const t).mul_const G
  let gap : ℝ → ℝ := fun r => r * t * G - Real.sinh (r * t)
  have hgapInt : Integrable gap P := hlowScaledInt.sub hlowInt
  have hgapPos : ∀ᵐ r ∂P, 0 < gap r := by
    filter_upwards [hP] with r hr
    have hrt : 0 < r * t := mul_pos hr.1 ht
    have hmono := GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
      (show r * t ∈ Ioi 0 from hrt)
      (show kappa * t ∈ Ioi 0 from hkt)
      (mul_lt_mul_of_pos_right hr.2 ht)
    dsimp only [gap, G]
    have heq : Real.sinh (r * t) =
        r * t * (Real.sinh (r * t) / (r * t)) := by
      field_simp [hr.1.ne', ht.ne']
    rw [heq]
    exact sub_pos.mpr (mul_lt_mul_of_pos_left hmono hrt)
  have hgapNonneg : 0 ≤ᵐ[P] gap := hgapPos.mono fun _ h => h.le
  have hsupport : P Set.univ ≤ P (Function.support gap) := by
    apply measure_mono_ae
    filter_upwards [hgapPos] with r hr
    intro _
    exact hr.ne'
  have hgapIntegralPos : 0 < ∫ r, gap r ∂P := by
    rw [integral_pos_iff_support_of_nonneg_ae hgapNonneg hgapInt]
    exact (Measure.measure_univ_pos.mpr hPne).trans_le hsupport
  have hlowStrict : (∫ r, Real.sinh (r * t) ∂P) <
      ∫ r, r * t * G ∂P := by
    have hgapEq : (∫ r, gap r ∂P) =
        (∫ r, r * t * G ∂P) - ∫ r, Real.sinh (r * t) ∂P := by
      exact integral_sub hlowScaledInt hlowInt
    rw [hgapEq] at hgapIntegralPos
    linarith
  have hhighLe : (∫ r, r * t * G ∂Q) ≤
      ∫ r, Real.sinh (r * t) ∂Q := by
    apply integral_mono_ae hhighScaledInt hhighInt
    filter_upwards [hQ] with r hr
    have hrpos : 0 < r := hkappa.trans_le hr
    have hrt : 0 < r * t := mul_pos hrpos ht
    have hmono : G ≤ Real.sinh (r * t) / (r * t) := by
      rcases eq_or_lt_of_le hr with heq | hlt
      · simp [G, heq]
      · exact (GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
          (show kappa * t ∈ Ioi 0 from hkt)
          (show r * t ∈ Ioi 0 from hrt)
          (mul_lt_mul_of_pos_right hlt ht)).le
    have heq : Real.sinh (r * t) =
        r * t * (Real.sinh (r * t) / (r * t)) := by
      field_simp [hrpos.ne', ht.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmono hrt.le
  have hcommon : (∫ r, r * t * G ∂P) ≤ ∫ r, r * t * G ∂Q := by
    have hsum : (∫ r, r ∂P) ≤ ∫ r, r ∂Q := by
      simpa [reflectedBiHeatMeasureSeparatedSignWallDerivative] using hderiv
    have hmul := mul_le_mul_of_nonneg_right hsum (mul_nonneg ht.le hG.le)
    simpa only [integral_mul_const, mul_assoc] using hmul
  rw [reflectedBiHeatMeasureSeparatedSignReporter]
  linarith

theorem reflectedBiHeatMeasureSeparatedSignWallOriented_iff
    (P Q : Measure ℝ) [IsFiniteMeasure P] {kappa : ℝ}
    (hkappa : 0 < kappa) (hPne : P ≠ 0)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q) :
    0 ≤ reflectedBiHeatMeasureSeparatedSignWallDerivative P Q ↔
      ∀ t : ℝ, 0 < t →
        0 < reflectedBiHeatMeasureSeparatedSignReporter P Q t := by
  constructor
  · intro hderiv t ht
    exact reflectedBiHeatMeasureSeparatedSignReporter_pos
      P Q hkappa ht hPne hP hQ hhigh hderiv
  · intro horiented
    by_contra hnot
    have hderiv : reflectedBiHeatMeasureSeparatedSignWallDerivative P Q < 0 :=
      lt_of_not_ge hnot
    have hlim :=
      tendsto_reflectedBiHeatMeasureSeparatedSignReporter_div_self_nhdsGT_zero
        P Q hkappa hP hQ hhigh
    have hevNeg : ∀ᶠ t in 𝓝[>] 0,
        reflectedBiHeatMeasureSeparatedSignReporter P Q t / t < 0 :=
      (tendsto_order.mp hlim).2 0 hderiv
    have hevPos : ∀ᶠ t in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    rcases (hevPos.and hevNeg).exists with ⟨t, ht, hneg⟩
    have hvalue : reflectedBiHeatMeasureSeparatedSignReporter P Q t < 0 := by
      have := (div_lt_iff₀ (show 0 < t from ht)).mp hneg
      simpa using this
    exact (not_lt_of_ge (horiented t ht).le) hvalue

theorem reflectedBiHeatMeasureSeparatedSignReporter_neg
    (P Q : Measure ℝ) (t : ℝ) :
    reflectedBiHeatMeasureSeparatedSignReporter P Q (-t) =
      -reflectedBiHeatMeasureSeparatedSignReporter P Q t := by
  simp only [reflectedBiHeatMeasureSeparatedSignReporter]
  simp_rw [show ∀ r : ℝ, r * -t = -(r * t) by intro r; ring,
    Real.sinh_neg]
  rw [integral_neg, integral_neg]
  ring

theorem tendsto_reflectedBiHeatMeasureLowRateIntegral_div_sinh_atTop
    (P : Measure ℝ) [IsFiniteMeasure P] {kappa : ℝ}
    (hkappa : 0 < kappa) (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa) :
    Tendsto
      (fun t : ℝ =>
        (∫ r, Real.sinh (r * t) ∂P) / Real.sinh (kappa * t))
      atTop (𝓝 0) := by
  have hmain : Tendsto
      (fun t : ℝ => ∫ r, Real.sinh (r * t) / Real.sinh (kappa * t) ∂P)
      atTop (𝓝 (∫ _r : ℝ, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => (1 : ℝ)) ?_ ?_ (integrable_const 1) ?_
    · filter_upwards with t
      fun_prop
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      filter_upwards [hP] with r hr
      have hnum : 0 ≤ Real.sinh (r * t) :=
        (Real.sinh_pos_iff.mpr (mul_pos hr.1 ht)).le
      have hden : 0 < Real.sinh (kappa * t) :=
        Real.sinh_pos_iff.mpr (mul_pos hkappa ht)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden.le),
        div_le_one hden]
      exact Real.sinh_le_sinh.mpr
        (mul_le_mul_of_nonneg_right hr.2.le ht.le)
    · filter_upwards [hP] with r hr
      have htop := tendsto_sinh_rate_ratio_atTop hr.1 hr.2
      have hinv : Tendsto
          (fun t : ℝ => 1 /
            (Real.sinh (kappa * t) / Real.sinh (r * t)))
          atTop (𝓝 0) := htop.const_div_atTop 1
      apply hinv.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hsr : Real.sinh (r * t) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos hr.1 ht)).ne'
      have hsk : Real.sinh (kappa * t) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos hkappa ht)).ne'
      field_simp
  have heq :
      (fun t : ℝ => ∫ r, Real.sinh (r * t) / Real.sinh (kappa * t) ∂P) =
      (fun t : ℝ =>
        (∫ r, Real.sinh (r * t) ∂P) / Real.sinh (kappa * t)) := by
    funext t
    rw [div_eq_mul_inv, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with r
    ring
  simpa [heq] using hmain

theorem continuousOn_reflectedBiHeatMeasureSeparatedSignReporter_Icc
    (P Q : Measure ℝ) [IsFiniteMeasure P] {kappa b : ℝ}
    (hkappa : 0 < kappa) (hb : 0 < b)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q) :
    ContinuousOn (reflectedBiHeatMeasureSeparatedSignReporter P Q) (Icc 0 b) := by
  have hlowCont : ContinuousOn
      (fun t : ℝ => ∫ r, Real.sinh (r * t) ∂P) (Icc 0 b) := by
    intro x hx
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => Real.sinh (kappa * b)) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      fun_prop
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hP] with r hr
      have hterm : 0 ≤ Real.sinh (r * t) :=
        Real.sinh_nonneg_iff.mpr (mul_nonneg hr.1.le ht.1)
      rw [Real.norm_eq_abs, abs_of_nonneg hterm]
      rw [Real.sinh_le_sinh]
      calc
        r * t ≤ kappa * t := mul_le_mul_of_nonneg_right hr.2.le ht.1
        _ ≤ kappa * b := mul_le_mul_of_nonneg_left ht.2 hkappa.le
    · filter_upwards with r
      have hc : Continuous (fun t : ℝ => Real.sinh (r * t)) := by fun_prop
      exact (hc.tendsto x).mono_left nhdsWithin_le_nhds
  have hhighCont : ContinuousOn
      (fun t : ℝ => ∫ r, Real.sinh (r * t) ∂Q) (Icc 0 b) := by
    intro x hx
    refine tendsto_integral_filter_of_dominated_convergence
      (fun r => Real.sinh (r * b)) ?_ ?_ (hhigh b hb) ?_
    · filter_upwards with t
      fun_prop
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hQ] with r hr
      have hrpos : 0 < r := hkappa.trans_le hr
      have hterm : 0 ≤ Real.sinh (r * t) :=
        Real.sinh_nonneg_iff.mpr (mul_nonneg hrpos.le ht.1)
      rw [Real.norm_eq_abs, abs_of_nonneg hterm]
      exact Real.sinh_le_sinh.mpr
        (mul_le_mul_of_nonneg_left ht.2 hrpos.le)
    · filter_upwards with r
      have hc : Continuous (fun t : ℝ => Real.sinh (r * t)) := by fun_prop
      exact (hc.tendsto x).mono_left nhdsWithin_le_nhds
  change ContinuousOn
    (fun t : ℝ => -(∫ r, Real.sinh (r * t) ∂P) +
      ∫ r, Real.sinh (r * t) ∂Q) (Icc 0 b)
  exact hlowCont.neg.add hhighCont

theorem exists_pos_reflectedBiHeatMeasureSeparatedSignReporter_eq_zero_of_derivative_neg
    (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] {kappa : ℝ}
    (hkappa : 0 < kappa) (hQne : Q ≠ 0)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q)
    (hderiv : reflectedBiHeatMeasureSeparatedSignWallDerivative P Q < 0) :
    ∃ t : ℝ, 0 < t ∧ reflectedBiHeatMeasureSeparatedSignReporter P Q t = 0 := by
  have hzeroLim :=
    tendsto_reflectedBiHeatMeasureSeparatedSignReporter_div_self_nhdsGT_zero
      P Q hkappa hP hQ hhigh
  have hevNeg : ∀ᶠ t in 𝓝[>] 0,
      reflectedBiHeatMeasureSeparatedSignReporter P Q t / t < 0 :=
    (tendsto_order.mp hzeroLim).2 0 hderiv
  obtain ⟨t0, ht0, hneg0⟩ : ∃ t0 : ℝ, 0 < t0 ∧
      reflectedBiHeatMeasureSeparatedSignReporter P Q t0 < 0 := by
    have hevPos : ∀ᶠ t in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    rcases (hevPos.and hevNeg).exists with ⟨t, ht, hnorm⟩
    have hvalue : reflectedBiHeatMeasureSeparatedSignReporter P Q t < 0 := by
      have := (div_lt_iff₀ (show 0 < t from ht)).mp hnorm
      simpa using this
    exact ⟨t, ht, hvalue⟩
  let mass : ℝ := (Q Set.univ).toReal
  have hmass : 0 < mass := by
    apply ENNReal.toReal_pos
    · exact Measure.measure_univ_ne_zero.mpr hQne
    · exact ne_of_lt IsFiniteMeasure.measure_univ_lt_top
  have hratioLim := tendsto_reflectedBiHeatMeasureLowRateIntegral_div_sinh_atTop
    P hkappa hP
  have hevRatio : ∀ᶠ t in atTop,
      (∫ r, Real.sinh (r * t) ∂P) / Real.sinh (kappa * t) < mass :=
    (tendsto_order.mp hratioLim).2 mass hmass
  obtain ⟨t1, ht01, hratio⟩ : ∃ t1 : ℝ, t0 ≤ t1 ∧
      (∫ r, Real.sinh (r * t1) ∂P) / Real.sinh (kappa * t1) < mass := by
    exact ((eventually_ge_atTop t0).and hevRatio).exists
  have ht1 : 0 < t1 := ht0.trans_le ht01
  have hsk : 0 < Real.sinh (kappa * t1) :=
    Real.sinh_pos_iff.mpr (mul_pos hkappa ht1)
  have hlowLt : (∫ r, Real.sinh (r * t1) ∂P) <
      mass * Real.sinh (kappa * t1) :=
    (div_lt_iff₀ hsk).mp hratio
  have hhighLower : mass * Real.sinh (kappa * t1) ≤
      ∫ r, Real.sinh (r * t1) ∂Q := by
    have hconstInt : Integrable (fun _r : ℝ => Real.sinh (kappa * t1)) Q :=
      integrable_const _
    have hmono : (fun _r : ℝ => Real.sinh (kappa * t1)) ≤ᵐ[Q]
        (fun r => Real.sinh (r * t1)) := by
      filter_upwards [hQ] with r hr
      exact Real.sinh_le_sinh.mpr
        (mul_le_mul_of_nonneg_right hr ht1.le)
    have hint := integral_mono_ae hconstInt (hhigh t1 ht1) hmono
    simpa [mass, integral_const, Measure.real, measureReal_def] using hint
  have hpos1 : 0 < reflectedBiHeatMeasureSeparatedSignReporter P Q t1 := by
    rw [reflectedBiHeatMeasureSeparatedSignReporter]
    linarith
  have hcont0 := continuousOn_reflectedBiHeatMeasureSeparatedSignReporter_Icc
    P Q hkappa ht1 hP hQ hhigh
  have hcont : ContinuousOn
      (reflectedBiHeatMeasureSeparatedSignReporter P Q) (Icc t0 t1) :=
    hcont0.mono (fun t ht => ⟨ht0.le.trans ht.1, ht.2⟩)
  have hmem : (0 : ℝ) ∈ Icc
      (reflectedBiHeatMeasureSeparatedSignReporter P Q t0)
      (reflectedBiHeatMeasureSeparatedSignReporter P Q t1) :=
    ⟨hneg0.le, hpos1.le⟩
  rcases intermediate_value_Icc ht01 hcont hmem with ⟨t, ht, hzero⟩
  exact ⟨t, ht0.trans_le ht.1, hzero⟩

theorem reflectedBiHeatMeasureSeparatedSignWallSelective_iff
    (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] {kappa : ℝ}
    (hkappa : 0 < kappa) (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q) :
    0 ≤ reflectedBiHeatMeasureSeparatedSignWallDerivative P Q ↔
      ∀ t : ℝ, reflectedBiHeatMeasureSeparatedSignReporter P Q t = 0 ↔ t = 0 := by
  constructor
  · intro hderiv t
    constructor
    · intro hzero
      by_contra ht
      rcases lt_or_gt_of_ne ht with htneg | htpos
      · have hpos := reflectedBiHeatMeasureSeparatedSignReporter_pos
          P Q hkappa (neg_pos.mpr htneg) hPne hP hQ hhigh hderiv
        have hnegzero : reflectedBiHeatMeasureSeparatedSignReporter P Q (-t) = 0 := by
          rw [reflectedBiHeatMeasureSeparatedSignReporter_neg, hzero, neg_zero]
        exact hpos.ne' hnegzero
      · have hpos := reflectedBiHeatMeasureSeparatedSignReporter_pos
          P Q hkappa htpos hPne hP hQ hhigh hderiv
        exact hpos.ne' hzero
    · rintro rfl
      simp [reflectedBiHeatMeasureSeparatedSignReporter]
  · intro hselect
    by_contra hnot
    have hderiv : reflectedBiHeatMeasureSeparatedSignWallDerivative P Q < 0 :=
      lt_of_not_ge hnot
    rcases
        exists_pos_reflectedBiHeatMeasureSeparatedSignReporter_eq_zero_of_derivative_neg
          P Q hkappa hQne hP hQ hhigh hderiv with ⟨t, ht, hzero⟩
    exact ht.ne' ((hselect t).mp hzero)

def reflectedBiHeatMeasureSeparatedSignApertureGap
    (P Q : Measure ℝ) (x : ℝ) (rho : XiDivisorSupport) : ℝ :=
  -(∫ r, x ^ (r / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ r) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ r) ^ 2) ∂P) +
    ∫ r, x ^ (r / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ r) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ r) ^ 2) ∂Q

theorem reflectedBiHeatMeasureSeparatedSignApertureGap_eq_reporter
    (P Q : Measure ℝ) {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatMeasureSeparatedSignApertureGap P Q x rho =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        reflectedBiHeatMeasureSeparatedSignReporter P Q
          (Real.log x * ((rho : ℂ).re - 1 / 2)) := by
  let C : ℝ := 2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2
  let u : ℝ := Real.log x * ((rho : ℂ).re - 1 / 2)
  have hPInt :
      (∫ r, x ^ (r / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ r) ^ 2 -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ r) ^ 2) ∂P) =
      ∫ r, C * Real.sinh (r * u) ∂P := by
    apply integral_congr_ae
    filter_upwards with r
    have hr := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh r hx rho
    simpa only [C, u] using hr
  have hQInt :
      (∫ r, x ^ (r / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ r) ^ 2 -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ r) ^ 2) ∂Q) =
      ∫ r, C * Real.sinh (r * u) ∂Q := by
    apply integral_congr_ae
    filter_upwards with r
    have hr := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh r hx rho
    simpa only [C, u] using hr
  rw [reflectedBiHeatMeasureSeparatedSignApertureGap,
    reflectedBiHeatMeasureSeparatedSignReporter, hPInt, hQInt,
    integral_const_mul, integral_const_mul]
  ring

theorem reflectedBiHeatMeasureSeparatedSignApertureGap_eq_zero_iff
    (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] {kappa : ℝ}
    (hkappa : 0 < kappa) (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q)
    (hderiv : 0 ≤ reflectedBiHeatMeasureSeparatedSignWallDerivative P Q)
    {x : ℝ} (hx : 1 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatMeasureSeparatedSignApertureGap P Q x rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatMeasureSeparatedSignApertureGap_eq_reporter
    P Q (lt_trans zero_lt_one hx) rho]
  have hcoef :
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)))
  have hselect :=
    (reflectedBiHeatMeasureSeparatedSignWallSelective_iff
      P Q hkappa hPne hQne hP hQ hhigh).mp hderiv
  constructor
  · intro hzero
    have hreport : reflectedBiHeatMeasureSeparatedSignReporter P Q
        (Real.log x * ((rho : ℂ).re - 1 / 2)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcoef
    have hu := (hselect
      (Real.log x * ((rho : ℂ).re - 1 / 2))).mp hreport
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsub : (rho : ℂ).re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hu).resolve_left hlog.ne'
    exact sub_eq_zero.mp hsub
  · intro hre
    rw [hre, sub_self, mul_zero]
    simp [reflectedBiHeatMeasureSeparatedSignReporter]

theorem riemannHypothesis_iff_reflectedBiHeatMeasureSeparatedSignApertureGap_eq_zero
    (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q] {kappa : ℝ}
    (hkappa : 0 < kappa) (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hP : ∀ᵐ r ∂P, 0 < r ∧ r < kappa)
    (hQ : ∀ᵐ r ∂Q, kappa ≤ r)
    (hhigh : ∀ T : ℝ, 0 < T → Integrable (fun r => Real.sinh (r * T)) Q)
    (hderiv : 0 ≤ reflectedBiHeatMeasureSeparatedSignWallDerivative P Q)
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatMeasureSeparatedSignApertureGap P Q x rho = 0 := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatMeasureSeparatedSignApertureGap_eq_zero_iff
      P Q hkappa hPne hQne hP hQ hhigh hderiv hx rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatMeasureSeparatedSignApertureGap_eq_zero_iff
        P Q hkappa hPne hQne hP hQ hhigh hderiv hx rho).mp (h rho)

end

end RHTower

