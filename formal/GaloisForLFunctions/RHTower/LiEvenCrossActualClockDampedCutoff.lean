import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveLaplace
import GaloisForLFunctions.RHTower.LiClockCoshCosCutoff

/-!
# Damped cutoffs of the integrated actual clock

For real `a` and `T ≥ 0` put `D_a(T) = ∫_0^T e^{-at} P(t)/t dt`.  With `u_q = |Re w_q|`,
`v_q = |Im w_q|` the complete copy sum gives
`D_a(T) = Σ_q G(u_q, v_q; a, T)`, `G(u, v; a, T) = ∫_0^T e^{-at} (1 - cos(ut) cosh(vt))/t dt`,
with absolutely summable integrated atom norms.  Every atom satisfies `u_q > v_q`, so the scalar
cosh–cos cutoff theorem gives `D_a(T) > 0` for every `T > 0` and every `a ≥ β`; under RH every
`v_q = 0` and `D_a(T) > 0` for every real `a`.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "β" => liEvenCrossActualClockMaxGrowthRate
local notation "u" => liEvenCrossActualClockReciprocalFrequency
local notation "v" => liEvenCrossActualClockReciprocalGrowthRate

/-- `D_a(T) = ∫_0^T e^{-at} P(t)/t dt`. -/
def liEvenCrossActualClockDampedCutoff (a T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, Real.exp (-a * t) * P t / t

/-- The cosh–cos atom `1 - cos(u_q t) cosh(v_q t)`. -/
def liEvenCrossActualClockCoshCosAtom (q : XiZeroCopy) (t : ℝ) : ℝ :=
  1 - Real.cos (u q * t) * Real.cosh (v q * t)

theorem abs_liEvenCrossActualClockCoshCosAtom_le (q : XiZeroCopy) {t : ℝ} (ht : 0 ≤ t) :
    |liEvenCrossActualClockCoshCosAtom q t| ≤
      t ^ 2 / 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * Real.exp (v q * t) := by
  unfold liEvenCrossActualClockCoshCosAtom
  rw [← re_liEvenCrossActualClockCosineAtom]
  refine (Complex.abs_re_le_norm _).trans ?_
  have h := liClock_norm_one_sub_cos_le_imaginary_exp t (xiSpectralPoint q)⁻¹
  rw [abs_of_nonneg ht, mul_comm t] at h
  exact h

theorem abs_liEvenCrossActualClockCoshCosAtom_le_max (q : XiZeroCopy) {t : ℝ} (ht : 0 ≤ t) :
    |liEvenCrossActualClockCoshCosAtom q t| ≤
      t ^ 2 / 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * Real.exp (β * t) :=
  (abs_liEvenCrossActualClockCoshCosAtom_le q ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (liEvenCrossActualClockReciprocalGrowthRate_le_max q) ht)) (by positivity))

theorem summable_liEvenCrossActualClockCoshCosAtom (t : ℝ) :
    Summable fun q => liEvenCrossActualClockCoshCosAtom q t := by
  refine Summable.of_norm_bounded (summable_norm_liEvenCrossActualClockCosineAtom t) fun q => ?_
  unfold liEvenCrossActualClockCoshCosAtom
  rw [Real.norm_eq_abs, ← re_liEvenCrossActualClockCosineAtom]
  exact Complex.abs_re_le_norm _

theorem tsum_liEvenCrossActualClockCoshCosAtom (t : ℝ) :
    ∑' q, liEvenCrossActualClockCoshCosAtom q t = P t :=
  (liEvenCrossActualClockPrimitive_eq_tsum_coshCos t).symm

/-! ## Interval admissions -/

private theorem measurable_atom_profile (q : XiZeroCopy) (a : ℝ) :
    Measurable fun t => Real.exp (-a * t) * liEvenCrossActualClockCoshCosAtom q t / t := by
  unfold liEvenCrossActualClockCoshCosAtom
  exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-a * t) *
    (1 - Real.cos (u q * t) * Real.cosh (v q * t)))).measurable.div measurable_id

private theorem atom_profile_bound (q : XiZeroCopy) (a : ℝ) {T t : ℝ} (ht : t ∈ Ioc 0 T) :
    ‖Real.exp (-a * t) * liEvenCrossActualClockCoshCosAtom q t / t‖ ≤
      Real.exp (|a| * T) * (T / 2 * Real.exp (β * T)) * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hb := abs_liEvenCrossActualClockCoshCosAtom_le_max q ht0.le
  rw [Real.norm_eq_abs, abs_div, abs_mul, Real.abs_exp, abs_of_pos ht0, div_le_iff₀ ht0]
  have h1 : Real.exp (-a * t) ≤ Real.exp (|a| * T) :=
    Real.exp_le_exp.2 (by nlinarith [neg_abs_le a, abs_nonneg a])
  have h2 : Real.exp (β * t) ≤ Real.exp (β * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT liEvenCrossActualClockMaxGrowthRate_nonneg)
  calc Real.exp (-a * t) * |liEvenCrossActualClockCoshCosAtom q t| ≤
      Real.exp (|a| * T) * (t ^ 2 / 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * Real.exp (β * T)) :=
        mul_le_mul h1 (hb.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) (abs_nonneg _)
          (Real.exp_pos _).le
    _ ≤ _ := by
        have : t ^ 2 ≤ T * t := by nlinarith
        have hw := sq_nonneg ‖(xiSpectralPoint q)⁻¹‖
        have he := (Real.exp_pos (|a| * T)).le
        have he2 := (Real.exp_pos (β * T)).le
        calc Real.exp (|a| * T) * (t ^ 2 / 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * Real.exp (β * T)) ≤
            Real.exp (|a| * T) * (T * t / 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * Real.exp (β * T)) := by
              gcongr
          _ = _ := by ring

theorem integrableOn_liEvenCrossActualClockCoshCosAtom_profile (q : XiZeroCopy) (a T : ℝ) :
    IntegrableOn (fun t => Real.exp (-a * t) * liEvenCrossActualClockCoshCosAtom q t / t)
      (Ioc 0 T) :=
  Measure.integrableOn_of_bounded (M := Real.exp (|a| * T) * (T / 2 * Real.exp (β * T)) *
    ‖(xiSpectralPoint q)⁻¹‖ ^ 2) measure_Ioc_lt_top.ne
    (measurable_atom_profile q a).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun _ ht => atom_profile_bound q a ht)

private theorem measurable_profile (a : ℝ) :
    Measurable fun t => Real.exp (-a * t) * P t / t :=
  ((by fun_prop : Continuous fun t : ℝ => Real.exp (-a * t)).mul
    continuous_liEvenCrossActualClockPrimitive).measurable.div measurable_id

theorem abs_exp_mul_liEvenCrossActualClockPrimitive_div_le (a : ℝ) {t : ℝ} (ht : 0 < t) :
    |Real.exp (-a * t) * P t / t| ≤ xiShiftAbsoluteMass 0 / 2 * t * Real.exp ((β - a) * t) := by
  have hb := abs_liEvenCrossActualClockPrimitive_le_max ht.le
  rw [abs_div, abs_mul, Real.abs_exp, abs_of_pos ht, div_le_iff₀ ht]
  calc Real.exp (-a * t) * |P t| ≤ Real.exp (-a * t) *
      (xiShiftAbsoluteMass 0 * t ^ 2 / 2 * Real.exp (β * t)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by rw [show (β - a) * t = -a * t + β * t by ring, Real.exp_add]; ring

theorem intervalIntegrable_liEvenCrossActualClockDampedCutoff_profile_zero (a : ℝ) {T : ℝ}
    (hT : 0 ≤ T) : IntervalIntegrable (fun t => Real.exp (-a * t) * P t / t) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  refine Measure.integrableOn_of_bounded (M := xiShiftAbsoluteMass 0 / 2 * T *
    Real.exp (|β - a| * T)) measure_Ioc_lt_top.ne (measurable_profile a).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_exp_mul_liEvenCrossActualClockPrimitive_div_le a ht.1).trans ?_
  have hA := xiShiftAbsoluteMass_nonneg 0
  have h1 : (β - a) * t ≤ |β - a| * T :=
    (le_abs_self _ |> mul_le_mul_of_nonneg_right <| ht.1.le).trans
      (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _))
  have h2 := Real.exp_le_exp.2 h1
  have h3 : xiShiftAbsoluteMass 0 / 2 * t ≤ xiShiftAbsoluteMass 0 / 2 * T :=
    mul_le_mul_of_nonneg_left ht.2 (by positivity)
  exact mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)

theorem intervalIntegrable_liEvenCrossActualClockDampedCutoff_profile (a : ℝ) {S T : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => Real.exp (-a * t) * P t / t) volume S T :=
  (intervalIntegrable_liEvenCrossActualClockDampedCutoff_profile_zero a hS).symm.trans
    (intervalIntegrable_liEvenCrossActualClockDampedCutoff_profile_zero a hT)

/-! ## The atom decomposition -/

/-- **Atom decomposition (I6).**  `D_a(T) = Σ_q G(u_q, v_q; a, T)` for `T ≥ 0`. -/
theorem liEvenCrossActualClockDampedCutoff_eq_tsum (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    liEvenCrossActualClockDampedCutoff a T = ∑' q, liClockCoshCosCutoff (u q) (v q) a T := by
  set C := Real.exp (|a| * T) * (T / 2 * Real.exp (β * T))
  have hint := fun q => integrableOn_liEvenCrossActualClockCoshCosAtom_profile q a T
  have hnorm : ∀ q, ∫ t in Ioc 0 T, ‖Real.exp (-a * t) * liEvenCrossActualClockCoshCosAtom q t / t‖ ≤
      T * (C * ‖(xiSpectralPoint q)⁻¹‖ ^ 2) := by
    intro q
    have h := setIntegral_mono_on (hint q).norm (integrableOn_const (C := C * ‖(xiSpectralPoint q)⁻¹‖ ^ 2)
      measure_Ioc_lt_top.ne) measurableSet_Ioc fun t ht => atom_profile_bound q a ht
    rw [setIntegral_const, Real.volume_real_Ioc, max_eq_left (by linarith), sub_zero,
      smul_eq_mul] at h
    exact h
  have hsum : Summable fun q => ∫ t in Ioc 0 T,
      ‖Real.exp (-a * t) * liEvenCrossActualClockCoshCosAtom q t / t‖ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun t => norm_nonneg _) hnorm
      ((summable_norm_inv_xiSpectralPoint_sq.mul_left C).mul_left T)
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have e : ∀ q, liClockCoshCosCutoff (u q) (v q) a T =
      ∫ t in Ioc 0 T, Real.exp (-a * t) * liEvenCrossActualClockCoshCosAtom q t / t := by
    intro q
    unfold liClockCoshCosCutoff liEvenCrossActualClockCoshCosAtom
    rw [intervalIntegral.integral_of_le hT]
  rw [tsum_congr e, hswap]
  unfold liEvenCrossActualClockDampedCutoff
  rw [intervalIntegral.integral_of_le hT]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [tsum_div_const, tsum_mul_left, tsum_liEvenCrossActualClockCoshCosAtom]

/-! ## Positivity for `a ≥ β` and under RH -/

private theorem norm_liClockCoshCosCutoff_le (q : XiZeroCopy) (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖liClockCoshCosCutoff (u q) (v q) a T‖ ≤
      T * (Real.exp (|a| * T) * (T / 2 * Real.exp (β * T)) * ‖(xiSpectralPoint q)⁻¹‖ ^ 2) := by
  unfold liClockCoshCosCutoff
  rw [intervalIntegral.integral_of_le hT]
  refine (norm_setIntegral_le_of_norm_le_const (C := Real.exp (|a| * T) * (T / 2 * Real.exp (β * T)) *
    ‖(xiSpectralPoint q)⁻¹‖ ^ 2) measure_Ioc_lt_top fun t ht => atom_profile_bound q a ht).trans ?_
  rw [Real.volume_real_Ioc, max_eq_left (by linarith), sub_zero, mul_comm]

theorem summable_liClockCoshCosCutoff (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Summable fun q => liClockCoshCosCutoff (u q) (v q) a T :=
  Summable.of_norm_bounded ((summable_norm_inv_xiSpectralPoint_sq.mul_left _).mul_left T)
    fun q => norm_liClockCoshCosCutoff_le q a hT

/-- **Cutoff positivity (I9).**  `D_a(T) > 0` for every `T > 0` and every `a ≥ β`. -/
theorem liEvenCrossActualClockDampedCutoff_pos {a T : ℝ} (ha : β ≤ a) (hT : 0 < T) :
    0 < liEvenCrossActualClockDampedCutoff a T := by
  rw [liEvenCrossActualClockDampedCutoff_eq_tsum a hT.le]
  have hpos : ∀ q, 0 < liClockCoshCosCutoff (u q) (v q) a T := fun q =>
    liClockCoshCosCutoff_pos (liEvenCrossActualClockReciprocalGrowthRate_nonneg q)
      (liEvenCrossActualClockReciprocalGrowthRate_lt_frequency q).le
      (liEvenCrossActualClockReciprocalFrequency_pos q)
      ((liEvenCrossActualClockReciprocalGrowthRate_le_max q).trans ha) hT
  exact (summable_liClockCoshCosCutoff a hT.le).tsum_pos (fun q => (hpos q).le)
    (Classical.choice nonempty_xiZeroCopy) (hpos _)

private theorem intervalIntegrable_undamped_atom (w a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => Real.exp (-a * t) * (1 - Real.cos (w * t) * Real.cosh (0 * t)) / t)
      volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  refine Measure.integrableOn_of_bounded (M := Real.exp (|a| * T) * (w ^ 2 * T / 2))
    measure_Ioc_lt_top.ne (((by fun_prop : Continuous fun t : ℝ => Real.exp (-a * t) *
      (1 - Real.cos (w * t) * Real.cosh (0 * t)))).measurable.div measurable_id).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  obtain ⟨ht0, htT⟩ := ht
  simp only [zero_mul, Real.cosh_zero, mul_one]
  rw [Real.norm_eq_abs, abs_div, abs_mul, Real.abs_exp, abs_of_pos ht0, div_le_iff₀ ht0]
  have hc := Real.one_sub_sq_div_two_le_cos (x := w * t)
  have h1 : |1 - Real.cos (w * t)| ≤ (w * t) ^ 2 / 2 := by
    rw [abs_of_nonneg (by linarith [Real.cos_le_one (w * t)])]; linarith
  have h2 : Real.exp (-a * t) ≤ Real.exp (|a| * T) :=
    Real.exp_le_exp.2 (by nlinarith [neg_abs_le a, abs_nonneg a])
  calc Real.exp (-a * t) * |1 - Real.cos (w * t)| ≤ Real.exp (|a| * T) * ((w * t) ^ 2 / 2) :=
        mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := by
        have : (w * t) ^ 2 / 2 ≤ w ^ 2 * T / 2 * t := by nlinarith [sq_nonneg w]
        calc Real.exp (|a| * T) * ((w * t) ^ 2 / 2) ≤ Real.exp (|a| * T) * (w ^ 2 * T / 2 * t) :=
              mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = _ := by ring

/-- The undamped real atom `G(u, 0; a, T) > 0` for every real damping `a`. -/
theorem liClockCoshCosCutoff_zero_pos {w : ℝ} (hw : 0 < w) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    0 < liClockCoshCosCutoff w 0 a T := by
  rcases le_total 0 a with ha | ha
  · exact liClockCoshCosCutoff_pos le_rfl hw.le hw ha hT
  · have h0 := liClockCoshCosCutoff_pos le_rfl hw.le hw le_rfl hT
    refine h0.trans_le ?_
    unfold liClockCoshCosCutoff
    refine intervalIntegral.integral_mono_on hT.le (intervalIntegrable_undamped_atom w 0 hT.le)
      (intervalIntegrable_undamped_atom w a hT.le) fun t ht => ?_
    simp only [zero_mul, Real.cosh_zero, mul_one, neg_zero, Real.exp_zero, one_mul]
    have h1 : 0 ≤ 1 - Real.cos (w * t) := by linarith [Real.cos_le_one (w * t)]
    have h2 : 1 ≤ Real.exp (-a * t) := Real.one_le_exp (by nlinarith [ht.1])
    rcases ht.1.eq_or_lt with h | h
    · subst h; simp
    · rw [div_le_div_iff_of_pos_right h]
      nlinarith

/-- Under RH, `D_a(T) > 0` for every real `a` and every `T > 0`. -/
theorem liEvenCrossActualClockDampedCutoff_pos_of_rh (hRH : RiemannHypothesis) (a : ℝ) {T : ℝ}
    (hT : 0 < T) : 0 < liEvenCrossActualClockDampedCutoff a T := by
  rw [liEvenCrossActualClockDampedCutoff_eq_tsum a hT.le]
  have hpos : ∀ q, 0 < liClockCoshCosCutoff (u q) (v q) a T := fun q => by
    rw [liEvenCrossActualClockReciprocalGrowthRate_eq_zero_of_rh hRH q]
    exact liClockCoshCosCutoff_zero_pos (liEvenCrossActualClockReciprocalFrequency_pos q) a hT
  exact (summable_liClockCoshCosCutoff a hT.le).tsum_pos (fun q => (hpos q).le)
    (Classical.choice nonempty_xiZeroCopy) (hpos _)

end RHTower
