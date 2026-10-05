import GaloisForLFunctions.RHTower.LiClockThetaSignedGammaJumps
import Mathlib.Tactic

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
namespace RHTower
noncomputable section
local notation "P" => liEvenCrossActualClockPrimitive

def liClockThetaUndampedJumpCoefficient (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    (-1 : ℝ)^(j-1) * normalizedPrimeArchMoment (j-1) / (2*j : ℝ)

def liClockThetaMarkedJumpDensity (positive : Bool) (u : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun u =>
    ∑' j : ℕ,
      max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ)) u

def liClockThetaCompactMarkedGammaMeasure
    (p : ℝ) (positive : Bool) (T : ℝ) : Measure ℝ :=
  ((liClockThetaGammaJumpMeasure p positive).restrict (Ioc 0 T)).withDensity
    (fun u => ENNReal.ofReal (Real.exp (p*u)))

theorem liClockThetaUndampedJumpCoefficient_eq_scaled_wide
    {p : ℝ} (hp : liClockThetaWideThreshold < p) (j : ℕ) :
    liClockThetaUndampedJumpCoefficient j =
      p^(2*j) * liClockThetaLogJumpCoefficient p j := by
  by_cases hj : j = 0
  · simp [liClockThetaUndampedJumpCoefficient, liClockThetaLogJumpCoefficient, hj]
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hj0 : 0 < j := Nat.pos_of_ne_zero hj
  simp only [liClockThetaUndampedJumpCoefficient, liClockThetaLogJumpCoefficient, if_neg hj]
  field_simp

private theorem sgm_density_measurable (p : ℝ) (j : ℕ) :
    Measurable (liClockThetaGammaRowDensity p j) := by
  unfold liClockThetaGammaRowDensity
  split_ifs
  · fun_prop
  · exact Measurable.indicator (by fun_prop) measurableSet_Ioi

private theorem sgm_density_nonneg {p : ℝ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    0 ≤ liClockThetaGammaRowDensity p j t := by
  by_cases hj : j = 0
  · simp [liClockThetaGammaRowDensity, hj]
  by_cases ht : 0 < t
  · simp only [liClockThetaGammaRowDensity, if_neg hj,
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    positivity
  · simp [liClockThetaGammaRowDensity, hj, ht]

private theorem sgm_rowDensity_le {p : ℝ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    liClockThetaGammaRowDensity p j t ≤ p := by
  by_cases hj : j = 0
  · simp [liClockThetaGammaRowDensity, hj, hp.le]
  by_cases ht : 0 < t
  · have he : 2*j = (2*j-1)+1 := by omega
    have hf : ((2*j-1).factorial : ℝ) ≠ 0 := by positivity
    have hid : liClockThetaGammaRowDensity p j t =
        p * ((p*t)^(2*j-1)/((2*j-1).factorial : ℝ)) * Real.exp (-(p*t)) := by
      simp only [liClockThetaGammaRowDensity, if_neg hj,
        indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      have hpPow : p^(2*j) = p^(2*j-1)*p := by
        calc
          _ = p^((2*j-1)+1) := congrArg (fun n : ℕ => p^n) he
          _ = _ := pow_succ _ _
      rw [hpPow, mul_pow]
      field_simp
    rw [hid]
    calc
      _ ≤ p * Real.exp (p*t) * Real.exp (-(p*t)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.pow_div_factorial_le_exp (p*t) (mul_nonneg hp.le ht.le) _) hp.le)
          (Real.exp_pos _).le
      _ = p := by rw [Real.exp_neg]; field_simp
  · simp [liClockThetaGammaRowDensity, hj, ht, hp.le]

private theorem sgm_density_summable {p : ℝ} (hp : 0 < p)
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hs : Summable w) (t : ℝ) :
    Summable (fun j => w j * liClockThetaGammaRowDensity p j t) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (hw j) (sgm_density_nonneg hp j t))
    (fun j => ?_) (hs.mul_left p)
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (sgm_rowDensity_le hp j t) (hw j)

private def sgm_term (positive : Bool) (u : ℝ) (j : ℕ) : ℝ :=
  max (if positive then liClockThetaUndampedJumpCoefficient j
    else -liClockThetaUndampedJumpCoefficient j) 0 *
    u^(2*j-1) / ((2*j-1).factorial : ℝ)

private theorem sgm_part_nonneg (p : ℝ) (positive : Bool) (j : ℕ) :
    0 ≤ liClockThetaJumpPart p positive j := by
  cases positive <;> simp [liClockThetaJumpPart]

private theorem sgm_part_le_abs (p : ℝ) (positive : Bool) (j : ℕ) :
    liClockThetaJumpPart p positive j ≤ |liClockThetaLogJumpCoefficient p j| := by
  cases positive
  · change max (-liClockThetaLogJumpCoefficient p j) 0 ≤
      |liClockThetaLogJumpCoefficient p j|
    apply max_le
    · simpa using le_abs_self (-liClockThetaLogJumpCoefficient p j)
    · exact abs_nonneg _
  · change max (liClockThetaLogJumpCoefficient p j) 0 ≤
      |liClockThetaLogJumpCoefficient p j|
    exact max_le (le_abs_self _) (abs_nonneg _)

private theorem sgm_part_scaled {p : ℝ} (hp : liClockThetaWideThreshold < p) (positive : Bool) (j : ℕ) :
    max (if positive then liClockThetaUndampedJumpCoefficient j
      else -liClockThetaUndampedJumpCoefficient j) 0 =
      p^(2*j) * liClockThetaJumpPart p positive j := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hpow : 0 ≤ p^(2*j) := (pow_pos hp0 _).le
  cases positive
  · change max (-liClockThetaUndampedJumpCoefficient j) 0 =
      p^(2*j) * max (-liClockThetaLogJumpCoefficient p j) 0
    rw [liClockThetaUndampedJumpCoefficient_eq_scaled_wide hp,
      mul_max_of_nonneg _ _ hpow, mul_zero]
    congr 1
    ring
  · change max (liClockThetaUndampedJumpCoefficient j) 0 =
      p^(2*j) * max (liClockThetaLogJumpCoefficient p j) 0
    rw [liClockThetaUndampedJumpCoefficient_eq_scaled_wide hp,
      mul_max_of_nonneg _ _ hpow, mul_zero]

private theorem sgm_marked_row_eq {p u : ℝ} (hp : liClockThetaWideThreshold < p) (hu : 0 < u)
    (positive : Bool) (j : ℕ) :
    Real.exp (p*u) * (liClockThetaJumpPart p positive j *
      liClockThetaGammaRowDensity p j u) = sgm_term positive u j := by
  by_cases hj : j = 0
  · subst j
    cases positive <;>
      simp [sgm_term, liClockThetaGammaRowDensity, liClockThetaUndampedJumpCoefficient]
  unfold sgm_term
  rw [sgm_part_scaled hp]
  simp only [liClockThetaGammaRowDensity, if_neg hj,
    indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
  rw [Real.exp_neg]
  field_simp

private theorem sgm_term_hasSum {p u : ℝ} (hp : liClockThetaWideThreshold < p) (hu : 0 < u)
    (positive : Bool) :
    HasSum (sgm_term positive u)
      (Real.exp (p*u) * liClockThetaGammaJumpDensity p positive u) := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hsPart : Summable (liClockThetaJumpPart p positive) :=
    Summable.of_nonneg_of_le (sgm_part_nonneg p positive)
      (sgm_part_le_abs p positive) (liClockThetaLogJumpCoefficient_admission_wide hp).1
  have hsRows := sgm_density_summable hp0 (sgm_part_nonneg p positive) hsPart u
  have hrows : HasSum (fun j => liClockThetaJumpPart p positive j *
      liClockThetaGammaRowDensity p j u) (liClockThetaGammaJumpDensity p positive u) := by
    simpa only [liClockThetaGammaJumpDensity] using hsRows.hasSum
  exact (hrows.mul_left (Real.exp (p*u))).congr_fun
    (fun j => (sgm_marked_row_eq hp hu positive j).symm)

theorem liClockThetaMarkedJumpDensity_series_wide
    (positive : Bool) {u : ℝ} (hu : 0 < u) :
    Summable (fun j : ℕ =>
      ‖max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ)‖) ∧
    HasSum (fun j : ℕ =>
      max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ))
      (liClockThetaMarkedJumpDensity positive u) ∧
    (∀ p : ℝ, liClockThetaWideThreshold < p →
      Real.exp (p*u) * liClockThetaGammaJumpDensity p positive u =
        liClockThetaMarkedJumpDensity positive u) := by
  have hs := (sgm_term_hasSum (p := 2) (liClockThetaWideThreshold_lt_one.trans one_lt_two) hu positive).summable
  have he : liClockThetaMarkedJumpDensity positive u = ∑' j, sgm_term positive u j := by
    simp only [liClockThetaMarkedJumpDensity,
      indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu), sgm_term]
  refine ⟨hs.norm, ?_, ?_⟩
  · rw [he]
    exact hs.hasSum.congr_fun (fun j => rfl)
  · intro p hp
    rw [he, (sgm_term_hasSum hp hu positive).tsum_eq]
private theorem sgm_gamma_measurable (p : ℝ) (positive : Bool) :
    Measurable (liClockThetaGammaJumpDensity p positive) := by
  unfold liClockThetaGammaJumpDensity
  exact Measurable.tsum (fun j => measurable_const.mul (sgm_density_measurable p j))

private theorem sgm_marked_measurable (positive : Bool) :
    Measurable (liClockThetaMarkedJumpDensity positive) := by
  unfold liClockThetaMarkedJumpDensity
  apply Measurable.indicator _ measurableSet_Ioi
  exact Measurable.tsum (fun j => by fun_prop)

private theorem sgm_marked_eq {p : ℝ} (hp : liClockThetaWideThreshold < p) (positive : Bool) (u : ℝ) :
    Real.exp (p*u) * liClockThetaGammaJumpDensity p positive u =
      liClockThetaMarkedJumpDensity positive u := by
  by_cases hu : 0 < u
  · exact (liClockThetaMarkedJumpDensity_series_wide positive hu).2.2 p hp
  · have hrow : ∀ j, liClockThetaGammaRowDensity p j u = 0 := by
      intro j
      simp [liClockThetaGammaRowDensity, hu]
    simp [liClockThetaGammaJumpDensity, hrow, liClockThetaMarkedJumpDensity, hu]

 theorem liClockThetaMarkedJumpDensity_admission (positive : Bool) :
  (∀ u : ℝ, 0 ≤ liClockThetaMarkedJumpDensity positive u) ∧
  (∀ T : ℝ, 0 < T →
    IntegrableOn (liClockThetaMarkedJumpDensity positive) (Ioc 0 T)) := by
  have had := (liClockThetaGammaJumpDensity_admission (p := 2) (by norm_num)).1 positive
  refine ⟨?_, ?_⟩
  · intro u
    rw [← sgm_marked_eq (p := 2) (liClockThetaWideThreshold_lt_one.trans one_lt_two) positive u]
    exact mul_nonneg (Real.exp_pos _).le (had.2.1 u)
  · intro T hT
    have hb : ∀ᵐ u ∂volume.restrict (Ioc 0 T), ‖Real.exp (2*u)‖ ≤ Real.exp (2*T) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith [hu.2])
    have hi := had.1.integrableOn.bdd_mul
      (show Measurable (fun u : ℝ => Real.exp (2*u)) by fun_prop).aestronglyMeasurable hb
    have he : (fun u => Real.exp (2*u) * liClockThetaGammaJumpDensity 2 positive u) =
        liClockThetaMarkedJumpDensity positive := by
      funext u
      exact sgm_marked_eq (liClockThetaWideThreshold_lt_one.trans one_lt_two) positive u
    rw [he] at hi
    exact hi

private theorem sgm_measure_eq {p T : ℝ} (hp : liClockThetaWideThreshold < p) (positive : Bool) :
    liClockThetaCompactMarkedGammaMeasure p positive T =
      (volume.restrict (Ioc 0 T)).withDensity
        (fun u => ENNReal.ofReal (liClockThetaMarkedJumpDensity positive u)) := by
  have had := (liClockThetaGammaJumpDensity_admission_wide hp).1 positive
  unfold liClockThetaCompactMarkedGammaMeasure
  rw [had.2.2.2, restrict_withDensity measurableSet_Ioc]
  rw [← withDensity_mul _ (sgm_gamma_measurable p positive).ennreal_ofReal
    (show Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (p*u))) by fun_prop)]
  congr 1
  funext u
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (had.2.1 u), mul_comm,
    sgm_marked_eq hp positive u]

 theorem liClockThetaCompactMarkedGammaMeasure_admission_wide
    {p T : ℝ} (hp : liClockThetaWideThreshold < p) (hT : 0 < T) (positive : Bool) :
  IsFiniteMeasure (liClockThetaCompactMarkedGammaMeasure p positive T) ∧
  (∀ᵐ u ∂liClockThetaCompactMarkedGammaMeasure p positive T, u ∈ Ioc 0 T) ∧
  liClockThetaCompactMarkedGammaMeasure p positive T =
    (volume.restrict (Ioc 0 T)).withDensity
      (fun u => ENNReal.ofReal (liClockThetaMarkedJumpDensity positive u)) := by
  have had := liClockThetaMarkedJumpDensity_admission positive
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] liClockThetaMarkedJumpDensity positive :=
    ae_of_all _ had.1
  have hf := (hasFiniteIntegral_iff_ofReal hn).mp (had.2 T hT).hasFiniteIntegral
  have he := sgm_measure_eq (T := T) hp positive
  refine ⟨?_, ?_, he⟩
  · rw [he]
    exact isFiniteMeasure_withDensity hf.ne
  · rw [he]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

 theorem liClockThetaCompactMarkedGammaMeasure_eq_wide
    {p q T : ℝ} (hp : liClockThetaWideThreshold < p) (hq : liClockThetaWideThreshold < q) (hT : 0 < T)
    (positive : Bool) :
  liClockThetaCompactMarkedGammaMeasure p positive T =
    liClockThetaCompactMarkedGammaMeasure q positive T := by
  exact (liClockThetaCompactMarkedGammaMeasure_admission_wide hp hT positive).2.2.trans
    (liClockThetaCompactMarkedGammaMeasure_admission_wide hq hT positive).2.2.symm

 theorem liClockThetaCompactMarkedGammaMeasure_test_wide
    {p T : ℝ} (hp : liClockThetaWideThreshold < p) (hT : 0 < T) (positive : Bool)
    (h : ℝ → ℝ) (hh : Measurable h)
    (hC : ∃ C : ℝ, ∀ u ∈ Ioc 0 T, |h u| ≤ C) :
  Integrable h (liClockThetaCompactMarkedGammaMeasure p positive T) ∧
  IntegrableOn (fun u => h u * liClockThetaMarkedJumpDensity positive u)
    (Ioc 0 T) ∧
  (∫ u, h u ∂liClockThetaCompactMarkedGammaMeasure p positive T) =
    ∫ u in Ioc 0 T, h u * liClockThetaMarkedJumpDensity positive u := by
  have had := liClockThetaMarkedJumpDensity_admission positive
  obtain ⟨C, hC⟩ := hC
  have hb : ∀ᵐ u ∂volume.restrict (Ioc 0 T), ‖h u‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa only [Real.norm_eq_abs] using hC u hu
  have hi := (had.2 T hT).bdd_mul hh.aestronglyMeasurable hb
  have hm := (sgm_marked_measurable positive).ennreal_ofReal
  have ht : ∀ᵐ u ∂volume.restrict (Ioc 0 T),
      ENNReal.ofReal (liClockThetaMarkedJumpDensity positive u) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have he := sgm_measure_eq (T := T) hp positive
  have hsm : (fun u => (ENNReal.ofReal (liClockThetaMarkedJumpDensity positive u)).toReal • h u) =
      (fun u => h u * liClockThetaMarkedJumpDensity positive u) := by
    funext u
    rw [ENNReal.toReal_ofReal (had.1 u), smul_eq_mul, mul_comm]
  refine ⟨?_, hi, ?_⟩
  · rw [he, integrable_withDensity_iff_integrable_smul' hm ht, hsm]
    exact hi
  · rw [he, integral_withDensity_eq_integral_toReal_smul hm ht, hsm]

private theorem sgm_parts_sub (p : ℝ) (j : ℕ) :
    liClockThetaJumpPart p true j - liClockThetaJumpPart p false j =
      liClockThetaLogJumpCoefficient p j := by
  by_cases h : 0 ≤ liClockThetaLogJumpCoefficient p j
  · simp [liClockThetaJumpPart, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have hle : liClockThetaLogJumpCoefficient p j ≤ 0 := (lt_of_not_ge h).le
    simp [liClockThetaJumpPart, max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)]

private theorem sgm_signed_eq_sub {p : ℝ} (hp : liClockThetaWideThreshold < p) (u : ℝ) :
    liClockThetaSignedGammaDensity p u =
      liClockThetaGammaJumpDensity p true u - liClockThetaGammaJumpDensity p false u := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hs : ∀ positive, Summable (fun j =>
      liClockThetaJumpPart p positive j * liClockThetaGammaRowDensity p j u) := by
    intro positive
    have hsPart : Summable (liClockThetaJumpPart p positive) :=
      Summable.of_nonneg_of_le (sgm_part_nonneg p positive)
        (sgm_part_le_abs p positive) (liClockThetaLogJumpCoefficient_admission_wide hp).1
    exact sgm_density_summable hp0 (sgm_part_nonneg p positive) hsPart u
  unfold liClockThetaSignedGammaDensity liClockThetaGammaJumpDensity
  rw [← (hs true).tsum_sub (hs false)]
  apply tsum_congr
  intro j
  rw [← sub_mul, sgm_parts_sub]

 theorem liClockThetaMarkedJumpDensity_sub (u : ℝ) :
  liClockThetaMarkedJumpDensity true u -
    liClockThetaMarkedJumpDensity false u =
  (Ioi (0 : ℝ)).indicator (fun u => P u / u) u := by
  rw [← sgm_marked_eq (p := 2) (liClockThetaWideThreshold_lt_one.trans one_lt_two) true u,
    ← sgm_marked_eq (p := 2) (liClockThetaWideThreshold_lt_one.trans one_lt_two) false u,
    ← mul_sub, ← sgm_signed_eq_sub (liClockThetaWideThreshold_lt_one.trans one_lt_two)]
  rw [liClockThetaSignedGammaDensity_eq_primitive (by norm_num)]
  by_cases hu : 0 < u
  · simp only [indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
    rw [Real.exp_neg]
    field_simp
  · simp [hu]

end
end RHTower

namespace RHTower

/-! ## The original `p > 1` statements -/

theorem liClockThetaUndampedJumpCoefficient_eq_scaled
    {p : ℝ} (hp : 1 < p) (j : ℕ) :
    liClockThetaUndampedJumpCoefficient j =
      p^(2*j) * liClockThetaLogJumpCoefficient p j :=
  liClockThetaUndampedJumpCoefficient_eq_scaled_wide (liClockThetaWideThreshold_lt_one.trans hp) j

theorem liClockThetaMarkedJumpDensity_series
    (positive : Bool) {u : ℝ} (hu : 0 < u) :
    Summable (fun j : ℕ =>
      ‖max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ)‖) ∧
    HasSum (fun j : ℕ =>
      max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ))
      (liClockThetaMarkedJumpDensity positive u) ∧
    (∀ p : ℝ, 1 < p →
      Real.exp (p*u) * liClockThetaGammaJumpDensity p positive u =
        liClockThetaMarkedJumpDensity positive u) :=
  let h := liClockThetaMarkedJumpDensity_series_wide positive hu
  ⟨h.1, h.2.1, fun p hp => h.2.2 p (liClockThetaWideThreshold_lt_one.trans hp)⟩

theorem liClockThetaCompactMarkedGammaMeasure_admission
    {p T : ℝ} (hp : 1 < p) (hT : 0 < T) (positive : Bool) :
  IsFiniteMeasure (liClockThetaCompactMarkedGammaMeasure p positive T) ∧
  (∀ᵐ u ∂liClockThetaCompactMarkedGammaMeasure p positive T, u ∈ Ioc 0 T) ∧
  liClockThetaCompactMarkedGammaMeasure p positive T =
    (volume.restrict (Ioc 0 T)).withDensity
      (fun u => ENNReal.ofReal (liClockThetaMarkedJumpDensity positive u)) :=
  liClockThetaCompactMarkedGammaMeasure_admission_wide (liClockThetaWideThreshold_lt_one.trans hp) hT positive

theorem liClockThetaCompactMarkedGammaMeasure_eq
    {p q T : ℝ} (hp : 1 < p) (hq : 1 < q) (hT : 0 < T)
    (positive : Bool) :
  liClockThetaCompactMarkedGammaMeasure p positive T =
    liClockThetaCompactMarkedGammaMeasure q positive T :=
  liClockThetaCompactMarkedGammaMeasure_eq_wide (liClockThetaWideThreshold_lt_one.trans hp)
    (liClockThetaWideThreshold_lt_one.trans hq) hT positive

theorem liClockThetaCompactMarkedGammaMeasure_test
    {p T : ℝ} (hp : 1 < p) (hT : 0 < T) (positive : Bool)
    (h : ℝ → ℝ) (hh : Measurable h)
    (hC : ∃ C : ℝ, ∀ u ∈ Ioc 0 T, |h u| ≤ C) :
  Integrable h (liClockThetaCompactMarkedGammaMeasure p positive T) ∧
  IntegrableOn (fun u => h u * liClockThetaMarkedJumpDensity positive u)
    (Ioc 0 T) ∧
  (∫ u, h u ∂liClockThetaCompactMarkedGammaMeasure p positive T) =
    ∫ u in Ioc 0 T, h u * liClockThetaMarkedJumpDensity positive u :=
  liClockThetaCompactMarkedGammaMeasure_test_wide (liClockThetaWideThreshold_lt_one.trans hp) hT positive h hh hC

end RHTower
