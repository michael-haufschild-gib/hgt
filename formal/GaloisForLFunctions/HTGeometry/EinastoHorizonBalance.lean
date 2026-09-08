import GaloisForLFunctions.HTGeometry.EinastoInformationCurvature
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Einasto horizon balance: one maximum and one zero

Supplies the analytic uniqueness argument behind the horizon plot in section
4.1 of arXiv:2608.23600v1. For the actual integrated mass, the balance
`r*m'(r)-m(r)` has one explicit derivative sign change and exactly one zero at
positive radius. It is positive before that zero and negative after it.

The proof builds the missing density-tail infrastructure for every polynomial
radial weight, uses the finite total mass to fix the negative limit, and
combines strict monotonicity with the intermediate value theorem. No numerical
root finding, asymptotic hypothesis, or assumed horizon classification occurs.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The numerator controlling the radial derivative of enclosed mass divided by radius. -/
def einastoHorizonBalance (d l a r : ℝ) : ℝ :=
  4 * Real.pi * (r ^ 3 * einastoDensity d l a r) - einastoMass d l a r

theorem einastoHorizonBalance_derivative (d l a t : ℝ) :
    HasDerivAt (einastoHorizonBalance d l a)
      (4 * Real.pi * exp t ^ 2 * einastoDensity d l a (exp t) *
        (2 - exp (-a) * (exp t / exp l) ^ exp (-a))) (exp t) := by
  have h := ((((hasDerivAt_id (exp t)).pow 3).mul (einastoDensity_derivative d l a t)).const_mul
    (4 * Real.pi)).sub (einastoMass_derivative d l a (exp t))
  apply h.congr_deriv
  dsimp [einastoSlope]
  field_simp
  ring

theorem einastoShape_log_coordinate (l a t : ℝ) :
    exp (-a) * (exp t / exp l) ^ exp (-a) = exp (-a + exp (-a) * (t - l)) := by
  rw [← exp_sub, rpow_def_of_pos (exp_pos (t - l)), log_exp, exp_add]
  congr 1
  congr 1
  ring

/-- The unique critical logarithmic radius of the horizon-balance function. -/
def einastoBalanceCriticalLogRadius (l a : ℝ) : ℝ := l + exp a * (a + log 2)

theorem einastoShape_shifted_critical (l a u : ℝ) :
    exp (-a) * (exp (einastoBalanceCriticalLogRadius l a + u) / exp l) ^ exp (-a) =
      2 * exp (exp (-a) * u) := by
  rw [einastoShape_log_coordinate]
  have he : -a + exp (-a) * (einastoBalanceCriticalLogRadius l a + u - l) =
      log 2 + exp (-a) * u := by
    unfold einastoBalanceCriticalLogRadius
    rw [exp_neg]
    field_simp
    ring
  rw [he, exp_add, exp_log (by norm_num : (0 : ℝ) < 2)]

theorem einastoHorizonBalance_derivative_pos_iff (d l a u : ℝ) :
    0 < deriv (einastoHorizonBalance d l a) (exp (einastoBalanceCriticalLogRadius l a + u)) ↔ u < 0 := by
  rw [(einastoHorizonBalance_derivative d l a _).deriv, einastoShape_shifted_critical]
  have hp : 0 < 4 * Real.pi * exp (einastoBalanceCriticalLogRadius l a + u) ^ 2 *
      einastoDensity d l a (exp (einastoBalanceCriticalLogRadius l a + u)) := by
    exact mul_pos (by positivity) (einastoDensity_pos _ _ _ _)
  have he : exp (exp (-a) * u) < 1 ↔ u < 0 := by
    rw [← exp_zero, exp_lt_exp]
    constructor <;> intro h <;> nlinarith [exp_pos (-a)]
  constructor
  · intro h
    apply he.mp
    nlinarith
  · intro h
    have hh := he.mpr h
    exact mul_pos hp (by linarith)

theorem einastoHorizonBalance_derivative_neg_iff (d l a u : ℝ) :
    deriv (einastoHorizonBalance d l a) (exp (einastoBalanceCriticalLogRadius l a + u)) < 0 ↔ 0 < u := by
  rw [(einastoHorizonBalance_derivative d l a _).deriv, einastoShape_shifted_critical]
  have hp : 0 < 4 * Real.pi * exp (einastoBalanceCriticalLogRadius l a + u) ^ 2 *
      einastoDensity d l a (exp (einastoBalanceCriticalLogRadius l a + u)) := by
    exact mul_pos (by positivity) (einastoDensity_pos _ _ _ _)
  have he : 1 < exp (exp (-a) * u) ↔ 0 < u := by
    rw [← exp_zero, exp_lt_exp]
    constructor <;> intro h <;> nlinarith [exp_pos (-a)]
  constructor
  · intro h
    apply he.mp
    nlinarith
  · intro h
    have hh := he.mpr h
    exact mul_neg_of_pos_of_neg hp (by linarith)

theorem einastoHorizonBalance_derivative_zero_iff (d l a u : ℝ) :
    deriv (einastoHorizonBalance d l a) (exp (einastoBalanceCriticalLogRadius l a + u)) = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hp := einastoHorizonBalance_derivative_pos_iff d l a u
    have hn := einastoHorizonBalance_derivative_neg_iff d l a u
    rw [h] at hp hn
    have h1 : ¬ u < 0 := fun hh => (lt_irrefl 0) (hp.mpr hh)
    have h2 : ¬ 0 < u := fun hh => (lt_irrefl 0) (hn.mpr hh)
    linarith
  · rintro rfl
    rw [(einastoHorizonBalance_derivative d l a _).deriv, einastoShape_shifted_critical]
    simp

/-- Every polynomial radial weight is dominated by the actual Einasto density tail. -/
theorem einastoDensity_weighted_decay (n : ℕ) (d l a : ℝ) :
    Tendsto (fun t => exp t ^ n * einastoDensity d l a (exp t)) atTop (𝓝 0) := by
  have hz : Tendsto (fun t : ℝ => exp (exp (-a) * (t - l))) atTop atTop :=
    tendsto_exp_atTop.comp ((show Tendsto (fun t : ℝ => t - l) atTop atTop from by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-l) tendsto_id).const_mul_atTop (exp_pos (-a)))
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n : ℝ) * exp a) 1 zero_lt_one).comp hz).const_mul
    (exp (d + (n : ℝ) * l))
  have he (t : ℝ) : exp t ^ n * einastoDensity d l a (exp t) =
      exp (d + (n : ℝ) * l) * (exp (exp (-a) * (t - l)) ^ ((n : ℝ) * exp a) *
        exp (-1 * exp (exp (-a) * (t - l)))) := by
    have hp : exp (exp (-a) * (t - l)) ^ ((n : ℝ) * exp a) = exp ((n : ℝ) * (t - l)) := by
      rw [rpow_def_of_pos (exp_pos _), log_exp]
      congr 1
      rw [exp_neg]
      field_simp
    rw [hp, einastoDensity, ← exp_sub, rpow_def_of_pos (exp_pos _), log_exp]
    rw [show (t - l) * exp (-a) = exp (-a) * (t - l) by ring]
    rw [← exp_nat_mul]
    simp only [← exp_add]
    congr 1
    ring
  simp only [neg_mul, one_mul, mul_zero, Function.comp_def] at h
  simp only [funext he]
  simpa only [neg_mul, one_mul] using h

theorem einastoHorizonBalance_continuous (d l a : ℝ) : Continuous (einastoHorizonBalance d l a) := by
  have hm : Continuous (einastoMass d l a) :=
    (show Differentiable ℝ (einastoMass d l a) from
      fun r => (einastoMass_derivative d l a r).differentiableAt).continuous
  exact (continuous_const.mul ((continuous_id.pow 3).mul (einastoDensity_continuous d l a))).sub hm

theorem einastoHorizonBalance_zero (d l a : ℝ) : einastoHorizonBalance d l a 0 = 0 := by
  simp [einastoHorizonBalance, einastoMass_core]

theorem einastoHorizonBalance_core_limit (d l a : ℝ) :
    Tendsto (fun t => einastoHorizonBalance d l a (exp t)) atBot (𝓝 0) := by
  simpa only [einastoHorizonBalance_zero, Function.comp_def] using
    (einastoHorizonBalance_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoHorizonBalance_infinity_limit (d l a : ℝ) :
    Tendsto (fun t => einastoHorizonBalance d l a (exp t)) atTop
      (𝓝 (-(4 * Real.pi * exp d * exp l ^ 3 * exp a * Gamma (3 * exp a)))) := by
  have h := ((einastoDensity_weighted_decay 3 d l a).const_mul (4 * Real.pi)).sub
    ((einastoMass_total d l a).comp tendsto_exp_atTop)
  simpa only [einastoHorizonBalance, mul_zero, zero_sub, Function.comp_def] using h

/-- The horizon balance increases strictly up to its explicit critical radius. -/
theorem einastoHorizonBalance_strictMono_left (d l a : ℝ) :
    StrictMonoOn (fun t => einastoHorizonBalance d l a (exp t))
      (Iic (einastoBalanceCriticalLogRadius l a)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
    ((einastoHorizonBalance_continuous d l a).comp continuous_exp).continuousOn
  intro x hx
  have hx' : x < einastoBalanceCriticalLogRadius l a := by
    simpa only [interior_Iic, mem_Iio] using hx
  have hp := (einastoHorizonBalance_derivative_pos_iff d l a
    (x - einastoBalanceCriticalLogRadius l a)).mpr (by linarith)
  rw [show einastoBalanceCriticalLogRadius l a + (x - einastoBalanceCriticalLogRadius l a) = x by ring,
    (einastoHorizonBalance_derivative d l a x).deriv] at hp
  rw [((einastoHorizonBalance_derivative d l a x).comp x (hasDerivAt_exp x)).deriv]
  exact mul_pos hp (exp_pos x)

/-- Beyond its explicit critical radius the horizon balance decreases strictly. -/
theorem einastoHorizonBalance_strictAnti_right (d l a : ℝ) :
    StrictAntiOn (fun t => einastoHorizonBalance d l a (exp t))
      (Ici (einastoBalanceCriticalLogRadius l a)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
    ((einastoHorizonBalance_continuous d l a).comp continuous_exp).continuousOn
  intro x hx
  have hx' : einastoBalanceCriticalLogRadius l a < x := by
    simpa only [interior_Ici, mem_Ioi] using hx
  have hp := (einastoHorizonBalance_derivative_neg_iff d l a
    (x - einastoBalanceCriticalLogRadius l a)).mpr (by linarith)
  rw [show einastoBalanceCriticalLogRadius l a + (x - einastoBalanceCriticalLogRadius l a) = x by ring,
    (einastoHorizonBalance_derivative d l a x).deriv] at hp
  rw [((einastoHorizonBalance_derivative d l a x).comp x (hasDerivAt_exp x)).deriv]
  exact mul_neg_of_neg_of_pos hp (exp_pos x)

/-- The balance is strictly positive everywhere up to and including its maximum. -/
theorem einastoHorizonBalance_before_maximum_pos (d l a t : ℝ) :
    0 < einastoHorizonBalance d l a (exp (min t (einastoBalanceCriticalLogRadius l a))) := by
  let s := min t (einastoBalanceCriticalLogRadius l a)
  have hs : s ≤ einastoBalanceCriticalLogRadius l a := min_le_right _ _
  have hmono := einastoHorizonBalance_strictMono_left d l a
  have hnonneg : 0 ≤ einastoHorizonBalance d l a (exp (s - 1)) := by
    apply le_of_tendsto (einastoHorizonBalance_core_limit d l a)
    filter_upwards [eventually_le_atBot (s - 1)] with u hu
    exact hmono.monotoneOn (mem_Iic.mpr (by linarith)) (mem_Iic.mpr (by linarith)) hu
  have hlt := hmono (mem_Iic.mpr (by linarith : s - 1 ≤ einastoBalanceCriticalLogRadius l a))
    (mem_Iic.mpr hs) (by linarith : s - 1 < s)
  exact hnonneg.trans_lt hlt

/-- The balance controlling horizon formation has exactly one zero on the positive-radius branch. -/
theorem einastoHorizonBalance_unique_zero (d l a : ℝ) :
    ∃! t : ℝ, einastoHorizonBalance d l a (exp t) = 0 := by
  let c := einastoBalanceCriticalLogRadius l a
  let q := fun t => einastoHorizonBalance d l a (exp t)
  have hmono := einastoHorizonBalance_strictMono_left d l a
  have hanti := einastoHorizonBalance_strictAnti_right d l a
  have hpos : ∀ t, t ≤ c → 0 < q t := by
    intro t ht
    have ht' : t ≤ einastoBalanceCriticalLogRadius l a := ht
    simpa only [min_eq_left ht'] using einastoHorizonBalance_before_maximum_pos d l a t
  have htotal : 0 < 4 * Real.pi * exp d * exp l ^ 3 * exp a * Gamma (3 * exp a) := by
    have hg := Gamma_pos_of_pos (by positivity : (0 : ℝ) < 3 * exp a)
    positivity
  have hneg : ∀ᶠ t in atTop, q t < 0 :=
    (einastoHorizonBalance_infinity_limit d l a).eventually (eventually_lt_nhds (neg_neg_of_pos htotal))
  obtain ⟨R, hRn, hRc⟩ := (hneg.and (eventually_gt_atTop c)).exists
  have hc : Continuous q := (einastoHorizonBalance_continuous d l a).comp continuous_exp
  obtain ⟨z, hz, hqz⟩ := intermediate_value_Icc' hRc.le hc.continuousOn
    (show (0 : ℝ) ∈ Icc (q R) (q c) from ⟨hRn.le, (hpos c le_rfl).le⟩)
  refine ⟨z, hqz, ?_⟩
  intro y hy
  change q y = 0 at hy
  have hyc : c ≤ y := by
    by_contra h
    have hp := hpos y (not_le.mp h).le
    rw [hy] at hp
    exact lt_irrefl 0 hp
  exact hanti.injOn (mem_Ici.mpr hyc) (mem_Ici.mpr hz.1) (hy.trans hqz.symm)

/-- The unique logarithmic radius where the compactness derivative vanishes. -/
def einastoBalanceZeroLogRadius (d l a : ℝ) : ℝ :=
  Classical.choose (einastoHorizonBalance_unique_zero d l a)

theorem einastoBalanceZeroLogRadius_eq (d l a : ℝ) :
    einastoHorizonBalance d l a (exp (einastoBalanceZeroLogRadius d l a)) = 0 := by
  exact (Classical.choose_spec (einastoHorizonBalance_unique_zero d l a)).1

theorem einastoHorizonBalance_zero_iff (d l a t : ℝ) :
    einastoHorizonBalance d l a (exp t) = 0 ↔ t = einastoBalanceZeroLogRadius d l a := by
  constructor
  · exact (Classical.choose_spec (einastoHorizonBalance_unique_zero d l a)).2 t
  · rintro rfl
    exact einastoBalanceZeroLogRadius_eq d l a

theorem einastoBalanceZeroLogRadius_after_maximum (d l a : ℝ) :
    einastoBalanceCriticalLogRadius l a < einastoBalanceZeroLogRadius d l a := by
  by_contra h
  have ht := not_lt.mp h
  have hp := einastoHorizonBalance_before_maximum_pos d l a (einastoBalanceZeroLogRadius d l a)
  rw [min_eq_left ht, einastoBalanceZeroLogRadius_eq] at hp
  exact lt_irrefl 0 hp

/-- Positive balance holds exactly before its unique zero. -/
theorem einastoHorizonBalance_pos_iff (d l a t : ℝ) :
    0 < einastoHorizonBalance d l a (exp t) ↔ t < einastoBalanceZeroLogRadius d l a := by
  let c := einastoBalanceCriticalLogRadius l a
  let z := einastoBalanceZeroLogRadius d l a
  have hz : c < z := einastoBalanceZeroLogRadius_after_maximum d l a
  have hqz : einastoHorizonBalance d l a (exp z) = 0 := einastoBalanceZeroLogRadius_eq d l a
  have hanti := einastoHorizonBalance_strictAnti_right d l a
  constructor
  · intro hp
    by_contra h
    have hzt : z ≤ t := not_lt.mp h
    have hh := hanti.antitoneOn (mem_Ici.mpr hz.le) (mem_Ici.mpr (hz.le.trans hzt)) hzt
    simp only [hqz] at hh
    linarith
  · intro htz
    by_cases htc : t ≤ c
    · have ht' : t ≤ einastoBalanceCriticalLogRadius l a := htc
      simpa only [min_eq_left ht'] using einastoHorizonBalance_before_maximum_pos d l a t
    · have hct := (not_le.mp htc).le
      have hh := hanti (mem_Ici.mpr hct) (mem_Ici.mpr hz.le) htz
      simp only [hqz] at hh
      exact hh

/-- Negative balance holds exactly after its unique zero. -/
theorem einastoHorizonBalance_neg_iff (d l a t : ℝ) :
    einastoHorizonBalance d l a (exp t) < 0 ↔ einastoBalanceZeroLogRadius d l a < t := by
  let c := einastoBalanceCriticalLogRadius l a
  let z := einastoBalanceZeroLogRadius d l a
  have hz : c < z := einastoBalanceZeroLogRadius_after_maximum d l a
  have hqz : einastoHorizonBalance d l a (exp z) = 0 := einastoBalanceZeroLogRadius_eq d l a
  constructor
  · intro hn
    by_contra h
    rcases lt_or_eq_of_le (not_lt.mp h) with ht | ht
    · have hp := (einastoHorizonBalance_pos_iff d l a t).mpr ht
      linarith
    · rw [ht, hqz] at hn
      exact lt_irrefl 0 hn
  · intro hzt
    have hh := einastoHorizonBalance_strictAnti_right d l a
      (mem_Ici.mpr hz.le) (mem_Ici.mpr (hz.le.trans hzt.le)) hzt
    simp only [hqz] at hh
    exact hh

end GaloisForLFunctions.HTGeometry
