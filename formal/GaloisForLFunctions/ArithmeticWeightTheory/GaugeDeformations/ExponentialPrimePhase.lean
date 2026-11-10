import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.LiouvilleBoundaryPath

/-!
# Exponentially damped Liouville phases

The entire prime coordinates `exp(-iπ exp(-z log p))` approach Liouville
at zero. Every positive real parameter has summable prime perturbations
below one. The first Taylor remainder has twice the prime decay rate;
this separates the first moving prime-logarithm singularity.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Entire prime phases, with Liouville value at zero. -/
def exponentialPrimePhase (p : Nat.Primes) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * I * Complex.exp (-z * (Real.log (p : ℝ) : ℂ)))

/-- Actual real gauge of the exponentially damped phases. -/
def exponentialPhaseGauge (t : ℝ) : GaugeTorus :=
  linearPhaseGauge (fun p => -Real.pi * Real.exp (-t * Real.log (p : ℝ))) 1

theorem exponentialPrimePhase_zero (p : Nat.Primes) : exponentialPrimePhase p 0 = -1 := by
  simp only [exponentialPrimePhase, neg_zero, zero_mul, Complex.exp_zero, mul_one, neg_mul,
    Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

theorem exponentialPrimePhase_eq_twist (t : ℝ) (p : Nat.Primes) :
    exponentialPrimePhase p (t : ℂ) = twist (exponentialPhaseGauge t) p := by
  rw [exponentialPhaseGauge, twist_linearPhaseGauge_prime]
  simp only [exponentialPrimePhase, linearPrimePhase, ofReal_mul, ofReal_neg, ofReal_one,
    ofReal_exp, mul_one]
  congr 1
  ring

theorem differentiable_exponentialPrimePhase (p : Nat.Primes) :
    Differentiable ℂ (exponentialPrimePhase p) := by
  unfold exponentialPrimePhase
  fun_prop

/-- The inner exponential has exactly the expected prime decay. -/
theorem norm_exponentialPrime_damping (p : Nat.Primes) (z : ℂ) :
    ‖Complex.exp (-z * (Real.log (p : ℝ) : ℂ))‖ = (p : ℝ) ^ (-z.re) := by
  rw [Complex.norm_exp, Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

private theorem norm_exponentialPrime_argument (p : Nat.Primes) (z : ℂ) :
    ‖-(Real.pi : ℂ) * I * Complex.exp (-z * (Real.log (p : ℝ) : ℂ))‖ =
      Real.pi * (p : ℝ) ^ (-z.re) := by
  rw [norm_mul, norm_mul, norm_neg, norm_I, mul_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_exponentialPrime_damping]

theorem norm_exponentialPrimePhase_le (p : Nat.Primes) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖exponentialPrimePhase p z‖ ≤ Real.exp Real.pi := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_exponentialPrime_argument]
  have hp : (p : ℝ) ^ (-z.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr hz)
  nlinarith only [hp, Real.pi_pos]

/-- Uniform decay on every right half-plane of parameters. -/
theorem norm_exponentialPrimePhase_sub_one_le (p : Nat.Primes) {δ : ℝ} (hδ : 0 ≤ δ)
    {z : ℂ} (hz : δ ≤ z.re) :
    ‖exponentialPrimePhase p z - 1‖ ≤
      (Real.pi * Real.exp Real.pi) * (p : ℝ) ^ (-δ) := by
  have hp : (p : ℝ) ^ (-z.re) ≤ (p : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (neg_le_neg hz)
  have hδp : (p : ℝ) ^ (-δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr hδ)
  have hn : ‖-(Real.pi : ℂ) * I * Complex.exp (-z * (Real.log (p : ℝ) : ℂ))‖ ≤
      Real.pi * (p : ℝ) ^ (-δ) := by
    rw [norm_exponentialPrime_argument]
    exact mul_le_mul_of_nonneg_left hp Real.pi_pos.le
  have hnπ : ‖-(Real.pi : ℂ) * I * Complex.exp (-z * (Real.log (p : ℝ) : ℂ))‖ ≤ Real.pi :=
    hn.trans (by nlinarith only [hδp, Real.pi_pos])
  exact (FiniteFreeProbability.norm_exp_sub_one_le_mul_exp _).trans
    ((mul_le_mul hn (Real.exp_le_exp.mpr hnπ) (Real.exp_pos _).le
      (by positivity)).trans_eq (by ring))

/-- Real phases give the sharper constant π. -/
theorem norm_exponentialPrimePhase_real_sub_one_le (p : Nat.Primes) (t : ℝ) :
    ‖exponentialPrimePhase p (t : ℂ) - 1‖ ≤ Real.pi * (p : ℝ) ^ (-t) := by
  have he : exponentialPrimePhase p (t : ℂ) =
      Complex.exp (I * ((-Real.pi * Real.exp (-t * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
    simp only [exponentialPrimePhase, ofReal_mul, ofReal_neg, ofReal_exp]
    congr 1
    ring
  rw [he]
  convert Real.norm_exp_I_mul_ofReal_sub_one_le (x := -Real.pi * Real.exp (-t * Real.log (p : ℝ))) using 1
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
    abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]
  congr 2
  ring

/-- The real perturbation is absolutely summable as soon as `σ+t>1`. -/
theorem exponentialPhase_prime_summability {t σ : ℝ} (h : 1 < σ + t) :
    Summable (fun p : Nat.Primes => ‖twist (exponentialPhaseGauge t) p - 1‖ *
      (p : ℝ) ^ (-σ)) := by
  have hs := (summable_primes_rpow (show -(σ + t) < -1 by linarith only [h])).mul_left Real.pi
  apply hs.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (by positivity))
  intro p
  rw [← exponentialPrimePhase_eq_twist]
  calc
    _ ≤ (Real.pi * (p : ℝ) ^ (-t)) * (p : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (norm_exponentialPrimePhase_real_sub_one_le p t) (by positivity)
    _ = Real.pi * (p : ℝ) ^ (-(σ + t)) := by
      rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast p.2.pos)]
      congr 2
      ring

/-- Every positive parameter has an isozeric continuation strictly left of one. -/
theorem exponentialPhase_isozeric {t : ℝ} (ht : 0 < t) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      AnalyticOnNhd ℂ (deformationExponent (exponentialPhaseGauge t)) {s | σ < s.re} ∧
      ∀ s : ℂ, 1 < s.re → gaugeFibre (exponentialPhaseGauge t) s =
        riemannZeta s * Complex.exp (deformationExponent (exponentialPhaseGauge t) s) := by
  let δ := min (t / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (by linarith only [ht]) (by norm_num)
  have hδt : δ ≤ t / 2 := min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hσ : 1 / 2 < 1 - δ := by linarith only [hδ4]
  refine ⟨1 - δ, hσ, by linarith only [hδ], ?_⟩
  exact exists_isozeric hσ.le
    (exponentialPhase_prime_summability (by linarith only [hδt, ht]))


/-- Removing the first phase term doubles the prime decay rate. -/
theorem norm_exponentialPrimePhase_remainder_le (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ‖exponentialPrimePhase p (t : ℂ) - 1 +
      (Real.pi : ℂ) * I * Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))‖ ≤
      (Real.pi ^ 2 * Real.exp Real.pi) * (p : ℝ) ^ (-(2 * t)) := by
  let a : ℂ := -(Real.pi : ℂ) * I * Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))
  have hn : ‖a‖ = Real.pi * (p : ℝ) ^ (-t) := norm_exponentialPrime_argument p (t : ℂ)
  have hp : (p : ℝ) ^ (-t) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr ht)
  have ha : ‖a‖ ≤ Real.pi := by rw [hn]; nlinarith only [hp, Real.pi_pos]
  have he : exponentialPrimePhase p (t : ℂ) - 1 +
      (Real.pi : ℂ) * I * Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)) =
      Complex.exp a - ∑ m ∈ Finset.range 2, a ^ m / (m.factorial : ℂ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add]
    dsimp [a, exponentialPrimePhase]
    ring
  rw [he]
  calc
    _ ≤ ‖a‖ ^ 2 * Real.exp ‖a‖ := Complex.norm_exp_sub_sum_le_norm_mul_exp a 2
    _ ≤ ‖a‖ ^ 2 * Real.exp Real.pi :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (sq_nonneg _)
    _ = _ := by
      rw [hn, mul_pow, pow_two ((p : ℝ) ^ (-t)),
        ← Real.rpow_add (by exact_mod_cast p.2.pos)]
      rw [show -t + -t = -(2 * t) by ring]
      ring

/-- Prime Dirichlet remainder after the first shifted prime-zeta term. -/
def exponentialPhasePrimeRemainder (t : ℝ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (exponentialPrimePhase p (t : ℂ) - 1 +
    (Real.pi : ℂ) * I * Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) *
      Complex.exp (-s * (Real.log (p : ℝ) : ℂ))

private theorem summable_exponentialPhase_remainder_majorant {t σ : ℝ}
    (h : 1 < σ + 2 * t) :
    Summable (fun p : Nat.Primes =>
      (Real.pi ^ 2 * Real.exp Real.pi) * (p : ℝ) ^ (-(2 * t)) * (p : ℝ) ^ (-σ)) := by
  have hs := (summable_primes_rpow (show -(σ + 2 * t) < -1 by linarith only [h])).mul_left
    (Real.pi ^ 2 * Real.exp Real.pi)
  refine hs.congr (fun p => ?_)
  symm
  rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast p.2.pos)]
  congr 2
  ring

/-- The first remainder extends across `Re s=1-t`, down to `Re s>1-2t`. -/
theorem analyticOnNhd_exponentialPhasePrimeRemainder {t : ℝ} (ht : 0 ≤ t) :
    AnalyticOnNhd ℂ (exponentialPhasePrimeRemainder t) {s | 1 < s.re + 2 * t} := by
  intro s hs
  change 1 < s.re + 2 * t at hs
  let σ := (1 - 2 * t + s.re) / 2
  have hσ : 1 < σ + 2 * t := by dsimp [σ]; linarith only [hs]
  have hσs : σ < s.re := by dsimp [σ]; linarith only [hs]
  have ho : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (exponentialPhasePrimeRemainder t) {w | σ < w.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_exponentialPhase_remainder_majorant hσ) (fun p => ?_) ho (fun p w hw => ?_)
    · intro w hw
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
    · rw [norm_mul, norm_exponentialPrime_damping]
      apply mul_le_mul (norm_exponentialPrimePhase_remainder_le p ht) ?_
        (by positivity) (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (neg_le_neg hw.le)
  exact hd.analyticAt (ho.mem_nhds hσs)


/-- Positive parameters admit an actual joint pole germ. -/
theorem exponentialPhase_interior_poles {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ (jointGaugeRegularization exponentialPrimePhase) ((t : ℂ), 1) ∧
      jointGaugeRegularization exponentialPrimePhase ((t : ℂ), 1) ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re →
        jointGaugeRegularization exponentialPrimePhase ((t : ℂ), s) =
          (s - 1) * gaugeFibre (exponentialPhaseGauge t) s := by
  let r := min (t / 4) (1 / 8)
  have hr : 0 < r := lt_min (by linarith only [ht]) (by norm_num)
  have hrt : r ≤ t / 4 := min_le_left _ _
  have hr8 : r ≤ 1 / 8 := min_le_right _ _
  let v : Nat.Primes → ℂ → ℂ := fun p z => exponentialPrimePhase p (z + (t : ℂ))
  have hshift {z : ℂ} (hz : ‖z‖ ≤ 2 * r) : 2 * r ≤ (z + (t : ℂ)).re := by
    have hneg := Complex.re_le_norm (-z)
    simp only [Complex.neg_re, norm_neg] at hneg
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hneg, hz, hrt]
  have hb (p : Nat.Primes) (z : ℂ) (hz : z ∈ ball (0 : ℂ) (2 * r)) :
      ‖v p z‖ ≤ Real.exp Real.pi := by
    apply norm_exponentialPrimePhase_le
    have h := hshift (show ‖z‖ ≤ 2 * r by
      exact (show ‖z‖ < 2 * r by simpa only [mem_ball, dist_zero_right] using hz).le)
    linarith only [h, hr]
  have hsum : Summable (fun p => primeDiskDeviation v r p * (p : ℝ) ^ (-(1 - r))) := by
    have hmaj := (summable_primes_rpow (show -(1 + r) < -1 by linarith only [hr])).mul_left
      (Real.pi * Real.exp Real.pi)
    apply hmaj.of_nonneg_of_le (fun p => mul_nonneg
      (primeDiskDeviation_bounds hr.le (by linarith only [hr]) hb p).1 (by positivity))
    intro p
    have hsup : primeDiskDeviation v r p ≤
        (Real.pi * Real.exp Real.pi) * (p : ℝ) ^ (-(2 * r)) := by
      apply csSup_le
      · exact ⟨_, ⟨0, mem_closedBall_self hr.le, rfl⟩⟩
      rintro b ⟨z, hz, rfl⟩
      apply norm_exponentialPrimePhase_sub_one_le p (by positivity)
      apply hshift
      have hzr : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
      linarith only [hzr, hr]
    calc
      _ ≤ ((Real.pi * Real.exp Real.pi) * (p : ℝ) ^ (-(2 * r))) *
          (p : ℝ) ^ (-(1 - r)) := mul_le_mul_of_nonneg_right hsup (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast p.2.pos)]
        congr 2
        ring
  have hv (p : Nat.Primes) : DifferentiableOn ℂ (v p) (ball 0 (2 * r)) := by
    exact ((differentiable_exponentialPrimePhase p).comp
      (differentiable_id.add_const (t : ℂ))).differentiableOn
  have hv0 (p : Nat.Primes) : ‖v p 0‖ ≤ 1 := by
    dsimp [v]
    rw [zero_add, exponentialPrimePhase_eq_twist, norm_twist_prime _ p p.2]
  obtain ⟨ρ, b, hρ, _, _, _, _, hW⟩ := exists_jointEuler_normal_form
    (by positivity : 0 < 2 * r) hr (by linarith only [hr])
    (by linarith only [hr8] : (1 / 2 : ℝ) < 1 - r) hv hb hv0 hsum
  have hW0 : AnalyticAt ℂ (jointGaugeRegularization v) ((t : ℂ) - (t : ℂ), 1) := by
    rw [sub_self]
    exact hW (0, 1) ⟨by simpa only [norm_zero] using hρ, by change 1 - r < 1; linarith only [hr]⟩
  have hmap : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.1 - (t : ℂ), q.2)) ((t : ℂ), 1) :=
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).sub analyticAt_const).prod
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _)
  have heq : (fun q : ℂ × ℂ => jointGaugeRegularization v (q.1 - (t : ℂ), q.2)) =
      jointGaugeRegularization exponentialPrimePhase := by
    funext q
    simp only [jointGaugeRegularization, jointDeformationExponent, jointEulerChange, v,
      sub_add_cancel]
  refine ⟨?_, ?_, fun s hs => jointGaugeRegularization_eq_gaugeFibre
    (exponentialPrimePhase_eq_twist t) hs⟩
  · have h := hW0.comp (f := fun q : ℂ × ℂ => (q.1 - (t : ℂ), q.2)) hmap
    change AnalyticAt ℂ (fun q : ℂ × ℂ => jointGaugeRegularization v (q.1 - (t : ℂ), q.2))
      ((t : ℂ), 1) at h
    rwa [heq] at h
  · rw [jointGaugeRegularization, zetaResidueFactor_one, one_mul]
    exact Complex.exp_ne_zero _

/-- Absolute convergence of the first phase remainder in its larger half-plane. -/
theorem summable_exponentialPhasePrimeRemainder {t : ℝ} (ht : 0 ≤ t) {s : ℂ}
    (hs : 1 < s.re + 2 * t) :
    Summable (fun p : Nat.Primes => (exponentialPrimePhase p (t : ℂ) - 1 +
      (Real.pi : ℂ) * I * Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) *
        Complex.exp (-s * (Real.log (p : ℝ) : ℂ))) := by
  apply Summable.of_norm
  apply (summable_exponentialPhase_remainder_majorant hs).of_nonneg_of_le
    (fun p => norm_nonneg _)
  intro p
  rw [norm_mul, norm_exponentialPrime_damping]
  exact mul_le_mul_of_nonneg_right (norm_exponentialPrimePhase_remainder_le p ht) (by positivity)

#print axioms exponentialPhase_interior_poles
#print axioms analyticOnNhd_exponentialPhasePrimeRemainder

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
