import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingJet
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ExponentialPrimePhase

/-!
# Analytic profiles of prime phases

A profile analytic on a disc larger than the unit disc gives normally
summable prime perturbations at every positive parameter. Its first
nonzero jet determines the precise half-plane of prime summability.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- A fixed analytic profile evaluated at a damped prime coordinate. -/
def analyticSmoothingPrimePhase (Φ : ℂ → ℂ) (p : Nat.Primes) (z : ℂ) : ℂ :=
  Φ (Complex.exp (-z * (Real.log (p : ℝ) : ℂ)))

/-- The actual real gauge determined by the arguments of the prime phases. -/
def analyticSmoothingGauge (Φ : ℂ → ℂ) (t : ℝ) : GaugeTorus :=
  linearPhaseGauge (fun p => (analyticSmoothingPrimePhase Φ p (t : ℂ)).arg) 1

theorem analyticSmoothingPrimePhase_zero (Φ : ℂ → ℂ) (p : Nat.Primes) :
    analyticSmoothingPrimePhase Φ p 0 = Φ 1 := by
  simp only [analyticSmoothingPrimePhase, neg_zero, zero_mul, Complex.exp_zero]

theorem norm_analyticSmoothingPrimePhase_real {Φ : ℂ → ℂ}
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) :
    ‖analyticSmoothingPrimePhase Φ p (t : ℂ)‖ = 1 := by
  have hp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.2.one_le)
  have hx : Real.exp (-t * Real.log (p : ℝ)) ∈ Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hp)⟩
  simpa only [analyticSmoothingPrimePhase, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp] using hunit _ hx

theorem analyticSmoothingPrimePhase_eq_twist {Φ : ℂ → ℂ}
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) :
    analyticSmoothingPrimePhase Φ p (t : ℂ) = twist (analyticSmoothingGauge Φ t) p := by
  rw [analyticSmoothingGauge, twist_linearPhaseGauge_prime]
  simp only [linearPrimePhase, Complex.ofReal_one, mul_one]
  have hh := Complex.norm_mul_exp_arg_mul_I (analyticSmoothingPrimePhase Φ p (t : ℂ))
  rw [norm_analyticSmoothingPrimePhase_real hunit ht p, Complex.ofReal_one, one_mul] at hh
  exact hh.symm

private theorem norm_dampedPrime_le_one (p : Nat.Primes) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.exp (-z * (Real.log (p : ℝ) : ℂ))‖ ≤ 1 := by
  rw [norm_exponentialPrime_damping]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr hz)

/-- Each prime coordinate is analytic throughout the closed right half-plane of parameters. -/
theorem analyticAt_analyticSmoothingPrimePhase {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (p : Nat.Primes) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (analyticSmoothingPrimePhase Φ p) z := by
  have hm : Complex.exp (-z * (Real.log (p : ℝ) : ℂ)) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right]
    exact (norm_dampedPrime_le_one p hz).trans hR.le
  exact (hΦ _ hm).comp (f := fun z : ℂ => Complex.exp (-z * (Real.log (p : ℝ) : ℂ)))
    ((analyticAt_id.neg.mul analyticAt_const).cexp)

/-- One compact profile bound controls every prime in the right parameter half-plane. -/
theorem analyticSmoothingPrimePhase_uniform_bound {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z‖ ≤ M := by
  have hc := hΦ.continuousOn.mono (Metric.closedBall_subset_closedBall hR.le)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun p z hz => ?_⟩
  exact (hM _ (by simpa only [mem_closedBall, dist_zero_right] using
    norm_dampedPrime_le_one p hz)).trans (le_max_left _ _)

/-- Powers of a damped prime coordinate multiply its real decay exponent. -/
theorem norm_dampedPrime_pow (p : Nat.Primes) (z : ℂ) (m : ℕ) :
    ‖Complex.exp (-z * (Real.log (p : ℝ) : ℂ))‖ ^ m =
      (p : ℝ) ^ (-((m : ℝ) * z.re)) := by
  rw [← norm_pow, ← Complex.exp_nat_mul]
  have he : (m : ℂ) * (-z * (Real.log (p : ℝ) : ℂ)) =
      -((m : ℂ) * z) * (Real.log (p : ℝ) : ℂ) := by ring
  rw [he, norm_exponentialPrime_damping]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]

/-- An exact vanishing factor supplies uniform prime decay at its order. -/
theorem analyticSmoothingPrimePhase_decay_of_factor {Φ G : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hG : AnalyticOnNhd ℂ G (closedBall 0 R)) {m : ℕ}
    (hfac : ∀ z : ℂ, Φ z - 1 = z ^ m * G z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ C * (p : ℝ) ^ (-((m : ℝ) * z.re)) := by
  have hc := hG.continuousOn.mono (Metric.closedBall_subset_closedBall hR.le)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun p z hz => ?_⟩
  have hb : ‖G (Complex.exp (-z * (Real.log (p : ℝ) : ℂ)))‖ ≤ max C 0 :=
    (hC _ (by simpa only [mem_closedBall, dist_zero_right] using
      norm_dampedPrime_le_one p hz)).trans (le_max_left _ _)
  rw [analyticSmoothingPrimePhase, hfac, norm_mul, norm_pow, norm_dampedPrime_pow]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (mul_comm _ _)

/-- The prime remainder after removing the leading Taylor coefficient. -/
def analyticSmoothingPrimeRemainder (Φ : ℂ → ℂ) (m : ℕ) (a : ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (analyticSmoothingPrimePhase Φ p (t : ℂ) - 1 -
    a * Complex.exp (-((m : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))) *
      Complex.exp (-s * (Real.log (p : ℝ) : ℂ))

/-- The profile remainder gains one full prime-decay order. -/
theorem analyticSmoothingPrimeRemainder_bound {Φ : ℂ → ℂ} {m : ℕ} {a : ℂ} {C : ℝ}
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - a * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1))
    (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ‖analyticSmoothingPrimePhase Φ p (t : ℂ) - 1 -
      a * Complex.exp (-((m : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))‖ ≤
      C * (p : ℝ) ^ (-(((m : ℝ) + 1) * t)) := by
  have hh := hC (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)))
    (norm_dampedPrime_le_one p ht)
  rw [norm_dampedPrime_pow] at hh
  rw [← Complex.exp_nat_mul, show (m : ℂ) * (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)) =
    -((m : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ) by ring] at hh
  simpa only [Nat.cast_add, Nat.cast_one, Complex.ofReal_re, analyticSmoothingPrimePhase] using hh

/-- A product of two prime powers is summable beyond its combined abscissa. -/
private theorem summable_smoothing_majorant {q σ : ℝ} (h : 1 < σ + q) (C : ℝ) :
    Summable (fun p : Nat.Primes => C * (p : ℝ) ^ (-q) * (p : ℝ) ^ (-σ)) := by
  have hs := (summable_primes_rpow (show -(σ + q) < -1 by linarith only [h])).mul_left C
  refine hs.congr (fun p => ?_)
  symm
  rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast p.2.pos)]
  congr 2
  ring

/-- A normally bounded profile remainder gives a larger analytic spectral half-plane. -/
theorem analyticOnNhd_analyticSmoothingPrimeRemainder {Φ : ℂ → ℂ} {m : ℕ} {a : ℂ} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - a * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticOnNhd ℂ (analyticSmoothingPrimeRemainder Φ m a t)
      {s | 1 < s.re + ((m : ℝ) + 1) * t} := by
  intro s hs
  change 1 < s.re + ((m : ℝ) + 1) * t at hs
  let σ := (1 - ((m : ℝ) + 1) * t + s.re) / 2
  have hσ : 1 < σ + ((m : ℝ) + 1) * t := by dsimp [σ]; linarith only [hs]
  have hσs : σ < s.re := by dsimp [σ]; linarith only [hs]
  have ho : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (analyticSmoothingPrimeRemainder Φ m a t) {w | σ < w.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_smoothing_majorant hσ C) (fun p => ?_) ho (fun p w hw => ?_)
    · intro w hw
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
    · rw [norm_mul, norm_exponentialPrime_damping]
      apply mul_le_mul (analyticSmoothingPrimeRemainder_bound hC p ht) ?_
        (by positivity) (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (neg_le_neg hw.le)
  exact hd.analyticAt (ho.mem_nhds hσs)

theorem summable_analyticSmoothingPrimeRemainder {Φ : ℂ → ℂ} {m : ℕ} {a : ℂ} {C : ℝ}
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - a * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1))
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re + ((m : ℝ) + 1) * t) :
    Summable (fun p : Nat.Primes => (analyticSmoothingPrimePhase Φ p (t : ℂ) - 1 -
      a * Complex.exp (-((m : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))) *
        Complex.exp (-s * (Real.log (p : ℝ) : ℂ))) := by
  apply Summable.of_norm
  apply (summable_smoothing_majorant hs C).of_nonneg_of_le (fun p => norm_nonneg _)
  intro p
  rw [norm_mul, norm_exponentialPrime_damping]
  exact mul_le_mul_of_nonneg_right (analyticSmoothingPrimeRemainder_bound hC p ht) (by positivity)


/-- Uniform prime decay gives absolute convergence of the actual gauge perturbation. -/
theorem analyticSmoothing_prime_summability_of_decay {Φ : ℂ → ℂ} {m : ℕ} {C : ℝ}
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (hdecay : ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ C * (p : ℝ) ^ (-((m : ℝ) * z.re)))
    {t σ : ℝ} (ht : 0 ≤ t) (h : 1 < σ + (m : ℝ) * t) :
    Summable (fun p : Nat.Primes => ‖twist (analyticSmoothingGauge Φ t) p - 1‖ *
      (p : ℝ) ^ (-σ)) := by
  apply (summable_smoothing_majorant h C).of_nonneg_of_le
    (fun p => mul_nonneg (norm_nonneg _) (by positivity))
  intro p
  rw [← analyticSmoothingPrimePhase_eq_twist hunit ht]
  exact mul_le_mul_of_nonneg_right (hdecay p (t : ℂ) ht) (by positivity)

/-- Every positive smoothing parameter has an actual joint pole with nonzero residue. -/
theorem analyticSmoothing_interior_poles {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ (jointGaugeRegularization (analyticSmoothingPrimePhase Φ)) ((t : ℂ), 1) ∧
      jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), 1) ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re →
        jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), s) =
          (s - 1) * gaugeFibre (analyticSmoothingGauge Φ t) s := by
  obtain ⟨m, hm, b, hb, G, hG, hG0, hfac, hcoeff, hbelow, C', hC', hrem⟩ :=
    analyticPhase_first_jet hR hΦ h0 h1 hunit
  obtain ⟨C, hC, hdecay⟩ := analyticSmoothingPrimePhase_decay_of_factor hR hG hfac
  obtain ⟨M, hM, hbound⟩ := analyticSmoothingPrimePhase_uniform_bound hR hΦ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let r := min (t / 4) (1 / 8)
  have hr : 0 < r := lt_min (by linarith only [ht]) (by norm_num)
  have hrt : r ≤ t / 4 := min_le_left _ _
  have hr8 : r ≤ 1 / 8 := min_le_right _ _
  let v : Nat.Primes → ℂ → ℂ := fun p z => analyticSmoothingPrimePhase Φ p (z + (t : ℂ))
  have hshift {z : ℂ} (hz : ‖z‖ ≤ 2 * r) : 2 * r ≤ (z + (t : ℂ)).re := by
    have hneg := Complex.re_le_norm (-z)
    simp only [Complex.neg_re, norm_neg] at hneg
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hneg, hz, hrt]
  have hright {z : ℂ} (hz : z ∈ ball (0 : ℂ) (2 * r)) : 0 ≤ (z + (t : ℂ)).re := by
    have hh := hshift (show ‖z‖ ≤ 2 * r by
      exact (show ‖z‖ < 2 * r by simpa only [mem_ball, dist_zero_right] using hz).le)
    linarith only [hh, hr]
  have hb (p : Nat.Primes) (z : ℂ) (hz : z ∈ ball (0 : ℂ) (2 * r)) : ‖v p z‖ ≤ M :=
    hbound p _ (hright hz)
  have hsum : Summable (fun p => primeDiskDeviation v r p * (p : ℝ) ^ (-(1 - r))) := by
    have hmaj := summable_smoothing_majorant
      (show 1 < (1 - r) + 2 * r by linarith only [hr]) C
    apply hmaj.of_nonneg_of_le (fun p => mul_nonneg
      (primeDiskDeviation_bounds hr.le (by linarith only [hr]) hb p).1 (by positivity))
    intro p
    have hsup : primeDiskDeviation v r p ≤ C * (p : ℝ) ^ (-(2 * r)) := by
      apply csSup_le
      · exact ⟨_, ⟨0, mem_closedBall_self hr.le, rfl⟩⟩
      rintro c ⟨z, hz, rfl⟩
      have hzr : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
      have hz2 := hshift (show ‖z‖ ≤ 2 * r by linarith only [hzr, hr])
      have hz0 : 0 ≤ (z + (t : ℂ)).re := by linarith only [hz2, hr]
      apply (hdecay p (z + (t : ℂ)) hz0).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
      have hmul := mul_le_mul_of_nonneg_right hm1 hz0
      linarith only [hmul, hz2]
    exact mul_le_mul_of_nonneg_right hsup (by positivity)
  have hv (p : Nat.Primes) : DifferentiableOn ℂ (v p) (ball 0 (2 * r)) := by
    intro z hz
    exact ((analyticAt_analyticSmoothingPrimePhase hR hΦ p (hright hz)).comp
      (f := fun z : ℂ => z + (t : ℂ)) (analyticAt_id.add analyticAt_const)).differentiableAt.differentiableWithinAt
  have hv0 (p : Nat.Primes) : ‖v p 0‖ ≤ 1 := by
    dsimp [v]
    rw [zero_add, norm_analyticSmoothingPrimePhase_real hunit ht.le p]
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
      jointGaugeRegularization (analyticSmoothingPrimePhase Φ) := by
    funext q
    simp only [jointGaugeRegularization, jointDeformationExponent, jointEulerChange, v,
      sub_add_cancel]
  refine ⟨?_, ?_, fun s hs => jointGaugeRegularization_eq_gaugeFibre
    (analyticSmoothingPrimePhase_eq_twist hunit ht.le) hs⟩
  · have hh := hW0.comp (f := fun q : ℂ × ℂ => (q.1 - (t : ℂ), q.2)) hmap
    change AnalyticAt ℂ (fun q : ℂ × ℂ => jointGaugeRegularization v (q.1 - (t : ℂ), q.2))
      ((t : ℂ), 1) at hh
    rwa [heq] at hh
  · rw [jointGaugeRegularization, zetaResidueFactor_one, one_mul]
    exact Complex.exp_ne_zero _

#print axioms analyticSmoothing_interior_poles
#print axioms analyticOnNhd_analyticSmoothingPrimeRemainder

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
