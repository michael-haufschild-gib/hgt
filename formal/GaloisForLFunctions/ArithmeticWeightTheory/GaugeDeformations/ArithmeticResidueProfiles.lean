import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ResidueProfileFourier
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticPrimeSmoothing

/-!
# Actual prime phases from residue-class profiles

Reduced residue classes select the unramified profiles; the finitely many
prime divisors of the modulus have independent profiles. Unit prime values
define an actual multiplicative gauge. The higher-prime-power remainder is
jointly continuous down to the common Liouville endpoint.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
variable {q : ℕ} [NeZero q]

/-- Exactly the prime divisors of the positive modulus. -/
def residueRamifiedPrimes (q : ℕ) : Finset Nat.Primes :=
  ((Finset.range (q + 1)).subtype Nat.Prime).filter (fun p => (p : ℕ) ∣ q)

theorem mem_residueRamifiedPrimes (p : Nat.Primes) :
    p ∈ residueRamifiedPrimes q ↔ (p : ℕ) ∣ q := by
  simp only [residueRamifiedPrimes, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact Finset.mem_subtype.mpr (Finset.mem_range.mpr
    (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) h)))

theorem residuePrime_not_isUnit (p : Nat.Primes) :
    ¬ IsUnit ((p : ℕ) : ZMod q) ↔ (p : ℕ) ∣ q := by
  rw [ZMod.isUnit_iff_coprime, p.2.coprime_iff_not_dvd, not_not]

/-- Each prime uses its reduced residue profile, or its own ramified profile. -/
def residuePrimeProfile (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ)
    (p : Nat.Primes) : ℂ → ℂ :=
  if h : IsUnit ((p : ℕ) : ZMod q) then Φ h.unit else ρ p

theorem residuePrimeProfile_of_ramified (Φ : (ZMod q)ˣ → ℂ → ℂ)
    (ρ : Nat.Primes → ℂ → ℂ) (p : Nat.Primes) (hp : (p : ℕ) ∣ q) :
    residuePrimeProfile Φ ρ p = ρ p := by
  rw [residuePrimeProfile, dif_neg ((residuePrime_not_isUnit p).mpr hp)]

theorem analyticOnNhd_residuePrimeProfile {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal}
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R)) (p : Nat.Primes) :
    AnalyticOnNhd ℂ (residuePrimeProfile Φ ρ p) (closedBall 0 R) := by
  unfold residuePrimeProfile
  split_ifs with h
  · exact hΦ h.unit
  · exact hρ p ((residuePrime_not_isUnit p).mp h)

theorem residuePrimeProfile_zero {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (h0 : ∀ a, Φ a 0 = 1) (hρ0 : ∀ p, (p : ℕ) ∣ q → ρ p 0 = 1) (p : Nat.Primes) :
    residuePrimeProfile Φ ρ p 0 = 1 := by
  unfold residuePrimeProfile
  split_ifs with h
  · exact h0 h.unit
  · exact hρ0 p ((residuePrime_not_isUnit p).mp h)

theorem residuePrimeProfile_one {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (h1 : ∀ a, Φ a 1 = -1) (hρ1 : ∀ p, (p : ℕ) ∣ q → ρ p 1 = -1) (p : Nat.Primes) :
    residuePrimeProfile Φ ρ p 1 = -1 := by
  unfold residuePrimeProfile
  split_ifs with h
  · exact h1 h.unit
  · exact hρ1 p ((residuePrime_not_isUnit p).mp h)

theorem norm_residuePrimeProfile {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    (p : Nat.Primes) {x : ℝ} (hx : x ∈ Icc 0 1) : ‖residuePrimeProfile Φ ρ p (x : ℂ)‖ = 1 := by
  unfold residuePrimeProfile
  split_ifs with h
  · exact hu h.unit x hx
  · exact hρu p ((residuePrime_not_isUnit p).mp h) x hx

/-- Only prime values are used; the values at composites carry no multiplicativity claim. -/
def residuePrimeValue (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ)
    (t : ℝ) (n : ℕ) : ℂ :=
  if hp : n.Prime then
    analyticSmoothingPrimePhase (residuePrimeProfile Φ ρ ⟨n, hp⟩) ⟨n, hp⟩ (t : ℂ)
  else 0

theorem residuePrimeValue_prime (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ)
    (t : ℝ) (p : Nat.Primes) : residuePrimeValue Φ ρ t p =
      analyticSmoothingPrimePhase (residuePrimeProfile Φ ρ p) p (t : ℂ) := by
  simp only [residuePrimeValue, dif_pos p.2]

/-- The multiplicative gauge determined by the selected unit prime phases. -/
def residueProfileGauge (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ) (t : ℝ) : GaugeTorus :=
  linearPhaseGauge (fun p => (residuePrimeValue Φ ρ t p).arg) 1

theorem norm_residuePrimeValue {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) : ‖residuePrimeValue Φ ρ t p‖ = 1 := by
  rw [residuePrimeValue_prime]
  exact norm_analyticSmoothingPrimePhase_real (fun x hx => norm_residuePrimeProfile hu hρu p hx) ht p

theorem residuePrimeValue_eq_twist {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) :
    residuePrimeValue Φ ρ t p = twist (residueProfileGauge Φ ρ t) p := by
  rw [residueProfileGauge, twist_linearPhaseGauge_prime]
  simp only [linearPrimePhase, Complex.ofReal_one, mul_one]
  have hh := Complex.norm_mul_exp_arg_mul_I (residuePrimeValue Φ ρ t p)
  rw [norm_residuePrimeValue hu hρu ht p, Complex.ofReal_one, one_mul] at hh
  exact hh.symm

theorem residuePrimeValue_zero {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (h1 : ∀ a, Φ a 1 = -1) (hρ1 : ∀ p, (p : ℕ) ∣ q → ρ p 1 = -1) (p : Nat.Primes) :
    residuePrimeValue Φ ρ 0 p = -1 := by
  rw [residuePrimeValue_prime, Complex.ofReal_zero, analyticSmoothingPrimePhase_zero,
    residuePrimeProfile_one h1 hρ1 p]

theorem continuousAt_residuePrimeValue {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun v : ℝ => residuePrimeValue Φ ρ v p) t := by
  have ha := analyticAt_analyticSmoothingPrimePhase hR
    (analyticOnNhd_residuePrimeProfile hΦ hρ p) p
    (z := (t : ℂ)) (by simpa only [Complex.ofReal_re] using ht)
  simpa only [Function.comp_def, residuePrimeValue_prime] using
    ha.continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- The actual higher-prime-power remainder, expressed directly in prime coordinates. -/
def residueHigherPrimeLog (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ)
    (t : ℝ) (s : ℂ) : ℂ := hullRem s (residuePrimeValue Φ ρ t)

theorem residueHigherPrimeLog_eq_gauge {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ}
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (s : ℂ) :
    residueHigherPrimeLog Φ ρ t s = hullRem s (twist (residueProfileGauge Φ ρ t)) := by
  unfold residueHigherPrimeLog hullRem
  apply tsum_congr
  intro p
  simp only [localRem, eulerVar, residuePrimeValue_eq_twist hu hρu ht p]

/-- One quadratic prime majorant controls the entire real parameter family. -/
theorem continuousOn_residueHigherPrimeLog {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {b : ℝ} (hb : 1 / 2 < b) :
    ContinuousOn (fun v : ℝ × ℂ => residueHigherPrimeLog Φ ρ v.1 v.2)
      (Ici 0 ×ˢ {s : ℂ | b < s.re}) := by
  have hsum : Summable (fun p : Nat.Primes => 2 * (p : ℝ) ^ (-(2 * b))) :=
    (Nat.Primes.summable_rpow.mpr (by linarith only [hb])).mul_left 2
  change ContinuousOn (fun v : ℝ × ℂ => ∑' p : Nat.Primes, localRem v.2 (residuePrimeValue Φ ρ v.1) p)
    (Ici 0 ×ˢ {s : ℂ | b < s.re})
  refine continuousOn_tsum (fun p v hv => ?_) hsum (fun p v hv => ?_)
  · have hu' : ∀ n : ℕ, n.Prime → ‖residuePrimeValue Φ ρ v.1 n‖ = 1 :=
      fun n hn => norm_residuePrimeValue hu hρu hv.1 ⟨n, hn⟩
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have he : ContinuousAt (fun v : ℝ × ℂ => eulerVar v.2 (residuePrimeValue Φ ρ v.1) p) v := by
      have hp : ContinuousAt (fun v : ℝ × ℂ => residuePrimeValue Φ ρ v.1 p) v :=
        (continuousAt_residuePrimeValue hR hΦ hρ p hv.1).comp continuousAt_fst
      dsimp only [eulerVar, powCoeff]
      have hpow : ContinuousAt (fun v : ℝ × ℂ => ((p : ℕ) : ℂ) ^ (-v.2)) v := by
        simpa only [Complex.cpow_def_of_ne_zero hp0, Pi.neg_apply] using
          ((continuousAt_snd.neg).const_mul (Complex.log ((p : ℕ) : ℂ))).cexp
      exact hpow.mul hp
    have hsl : 1 - eulerVar v.2 (residuePrimeValue Φ ρ v.1) p ∈ Complex.slitPlane := by
      rw [sub_eq_add_neg]
      apply Complex.mem_slitPlane_of_norm_lt_one
      rw [norm_neg]
      exact (norm_eulerVar_le hu' p.2 (hb.trans hv.2)).trans_lt (by norm_num)
    exact ((((continuousAt_const.sub he).clog hsl).neg).sub he).continuousWithinAt
  · have hu' : ∀ n : ℕ, n.Prime → ‖residuePrimeValue Φ ρ v.1 n‖ = 1 :=
      fun n hn => norm_residuePrimeValue hu hρu hv.1 ⟨n, hn⟩
    apply (norm_localRem_le hu' p.2 (hb.trans hv.2)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hvre : b < v.2.re := hv.2
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
      (by linarith only [hvre])

theorem residueHigherPrimeLog_zero {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ}
    (h1 : ∀ a, Φ a 1 = -1) (hρ1 : ∀ p, (p : ℕ) ∣ q → ρ p 1 = -1) (s : ℂ) :
    residueHigherPrimeLog Φ ρ 0 s = hullRem s (twist (exponentialPhaseGauge 0)) := by
  unfold residueHigherPrimeLog hullRem
  apply tsum_congr
  intro p
  simp only [localRem, eulerVar, residuePrimeValue_zero h1 hρ1 p,
    ← exponentialPrimePhase_eq_twist, Complex.ofReal_zero, exponentialPrimePhase_zero]

#print axioms residuePrimeValue_eq_twist
#print axioms continuousOn_residueHigherPrimeLog
#print axioms residueHigherPrimeLog_zero
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
