import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticPrimeSmoothing
import GaloisForLFunctions.ArithmeticGaugeTheory.TheLiouvilleTwinInequality

/-!
# Two unit phase profiles selected by a quadratic character

The polynomial mean `1-4z²+2z⁴` and skew part
`2z(1-z²)√(2-z²)` lie on the unit circle on the real unit interval.
The nonprincipal character modulo four selects conjugate phases at
odd primes; the positive phase fills the ramified prime two.
The skew Taylor coefficients have zero total mass, and the higher
prime powers vary continuously down to the Liouville endpoint.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticGaugeTheory
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Analytic square root on the profile disc. -/
def mixtureRoot (z : ℂ) : ℂ := Complex.exp (Complex.log (2 - z ^ 2) / 2)

/-- Polynomial mean of the conjugate unit profiles. -/
def mixtureMean (z : ℂ) : ℂ := 1 - 4 * z ^ 2 + 2 * z ^ 4

/-- Character-sensitive part of the phase. -/
def mixtureSkew (z : ℂ) : ℂ := 2 * z * (1 - z ^ 2) * mixtureRoot z

def mixtureProfile (a : ℂ) (z : ℂ) : ℂ := mixtureMean z + Complex.I * a * mixtureSkew z

private theorem mixture_root_slit {z : ℂ} (hz : ‖z‖ ≤ 6 / 5) :
    2 - z ^ 2 ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hnorm := norm_nonneg z
  have hre := Complex.re_le_norm (z ^ 2)
  rw [norm_pow] at hre
  have htwo : (2 : ℂ).re = 2 := by norm_num
  rw [Complex.sub_re, htwo]
  have hsq := pow_le_pow_left₀ hnorm hz 2
  nlinarith only [hsq, hre]

theorem mixtureRoot_sq {z : ℂ} (hz : ‖z‖ ≤ 6 / 5) :
    mixtureRoot z ^ 2 = 2 - z ^ 2 := by
  rw [mixtureRoot, ← Complex.exp_nat_mul]
  rw [show ((2 : ℕ) : ℂ) * (Complex.log (2 - z ^ 2) / 2) = Complex.log (2 - z ^ 2) by ring]
  exact Complex.exp_log (Complex.slitPlane_ne_zero (mixture_root_slit hz))

theorem analyticOnNhd_mixtureRoot :
    AnalyticOnNhd ℂ mixtureRoot (closedBall 0 (6 / 5)) := by
  intro z hz
  have hn : ‖z‖ ≤ 6 / 5 := by simpa only [mem_closedBall, dist_zero_right] using hz
  exact (((analyticAt_const.sub (analyticAt_id.pow 2)).clog (mixture_root_slit hn)).div_const).cexp

theorem analyticOnNhd_mixtureMean : AnalyticOnNhd ℂ mixtureMean Set.univ := by
  intro z _
  exact (analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))).add
    (analyticAt_const.mul (analyticAt_id.pow 4))

theorem analyticOnNhd_mixtureSkew :
    AnalyticOnNhd ℂ mixtureSkew (closedBall 0 (6 / 5)) := by
  intro z hz
  exact (((analyticAt_const.mul analyticAt_id).mul (analyticAt_const.sub (analyticAt_id.pow 2))).mul
    (analyticOnNhd_mixtureRoot z hz))

theorem analyticOnNhd_mixtureProfile (a : ℂ) :
    AnalyticOnNhd ℂ (mixtureProfile a) (closedBall 0 (6 / 5)) :=
  fun z hz => (analyticOnNhd_mixtureMean z (mem_univ z)).add
    (analyticAt_const.mul (analyticOnNhd_mixtureSkew z hz))

theorem mixtureMean_sq_add_skew_sq {z : ℂ} (hz : ‖z‖ ≤ 6 / 5) :
    mixtureMean z ^ 2 + mixtureSkew z ^ 2 = 1 := by
  have hr := mixtureRoot_sq hz
  dsimp only [mixtureMean, mixtureSkew]
  linear_combination (4 * z ^ 2 * (1 - z ^ 2) ^ 2) * hr

private theorem mixtureRoot_ofReal {x : ℝ} (hx : x ∈ Icc 0 1) :
    mixtureRoot (x : ℂ) = (Real.exp (Real.log (2 - x ^ 2) / 2) : ℝ) := by
  have hp : 0 < 2 - x ^ 2 := by nlinarith only [hx.1, hx.2]
  rw [mixtureRoot, show (2 : ℂ) - (x : ℂ) ^ 2 = ((2 - x ^ 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hp.le]
  norm_num [Complex.ofReal_exp, Complex.ofReal_div]

theorem mixtureSkew_ofReal_im {x : ℝ} (hx : x ∈ Icc 0 1) :
    (mixtureSkew (x : ℂ)).im = 0 := by
  have he : mixtureSkew (x : ℂ) =
      ((2 * x * (1 - x ^ 2) * Real.exp (Real.log (2 - x ^ 2) / 2) : ℝ) : ℂ) := by
    rw [mixtureSkew, mixtureRoot_ofReal hx]
    push_cast
    ring
  rw [he]
  exact Complex.ofReal_im _

theorem mixtureMean_ofReal_im (x : ℝ) : (mixtureMean (x : ℂ)).im = 0 := by
  have he : mixtureMean (x : ℂ) = ((1 - 4 * x ^ 2 + 2 * x ^ 4 : ℝ) : ℂ) := by
    unfold mixtureMean
    push_cast
    ring
  rw [he]
  exact Complex.ofReal_im _

theorem norm_mixtureProfile {x a : ℝ} (hx : x ∈ Icc 0 1) (ha : a ^ 2 = 1) :
    ‖mixtureProfile (a : ℂ) (x : ℂ)‖ = 1 := by
  have hn : ‖(x : ℂ)‖ ≤ 6 / 5 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    linarith only [hx.2]
  have hP := mixtureMean_ofReal_im x
  have hS := mixtureSkew_ofReal_im hx
  have hsq := congrArg Complex.re (mixtureMean_sq_add_skew_sq hn)
  simp only [Complex.add_re, Complex.mul_re, pow_two, hP, hS,
    mul_zero, sub_zero, Complex.one_re] at hsq
  have hf : ‖mixtureProfile (a : ℂ) (x : ℂ)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, mixtureProfile, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hP, hS, zero_mul, mul_zero, sub_zero,
      Complex.add_im, Complex.mul_im, zero_add, one_mul]
    have hm := congrArg (fun b : ℝ => b * (mixtureSkew (x : ℂ)).re ^ 2) ha
    nlinarith only [hsq, hm]
  nlinarith only [hf, norm_nonneg (mixtureProfile (a : ℂ) (x : ℂ))]

@[simp] theorem mixtureMean_zero : mixtureMean 0 = 1 := by norm_num [mixtureMean]
@[simp] theorem mixtureMean_one : mixtureMean 1 = -1 := by norm_num [mixtureMean]
@[simp] theorem mixtureSkew_zero : mixtureSkew 0 = 0 := by simp [mixtureSkew]
@[simp] theorem mixtureSkew_one : mixtureSkew 1 = 0 := by simp [mixtureSkew]
@[simp] theorem mixtureProfile_zero (a : ℂ) : mixtureProfile a 0 = 1 := by simp [mixtureProfile]
@[simp] theorem mixtureProfile_one (a : ℂ) : mixtureProfile a 1 = -1 := by simp [mixtureProfile]

/-- Fill the ramified prime with the positive profile. -/
def mixturePrimeSign (n : ℕ) : ℂ := if n = 2 then 1 else chiFour n

theorem chiFour_two : chiFour (2 : ℕ) = 0 := by
  rw [chiFour, MulChar.ringHomComp_apply, ZMod.χ₄_nat_eq_if_mod_four]
  norm_num

theorem mixturePrimeSign_eq (p : Nat.Primes) : mixturePrimeSign p = 1 ∨ mixturePrimeSign p = -1 := by
  rcases p.2.eq_two_or_odd with hp | hp
  · left
    simp [mixturePrimeSign, hp]
  · have hp2 : (p : ℕ) ≠ 2 := by intro he; rw [he] at hp; norm_num at hp
    rw [mixturePrimeSign, if_neg hp2, chiFour, MulChar.ringHomComp_apply,
      ZMod.χ₄_nat_eq_if_mod_four]
    simp only [hp, Nat.one_ne_zero, if_false]
    split_ifs <;> norm_num

theorem mixturePrimeSign_correction (n : ℕ) :
    mixturePrimeSign n = chiFour n + if n = 2 then 1 else 0 := by
  by_cases hn : n = 2
  · subst n
    have h2 : chiFour (2 : ZMod 4) = 0 := by
      simpa only [Nat.cast_ofNat] using chiFour_two
    simp [mixturePrimeSign, h2]
  · simp [mixturePrimeSign, hn]

#print axioms analyticOnNhd_mixtureProfile
#print axioms norm_mixtureProfile
#print axioms mixturePrimeSign_eq

/-- The genuine prime phases selected by residue classes modulo four. -/
def mixturePrimeValue (t : ℝ) (n : ℕ) : ℂ :=
  mixtureProfile (mixturePrimeSign n) (Complex.exp (-(t : ℂ) * (Real.log (n : ℝ) : ℂ)))

/-- The gauge point with these prime phases. -/
def mixturePhaseGauge (t : ℝ) : GaugeTorus :=
  linearPhaseGauge (fun p => (mixturePrimeValue t p).arg) 1

theorem norm_mixturePrimeValue {t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) :
    ‖mixturePrimeValue t p‖ = 1 := by
  change ‖analyticSmoothingPrimePhase (mixtureProfile (mixturePrimeSign p)) p (t : ℂ)‖ = 1
  apply norm_analyticSmoothingPrimePhase_real (t := t) _ ht p
  intro x hx
  rcases mixturePrimeSign_eq p with h | h
  · rw [h]
    simpa only [Complex.ofReal_one] using norm_mixtureProfile (a := 1) hx (by norm_num)
  · rw [h]
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
      norm_mixtureProfile (a := -1) hx (by norm_num)

theorem mixturePrimeValue_eq_twist {t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) :
    mixturePrimeValue t p = twist (mixturePhaseGauge t) p := by
  rw [mixturePhaseGauge, twist_linearPhaseGauge_prime]
  simp only [linearPrimePhase, Complex.ofReal_one, mul_one]
  have hh := Complex.norm_mul_exp_arg_mul_I (mixturePrimeValue t p)
  rw [norm_mixturePrimeValue ht p, Complex.ofReal_one, one_mul] at hh
  exact hh.symm

@[simp] theorem mixturePrimeValue_zero (n : ℕ) : mixturePrimeValue 0 n = -1 := by
  simp [mixturePrimeValue]

theorem continuousAt_mixturePrimeValue (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun v : ℝ => mixturePrimeValue v p) t := by
  have ha := analyticAt_analyticSmoothingPrimePhase (R := (6 / 5 : NNReal))
    (by norm_num) (analyticOnNhd_mixtureProfile (mixturePrimeSign p)) p
    (z := (t : ℂ)) (by simpa only [Complex.ofReal_re] using ht)
  exact ha.continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- Taylor coefficients of the character-sensitive part. -/
def mixtureSkewCoefficient (n : ℕ) : ℂ :=
  smoothingTaylorCoefficient (fun z => 1 + mixtureSkew z) n

private theorem analyticOnNhd_one_add_mixtureSkew :
    AnalyticOnNhd ℂ (fun z => 1 + mixtureSkew z) (closedBall 0 (6 / 5)) :=
  fun z hz => analyticAt_const.add (analyticOnNhd_mixtureSkew z hz)

theorem summable_norm_mixtureSkewCoefficient : Summable (fun n => ‖mixtureSkewCoefficient n‖) :=
  summable_norm_smoothingTaylorCoefficient (R := (6 / 5 : NNReal)) (by norm_num)
    analyticOnNhd_one_add_mixtureSkew

theorem mixtureSkewCoefficient_hasSum {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => mixtureSkewCoefficient n * z ^ n) (mixtureSkew z) := by
  have hh := smoothingTaylor_hasSum (R := (6 / 5 : NNReal)) (by norm_num)
    analyticOnNhd_one_add_mixtureSkew hz
  simpa only [mixtureSkewCoefficient, add_sub_cancel_left] using hh

theorem mixtureSkewCoefficient_tsum : ∑' n, mixtureSkewCoefficient n = 0 := by
  have hh := mixtureSkewCoefficient_hasSum (z := 1) (by norm_num)
  simpa only [one_pow, mul_one, mixtureSkew_one] using hh.tsum_eq

@[simp] theorem mixtureSkewCoefficient_zero : mixtureSkewCoefficient 0 = 0 :=
  smoothingTaylorCoefficient_zero (R := (6 / 5 : NNReal)) (by norm_num)
    analyticOnNhd_one_add_mixtureSkew (by simp)

#print axioms norm_mixturePrimeValue
#print axioms mixturePrimeValue_eq_twist
#print axioms mixtureSkewCoefficient_tsum

/-- Higher prime powers of the arithmetic mixture. -/
def mixtureHigherPrimeLog (t : ℝ) (s : ℂ) : ℂ := hullRem s (mixturePrimeValue t)

theorem analyticOnNhd_mixtureHigherPrimeLog {t : ℝ} (ht : 0 ≤ t) :
    AnalyticOnNhd ℂ (mixtureHigherPrimeLog t) {s : ℂ | 1 / 2 < s.re} :=
  analyticOnNhd_hullRem (fun p hp => norm_mixturePrimeValue ht ⟨p, hp⟩)

/-- The quadratic prime majorant is uniform down to the Liouville endpoint. -/
theorem continuousOn_mixtureHigherPrimeLog {b : ℝ} (hb : 1 / 2 < b) :
    ContinuousOn (fun q : ℝ × ℂ => mixtureHigherPrimeLog q.1 q.2)
      (Ici 0 ×ˢ {s : ℂ | b < s.re}) := by
  have hsum : Summable (fun p : Nat.Primes => 2 * (p : ℝ) ^ (-(2 * b))) :=
    (Nat.Primes.summable_rpow.mpr (by linarith only [hb])).mul_left 2
  change ContinuousOn (fun q : ℝ × ℂ => ∑' p : Nat.Primes, localRem q.2 (mixturePrimeValue q.1) p)
    (Ici 0 ×ˢ {s : ℂ | b < s.re})
  refine continuousOn_tsum (fun p q hq => ?_) hsum (fun p q hq => ?_)
  · have hu : ∀ n : ℕ, n.Prime → ‖mixturePrimeValue q.1 n‖ = 1 :=
      fun n hn => norm_mixturePrimeValue hq.1 ⟨n, hn⟩
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have he : ContinuousAt (fun q : ℝ × ℂ => eulerVar q.2 (mixturePrimeValue q.1) p) q := by
      have hp : ContinuousAt (fun q : ℝ × ℂ => mixturePrimeValue q.1 p) q :=
        (continuousAt_mixturePrimeValue p hq.1).comp continuousAt_fst
      dsimp only [eulerVar, powCoeff]
      have hpow : ContinuousAt (fun q : ℝ × ℂ => ((p : ℕ) : ℂ) ^ (-q.2)) q := by
        simpa only [Complex.cpow_def_of_ne_zero hp0] using
          ((continuousAt_snd.neg).const_mul (Complex.log ((p : ℕ) : ℂ))).cexp
      exact hpow.mul hp
    have hsl : 1 - eulerVar q.2 (mixturePrimeValue q.1) p ∈ Complex.slitPlane := by
      rw [sub_eq_add_neg]
      apply Complex.mem_slitPlane_of_norm_lt_one
      rw [norm_neg]
      exact (norm_eulerVar_le hu p.2 (hb.trans hq.2)).trans_lt (by norm_num)
    exact ((((continuousAt_const.sub he).clog hsl).neg).sub he).continuousWithinAt
  · have hu : ∀ n : ℕ, n.Prime → ‖mixturePrimeValue q.1 n‖ = 1 :=
      fun n hn => norm_mixturePrimeValue hq.1 ⟨n, hn⟩
    apply (norm_localRem_le hu p.2 (hb.trans hq.2)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hqre : b < q.2.re := hq.2
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
      (by linarith only [hqre])

theorem mixtureHigherPrimeLog_zero (s : ℂ) :
    mixtureHigherPrimeLog 0 s = hullRem s (twist (exponentialPhaseGauge 0)) := by
  unfold mixtureHigherPrimeLog hullRem
  apply tsum_congr
  intro p
  simp only [localRem, eulerVar, mixturePrimeValue_zero,
    ← exponentialPrimePhase_eq_twist, Complex.ofReal_zero, exponentialPrimePhase_zero]

#print axioms continuousOn_mixtureHigherPrimeLog

/-- Absolute Taylor mass bounds the skew profile on the closed unit disc. -/
theorem norm_mixtureSkew_le_tsum {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖mixtureSkew z‖ ≤ ∑' n, ‖mixtureSkewCoefficient n‖ := by
  rw [← (mixtureSkewCoefficient_hasSum hz).tsum_eq]
  have hb (n : ℕ) : ‖mixtureSkewCoefficient n * z ^ n‖ ≤ ‖mixtureSkewCoefficient n‖ := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
  have hn := summable_norm_mixtureSkewCoefficient.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb summable_norm_mixtureSkewCoefficient)

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
