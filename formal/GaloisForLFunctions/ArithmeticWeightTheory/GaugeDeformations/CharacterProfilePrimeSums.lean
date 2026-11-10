import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.CharacterPrimeLogContinuation
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingScaling

/-!
# Taylor expansion of weighted prime profiles

Absolute convergence separates any bounded prime weight from an analytic
profile. For a nonprincipal Dirichlet character, the shifted prime logarithms
extend through one on a fixed horizontal tube. A profile with endpoint one
has zero deviation mass, so its entire character contribution vanishes at
parameter zero.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Prime logarithm with a bounded arithmetic weight. -/
def weightedPrimeLog (a : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, a p * ((p : ℕ) : ℂ) ^ (-s)

/-- The actual weighted prime deviation of a common analytic profile. -/
def weightedProfilePrimeSum (a : Nat.Primes → ℂ) (Φ : ℂ → ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, a p * (analyticSmoothingPrimePhase Φ p (t : ℂ) - 1) *
    ((p : ℕ) : ℂ) ^ (-s)

private theorem profile_prime_decay (p : Nat.Primes) (s : ℂ) :
    Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) = ((p : ℕ) : ℂ) ^ (-s) := by
  simpa only [primeFrequency, neg_mul] using prime_cexp_decay p s

private theorem norm_profile_prime_power (p : Nat.Primes) (s : ℂ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [← profile_prime_decay]
  exact norm_exponentialPrime_damping p s

private theorem profile_prime_shift (p : Nat.Primes) (s : ℂ) (t : ℝ) (n : ℕ) :
    ((p : ℕ) : ℂ) ^ (-(s + (n : ℂ) * (t : ℂ))) =
      Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)) ^ n * ((p : ℕ) : ℂ) ^ (-s) := by
  rw [← profile_prime_decay p (s + (n : ℂ) * (t : ℂ)), ← profile_prime_decay p s,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

private theorem profile_shift_re {t : ℝ} (ht : 0 ≤ t) (s : ℂ) (n : ℕ) :
    s.re ≤ (s + (n : ℂ) * (t : ℂ)).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) ht)

/-- A single absolutely convergent prime sum bounds every rightward shift. -/
theorem norm_weightedPrimeLog_le {a : Nat.Primes → ℂ} (ha : ∀ p, ‖a p‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖weightedPrimeLog a s‖ ≤ ∑' p : Nat.Primes, (p : ℝ) ^ (-σ) := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) :=
    Nat.Primes.summable_rpow.mpr (by linarith only [hσ])
  have hb (p : Nat.Primes) : ‖a p * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-σ) := by
    rw [norm_mul, norm_profile_prime_power]
    apply (mul_le_mul_of_nonneg_right (ha p) (by positivity)).trans
    rw [one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (neg_le_neg hs)
  have hn := hp.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb hp)

/-- Absolute Taylor mass controls the profile deviation on the unit disc. -/
theorem norm_profileDeviation_le {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Φ z - 1‖ ≤ ∑' n, ‖smoothingTaylorCoefficient Φ n‖ := by
  rw [← (smoothingTaylor_hasSum hR hΦ hz).tsum_eq]
  have hb (n : ℕ) : ‖smoothingTaylorCoefficient Φ n * z ^ n‖ ≤ ‖smoothingTaylorCoefficient Φ n‖ := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
  have hc := summable_norm_smoothingTaylorCoefficient hR hΦ
  have hn := hc.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb hc)

private theorem profile_damping_norm (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))‖ ≤ 1 := by
  rw [norm_exponentialPrime_damping, Complex.ofReal_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr ht)

theorem summable_weightedProfilePrimeTerm {a : Nat.Primes → ℂ} {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (ha : ∀ p, ‖a p‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => a p * (analyticSmoothingPrimePhase Φ p (t : ℂ) - 1) *
      ((p : ℕ) : ℂ) ^ (-s)) := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith only [hs])
  apply Summable.of_norm_bounded (hp.mul_left (∑' n, ‖smoothingTaylorCoefficient Φ n‖))
  intro p
  rw [norm_mul, norm_mul, norm_profile_prime_power]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (mul_le_mul_of_nonneg_right (ha p) (norm_nonneg _)).trans
    (by simpa only [one_mul, analyticSmoothingPrimePhase] using
      norm_profileDeviation_le hR hΦ (profile_damping_norm p ht))

private def weightedProfileShiftTerm (a : Nat.Primes → ℂ) (Φ : ℂ → ℂ)
    (t : ℝ) (s : ℂ) (p : Nat.Primes) (n : ℕ) : ℂ :=
  smoothingTaylorCoefficient Φ n * (a p * ((p : ℕ) : ℂ) ^ (-(s + (n : ℂ) * (t : ℂ))))

private theorem summable_weightedProfileShiftTerm {a : Nat.Primes → ℂ} {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (ha : ∀ p, ‖a p‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pn : Nat.Primes × ℕ => weightedProfileShiftTerm a Φ t s pn.1 pn.2) := by
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith only [hs])
  have hc := summable_norm_smoothingTaylorCoefficient hR hΦ
  refine Summable.of_norm_bounded (Summable.mul_of_nonneg hp hc
    (fun _ => by positivity) (fun _ => norm_nonneg _)) ?_
  rintro ⟨p, n⟩
  rw [weightedProfileShiftTerm, norm_mul, mul_comm ((p : ℝ) ^ (-s.re))]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [norm_mul, norm_profile_prime_power]
  apply (mul_le_mul_of_nonneg_right (ha p) (by positivity)).trans
  rw [one_mul]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
    (neg_le_neg (profile_shift_re ht s n))

/-- Absolute Fubini gives the actual weighted prime expansion. -/
theorem weightedProfilePrimeSum_shifted {a : Nat.Primes → ℂ} {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (ha : ∀ p, ‖a p‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    weightedProfilePrimeSum a Φ t s =
      ∑' n, smoothingTaylorCoefficient Φ n * weightedPrimeLog a (s + (n : ℂ) * (t : ℂ)) := by
  have hsum := summable_weightedProfileShiftTerm hR hΦ ha ht hs
  calc
    _ = ∑' p : Nat.Primes, ∑' n, weightedProfileShiftTerm a Φ t s p n := by
      unfold weightedProfilePrimeSum
      apply tsum_congr
      intro p
      have hh := ((smoothingTaylor_hasSum hR hΦ (profile_damping_norm p ht)).mul_left
        (a p)).mul_right (((p : ℕ) : ℂ) ^ (-s))
      change a p * (Φ (Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) - 1) *
        ((p : ℕ) : ℂ) ^ (-s) = ∑' n, weightedProfileShiftTerm a Φ t s p n
      rw [← hh.tsum_eq]
      apply tsum_congr
      intro n
      rw [weightedProfileShiftTerm, profile_prime_shift]
      ring
    _ = ∑' n, ∑' p : Nat.Primes, weightedProfileShiftTerm a Φ t s p n :=
      (Summable.tsum_comm (f := fun p n => weightedProfileShiftTerm a Φ t s p n) hsum).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [weightedProfileShiftTerm, weightedPrimeLog, tsum_mul_left]

theorem summable_weightedProfilePrimeLog {a : Nat.Primes → ℂ} {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (ha : ∀ p, ‖a p‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => smoothingTaylorCoefficient Φ n * weightedPrimeLog a (s + (n : ℂ) * (t : ℂ))) := by
  apply Summable.of_norm_bounded ((summable_norm_smoothingTaylorCoefficient hR hΦ).mul_right
    (∑' p : Nat.Primes, (p : ℝ) ^ (-s.re)))
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_weightedPrimeLog_le ha hs (profile_shift_re ht s n))
    (norm_nonneg _)

/-- A nonprincipal arithmetic profile with zero endpoint deviation extends
through one, and its entire contribution vanishes at parameter zero. -/
theorem exists_characterProfile_continuation {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = 1) :
    ∃ e : ℝ, 0 < e ∧ ∃ K : ℝ → ℂ → ℂ,
      (∀ t : ℝ, 0 ≤ t → AnalyticOnNhd ℂ (K t) {s | 1 - e < s.re ∧ |s.im| < e}) ∧
      ContinuousOn (fun v : ℝ × ℂ => K v.1 v.2)
        (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}) ∧
      (∀ s : ℂ, K 0 s = 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ s : ℂ, 1 < s.re →
        K t s = weightedProfilePrimeSum (fun p => χ p) Φ t s) := by
  obtain ⟨e, he, F, C, hC, hF, hb, heq⟩ := exists_bounded_characterPrimeLog_tube hχ
  have hc := summable_norm_smoothingTaylorCoefficient hR hΦ
  have hmass : ∑' n, smoothingTaylorCoefficient Φ n = 0 := by
    have hh := (smoothingTaylor_hasSum hR hΦ (z := 1) (by norm_num)).tsum_eq
    simpa only [one_pow, mul_one, h1, sub_self] using hh
  have ha (p : Nat.Primes) : ‖χ p‖ ≤ 1 := by
    simpa using norm_char_prime_cpow_le χ (w := 0) p
  refine ⟨e, he, characterShiftSeries (smoothingTaylorCoefficient Φ) F,
    fun t ht => analyticOnNhd_characterShiftSeries hF hb hc ht,
    continuousOn_characterShiftSeries hF hb hc,
    characterShiftSeries_zero F hmass, ?_⟩
  intro t ht s hs
  rw [weightedProfilePrimeSum_shifted hR hΦ ha ht hs]
  unfold characterShiftSeries
  apply tsum_congr
  intro n
  rw [heq _ (hs.trans_le (profile_shift_re ht s n))]
  rfl

#print axioms weightedProfilePrimeSum_shifted
#print axioms exists_characterProfile_continuation
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
