import GaloisForLFunctions.RHTower.MobiusDivisorPrimeWindowSynthesis
import GaloisForLFunctions.RHTower.MobiusDivisorCompactClockCone

/-!
# Uniform clock control by distinct actual primes

The positive complete-source cone has an arithmetic realization with no
individual prime weights. At every sufficiently large common scale, one
finite set of terminal primes approximates an arbitrary continuous clock
profile. The same set has arbitrarily small quadratic diagonal cost.
-/

noncomputable section
open Finset Set Filter Topology
open scoped NNReal

namespace RHTower

/-- A normalized literal prime child on the entire compact clock interval. -/
def criticalPrimeClockAtom (a : ℝ≥0) (N p : ℕ) : C(CriticalClockWindow a, ℝ) :=
  (Real.sqrt N / p) • criticalClockProfile a (Real.log ((N : ℝ) / p))

private def primeClockRatioSource (a : ℝ≥0) (r : ℝ) : C(CriticalClockWindow a, ℝ) :=
  r⁻¹ • criticalClockProfile a (-Real.log r)

private lemma continuousAt_primeClockRatioSource (a : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (primeClockRatioSource a) r := by
  unfold primeClockRatioSource
  exact (continuousAt_inv₀ hr.ne').smul
    ((continuous_criticalClockProfile a).continuousAt.comp (Real.continuousAt_log hr.ne').neg)

private lemma primeClockRatioSource_normalized (a : ℝ≥0) {N p : ℕ}
    (hN : 0 < N) (hp : 0 < p) :
    (Real.sqrt N)⁻¹ • primeClockRatioSource a ((p : ℝ) / N) =
      criticalPrimeClockAtom a N p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hl : -Real.log ((p : ℝ) / N) = Real.log ((N : ℝ) / p) := by
    rw [Real.log_div hp0.ne' hN0.ne', Real.log_div hN0.ne' hp0.ne']
    ring
  unfold primeClockRatioSource criticalPrimeClockAtom
  rw [smul_smul, hl]
  congr 1
  field_simp [hs.ne', hp0.ne', hN0.ne']
  nlinarith only [Real.sq_sqrt hN0.le]

/-- An arbitrary continuous clock target is realized by one set of distinct
actual terminal primes, at every sufficiently large integer scale. There are
no adjustable individual prime coefficients, and the same set makes the
quadratic diagonal cost arbitrarily small. -/
theorem eventually_exists_criticalPrimeClock_realization
    (a : ℝ≥0) (T : ℝ) (f : C(CriticalClockWindow a, ℝ))
    (ε : Set.Ioi (0 : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T < Real.log ((N : ℝ) / p)) ∧
      ‖(∑ p ∈ S, criticalPrimeClockAtom a N p) - f‖ < ε ∧
      (∑ p ∈ S, ‖criticalPrimeClockAtom a N p‖ ^ 2) < ε := by
  classical
  have hε : (0 : ℝ) < ε.val := ε.property
  obtain ⟨c, hc⟩ := exists_positive_criticalClockProfile_approximation a T f
    (show (0 : ℝ) < ε.val / 2 by positivity)
  let r (t : {t : ℝ // T < t}) : ℝ := Real.exp (-t.val)
  let w (t : {t : ℝ // T < t}) : ℝ := (c t : ℝ) * r t
  have hr (t : {t : ℝ // T < t}) (_ht : t ∈ c.support) :
      0 < r t ∧ r t < Real.exp (-T) :=
    ⟨Real.exp_pos _, Real.exp_lt_exp.mpr (neg_lt_neg t.property)⟩
  have hw (t : {t : ℝ // T < t}) (_ht : t ∈ c.support) : 0 ≤ w t := by
    dsimp [w, r]
    positivity
  have hinj : Set.InjOn r (↑c.support) := by
    intro t ht s hs he
    apply Subtype.ext
    exact neg_injective (Real.exp_injective he)
  have hsource (t : {t : ℝ // T < t}) (ht : t ∈ c.support) :
      ContinuousAt (primeClockRatioSource a) (r t) :=
    continuousAt_primeClockRatioSource a (hr t ht).1
  have he := PrimePreparation.eventually_exists_prime_vector_synthesis
    c.support r w (primeClockRatioSource a)
    (show (0 : ℝ) < ε.val / 2 by positivity) hr hw hinj hsource
  have hmixture : (∑ t ∈ c.support, w t • primeClockRatioSource a (r t)) =
      c.sum (fun t b => b • criticalClockProfile a t) := by
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro t ht
    simp only [w, primeClockRatioSource, r, Real.log_exp, neg_neg,
      smul_smul, NNReal.smul_def]
    rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos (-t.val)).ne', mul_one]
  rw [hmixture] at he
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  obtain ⟨S, hS, happ, hdiag⟩ := hN
  have ha (p : ℕ) (hp : p ∈ S) :=
    primeClockRatioSource_normalized a hN0 (hS p hp).1.pos
  have hsum : (∑ p ∈ S, (Real.sqrt N)⁻¹ • primeClockRatioSource a ((p : ℝ) / N)) =
      ∑ p ∈ S, criticalPrimeClockAtom a N p := Finset.sum_congr rfl ha
  rw [hsum] at happ
  have hsum2 : (∑ p ∈ S, ‖(Real.sqrt N)⁻¹ • primeClockRatioSource a ((p : ℝ) / N)‖ ^ 2) =
      ∑ p ∈ S, ‖criticalPrimeClockAtom a N p‖ ^ 2 :=
    Finset.sum_congr rfl fun p hp => by rw [ha p hp]
  rw [hsum2] at hdiag
  refine ⟨S, ?_, ?_, hdiag.trans (by linarith only [hε])⟩
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
    have hl := Real.log_lt_log (div_pos hp0 hN') (hS p hp).2.2
    rw [Real.log_exp, Real.log_div hp0.ne' hN'.ne'] at hl
    refine ⟨(hS p hp).1, (hS p hp).2.1, ?_⟩
    rw [Real.log_div hN'.ne' hp0.ne']
    linarith only [hl]
  · have hc' : ‖c.sum (fun t b => b • criticalClockProfile a t) - f‖ < ε.val / 2 := by
      simpa only [norm_sub_rev] using hc
    calc
      _ = ‖((∑ p ∈ S, criticalPrimeClockAtom a N p) -
          c.sum (fun t b => b • criticalClockProfile a t)) +
          (c.sum (fun t b => b • criticalClockProfile a t) - f)‖ := by
        congr 1
        abel
      _ ≤ ‖(∑ p ∈ S, criticalPrimeClockAtom a N p) -
          c.sum (fun t b => b • criticalClockProfile a t)‖ +
          ‖c.sum (fun t b => b • criticalClockProfile a t) - f‖ := norm_add_le _ _
      _ < ε := (add_lt_add happ hc').trans_eq (by ring)

end RHTower
