import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.SignedIncidenceForms
import GaloisForLFunctions.RHTower.Sieve.TruncatedMoebius
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Riemann hypothesis and additive prime-pair statistics

The total weight of prime pairs in a square is exactly `θ(x)²`. Its error
of order `x √x log²x` is equivalent to RH. At an individual sum, the prime-pair
weight also contains a reflected correlation of the centered prime weights.
Its positivity is exactly the binary Goldbach condition at that sum.

The boxed average criterion does not assert positivity of each coefficient.
All pair weights below use actual primes, with prime powers removed.

The same count is a signed incidence energy, even energy minus odd energy,
and mass minus reflection defect. It is also the quadratic damping coefficient
of the squarefree, unit-removed divisor source used by the pronic RH receiver.
After symmetric gauge, damping reversal reads the Möbius sign. Its odd sector
gives a finite two-scale criterion: some positive damping has amplification
strictly below sixteen exactly when the target contains a prime pair.
The normalized defect is a global lower approximation to the prime-pair weight.
A nonnegative three-scale compensation gives its exact gain under halving.
-/

namespace GaloisForLFunctions.Goldbach

open Finset Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false

/-- Logarithmic weight supported on primes, excluding proper prime powers. -/
def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

theorem primeLogWeight_nonneg (n : ℕ) : 0 ≤ primeLogWeight n := by
  unfold primeLogWeight
  split_ifs with hn
  · exact Real.log_nonneg (by exact_mod_cast hn.one_le)
  · exact le_rfl

theorem primeLogWeight_pos_iff (n : ℕ) : 0 < primeLogWeight n ↔ n.Prime := by
  by_cases hn : n.Prime
  · rw [primeLogWeight, if_pos hn]
    exact ⟨fun _ => hn, fun _ => Real.log_pos (by exact_mod_cast hn.one_lt)⟩
  · rw [primeLogWeight, if_neg hn]
    exact ⟨fun h => False.elim (lt_irrefl 0 h), fun hp => False.elim (hn hp)⟩

/-- The one-point prime weight is the Chebyshev theta function. -/
theorem sum_primeLogWeight_eq_theta (x : ℝ) :
    ∑ n ∈ range (⌊x⌋₊ + 1), primeLogWeight n = Chebyshev.theta x := by
  have hr : Icc 0 ⌊x⌋₊ = range (⌊x⌋₊ + 1) := by
    ext n
    simp only [mem_Icc, mem_range]
    omega
  rw [Chebyshev.theta_eq_sum_Icc, hr, sum_filter]
  rfl

/-- Additive convolution, with both endpoints included. -/
def additivePairWeight (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ antidiagonal n, w p.1 * w p.2

/-- Logarithmically weighted ordered Goldbach representations. -/
def primePairWeight (n : ℕ) : ℝ := additivePairWeight primeLogWeight n

/-- The centered reflected correlation at a fixed sum. -/
def reflectedPrimeCorrelation (n : ℕ) : ℝ :=
  additivePairWeight (fun k => primeLogWeight k - 1) n

theorem primePairWeight_nonneg (n : ℕ) : 0 ≤ primePairWeight n := by
  unfold primePairWeight additivePairWeight
  exact sum_nonneg fun p _ => mul_nonneg (primeLogWeight_nonneg p.1)
    (primeLogWeight_nonneg p.2)

/-- Positivity detects actual prime pairs, without a prime-power error. -/
theorem primePairWeight_pos_iff (n : ℕ) :
    0 < primePairWeight n ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  unfold primePairWeight additivePairWeight
  rw [sum_pos_iff_of_nonneg (fun p _ =>
    mul_nonneg (primeLogWeight_nonneg p.1) (primeLogWeight_nonneg p.2))]
  constructor
  · rintro ⟨⟨p, q⟩, hpq, hpos⟩
    rcases mul_pos_iff.mp hpos with h | h
    · exact ⟨p, q, (primeLogWeight_pos_iff p).mp h.1,
        (primeLogWeight_pos_iff q).mp h.2, mem_antidiagonal.mp hpq⟩
    · exact False.elim (not_lt_of_ge (primeLogWeight_nonneg p) h.1)
  · rintro ⟨p, q, hp, hq, hpq⟩
    exact ⟨(p, q), mem_antidiagonal.mpr hpq,
      mul_pos ((primeLogWeight_pos_iff p).mpr hp) ((primeLogWeight_pos_iff q).mpr hq)⟩

/-- Expanding the centered weights separates one-point and reflected errors. -/
theorem primePairWeight_eq_theta_and_reflection (n : ℕ) :
    primePairWeight n = 2 * Chebyshev.theta n - ((n : ℝ) + 1) +
      reflectedPrimeCorrelation n := by
  have hf : (∑ p ∈ antidiagonal n, primeLogWeight p.1) = Chebyshev.theta n := by
    rw [Finset.Nat.antidiagonal_eq_map]
    simpa only [sum_map, Function.Embedding.coeFn_mk, Nat.floor_natCast] using
      sum_primeLogWeight_eq_theta (n : ℝ)
  have hs : (∑ p ∈ antidiagonal n, primeLogWeight p.2) = Chebyshev.theta n := by
    rw [Finset.Nat.antidiagonal_eq_map']
    simpa only [sum_map, Function.Embedding.coeFn_mk, Nat.floor_natCast] using
      sum_primeLogWeight_eq_theta (n : ℝ)
  have he : reflectedPrimeCorrelation n =
      primePairWeight n - Chebyshev.theta n -
        (Chebyshev.theta n - ((n : ℝ) + 1)) := by
    unfold reflectedPrimeCorrelation additivePairWeight primePairWeight
    simp only [additivePairWeight, sub_mul, mul_sub, one_mul, mul_one, sum_sub_distrib,
      hf, hs, sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, mul_one]
  linarith

/-- Goldbach's exact missing pointwise inequality in centered prime coordinates. -/
theorem goldbach_iff_reflectedPrimeCorrelation :
    (∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * (n + 2)) ↔
      ∀ n : ℕ, ((2 * (n + 2) : ℕ) : ℝ) + 1 -
        2 * Chebyshev.theta (2 * (n + 2) : ℕ) <
          reflectedPrimeCorrelation (2 * (n + 2)) := by
  simp_rw [← primePairWeight_pos_iff, primePairWeight_eq_theta_and_reflection]
  constructor <;> intro h n <;> have hn := h n <;> linarith

/-- A sum coefficient with both summands restricted to `0, …, N`. -/
def boxedPairCoefficient (w : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ p ∈ ((range (N + 1)) ×ˢ (range (N + 1))).filter
    (fun p : ℕ × ℕ => p.1 + p.2 = n), w p.1 * w p.2

/-- Partitioning a square by its additive antidiagonals. -/
theorem sum_boxedPairCoefficient (w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range (2 * N + 1), boxedPairCoefficient w N n =
      (∑ p ∈ range (N + 1), w p) ^ 2 := by
  have hm : ∀ p ∈ (range (N + 1)) ×ˢ (range (N + 1)),
      p.1 + p.2 ∈ range (2 * N + 1) := by
    intro p hp
    simp only [mem_product, mem_range] at hp ⊢
    omega
  unfold boxedPairCoefficient
  rw [sum_fiberwise_of_maps_to hm, sum_product, pow_two, sum_mul_sum]

/-- At sum `N`, the box contains the whole antidiagonal. -/
theorem boxedPairCoefficient_self (w : ℕ → ℝ) (n : ℕ) :
    boxedPairCoefficient w n n = additivePairWeight w n := by
  have hf : ((range (n + 1)) ×ˢ (range (n + 1))).filter
      (fun p : ℕ × ℕ => p.1 + p.2 = n) = antidiagonal n := by
    ext p
    simp only [mem_filter, mem_product, mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  simp only [boxedPairCoefficient, hf, additivePairWeight]

/-- Total prime-pair weight in the square with real cutoff `x`. -/
def boxedPrimePairMass (x : ℝ) : ℝ :=
  ∑ n ∈ range (2 * ⌊x⌋₊ + 1), boxedPairCoefficient primeLogWeight ⌊x⌋₊ n

/-- The boxed Goldbach average is exactly the square of the prime-counting weight. -/
theorem boxedPrimePairMass_eq_theta_sq (x : ℝ) :
    boxedPrimePairMass x = Chebyshev.theta x ^ 2 := by
  rw [boxedPrimePairMass, sum_boxedPairCoefficient, sum_primeLogWeight_eq_theta]

/-- Proper prime powers fit within the von Koch error scale unconditionally. -/
theorem psi_sub_theta_isBigO_sqrt_log_sq :
    (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))]
  have hl := RHTower.two_le_log_of_sixteen_le hx
  calc
    |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)
    _ ≤ 2 * Real.sqrt x * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith : Real.log x ≤ Real.log x ^ 2)
        (by positivity)
    _ = 2 * (Real.sqrt x * Real.log x ^ 2) := by ring

/-- Von Koch's criterion expressed using actual primes only. -/
theorem riemannHypothesis_iff_theta_error_isBigO :
    RiemannHypothesis ↔ (fun x : ℝ => Chebyshev.theta x - x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) := by
  rw [RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO]
  constructor
  · intro h
    have he : (fun x : ℝ => Chebyshev.theta x - x) =
        (fun x : ℝ => (Chebyshev.psi x - x) -
          (Chebyshev.psi x - Chebyshev.theta x)) := by funext x; ring
    rw [he]
    exact h.sub psi_sub_theta_isBigO_sqrt_log_sq
  · intro h
    have he : (fun x : ℝ => Chebyshev.psi x - x) =
        (fun x : ℝ => (Chebyshev.theta x - x) +
          (Chebyshev.psi x - Chebyshev.theta x)) := by funext x; ring
    rw [he]
    exact h.add psi_sub_theta_isBigO_sqrt_log_sq

/-- The average error and one-point error have exactly one factor of scale between them. -/
theorem boxedPrimePairMass_error_comparison {x : ℝ} (hx : 0 ≤ x) :
    x * |Chebyshev.theta x - x| ≤ |boxedPrimePairMass x - x ^ 2| ∧
      |boxedPrimePairMass x - x ^ 2| ≤
        (Real.log 4 + 1) * x * |Chebyshev.theta x - x| := by
  rw [boxedPrimePairMass_eq_theta_sq,
    show Chebyshev.theta x ^ 2 - x ^ 2 =
      (Chebyshev.theta x - x) * (Chebyshev.theta x + x) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (Chebyshev.theta_nonneg x) hx)]
  constructor
  · nlinarith [Chebyshev.theta_nonneg x, abs_nonneg (Chebyshev.theta x - x)]
  · have ht := Chebyshev.theta_le_log4_mul_x hx
    have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg (Chebyshev.theta x - x))
    nlinarith

/-- RH is exactly the square-root-scale error law for the boxed average of prime pairs. -/
theorem riemannHypothesis_iff_boxedPrimePairMass_error :
    RiemannHypothesis ↔ (fun x : ℝ => boxedPrimePairMass x - x ^ 2)
      =O[atTop] (fun x : ℝ => x * (Real.sqrt x * Real.log x ^ 2)) := by
  rw [riemannHypothesis_iff_theta_error_isBigO]
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h.bound
    refine IsBigO.of_bound ((Real.log 4 + 1) * C) ?_
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with x hb hx
    have hx0 : 0 ≤ x := by linarith
    have hg : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by positivity
    have hl : 0 ≤ Real.log 4 + 1 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg] at hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 hg)]
    calc
      |boxedPrimePairMass x - x ^ 2| ≤
          (Real.log 4 + 1) * x * |Chebyshev.theta x - x| :=
        (boxedPrimePairMass_error_comparison hx0).2
      _ ≤ (Real.log 4 + 1) * x * (C * (Real.sqrt x * Real.log x ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hl hx0)
      _ = (Real.log 4 + 1) * C * (x * (Real.sqrt x * Real.log x ^ 2)) := by ring
  · intro h
    obtain ⟨C, hC⟩ := h.bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with x hb hx
    have hx0 : 0 < x := by linarith
    have hg : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0.le hg)] at hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg]
    apply (mul_le_mul_iff_right₀ hx0).mp
    calc
      x * |Chebyshev.theta x - x| ≤ |boxedPrimePairMass x - x ^ 2| :=
        (boxedPrimePairMass_error_comparison hx0.le).1
      _ ≤ C * (x * (Real.sqrt x * Real.log x ^ 2)) := hb
      _ = x * (C * (Real.sqrt x * Real.log x ^ 2)) := by ring

/-! The anchored reflection, its two sectors, and its incidence form. -/

/-- Mass of a real arithmetic profile on the target interval. -/
def reflectionMass (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), w k ^ 2

/-- Energy of the part even under `k ↦ N-k`. -/
def reflectionEvenEnergy (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ antidiagonal N, ((w p.1 + w p.2) / 2) ^ 2

/-- Energy of the part odd under `k ↦ N-k`. -/
def reflectionOddEnergy (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ antidiagonal N, ((w p.1 - w p.2) / 2) ^ 2

/-- Half the squared distance between a profile and its target reflection. -/
def additiveReflectionDefect (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  (1 / 2) * ∑ p ∈ antidiagonal N, (w p.1 - w p.2) ^ 2

theorem additivePairWeight_eq_even_sub_odd (w : ℕ → ℝ) (N : ℕ) :
    additivePairWeight w N = reflectionEvenEnergy w N - reflectionOddEnergy w N := by
  rw [additivePairWeight, reflectionEvenEnergy, reflectionOddEnergy, ← sum_sub_distrib]
  exact sum_congr rfl fun p _ => by ring

theorem reflectionEvenEnergy_add_odd (w : ℕ → ℝ) (N : ℕ) :
    reflectionEvenEnergy w N + reflectionOddEnergy w N = reflectionMass w N := by
  have hf : (∑ p ∈ antidiagonal N, w p.1 ^ 2) = reflectionMass w N := by
    rw [Finset.Nat.antidiagonal_eq_map]
    simp only [sum_map, Function.Embedding.coeFn_mk, reflectionMass]
  have hs : (∑ p ∈ antidiagonal N, w p.2 ^ 2) = reflectionMass w N := by
    rw [Finset.Nat.antidiagonal_eq_map']
    simp only [sum_map, Function.Embedding.coeFn_mk, reflectionMass]
  have hid (a b : ℝ) : ((a + b) / 2) ^ 2 + ((a - b) / 2) ^ 2 =
      (a ^ 2 + b ^ 2) / 2 := by ring
  rw [reflectionEvenEnergy, reflectionOddEnergy, ← sum_add_distrib]
  simp_rw [hid]
  rw [← sum_div, sum_add_distrib, hf, hs]
  ring

theorem additiveReflectionDefect_eq_twice_odd (w : ℕ → ℝ) (N : ℕ) :
    additiveReflectionDefect w N = 2 * reflectionOddEnergy w N := by
  simp only [additiveReflectionDefect, reflectionOddEnergy, mul_sum]
  exact sum_congr rfl fun p _ => by ring

/-- The finite arithmetic version of mass minus reflection defect. -/
theorem additivePairWeight_eq_mass_sub_defect (w : ℕ → ℝ) (N : ℕ) :
    additivePairWeight w N = reflectionMass w N - additiveReflectionDefect w N := by
  rw [additivePairWeight_eq_even_sub_odd, additiveReflectionDefect_eq_twice_odd]
  linarith only [reflectionEvenEnergy_add_odd w N]

/-- Goldbach asks for strict dominance of the even sector of the actual prime source. -/
theorem goldbach_iff_reflection_even_dominates :
    (∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * (n + 2)) ↔
      ∀ n : ℕ, reflectionOddEnergy primeLogWeight (2 * (n + 2)) <
        reflectionEvenEnergy primeLogWeight (2 * (n + 2)) := by
  simp_rw [← primePairWeight_pos_iff, primePairWeight,
    additivePairWeight_eq_even_sub_odd, sub_pos]

/-- Goldbach excludes saturation of the prime source's reflection defect. -/
theorem goldbach_iff_reflection_defect_lt_mass :
    (∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * (n + 2)) ↔
      ∀ n : ℕ, additiveReflectionDefect primeLogWeight (2 * (n + 2)) <
        reflectionMass primeLogWeight (2 * (n + 2)) := by
  simp_rw [← primePairWeight_pos_iff, primePairWeight,
    additivePairWeight_eq_mass_sub_defect, sub_pos]

/-- The target antidiagonal as a finite incidence coupling. -/
def goldbachReflectionCoupling (N : ℕ) (i j : Fin (N + 1)) : ℝ :=
  if (i : ℕ) + (j : ℕ) = N then 1 else 0

theorem goldbachReflectionCoupling_symmetric (N : ℕ) :
    SignedArithmeticEnergyIncidence.IsSymmetricCoupling (goldbachReflectionCoupling N) := by
  intro i j
  simp only [goldbachReflectionCoupling, Nat.add_comm]

/-- Literal specialization of the signed-incidence programme's energy. -/
theorem incidenceEnergy_goldbachReflectionCoupling (w : ℕ → ℝ) (N : ℕ) :
    SignedArithmeticEnergyIncidence.incidenceEnergy (goldbachReflectionCoupling N)
      (fun i => w i) = additivePairWeight w N := by
  rw [← boxedPairCoefficient_self]
  simp only [SignedArithmeticEnergyIncidence.incidenceEnergy, goldbachReflectionCoupling,
    ite_mul, one_mul, zero_mul, boxedPairCoefficient, sum_filter, sum_product]
  simp_rw [Finset.sum_range]

theorem goldbach_iff_positive_reflection_incidenceEnergy :
    (∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * (n + 2)) ↔
      ∀ n : ℕ, 0 < SignedArithmeticEnergyIncidence.incidenceEnergy
        (goldbachReflectionCoupling (2 * (n + 2))) (fun i => primeLogWeight i) := by
  simp_rw [incidenceEnergy_goldbachReflectionCoupling, ← primePairWeight_pos_iff, primePairWeight]

/-! The divisor source of the RH receiver, read through its squarefree tangent. -/

open _root_.RHTower ArithmeticFunction BezoutValuationIncidence

/-- Squarefree part of the damped divisor response, with the unit removed. -/
def squarefreeDampedSource (ε : ℝ) (k : ℕ) : ℝ :=
  if Squarefree k ∧ k ≠ 1 then pmPowerDampedDivisorCoeff ε k else 0

theorem squarefreeDampedSource_zero (k : ℕ) : squarefreeDampedSource 0 k = 0 := by
  unfold squarefreeDampedSource
  split_ifs with hk
  · rw [pmPowerDampedDivisorCoeff_zero_damping, if_neg hk.2]
  · rfl

/-- The first damping coefficient is the actual prime weight. -/
theorem hasDerivAt_squarefreeDampedSource_zero (k : ℕ) :
    HasDerivAt (fun ε => squarefreeDampedSource ε k) (primeLogWeight k) 0 := by
  by_cases hk : Squarefree k ∧ k ≠ 1
  · have h := hasDerivAt_pmPowerDampedDivisorCoeff 0 k
    rw [dampedVonMangoldt_zero] at h
    have hw : vonMangoldt k = primeLogWeight k := by
      by_cases hp : k.Prime
      · simp only [primeLogWeight, if_pos hp, vonMangoldt_apply_prime hp]
      · have hz : vonMangoldt k = 0 := vonMangoldt_eq_zero_iff.mpr
          (fun hpow => hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hk.1, hpow⟩))
        simp only [primeLogWeight, if_neg hp, hz]
    simpa only [squarefreeDampedSource, if_pos hk, hw] using h
  · have hp : ¬ k.Prime := fun h => hk ⟨h.squarefree, h.ne_one⟩
    simpa only [squarefreeDampedSource, if_neg hk, primeLogWeight, if_neg hp] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))

/-- Normalizing the source by damping extracts its prime-only tangent. -/
theorem tendsto_squarefreeDampedSource_div (k : ℕ) :
    Tendsto (fun ε => squarefreeDampedSource ε k / ε)
      (𝓝[≠] 0) (𝓝 (primeLogWeight k)) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.mp
    (hasDerivAt_squarefreeDampedSource_zero k)
  simpa only [zero_add, squarefreeDampedSource_zero, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

/-- Anchored additive overlap of the projected arithmetic source. -/
def dampedReflectionOverlap (N : ℕ) (ε : ℝ) : ℝ :=
  additivePairWeight (squarefreeDampedSource ε) N

/-- Its quadratic damping coefficient counts actual prime pairs exactly. -/
theorem tendsto_dampedReflectionOverlap_div_sq (N : ℕ) :
    Tendsto (fun ε => dampedReflectionOverlap N ε / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (primePairWeight N)) := by
  have h := tendsto_finsetSum (antidiagonal N) (fun p _ =>
    (tendsto_squarefreeDampedSource_div p.1).mul
      (tendsto_squarefreeDampedSource_div p.2))
  simpa only [dampedReflectionOverlap, primePairWeight, additivePairWeight,
    sum_div, pow_two, div_mul_div_comm] using h

/-- Goldbach is strict positivity of every even target's second damping coefficient. -/
theorem goldbach_iff_positive_dampedReflection_limit :
    (∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * (n + 2)) ↔
      ∀ n : ℕ, ∃ L : ℝ, 0 < L ∧
        Tendsto (fun ε => dampedReflectionOverlap (2 * (n + 2)) ε / ε ^ 2)
          (𝓝[≠] 0) (𝓝 L) := by
  constructor
  · intro h n
    exact ⟨primePairWeight (2 * (n + 2)),
      (primePairWeight_pos_iff _).mpr (h n), tendsto_dampedReflectionOverlap_div_sq _⟩
  · intro h n
    obtain ⟨L, hL, hlim⟩ := h n
    have heq := tendsto_nhds_unique (tendsto_dampedReflectionOverlap_div_sq (2 * (n + 2))) hlim
    exact (primePairWeight_pos_iff _).mp (heq.symm ▸ hL)

/-! Reversing damping reads arithmetic parity after a symmetric gauge. -/

/-- Negative damping inserts the Möbius sign on the squarefree source. -/
theorem squarefreeDampedSource_neg (ε : ℝ) (k : ℕ) :
    squarefreeDampedSource (-ε) k =
      (moebius k : ℝ) * (k : ℝ) ^ ε * squarefreeDampedSource ε k := by
  by_cases hk : Squarefree k ∧ k ≠ 1
  · have hμ : (moebius k : ℝ) = (-1 : ℝ) ^ k.primeFactors.card := by
      exact_mod_cast Sieve.moebius_eq_neg_one_pow_card_primeFactors hk.1
    have hpowers : (∏ p ∈ k.primeFactors, (p : ℝ) ^ ε) = (k : ℝ) ^ ε := by
      simpa only [map_prod, pmNaturalRpowHom, MonoidHom.coe_mk, OneHom.coe_mk,
        neg_neg] using congrArg (pmNaturalRpowHom (-ε))
          (Nat.prod_primeFactors_of_squarefree hk.1)
    have hfactor (p : ℕ) (hp : p ∈ k.primeFactors) :
        1 - (p : ℝ) ^ ε = -(p : ℝ) ^ ε * (1 - (p : ℝ) ^ (-ε)) := by
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have hinv : (p : ℝ) ^ ε * (p : ℝ) ^ (-ε) = 1 := by
        rw [← Real.rpow_add hp0, add_neg_cancel, Real.rpow_zero]
      nlinarith only [hinv]
    simp only [squarefreeDampedSource, if_pos hk,
      pmPowerDampedDivisorCoeff_eq_prod _ hk.1.ne_zero, neg_neg]
    calc
      (∏ p ∈ k.primeFactors, (1 - (p : ℝ) ^ ε)) =
          ∏ p ∈ k.primeFactors, (-(p : ℝ) ^ ε * (1 - (p : ℝ) ^ (-ε))) :=
        prod_congr rfl hfactor
      _ = (moebius k : ℝ) * (k : ℝ) ^ ε *
          ∏ p ∈ k.primeFactors, (1 - (p : ℝ) ^ (-ε)) := by
        rw [prod_mul_distrib, prod_neg, hpowers, ← hμ]
  · simp only [squarefreeDampedSource, if_neg hk, mul_zero]

/-- The exponential gauge is defined at every integer, including zero. -/
def symmetricDampedSource (ε : ℝ) (k : ℕ) : ℝ :=
  Real.exp (ε * Real.log k / 2) * squarefreeDampedSource ε k

/-- Arithmetic factor-count parity is reflection of the damping variable. -/
theorem symmetricDampedSource_neg (ε : ℝ) (k : ℕ) :
    symmetricDampedSource (-ε) k = (moebius k : ℝ) * symmetricDampedSource ε k := by
  by_cases hk : Squarefree k ∧ k ≠ 1
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk.1.ne_zero
    have hexp : Real.exp (-ε * Real.log k / 2) * Real.exp (Real.log k * ε) =
        Real.exp (ε * Real.log k / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [symmetricDampedSource, squarefreeDampedSource_neg,
      Real.rpow_def_of_pos hk0]
    calc
      Real.exp (-ε * Real.log k / 2) *
          ((moebius k : ℝ) * Real.exp (Real.log k * ε) * squarefreeDampedSource ε k) =
          (moebius k : ℝ) *
            (Real.exp (-ε * Real.log k / 2) * Real.exp (Real.log k * ε)) *
              squarefreeDampedSource ε k := by ring
      _ = _ := by rw [hexp]; ring
  · simp only [symmetricDampedSource, squarefreeDampedSource, if_neg hk, mul_zero]

/-- The symmetric source factors into the RH programme's hyperbolic multipliers. -/
theorem symmetricDampedSource_eq_prod_sinh (ε : ℝ) (k : ℕ) :
    symmetricDampedSource ε k = if Squarefree k ∧ k ≠ 1 then
      ∏ p ∈ k.primeFactors, (2 * Real.sinh (ε * Real.log p / 2)) else 0 := by
  by_cases hk : Squarefree k ∧ k ≠ 1
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk.1.ne_zero
    have hpowers : (∏ p ∈ k.primeFactors, (p : ℝ) ^ (ε / 2)) = (k : ℝ) ^ (ε / 2) := by
      simpa only [map_prod, pmNaturalRpowHom, MonoidHom.coe_mk, OneHom.coe_mk,
        neg_neg] using congrArg (pmNaturalRpowHom (-(ε / 2)))
          (Nat.prod_primeFactors_of_squarefree hk.1)
    have hgauge : Real.exp (ε * Real.log k / 2) = (k : ℝ) ^ (ε / 2) := by
      rw [Real.rpow_def_of_pos hk0]
      congr 1
      ring
    simp only [symmetricDampedSource, squarefreeDampedSource, if_pos hk,
      pmPowerDampedDivisorCoeff_eq_prod _ hk.1.ne_zero, hgauge, ← hpowers,
      ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    rw [mul_sub, mul_one, ← Real.rpow_add hp0,
      show ε / 2 + -ε = -(ε / 2) by ring,
      Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0, Real.sinh_eq]
    rw [show Real.log p * (ε / 2) = ε * Real.log p / 2 by ring,
      show Real.log p * -(ε / 2) = -(ε * Real.log p / 2) by ring]
    ring
  · simp only [symmetricDampedSource, squarefreeDampedSource, if_neg hk, mul_zero]

/-- Odd damping sector of the actual arithmetic source. -/
def oddDampedSource (ε : ℝ) (k : ℕ) : ℝ :=
  (symmetricDampedSource ε k - symmetricDampedSource (-ε) k) / 2

theorem oddDampedSource_eq_moebiusProjection (ε : ℝ) (k : ℕ) :
    oddDampedSource ε k = (1 - (moebius k : ℝ)) / 2 * symmetricDampedSource ε k := by
  rw [oddDampedSource, symmetricDampedSource_neg]
  ring

/-- The odd sector keeps exactly the negative-Möbius component. -/
theorem oddDampedSource_eq_negativeMoebius (ε : ℝ) (k : ℕ) :
    oddDampedSource ε k = if moebius k = -1 then symmetricDampedSource ε k else 0 := by
  rw [oddDampedSource_eq_moebiusProjection]
  by_cases hk : Squarefree k ∧ k ≠ 1
  · have hsq : (moebius k : ℝ) ^ 2 = 1 := by
      exact_mod_cast moebius_sq_eq_one_of_squarefree hk.1
    by_cases hm : moebius k = -1
    · simp only [hm, Int.cast_neg, Int.cast_one, if_true]
      ring
    · have hne : (moebius k : ℝ) ≠ -1 := by exact_mod_cast hm
      have hone : (moebius k : ℝ) = 1 := (sq_eq_one_iff.mp hsq).resolve_right hne
      simp only [if_neg hm, hone, sub_self, zero_div, zero_mul]
  · have hz : symmetricDampedSource ε k = 0 := by
      simp only [symmetricDampedSource, squarefreeDampedSource, if_neg hk, mul_zero]
    simp only [hz, mul_zero, ite_self]

theorem oddDampedSource_neg (ε : ℝ) (k : ℕ) :
    oddDampedSource (-ε) k = -oddDampedSource ε k := by
  simp only [oddDampedSource, neg_neg]
  ring

theorem symmetricDampedSource_zero (k : ℕ) : symmetricDampedSource 0 k = 0 := by
  simp only [symmetricDampedSource, squarefreeDampedSource_zero, mul_zero]

theorem oddDampedSource_zero (k : ℕ) : oddDampedSource 0 k = 0 := by
  simp only [oddDampedSource, neg_zero, sub_self, zero_div]

theorem hasDerivAt_symmetricDampedSource_zero (k : ℕ) :
    HasDerivAt (fun ε => symmetricDampedSource ε k) (primeLogWeight k) 0 := by
  have hg := (((hasDerivAt_id (0 : ℝ)).mul_const (Real.log k)).div_const 2).exp
  have h := hg.fun_mul (hasDerivAt_squarefreeDampedSource_zero k)
  simpa only [symmetricDampedSource, squarefreeDampedSource_zero, id_eq, mul_zero,
    zero_mul, zero_div, Real.exp_zero, one_mul, zero_add] using h

/-- Removing the even arithmetic sector preserves the prime tangent. -/
theorem hasDerivAt_oddDampedSource_zero (k : ℕ) :
    HasDerivAt (fun ε => oddDampedSource ε k) (primeLogWeight k) 0 := by
  have hn : HasDerivAt (fun ε => symmetricDampedSource (-ε) k)
      (primeLogWeight k * (-1)) 0 := by
    have hb : HasDerivAt (fun ε => symmetricDampedSource ε k) (primeLogWeight k)
        (-(0 : ℝ)) := by
      simpa only [neg_zero] using hasDerivAt_symmetricDampedSource_zero k
    exact hb.comp 0 (hasDerivAt_neg (0 : ℝ))
  have h := ((hasDerivAt_symmetricDampedSource_zero k).fun_sub hn).div_const 2
  change HasDerivAt
    (fun ε => (symmetricDampedSource ε k - symmetricDampedSource (-ε) k) / 2)
    (primeLogWeight k) 0
  exact h.congr_deriv (by ring)

theorem tendsto_oddDampedSource_div (k : ℕ) :
    Tendsto (fun ε => oddDampedSource ε k / ε)
      (𝓝[≠] 0) (𝓝 (primeLogWeight k)) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.mp (hasDerivAt_oddDampedSource_zero k)
  simpa only [zero_add, oddDampedSource_zero, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

/-- Reflection overlap after the arithmetic odd-sector projection. -/
def oddDampedReflectionOverlap (N : ℕ) (ε : ℝ) : ℝ :=
  additivePairWeight (oddDampedSource ε) N

theorem oddDampedReflectionOverlap_neg (N : ℕ) (ε : ℝ) :
    oddDampedReflectionOverlap N (-ε) = oddDampedReflectionOverlap N ε := by
  simp only [oddDampedReflectionOverlap, additivePairWeight, oddDampedSource_neg, neg_mul_neg]

theorem tendsto_oddDampedReflectionOverlap_div_sq (N : ℕ) :
    Tendsto (fun ε => oddDampedReflectionOverlap N ε / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (primePairWeight N)) := by
  have h := tendsto_finsetSum (antidiagonal N) (fun p _ =>
    (tendsto_oddDampedSource_div p.1).mul (tendsto_oddDampedSource_div p.2))
  simpa only [oddDampedReflectionOverlap, primePairWeight, additivePairWeight,
    sum_div, pow_two, div_mul_div_comm] using h

/-- Exact multiplier when damping doubles. -/
def dampingDoublingMultiplier (ε : ℝ) (k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors, (2 * Real.cosh (ε * Real.log p / 2))

theorem symmetricDampedSource_two_mul (ε : ℝ) (k : ℕ) :
    symmetricDampedSource (2 * ε) k =
      dampingDoublingMultiplier ε k * symmetricDampedSource ε k := by
  simp only [symmetricDampedSource_eq_prod_sinh]
  split_ifs with hk
  · rw [dampingDoublingMultiplier, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    rw [show 2 * ε * Real.log p / 2 = 2 * (ε * Real.log p / 2) by ring,
      Real.sinh_two_mul]
    ring
  · rw [mul_zero]

theorem oddDampedSource_two_mul (ε : ℝ) (k : ℕ) :
    oddDampedSource (2 * ε) k = dampingDoublingMultiplier ε k * oddDampedSource ε k := by
  simp only [oddDampedSource_eq_moebiusProjection, symmetricDampedSource_two_mul]
  ring

/-- Each distinct prime contributes at least a factor of two. -/
theorem primeFactorPower_le_dampingDoublingMultiplier (ε : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k.primeFactors.card ≤ dampingDoublingMultiplier ε k := by
  rw [← prod_const, dampingDoublingMultiplier]
  apply Finset.prod_le_prod
  · intro p _
    norm_num
  · intro p _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_cosh (ε * Real.log p / 2)) (show (0 : ℝ) ≤ 2 by norm_num)

theorem oddDampedSource_nonneg (ε : NNReal) (k : ℕ) : 0 ≤ oddDampedSource ε k := by
  rw [oddDampedSource_eq_negativeMoebius]
  split_ifs
  · rw [symmetricDampedSource, squarefreeDampedSource]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (pmPowerDampedDivisorCoeff_nonneg ε.coe_nonneg k)
    · simp only [mul_zero, le_refl]
  · exact le_refl 0

/-- Scaling damping scales the extracted tangent by the same factor. -/
theorem tendsto_oddDampedSource_mul_div (c : ℝ) (k : ℕ) :
    Tendsto (fun ε => oddDampedSource (c * ε) k / ε)
      (𝓝[≠] 0) (𝓝 (primeLogWeight k * c)) := by
  have hb : HasDerivAt (fun ε => oddDampedSource ε k) (primeLogWeight k) (c * 0) := by
    simpa only [mul_zero] using hasDerivAt_oddDampedSource_zero k
  have hi : HasDerivAt (fun ε : ℝ => c * ε) c 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul c
  have h := hasDerivAt_iff_tendsto_slope_zero.mp (hb.comp 0 hi)
  simpa only [Function.comp_def, zero_add, mul_zero, oddDampedSource_zero, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

theorem tendsto_oddDampedReflectionOverlap_mul_div_sq (N : ℕ) (c : ℝ) :
    Tendsto (fun ε => oddDampedReflectionOverlap N (c * ε) / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (c ^ 2 * primePairWeight N)) := by
  have h := tendsto_finsetSum (antidiagonal N) (fun p _ =>
    (tendsto_oddDampedSource_mul_div c p.1).mul (tendsto_oddDampedSource_mul_div c p.2))
  have hsum : (∑ p ∈ antidiagonal N,
      (primeLogWeight p.1 * c) * (primeLogWeight p.2 * c)) = c ^ 2 * primePairWeight N := by
    rw [primePairWeight, additivePairWeight, mul_sum]
    exact sum_congr rfl fun p _ => by ring
  simpa only [oddDampedReflectionOverlap, additivePairWeight, sum_div, pow_two,
    div_mul_div_comm, hsum] using h

/-- A two-scale test that discards the first composite damping order. -/
def oddDampedDyadicDefect (N : ℕ) (ε : ℝ) : ℝ :=
  16 * oddDampedReflectionOverlap N ε - oddDampedReflectionOverlap N (2 * ε)

theorem tendsto_oddDampedDyadicDefect_div_sq (N : ℕ) :
    Tendsto (fun ε => oddDampedDyadicDefect N ε / ε ^ 2)
      (𝓝[≠] 0) (𝓝 (12 * primePairWeight N)) := by
  have h := ((tendsto_oddDampedReflectionOverlap_div_sq N).const_mul 16).sub
    (tendsto_oddDampedReflectionOverlap_mul_div_sq N 2)
  have hc : 16 * primePairWeight N - 2 ^ 2 * primePairWeight N =
      12 * primePairWeight N := by ring
  simpa only [oddDampedDyadicDefect, sub_div, mul_div_assoc, hc] using h

private theorem oddDampedPair_amplification_cases (a b : ℕ) (ε : ℝ) :
    (a.Prime ∧ b.Prime) ∨ oddDampedSource ε a * oddDampedSource ε b = 0 ∨
      16 ≤ dampingDoublingMultiplier ε a * dampingDoublingMultiplier ε b := by
  by_cases hab : a.Prime ∧ b.Prime
  · exact Or.inl hab
  apply Or.inr
  by_cases ha : moebius a = -1
  · by_cases hb : moebius b = -1
    · apply Or.inr
      have hcount (k : ℕ) (hm : moebius k = -1) :
          1 ≤ k.primeFactors.card ∧ (¬ k.Prime → 3 ≤ k.primeFactors.card) := by
        have hsq : Squarefree k := by
          by_contra hn
          have hz := moebius_eq_zero_of_not_squarefree hn
          rw [hm] at hz
          norm_num at hz
        have hs : (-1 : ℤ) ^ k.primeFactors.card = -1 := by
          rw [← Sieve.moebius_eq_neg_one_pow_card_primeFactors hsq, hm]
        have hz : k.primeFactors.card ≠ 0 := by
          intro hc
          norm_num [hc] at hs
        have ht : k.primeFactors.card ≠ 2 := by
          intro hc
          norm_num [hc] at hs
        have ho : k.primeFactors.card = 1 → k.Prime := fun hc =>
          Nat.squarefree_and_prime_pow_iff_prime.mp
            ⟨hsq, isPrimePow_iff_card_primeFactors_eq_one.mpr hc⟩
        exact ⟨by omega, fun hn => by have := mt ho hn; omega⟩
      have hca := hcount a ha
      have hcb := hcount b hb
      have hdegree : 4 ≤ a.primeFactors.card + b.primeFactors.card := by
        by_cases hp : a.Prime
        · have := hcb.2 (fun hq => hab ⟨hp, hq⟩)
          omega
        · have := hca.2 hp
          omega
      have hDa := primeFactorPower_le_dampingDoublingMultiplier ε a
      have hDb := primeFactorPower_le_dampingDoublingMultiplier ε b
      calc
        (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
        _ ≤ 2 ^ (a.primeFactors.card + b.primeFactors.card) :=
          pow_le_pow_right₀ (by norm_num) hdegree
        _ = (2 : ℝ) ^ a.primeFactors.card * 2 ^ b.primeFactors.card := pow_add _ _ _
        _ ≤ _ := mul_le_mul hDa hDb (by positivity)
          (le_trans (by positivity : 0 ≤ (2 : ℝ) ^ a.primeFactors.card) hDa)
    · left
      simp only [oddDampedSource_eq_negativeMoebius, if_neg hb, mul_zero]
  · left
    simp only [oddDampedSource_eq_negativeMoebius, if_neg ha, zero_mul]

private theorem three_mul_sinh_le (x : NNReal) :
    3 * Real.sinh x ≤ (x : ℝ) * (Real.cosh x + 2) := by
  have hd (t : ℝ) : HasDerivAt
      (fun u : ℝ => u * (Real.cosh u + 2) - 3 * Real.sinh u)
      (t * Real.sinh t + 2 - 2 * Real.cosh t) t := by
    have h := ((hasDerivAt_id t).fun_mul ((Real.hasDerivAt_cosh t).add_const 2)).fun_sub
      ((Real.hasDerivAt_sinh t).const_mul 3)
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hm : MonotoneOn
      (fun u : ℝ => u * (Real.cosh u + 2) - 3 * Real.sinh u) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) ?_
    intro t _
    rw [(hd t).deriv]
    linarith only [HTGeometry.two_cosh_sub_two_le_self_mul_sinh t]
  have h := hm Set.self_mem_Ici x.coe_nonneg x.coe_nonneg
  simpa only [Real.cosh_zero, Real.sinh_zero, zero_mul, mul_zero, sub_zero,
    sub_nonneg] using h

/-- The quartic term cancels, leaving a global quadratic upper bound. -/
private theorem sinh_pair_dyadicDefect_le (x y : NNReal) :
    Real.sinh x * Real.sinh y * (4 - Real.cosh x * Real.cosh y) ≤
      3 * (x : ℝ) * (y : ℝ) := by
  have hsx := Real.sinh_nonneg_iff.mpr x.coe_nonneg
  have hsy := Real.sinh_nonneg_iff.mpr y.coe_nonneg
  by_cases h : 0 ≤ 4 - Real.cosh x * Real.cosh y
  · have hp := mul_le_mul (three_mul_sinh_le x) (three_mul_sinh_le y)
      (by positivity) (by positivity)
    have hp' := mul_le_mul_of_nonneg_right hp h
    have hx : 0 ≤ Real.cosh x - 1 := sub_nonneg.mpr (Real.one_le_cosh x)
    have hy : 0 ≤ Real.cosh y - 1 := sub_nonneg.mpr (Real.one_le_cosh y)
    have hr : 0 ≤
        3 * (Real.cosh x - 1) ^ 2 + 3 * (Real.cosh y - 1) ^ 2 +
        12 * (Real.cosh x - 1) * (Real.cosh y - 1) +
        4 * (Real.cosh x - 1) ^ 2 * (Real.cosh y - 1) +
        4 * (Real.cosh x - 1) * (Real.cosh y - 1) ^ 2 +
        (Real.cosh x - 1) ^ 2 * (Real.cosh y - 1) ^ 2 := by positivity
    have hc : (Real.cosh x + 2) * (Real.cosh y + 2) *
        (4 - Real.cosh x * Real.cosh y) ≤ 27 := by nlinarith only [hr]
    have hc' := mul_le_mul_of_nonneg_left hc
      (mul_nonneg x.coe_nonneg y.coe_nonneg)
    nlinarith only [hp', hc']
  · exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsx hsy)
      (le_of_not_ge h)).trans (by positivity)

/-- Every reflected pair obeys the prime-only two-scale minorant. -/
theorem oddDampedPair_dyadicDefect_le (a b : ℕ) (ε : NNReal) :
    16 * (oddDampedSource ε a * oddDampedSource ε b) -
        oddDampedSource (2 * ε) a * oddDampedSource (2 * ε) b ≤
      12 * (ε : ℝ) ^ 2 * (primeLogWeight a * primeLogWeight b) := by
  by_cases hab : a.Prime ∧ b.Prime
  · obtain ⟨ha, hb⟩ := hab
    have hsource (p : ℕ) (hp : p.Prime) (t : ℝ) :
        oddDampedSource t p = 2 * Real.sinh (t * Real.log p / 2) := by
      rw [oddDampedSource_eq_negativeMoebius, if_pos (moebius_apply_prime hp),
        symmetricDampedSource_eq_prod_sinh, if_pos ⟨hp.squarefree, hp.ne_one⟩,
        hp.primeFactors, prod_singleton]
    have hla : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha.one_le)
    have hlb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hb.one_le)
    have hxy := sinh_pair_dyadicDefect_le
      ⟨(ε : ℝ) * Real.log a / 2, by positivity⟩
      ⟨(ε : ℝ) * Real.log b / 2, by positivity⟩
    change Real.sinh (ε * Real.log a / 2) * Real.sinh (ε * Real.log b / 2) *
      (4 - Real.cosh (ε * Real.log a / 2) * Real.cosh (ε * Real.log b / 2)) ≤
        3 * (ε * Real.log a / 2) * (ε * Real.log b / 2) at hxy
    simp only [hsource a ha, hsource b hb, primeLogWeight, if_pos ha, if_pos hb]
    rw [show 2 * (ε : ℝ) * Real.log a / 2 = 2 * (ε * Real.log a / 2) by ring,
      show 2 * (ε : ℝ) * Real.log b / 2 = 2 * (ε * Real.log b / 2) by ring,
      Real.sinh_two_mul, Real.sinh_two_mul]
    nlinarith only [hxy]
  · have hnonneg : 0 ≤ 12 * (ε : ℝ) ^ 2 * (primeLogWeight a * primeLogWeight b) :=
      mul_nonneg (by positivity) (mul_nonneg (primeLogWeight_nonneg a) (primeLogWeight_nonneg b))
    rcases (oddDampedPair_amplification_cases a b ε).resolve_left hab with hz | hD
    · have hz2 : oddDampedSource (2 * ε) a * oddDampedSource (2 * ε) b = 0 := by
        rw [oddDampedSource_two_mul, oddDampedSource_two_mul, mul_mul_mul_comm, hz, mul_zero]
      simpa only [hz, hz2, mul_zero, sub_zero] using hnonneg
    · have hw := mul_nonneg (oddDampedSource_nonneg ε a) (oddDampedSource_nonneg ε b)
      have h := mul_le_mul_of_nonneg_right hD hw
      rw [oddDampedSource_two_mul, oddDampedSource_two_mul]
      nlinarith only [h, hnonneg]

/-- The finite two-scale defect never overestimates its prime tangent. -/
theorem oddDampedDyadicDefect_le_primePairWeight (N : ℕ) (ε : ℝ) :
    oddDampedDyadicDefect N ε ≤ 12 * ε ^ 2 * primePairWeight N := by
  have hpos (t : NNReal) :
      oddDampedDyadicDefect N t ≤ 12 * (t : ℝ) ^ 2 * primePairWeight N := by
    simp only [oddDampedDyadicDefect, oddDampedReflectionOverlap, primePairWeight,
      additivePairWeight, mul_sum, ← sum_sub_distrib]
    exact sum_le_sum fun p _ => oddDampedPair_dyadicDefect_le p.1 p.2 t
  by_cases hε : 0 ≤ ε
  · exact hpos ⟨ε, hε⟩
  · have h : oddDampedDyadicDefect N (-ε) ≤ 12 * (-ε) ^ 2 * primePairWeight N :=
      hpos ⟨-ε, neg_nonneg.mpr (le_of_not_ge hε)⟩
    simpa only [oddDampedDyadicDefect, mul_neg, oddDampedReflectionOverlap_neg,
      neg_sq] using h

/-- A globally valid lower approximation, including damping zero. -/
def oddDampedExtractionMinorant (N : ℕ) (ε : ℝ) : ℝ :=
  oddDampedDyadicDefect N ε / (12 * ε ^ 2)

theorem oddDampedExtractionMinorant_le (N : ℕ) (ε : ℝ) :
    oddDampedExtractionMinorant N ε ≤ primePairWeight N := by
  by_cases hε : ε = 0
  · simp only [oddDampedExtractionMinorant, hε, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, div_zero]
    exact primePairWeight_nonneg N
  · exact (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_ne_zero hε))).mpr
      (by simpa only [mul_comm] using oddDampedDyadicDefect_le_primePairWeight N ε)

theorem tendsto_oddDampedExtractionMinorant (N : ℕ) :
    Tendsto (oddDampedExtractionMinorant N) (𝓝[≠] 0) (𝓝 (primePairWeight N)) := by
  have h := (tendsto_oddDampedDyadicDefect_div_sq N).div_const 12
  have he (ε : ℝ) : oddDampedDyadicDefect N ε / ε ^ 2 / 12 =
      oddDampedExtractionMinorant N ε := by
    rw [oddDampedExtractionMinorant, div_div, mul_comm (ε ^ 2) 12]
  simpa only [he, mul_div_cancel_left₀ (primePairWeight N) (by norm_num : (12 : ℝ) ≠ 0)] using h

/-- The actual odd source dominates its prime tangent at nonnegative damping. -/
theorem primeLogWeight_mul_damping_le (k : ℕ) (ε : NNReal) :
    (ε : ℝ) * primeLogWeight k ≤ oddDampedSource ε k := by
  by_cases hk : k.Prime
  · rw [primeLogWeight, if_pos hk, oddDampedSource_eq_negativeMoebius,
      if_pos (moebius_apply_prime hk), symmetricDampedSource_eq_prod_sinh,
      if_pos ⟨hk.squarefree, hk.ne_one⟩, hk.primeFactors, prod_singleton]
    have hl : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk.one_le)
    have hs := HTGeometry.self_le_sinh_of_nonneg
      (show 0 ≤ (ε : ℝ) * Real.log k / 2 by positivity)
    linarith only [hs]
  · rw [primeLogWeight, if_neg hk, mul_zero]
    exact oddDampedSource_nonneg ε k

/-- The one-scale reading is a majorant; together the two readings bracket the tangent. -/
theorem primePairWeight_mul_sq_le_oddDampedReflectionOverlap (N : ℕ) (ε : ℝ) :
    ε ^ 2 * primePairWeight N ≤ oddDampedReflectionOverlap N ε := by
  have hpos (t : NNReal) :
      (t : ℝ) ^ 2 * primePairWeight N ≤ oddDampedReflectionOverlap N t := by
    simp only [primePairWeight, oddDampedReflectionOverlap, additivePairWeight, mul_sum]
    apply sum_le_sum
    intro p _
    have h := mul_le_mul (primeLogWeight_mul_damping_le p.1 t)
      (primeLogWeight_mul_damping_le p.2 t)
      (mul_nonneg t.coe_nonneg (primeLogWeight_nonneg p.2))
      (oddDampedSource_nonneg t p.1)
    nlinarith only [h]
  by_cases hε : 0 ≤ ε
  · exact hpos ⟨ε, hε⟩
  · have h : (-ε) ^ 2 * primePairWeight N ≤ oddDampedReflectionOverlap N (-ε) :=
      hpos ⟨-ε, neg_nonneg.mpr (le_of_not_ge hε)⟩
    simpa only [neg_sq, oddDampedReflectionOverlap_neg] using h

/-- Doubling damping increases every factor of the amplification. -/
theorem dampingDoublingMultiplier_le_two_mul (ε : ℝ) (k : ℕ) :
    dampingDoublingMultiplier ε k ≤ dampingDoublingMultiplier (2 * ε) k := by
  simp only [dampingDoublingMultiplier]
  apply Finset.prod_le_prod
  · intro p _
    exact mul_nonneg (by norm_num) (Real.cosh_pos _).le
  · intro p _
    rw [show 2 * ε * Real.log p / 2 = 2 * (ε * Real.log p / 2) by ring,
      Real.cosh_two_mul, Real.sinh_sq]
    nlinarith only [Real.one_le_cosh (ε * Real.log p / 2),
      sq_nonneg (Real.cosh (ε * Real.log p / 2) - 1)]

private theorem cosh_pair_refinement_nonneg (x y : ℝ) :
    0 ≤ (2 * Real.cosh x * (2 * Real.cosh y)) *
      (2 * Real.cosh (2 * x) * (2 * Real.cosh (2 * y)) - 20) + 64 := by
  let D := 2 * Real.cosh x * (2 * Real.cosh y)
  let E := 2 * Real.cosh (2 * x) * (2 * Real.cosh (2 * y))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hp : 0 ≤ (Real.cosh x ^ 2 - 1) * (Real.cosh y ^ 2 - 1) := by
    rw [← Real.sinh_sq, ← Real.sinh_sq]
    positivity
  have hE : D ^ 2 / 2 - 4 ≤ E := by
    dsimp [D, E]
    rw [Real.cosh_two_mul, Real.cosh_two_mul, Real.sinh_sq, Real.sinh_sq]
    nlinarith only [hp]
  have hm := mul_le_mul_of_nonneg_left hE hD
  have hr : 0 ≤ (D - 4) ^ 2 * (D + 8) / 2 := by positivity
  change 0 ≤ D * (E - 20) + 64
  nlinarith only [hm, hr]

private theorem oddDampedPair_threeScale_nonneg (a b : ℕ) (ε : NNReal) :
    0 ≤ oddDampedSource (4 * ε) a * oddDampedSource (4 * ε) b -
      20 * (oddDampedSource (2 * ε) a * oddDampedSource (2 * ε) b) +
      64 * (oddDampedSource ε a * oddDampedSource ε b) := by
  let P := oddDampedSource ε a * oddDampedSource ε b
  let D := dampingDoublingMultiplier ε a * dampingDoublingMultiplier ε b
  let E := dampingDoublingMultiplier (2 * ε) a * dampingDoublingMultiplier (2 * ε) b
  have hP : 0 ≤ P :=
    mul_nonneg (oddDampedSource_nonneg ε a) (oddDampedSource_nonneg ε b)
  have h2 : oddDampedSource (2 * ε) a * oddDampedSource (2 * ε) b = D * P := by
    rw [oddDampedSource_two_mul, oddDampedSource_two_mul]
    dsimp [D, P]
    ring
  have h4 : oddDampedSource (4 * ε) a * oddDampedSource (4 * ε) b = E * (D * P) := by
    calc
      _ = (dampingDoublingMultiplier (2 * ε) a * oddDampedSource (2 * ε) a) *
          (dampingDoublingMultiplier (2 * ε) b * oddDampedSource (2 * ε) b) := by
        rw [show 4 * (ε : ℝ) = 2 * (2 * ε) by ring,
          oddDampedSource_two_mul (2 * ε) a, oddDampedSource_two_mul (2 * ε) b]
      _ = E * (oddDampedSource (2 * ε) a * oddDampedSource (2 * ε) b) := by
        dsimp [E]
        ring
      _ = _ := by rw [h2]
  rw [h2, h4]
  change 0 ≤ E * (D * P) - 20 * (D * P) + 64 * P
  rcases oddDampedPair_amplification_cases a b ε with hab | hz | hD
  · have hc := cosh_pair_refinement_nonneg (ε * Real.log a / 2) (ε * Real.log b / 2)
    have hc' : 0 ≤ D * (E - 20) + 64 := by
      simpa only [D, E, dampingDoublingMultiplier, hab.1.primeFactors,
        hab.2.primeFactors, prod_singleton,
        show 2 * (ε : ℝ) * Real.log a / 2 = 2 * (ε * Real.log a / 2) by ring,
        show 2 * (ε : ℝ) * Real.log b / 2 = 2 * (ε * Real.log b / 2) by ring] using hc
    nlinarith only [mul_nonneg hP hc']
  · have hz' : P = 0 := hz
    simp only [hz', mul_zero, sub_zero, add_zero, le_refl]
  · have hDa : 0 ≤ dampingDoublingMultiplier ε a :=
      le_trans (by positivity) (primeFactorPower_le_dampingDoublingMultiplier ε a)
    have hDb : 0 ≤ dampingDoublingMultiplier ε b :=
      le_trans (by positivity) (primeFactorPower_le_dampingDoublingMultiplier ε b)
    have hEa : 0 ≤ dampingDoublingMultiplier (2 * ε) a :=
      le_trans (by positivity) (primeFactorPower_le_dampingDoublingMultiplier (2 * ε) a)
    have hDE : D ≤ E := mul_le_mul
      (dampingDoublingMultiplier_le_two_mul ε a)
      (dampingDoublingMultiplier_le_two_mul ε b) hDb hEa
    have hD' : 16 ≤ D := hD
    have hm := mul_le_mul_of_nonneg_left hDE (mul_nonneg hDa hDb)
    have hr : 0 ≤ (D - 16) * (D - 4) := mul_nonneg
      (sub_nonneg.mpr hD') (sub_nonneg.mpr (le_trans (by norm_num : (4 : ℝ) ≤ 16) hD'))
    have hc : 0 ≤ D * (E - 20) + 64 := by nlinarith only [hm, hr]
    nlinarith only [mul_nonneg hP hc]

/-- The positive compensation paid by three consecutive damping scales. -/
def oddDampedRefinementGain (N : ℕ) (ε : ℝ) : ℝ :=
  oddDampedReflectionOverlap N (4 * ε) - 20 * oddDampedReflectionOverlap N (2 * ε) +
    64 * oddDampedReflectionOverlap N ε

theorem oddDampedRefinementGain_nonneg (N : ℕ) (ε : ℝ) :
    0 ≤ oddDampedRefinementGain N ε := by
  have hpos (t : NNReal) : 0 ≤ oddDampedRefinementGain N t := by
    simp only [oddDampedRefinementGain, oddDampedReflectionOverlap, additivePairWeight,
      mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_nonneg fun p _ => oddDampedPair_threeScale_nonneg p.1 p.2 t
  by_cases hε : 0 ≤ ε
  · exact hpos ⟨ε, hε⟩
  · have h : 0 ≤ oddDampedRefinementGain N (-ε) :=
      hpos ⟨-ε, neg_nonneg.mpr (le_of_not_ge hε)⟩
    simpa only [oddDampedRefinementGain, mul_neg, oddDampedReflectionOverlap_neg] using h

/-- Exact gain in the lower approximation when damping is halved. -/
theorem oddDampedExtractionMinorant_sub_two_mul (N : ℕ) (ε : ℝ) :
    oddDampedExtractionMinorant N ε - oddDampedExtractionMinorant N (2 * ε) =
      oddDampedRefinementGain N ε / (48 * ε ^ 2) := by
  by_cases hε : ε = 0
  · simp [hε, oddDampedExtractionMinorant]
  · dsimp [oddDampedExtractionMinorant, oddDampedDyadicDefect, oddDampedRefinementGain]
    rw [show 2 * (2 * ε) = 4 * ε by ring]
    field_simp
    ring

/-- The finite minorants increase under successive damping halving. -/
theorem oddDampedExtractionMinorant_two_mul_le (N : ℕ) (ε : ℝ) :
    oddDampedExtractionMinorant N (2 * ε) ≤ oddDampedExtractionMinorant N ε := by
  rw [← sub_nonneg, oddDampedExtractionMinorant_sub_two_mul]
  exact div_nonneg (oddDampedRefinementGain_nonneg N ε) (by positivity)

/-- A prime pair exists exactly when odd-sector doubling is slower than factor sixteen. -/
theorem primePair_iff_positive_oddDampedDyadicDefect (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N) ↔
      ∃ ε : ℝ, 0 < ε ∧ 0 < oddDampedDyadicDefect N ε := by
  constructor
  · intro hpq
    have hG : 0 < 12 * primePairWeight N :=
      mul_pos (by norm_num) ((primePairWeight_pos_iff N).mpr hpq)
    have hlim := (tendsto_oddDampedDyadicDefect_div_sq N).mono_left (nhdsGT_le_nhdsNE 0)
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < oddDampedDyadicDefect N ε / ε ^ 2 :=
      hlim.eventually (eventually_gt_nhds hG)
    have hepos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, hε, hval⟩ := (hepos.and hpos).exists
    have hnum := (lt_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hε))).mp hval
    exact ⟨ε, hε, by simpa only [zero_mul] using hnum⟩
  · rintro ⟨ε, _, hdef⟩
    apply (primePairWeight_pos_iff N).mp
    by_contra hn
    have hnp : primePairWeight N ≤ 0 := le_of_not_gt hn
    have h := (oddDampedDyadicDefect_le_primePairWeight N ε).trans
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp)
    exact (not_lt_of_ge h) hdef

/-- Goldbach in the finite two-scale language, with no analytic premise. -/
theorem goldbach_iff_positive_oddDampedDyadicDefect :
    (∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * (n + 2)) ↔
      ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ 0 < oddDampedDyadicDefect (2 * (n + 2)) ε := by
  simp_rw [primePair_iff_positive_oddDampedDyadicDefect]

end

end GaloisForLFunctions.Goldbach
