import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Riemann hypothesis and additive prime-pair statistics

The total weight of prime pairs in a square is exactly `θ(x)²`. Its error
of order `x √x log²x` is equivalent to RH. At an individual sum, the prime-pair
weight also contains a reflected correlation of the centered prime weights.
Its positivity is exactly the binary Goldbach condition at that sum.

The boxed average criterion does not assert positivity of each coefficient.
All pair weights below use actual primes, with prime powers removed.
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

end

end GaloisForLFunctions.Goldbach
