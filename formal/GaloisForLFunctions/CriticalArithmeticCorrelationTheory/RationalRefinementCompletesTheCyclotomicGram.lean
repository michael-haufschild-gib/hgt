import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AllDivisorConductorsRecoverTheDiscreteBridge
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheIntersectionOfTorsionOrbits
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabSlopeLawAndPrimeHorizonDissipation

/-!
# Rational refinement is positive conductor completion

On a grid of spacing `1 / L`, the signed arithmetic curvature is a positive
sum of primitive prefix energies. The contributing orders are exactly those
whose `L`-th powers have primitive order `m`. Centering therefore gives a
complete Gram identity, including every mixed coefficient. Finer resolution
changes the conductor family rather than introducing signed spectral weights.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticEffectivityTheory TransHorizonIncidenceMechanics

/-- Primitive orders whose `L`-th powers have order `m`. -/
def refinedCyclotomicConductors (m L : ℕ) : Finset ℕ :=
  (m * L).divisors.filter (fun e => e / Nat.gcd e L = m)

private theorem moebius_dvd_projector {m : ℕ} (hm : 0 < m) (c : ℕ) :
    (∑ d ∈ m.divisors, (μ (m / d) : ℝ) * (if c ∣ d then 1 else 0)) =
      if m = c then 1 else 0 := by
  apply sum_divisors_moebius_eq_of (f := fun i => if i = c then 1 else 0) ?_ hm
  intro b hb
  simp only [sum_ite_eq', Nat.mem_divisors, ne_eq, hb.ne', not_false_eq_true, and_true]

/-- Möbius inversion after dilation is an exact positive projection onto
the lifted primitive orders. -/
theorem moebius_dilated_divisor_sum {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (F : ℕ → ℝ) :
    (∑ d ∈ m.divisors, (μ (m / d) : ℝ) * ∑ e ∈ (d * L).divisors, F e) =
      ∑ e ∈ refinedCyclotomicConductors m L, F e := by
  have he (d : ℕ) (hd : d ∈ m.divisors) :
      (∑ e ∈ (d * L).divisors, F e) =
        ∑ e ∈ (m * L).divisors, if e ∣ L * d then F e else 0 := by
    rw [← sum_filter]
    congr 1
    rw [mul_comm L d, Nat.divisors_filter_dvd_of_dvd (Nat.mul_pos hm hL).ne'
      (Nat.mul_dvd_mul_right L (Nat.dvd_of_mem_divisors hd))]
  calc
    _ = ∑ d ∈ m.divisors, ∑ e ∈ (m * L).divisors,
        (μ (m / d) : ℝ) * (if e ∣ L * d then F e else 0) := by
      exact sum_congr rfl fun d hd => by rw [he d hd, mul_sum]
    _ = ∑ e ∈ (m * L).divisors, ∑ d ∈ m.divisors,
        (μ (m / d) : ℝ) * (if e ∣ L * d then F e else 0) := sum_comm
    _ = ∑ e ∈ (m * L).divisors,
        if e / Nat.gcd e L = m then F e else 0 := by
      refine sum_congr rfl fun e he => ?_
      simp_rw [dvd_mul_iff_div_gcd_dvd (Nat.pos_of_mem_divisors he)]
      have h := congrArg (fun t : ℝ => t * F e)
        (moebius_dvd_projector hm (e / Nat.gcd e L))
      simpa only [sum_mul, mul_ite, mul_one, mul_zero, ite_mul, one_mul,
        zero_mul, eq_comm] using h
    _ = _ := (sum_filter _ _ _).symm

private theorem scaled_fract_remainder {d L : ℕ} (hd : 0 < d) (hL : 0 < L) (k : ℕ) :
    (L : ℝ) ^ 2 * ((d : ℝ) ^ 2 * Int.fract (((k : ℝ) / L) / d) *
      (1 - Int.fract (((k : ℝ) / L) / d))) =
      (k % (d * L) : ℕ) * ((d * L : ℕ) - (k % (d * L) : ℕ) : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [div_div, mul_comm (L : ℝ) d, ← Nat.cast_mul,
    Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  field_simp [hdR, hLR]
  <;> ring

/-- The rational-grid curvature is exactly a sum of positive primitive
energies at the lifted conductors. -/
theorem arithmeticOverlapCurvature_rational_refinement {m L : ℕ}
    (hm : 1 < m) (hL : 0 < L) (k : ℕ) :
    (L : ℝ) ^ 2 * arithmeticOverlapCurvature m ((k : ℝ) / L) =
      ∑ e ∈ refinedCyclotomicConductors m L, primitiveRootPrefixEnergy e k := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  have hz : (∑ d ∈ m.divisors, (μ (m / d) : ℝ)) = 0 := by
    rw [sum_divisors_moebius hm0, if_neg (by omega)]
  calc
    _ = ∑ d ∈ m.divisors, (μ (m / d) : ℝ) *
        ((k % (d * L) : ℕ) * ((d * L : ℕ) - (k % (d * L) : ℕ) : ℝ)) := by
      rw [arithmeticOverlapCurvature, mul_sum]
      refine sum_congr rfl fun d hd => ?_
      have hs := scaled_fract_remainder (Nat.pos_of_mem_divisors hd) hL k
      linear_combination (μ (m / d) : ℝ) * hs
    _ = ∑ d ∈ m.divisors, (μ (m / d) : ℝ) *
        ((∑ e ∈ (d * L).divisors, primitiveRootPrefixEnergy e k) - (k : ℝ) ^ 2) := by
      refine sum_congr rfl fun d hd => ?_
      rw [sum_divisors_primitiveRootPrefixEnergy
        (Nat.mul_pos (Nat.pos_of_mem_divisors hd) hL)]
      ring
    _ = ∑ d ∈ m.divisors, (μ (m / d) : ℝ) *
        ∑ e ∈ (d * L).divisors, primitiveRootPrefixEnergy e k := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hz, zero_mul, sub_zero]
    _ = _ := moebius_dilated_divisor_sum hm0 hL _

/-- Centering the signed arithmetic distance gives its candidate Gram kernel. -/
def arithmeticOverlapGram (m : ℕ) (x y : ℝ) : ℝ :=
  (arithmeticOverlapCurvature m x + arithmeticOverlapCurvature m y -
    arithmeticOverlapCurvature m |x - y|) / 2

private theorem abs_nat_quotient_sub {L : ℕ} (hL : 0 < L) (i j : ℕ) :
    |(i : ℝ) / L - (j : ℝ) / L| = (Nat.dist i j : ℕ) / (L : ℝ) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [← sub_div, abs_div, abs_of_pos hLR]
  congr 1
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hij))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right hji, Nat.cast_sub hji,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hji))]

/-- Every mixed entry of a rational-grid overlap Gram is a positive sum of
primitive Gram entries; the equality is exact before taking a limit. -/
theorem arithmeticOverlapGram_rational_refinement {m L : ℕ}
    (hm : 1 < m) (hL : 0 < L) (i j : ℕ) :
    (L : ℝ) ^ 2 * arithmeticOverlapGram m ((i : ℝ) / L) ((j : ℝ) / L) =
      ∑ e ∈ refinedCyclotomicConductors m L, primitivePrefixGram e i j := by
  unfold arithmeticOverlapGram
  rw [abs_nat_quotient_sub hL]
  simp only [primitivePrefixGram, ← sum_div, sum_sub_distrib, sum_add_distrib]
  rw [← arithmeticOverlapCurvature_rational_refinement hm hL i,
    ← arithmeticOverlapCurvature_rational_refinement hm hL j,
    ← arithmeticOverlapCurvature_rational_refinement hm hL (Nat.dist i j)]
  ring

/-- The rational-grid overlap kernel is positive on every finite real
coefficient family, without a sign restriction on those coefficients. -/
theorem arithmeticOverlapGram_rational_quadratic_nonneg {ι : Type*} (s : Finset ι)
    {m L : ℕ} (hm : 1 < m) (hL : 0 < L) (a : ι → ℝ) (k : ι → ℕ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      a i * a j * arithmeticOverlapGram m ((k i : ℝ) / L) ((k j : ℝ) / L) := by
  have hs : (L : ℝ) ^ 2 * (∑ i ∈ s, ∑ j ∈ s,
      a i * a j * arithmeticOverlapGram m ((k i : ℝ) / L) ((k j : ℝ) / L)) =
      ∑ e ∈ refinedCyclotomicConductors m L, ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * primitivePrefixGram e (k i) (k j) := by
    simp only [mul_sum]
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, ∑ e ∈ refinedCyclotomicConductors m L,
          a i * a j * primitivePrefixGram e (k i) (k j) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [← mul_sum, ← arithmeticOverlapGram_rational_refinement hm hL]
        ring
      _ = ∑ i ∈ s, ∑ e ∈ refinedCyclotomicConductors m L, ∑ j ∈ s,
          a i * a j * primitivePrefixGram e (k i) (k j) :=
        sum_congr rfl fun _ _ => sum_comm
      _ = _ := sum_comm
  have hn : 0 ≤ ∑ e ∈ refinedCyclotomicConductors m L, ∑ i ∈ s, ∑ j ∈ s,
      a i * a j * primitivePrefixGram e (k i) (k j) :=
    sum_nonneg fun e he => primitivePrefixGram_quadratic_nonneg s
      (Nat.pos_of_mem_divisors (mem_filter.mp he).1) a k
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hLR)).mp (hs.symm ▸ hn)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.arithmeticOverlapCurvature_rational_refinement
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.arithmeticOverlapGram_rational_quadratic_nonneg
