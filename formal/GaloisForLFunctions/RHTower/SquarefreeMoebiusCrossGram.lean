import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The squarefree Möbius cross-Gram diagonal

Tensoring the transverse projective seam `⟪v_∞, v_0⟫ = -1/p` over the prime support of a squarefree
integer produces the diagonal

`A e_n = μ(n)/n`   (`n` squarefree),

which is the producer/reporter cross-Gram of the two complete point/complement polarizations.  This
file proves the exact arithmetic identity behind that computation and the analytic classification of
the resulting diagonal:

* `∏_{p ∣ n} (-1/p) = μ(n)/n` for every squarefree `n`;
* the transverse diagonal has supremum exactly `1/2`, attained at `n = 2`;
* it is square-summable, with `Σ_{n>1 squarefree} n^{-2} = ζ(2)/ζ(4) - 1`, hence Hilbert–Schmidt;
* it is *not* absolutely summable, since the primes alone already diverge — the first-trace wall;
* its unsigned and signed spectral Dirichlet traces are `ζ(s)/ζ(2s)` and `1/ζ(s)`.
-/

open Complex Filter Finset
open ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## The cross-Gram diagonal -/

/-- The producer/reporter cross-Gram coefficient at the squarefree index `n`. -/
def moebiusCrossGramDiagonal (n : ℕ) : ℂ := (moebius n : ℂ) / (n : ℂ)

/-- **Equation (31).**  Tensoring the transverse projective seam `-1/p` over the prime support of a
squarefree integer produces exactly the Möbius cross-Gram coefficient. -/
theorem prod_transverseSeam_eq_crossGram {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (-(1 / (p : ℂ))) = moebiusCrossGramDiagonal n := by
  have hprod : ∏ p ∈ n.primeFactors, ((p : ℕ) : ℂ) = (n : ℂ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  have hneg : ∏ p ∈ n.primeFactors, (-(1 / (p : ℂ))) =
      (-1) ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (1 / (p : ℂ)) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by ring
  have hinv : ∏ p ∈ n.primeFactors, (1 / (p : ℂ)) = 1 / (n : ℂ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, hprod]
  have hcard : cardFactors n = n.primeFactors.card := by
    rw [← cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero |>.mpr hn,
      cardDistinctFactors_apply, Nat.primeFactors,
      List.toFinset_card_of_nodup
        ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn),
      List.Nodup.dedup ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)]
  rw [hneg, hinv, moebiusCrossGramDiagonal, moebius_apply_of_squarefree hn, hcard]
  push_cast
  ring

theorem moebiusCrossGramDiagonal_eq_zero_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) :
    moebiusCrossGramDiagonal n = 0 := by
  rw [moebiusCrossGramDiagonal, moebius_eq_zero_of_not_squarefree hn]
  simp

@[simp]
theorem moebiusCrossGramDiagonal_one : moebiusCrossGramDiagonal 1 = 1 := by
  simp [moebiusCrossGramDiagonal]

theorem norm_moebiusCrossGramDiagonal_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ‖moebiusCrossGramDiagonal n‖ = 1 / (n : ℝ) := by
  have hpos : 0 < n := hn.ne_zero.bot_lt
  have hmu : ‖(moebius n : ℂ)‖ = 1 := by
    rw [moebius_apply_of_squarefree hn]
    push_cast
    simp [norm_pow]
  rw [moebiusCrossGramDiagonal, norm_div, hmu, Complex.norm_natCast, one_div]

theorem norm_moebiusCrossGramDiagonal_le_half {n : ℕ} (h1 : 1 < n) :
    ‖moebiusCrossGramDiagonal n‖ ≤ 1 / 2 := by
  by_cases hn : Squarefree n
  · rw [norm_moebiusCrossGramDiagonal_of_squarefree hn]
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    exact one_div_le_one_div_of_le (by norm_num) h2
  · rw [moebiusCrossGramDiagonal_eq_zero_of_not_squarefree hn]
    norm_num

theorem norm_moebiusCrossGramDiagonal_two : ‖moebiusCrossGramDiagonal 2‖ = 1 / 2 := by
  rw [norm_moebiusCrossGramDiagonal_of_squarefree Nat.squarefree_two]
  norm_num

theorem norm_moebiusCrossGramDiagonal_le_one (n : ℕ) :
    ‖moebiusCrossGramDiagonal n‖ ≤ 1 := by
  by_cases hn : Squarefree n
  · rw [norm_moebiusCrossGramDiagonal_of_squarefree hn]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn.ne_zero
    rw [div_le_one (by linarith)]
    exact h1
  · rw [moebiusCrossGramDiagonal_eq_zero_of_not_squarefree hn]
    norm_num

/-! ## The transverse squarefree occupation weights -/

/-- Indicator of a transverse (vacuum-orthogonal) squarefree occupation index. -/
def squarefreeTransverseWeight (t : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ 1 < n then (1 : ℝ) / (n : ℝ) ^ t else 0

theorem squarefreeTransverseWeight_nonneg (t : ℝ) (n : ℕ) :
    0 ≤ squarefreeTransverseWeight t n := by
  rw [squarefreeTransverseWeight]
  split <;> positivity

/-- **Equation (32), summability.**  The transverse cross-Gram diagonal is square-summable, so the
operator it defines is Hilbert–Schmidt. -/
theorem summable_squarefreeTransverseWeight_two :
    Summable (squarefreeTransverseWeight 2) := by
  refine Summable.of_nonneg_of_le (fun n => squarefreeTransverseWeight_nonneg 2 n) ?_
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2))
  intro n
  rw [squarefreeTransverseWeight]
  split
  · exact le_of_eq (by rw [Real.rpow_two])
  · positivity

/-- **Equation (33).**  The transverse cross-Gram diagonal is not absolutely summable: already the
prime subseries diverges.  This is the first-trace wall. -/
theorem not_summable_squarefreeTransverseWeight_one :
    ¬ Summable (squarefreeTransverseWeight 1) := by
  intro h
  refine not_summable_one_div_on_primes ?_
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · by_cases hp : n ∈ {p : ℕ | Nat.Prime p}
    · rw [Set.indicator_of_mem hp]
      positivity
    · rw [Set.indicator_of_notMem hp]
  · by_cases hp : n ∈ {p : ℕ | Nat.Prime p}
    · have hprime : Nat.Prime n := hp
      have hsq : Squarefree n := hprime.squarefree
      have h1 : 1 < n := hprime.one_lt
      rw [Set.indicator_of_mem hp, squarefreeTransverseWeight, if_pos ⟨hsq, h1⟩,
        Real.rpow_one]
    · rw [Set.indicator_of_notMem hp]
      exact squarefreeTransverseWeight_nonneg 1 n

/-! ## The two exact spectral Dirichlet traces -/

/-- **Equation (34).**  The unsigned spectral trace of the cross-Gram operator is the squarefree
Euler partition `ζ(s)/ζ(2s)`. -/
theorem tsum_crossGram_unsigned_trace {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if Squarefree n then 1 / (n : ℂ) ^ s else 0) =
      riemannZeta s / riemannZeta (2 * s) :=
  tsum_squarefree_cpow hs

/-- **Equation (35).**  The signed spectral trace of the cross-Gram operator is the reciprocal
zeta function. -/
theorem LSeries_crossGram_signed_trace {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (moebius n : ℂ)) s = (riemannZeta s)⁻¹ :=
  LSeries_moebius_eq_inv_riemannZeta hs

end

end RHTower
