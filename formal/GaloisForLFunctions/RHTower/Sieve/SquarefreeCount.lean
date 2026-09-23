import GaloisForLFunctions.RHTower.Sieve.InverseSquareTail
import GaloisForLFunctions.RHTower.MobiusFriableTaylorCoefficient
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The squarefree count of a short interval

Truncating the squarefree indicator `μ²(n) = ∑_{d² ∣ n} μ(d)` at a level `R` and exchanging the two
sums turns the count into `∑_{d ≤ R} μ(d) · #{n ∈ (t, t+L] : d² ∣ n}`.  Each inner count differs
from `L/d²` by less than one, so the truncated sum is

`L · ∑_{d ≤ R} μ(d)/d² + O(R) = L · C + O(R) + O(L/R)`,

where `C = ∑_{d ≥ 1} μ(d)/d²` is the squarefree density.  Choosing `R ≍ √L` gives the error
`O(√L)`, uniformly in the starting point `t` — the estimate the reciprocal-marker construction needs
at every start.

The truncation itself is exact arithmetic; the only analytic ingredient is the inverse-square tail
of `InverseSquareTail.lean`.
-/

namespace RHTower.Sieve

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- The Möbius series against inverse squares converges absolutely. -/
theorem summable_moebius_div_sq :
    Summable (fun d : ℕ => ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ)) := by
  refine Summable.of_norm_bounded (g := fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ (2 : ℕ))
    (Real.summable_one_div_nat_pow.2 (by norm_num)) ?_
  intro d
  have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    have hc : ((|μ d| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
    rwa [Int.cast_abs] at hc
  have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hsq]
  exact div_le_div_of_nonneg_right hmu hsq

/-- The squarefree density `∑_{d ≥ 1} μ(d)/d²`. -/
noncomputable def squarefreeDensity : ℝ := ∑' d : ℕ, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ)

/-- **Truncation error of the density.** -/
theorem abs_sum_Icc_moebius_div_sq_sub_le {R : ℕ} (hR : 1 ≤ R) :
    |∑ d ∈ Finset.Icc 1 R, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ) - squarefreeDensity| ≤ 1 / (R : ℝ) := by
  classical
  set f : ℕ → ℝ := fun d => ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ) with hf
  have hsum := summable_moebius_div_sq
  have hsplit : ∑ i ∈ Finset.range (R + 1), f i + ∑' n : ℕ, f (n + (R + 1)) = ∑' d : ℕ, f d :=
    hsum.sum_add_tsum_nat_add (R + 1)
  have hins : Finset.range (R + 1) = insert 0 (Finset.Icc 1 R) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : f 0 = 0 := by simp [hf]
  have hfin : ∑ i ∈ Finset.range (R + 1), f i = ∑ d ∈ Finset.Icc 1 R, f d := by
    rw [hins, Finset.sum_insert (by simp), h0, zero_add]
  have htail : |∑' n : ℕ, f (n + (R + 1))| ≤ 1 / (R : ℝ) := by
    have hbound : ∀ n : ℕ, ‖f (n + (R + 1))‖ ≤ (1 : ℝ) / ((n : ℝ) + R + 1) ^ (2 : ℕ) := by
      intro n
      have hmu : |((μ (n + (R + 1)) : ℤ) : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := n + (R + 1))
        have hc : ((|μ (n + (R + 1))| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
        rwa [Int.cast_abs] at hc
      have hcast : ((n + (R + 1) : ℕ) : ℝ) = (n : ℝ) + R + 1 := by push_cast; ring
      have hsq : (0 : ℝ) < ((n : ℝ) + R + 1) ^ (2 : ℕ) := by positivity
      rw [hf]
      simp only
      rw [hcast, Real.norm_eq_abs, abs_div, abs_of_nonneg hsq.le]
      exact div_le_div_of_nonneg_right hmu hsq.le
    have hsummable : Summable (fun n : ℕ => f (n + (R + 1))) :=
      (summable_nat_add_iff (R + 1)).2 hsum
    rw [← Real.norm_eq_abs]
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · exact hsummable.norm
    · refine le_trans (Summable.tsum_le_tsum hbound hsummable.norm (summable_inv_sq_shift R)) ?_
      exact tsum_inv_sq_shift_le hR
  rw [← hfin, squarefreeDensity, ← hf, ← hsplit]
  have : ∑ i ∈ Finset.range (R + 1), f i
      - (∑ i ∈ Finset.range (R + 1), f i + ∑' n : ℕ, f (n + (R + 1)))
      = -(∑' n : ℕ, f (n + (R + 1))) := by ring
  rw [this, abs_neg]
  exact htail

/-- Exchanging the truncated divisor sum with the interval sum. -/
theorem sum_truncated_moebius_eq (t L R : ℕ) :
    ∑ n ∈ Finset.Ioc t (t + L), ∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((μ d : ℤ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 R,
          ((μ d : ℤ) : ℝ) * ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) := by
  classical
  have hinner : ∀ n ∈ Finset.Ioc t (t + L),
      ∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((μ d : ℤ) : ℝ)
        = ∑ d ∈ Finset.Icc 1 R, (if d ^ (2 : ℕ) ∣ n then ((μ d : ℤ) : ℝ) else 0) := by
    intro n _
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Short-interval squarefree count, truncated form.**  Uniform in the starting point `t`. -/
theorem abs_truncated_squarefree_sub_le (t L R : ℕ) (hR : 1 ≤ R) :
    |∑ n ∈ Finset.Ioc t (t + L), ∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((μ d : ℤ) : ℝ)
        - (L : ℝ) * squarefreeDensity|
      ≤ (R : ℝ) + (L : ℝ) / (R : ℝ) := by
  classical
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    have : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  set A : ℝ := ∑ d ∈ Finset.Icc 1 R,
      ((μ d : ℤ) : ℝ) * ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) with hA
  set B : ℝ := (L : ℝ) * ∑ d ∈ Finset.Icc 1 R, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ) with hB
  have hAB : |A - B| ≤ (R : ℝ) := by
    have hdiff : A - B
        = ∑ d ∈ Finset.Icc 1 R, ((μ d : ℤ) : ℝ)
            * (((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ) - (L : ℝ) / (d : ℝ) ^ (2 : ℕ)) := by
      rw [hA, hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro d _
      ring
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.Icc 1 R,
        |((μ d : ℤ) : ℝ) * (((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
          - (L : ℝ) / (d : ℝ) ^ (2 : ℕ))| ≤ 1 := by
      intro d hd
      obtain ⟨hd1, -⟩ := Finset.mem_Icc.1 hd
      have hdsq : 0 < d ^ (2 : ℕ) := by positivity
      have hcount := abs_card_filter_dvd_Ioc_sub_lt (d ^ (2 : ℕ)) t (t + L) hdsq (by omega)
      have hcast : (((t + L : ℕ)) : ℝ) - (t : ℝ) = (L : ℝ) := by push_cast; ring
      have hcast2 : (((d ^ (2 : ℕ) : ℕ)) : ℝ) = (d : ℝ) ^ (2 : ℕ) := by push_cast; ring
      rw [hcast, hcast2] at hcount
      have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        have hc : ((|μ d| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
        rwa [Int.cast_abs] at hc
      rw [abs_mul]
      calc |((μ d : ℤ) : ℝ)| * |((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)
              - (L : ℝ) / (d : ℝ) ^ (2 : ℕ)|
          ≤ 1 * 1 := by
            refine mul_le_mul hmu hcount.le (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    simp [Nat.card_Icc]
  have hBC : |B - (L : ℝ) * squarefreeDensity| ≤ (L : ℝ) / (R : ℝ) := by
    have hdens := abs_sum_Icc_moebius_div_sq_sub_le hR
    have hrw : B - (L : ℝ) * squarefreeDensity
        = (L : ℝ) * ((∑ d ∈ Finset.Icc 1 R, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ)) - squarefreeDensity) := by
      rw [hB]; ring
    rw [hrw, abs_mul, abs_of_nonneg hLnn]
    calc (L : ℝ) * |(∑ d ∈ Finset.Icc 1 R, ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ)) - squarefreeDensity|
        ≤ (L : ℝ) * (1 / (R : ℝ)) := mul_le_mul_of_nonneg_left hdens hLnn
      _ = (L : ℝ) / (R : ℝ) := by ring
  rw [sum_truncated_moebius_eq t L R, ← hA]
  calc |A - (L : ℝ) * squarefreeDensity| ≤ |A - B| + |B - (L : ℝ) * squarefreeDensity| :=
        abs_sub_le A B ((L : ℝ) * squarefreeDensity)
    _ ≤ (R : ℝ) + (L : ℝ) / (R : ℝ) := by linarith

/-- The Möbius/inverse-square series is the `L`-series of `μ` at `s = 2`. -/
theorem lseries_moebius_two_eq :
    LSeries (fun n : ℕ => ((μ n : ℤ) : ℂ)) 2 = (squarefreeDensity : ℂ) := by
  have hreal : HasSum (fun d : ℕ => ((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ)) squarefreeDensity :=
    summable_moebius_div_sq.hasSum
  have hcomplex : HasSum (fun d : ℕ => ((((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ) : ℝ) : ℂ))
      ((squarefreeDensity : ℝ) : ℂ) := Complex.hasSum_ofReal.2 hreal
  have hterm : ∀ d : ℕ, LSeries.term (fun n : ℕ => ((μ n : ℤ) : ℂ)) 2 d
      = ((((μ d : ℤ) : ℝ) / (d : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero (by omega)]
      have hpow : ((d : ℂ)) ^ (2 : ℂ) = ((d : ℂ)) ^ (2 : ℕ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      rw [hpow]
      push_cast
      ring
  have := hcomplex.tsum_eq
  rw [LSeries, tsum_congr hterm, this]

/-- **The squarefree density is `6/π²`.** -/
theorem squarefreeDensity_eq : squarefreeDensity = 6 / Real.pi ^ (2 : ℕ) := by
  have hz : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have h := RHTower.LSeries_moebius_eq_inv_riemannZeta hz
  rw [lseries_moebius_two_eq, riemannZeta_two] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hval : (((Real.pi : ℂ)) ^ (2 : ℕ) / 6)⁻¹ = ((6 / Real.pi ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hval] at h
  exact_mod_cast h

end RHTower.Sieve
