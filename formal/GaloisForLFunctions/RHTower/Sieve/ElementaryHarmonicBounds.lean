import GaloisForLFunctions.RHTower.PrimeMassLowerBound
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.AuxResults

/-!
# Elementary harmonic and square-root sums

The unsigned estimates behind the Route E cofactor card's `(7)` and `(9)`: a two-sided comparison
for `∑_{n ≤ M} n^{-1/2}`, the reindexing of a divisibility-restricted sum, the resulting bounds for
the mass carried by the multiples of a fixed modulus, and the convergence of the reciprocal squares
of the odd numbers above one, with the explicit constant `1/4` that the squarefree extraction needs.

Everything is proved by telescoping; no analytic input is used.  The upper bound
`∑_{n ≤ M} n^{-1/2} ≤ 2√M` is already in the corpus as `RHTower.sum_one_div_sqrt_le` and is reused.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The square-root harmonic sum from below.**  `2√(M+1) − 2 ≤ ∑_{n ≤ M} n^{-1/2}`. -/
theorem two_mul_sqrt_succ_sub_two_le_sum (M : ℕ) :
    2 * Real.sqrt ((M : ℝ) + 1) - 2 ≤ ∑ n ∈ Finset.Icc 1 M, 1 / Real.sqrt (n : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hv : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
    have hw : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 2) := Real.sqrt_nonneg _
    have hv2 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hw2 : Real.sqrt ((m : ℝ) + 2) ^ 2 = (m : ℝ) + 2 := Real.sq_sqrt (by positivity)
    have hv1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by nlinarith [hv, hv2]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast, show ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 from by ring]
    have hstep : 2 * Real.sqrt ((m : ℝ) + 2) - 2 * Real.sqrt ((m : ℝ) + 1)
        ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg (Real.sqrt ((m : ℝ) + 2) - Real.sqrt ((m : ℝ) + 1)), hv2, hw2]
    linarith [ih, hstep]

/-- The multiples of `p` below `M`, reindexed by their cofactor. -/
theorem sum_filter_dvd_eq {M p : ℕ} (hp : 1 ≤ p) (f : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), f n
      = ∑ k ∈ Finset.Icc 1 (M / p), f (p * k) := by
  classical
  have hp0 : 0 < p := hp
  have himg : (Finset.Icc 1 M).filter (fun n => p ∣ n)
      = (Finset.Icc 1 (M / p)).image (fun k => p * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h1
        · exact hk
      · exact (Nat.le_div_iff_mul_le hp0).2 (by rw [Nat.mul_comm]; exact h2)
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.2 (by positivity)
      · have hkp := (Nat.le_div_iff_mul_le hp0).1 hk2
        rw [Nat.mul_comm]
        exact hkp
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hp0 hab

/-- **The square-root mass of the multiples of `p`.** -/
theorem sum_inv_sqrt_dvd_le {M p : ℕ} (hp : 1 ≤ p) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), 1 / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt (M : ℝ) / (p : ℝ) := by
  classical
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsp : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp0
  rw [sum_filter_dvd_eq hp (fun n => 1 / Real.sqrt (n : ℝ))]
  have hterm : ∀ k ∈ Finset.Icc 1 (M / p),
      1 / Real.sqrt ((p * k : ℕ) : ℝ) = (1 / Real.sqrt (p : ℝ)) * (1 / Real.sqrt (k : ℝ)) := by
    intro k _
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbase : ∑ k ∈ Finset.Icc 1 (M / p), 1 / Real.sqrt (k : ℝ)
      ≤ 2 * Real.sqrt ((M / p : ℕ) : ℝ) := sum_one_div_sqrt_le (M / p)
  have hdiv : ((M / p : ℕ) : ℝ) ≤ (M : ℝ) / (p : ℝ) := Nat.cast_div_le
  have hsq : Real.sqrt ((M / p : ℕ) : ℝ) ≤ Real.sqrt (M : ℝ) / Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_div' _ (le_of_lt hp0)] at *
    exact Real.sqrt_le_sqrt hdiv
  have hstep : (1 / Real.sqrt (p : ℝ)) * ∑ k ∈ Finset.Icc 1 (M / p), 1 / Real.sqrt (k : ℝ)
      ≤ (1 / Real.sqrt (p : ℝ)) * (2 * (Real.sqrt (M : ℝ) / Real.sqrt (p : ℝ))) := by
    refine mul_le_mul_of_nonneg_left (le_trans hbase ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  refine le_trans hstep (le_of_eq ?_)
  have hsp2 : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
    Real.mul_self_sqrt hp0.le
  field_simp
  nlinarith [hsp2, Real.sqrt_nonneg (M : ℝ)]

end

end RHTower.Sieve
