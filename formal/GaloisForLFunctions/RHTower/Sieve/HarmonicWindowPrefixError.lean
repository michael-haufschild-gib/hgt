import GaloisForLFunctions.RHTower.BourgainPartialSummation

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

theorem sum_Ioc_eq_sum_Icc_sub_one
    (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ k ∈ Finset.Ioc L U, f k) =
      (∑ k ∈ Finset.Icc 1 U, f k) - ∑ k ∈ Finset.Icc 1 L, f k := by
  have hsub : Finset.Icc 1 L ⊆ Finset.Icc 1 U := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans hLU⟩
  have hdiff : Finset.Icc 1 U \ Finset.Icc 1 L = Finset.Ioc L U := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hdiff, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff hsub

/-- A uniform linear prefix error transfers to a harmonic-window error by finite Abel summation. -/
theorem abs_sum_Ioc_div_sub_const_harmonic_le
    (f : ℕ → ℝ) (D E : ℝ) {L U : ℕ}
    (hLU : L < U)
    (hprefix : ∀ n, L ≤ n → n ≤ U →
      |(∑ k ∈ Finset.Icc 1 n, f k) - (n : ℝ) * D| ≤ E) :
    |(∑ k ∈ Finset.Ioc L U, f k / (k : ℝ)) -
        D * (∑ k ∈ Finset.Ioc L U, 1 / (k : ℝ))| ≤
      2 * E / ((L + 1 : ℕ) : ℝ) := by
  have hcenter : ∀ n ∈ Finset.Ioc L U,
      |∑ k ∈ Finset.Ioc L n, (f k - D)| ≤ 2 * E := by
    intro n hn
    have hLn : L ≤ n := (Finset.mem_Ioc.mp hn).1.le
    have hnU : n ≤ U := (Finset.mem_Ioc.mp hn).2
    have hnerr := hprefix n hLn hnU
    have hLerr := hprefix L le_rfl hLU.le
    have hidentity :
        (∑ k ∈ Finset.Ioc L n, (f k - D)) =
          ((∑ k ∈ Finset.Icc 1 n, f k) - (n : ℝ) * D) -
            ((∑ k ∈ Finset.Icc 1 L, f k) - (L : ℝ) * D) := by
      rw [sum_Ioc_eq_sum_Icc_sub_one _ hLn]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      push_cast
      ring
    rw [hidentity]
    calc
      |((∑ k ∈ Finset.Icc 1 n, f k) - (n : ℝ) * D) -
          ((∑ k ∈ Finset.Icc 1 L, f k) - (L : ℝ) * D)| ≤
        |(∑ k ∈ Finset.Icc 1 n, f k) - (n : ℝ) * D| +
          |(∑ k ∈ Finset.Icc 1 L, f k) - (L : ℝ) * D| := abs_sub _ _
      _ ≤ E + E := add_le_add hnerr hLerr
      _ = 2 * E := by ring
  have habel := RHTower.norm_sum_Ioc_weight_mul_le
    (fun k : ℕ => (((f k - D : ℝ) : ℝ) : ℂ))
    (fun k : ℕ => 1 / (k : ℝ)) hLU
    (fun k => by positivity)
    (fun k hk => by
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        have hkNat : 0 < k :=
          lt_of_le_of_lt (Nat.zero_le L) (Finset.mem_Ioc.mp hk).1
        exact_mod_cast hkNat
      have hksucc : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      exact one_div_le_one_div_of_le hkpos hksucc)
    (B := 2 * E) (fun n hn => by
      simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
        using hcenter n hn)
  have hrewrite :
      (∑ k ∈ Finset.Ioc L U, f k / (k : ℝ)) -
          D * (∑ k ∈ Finset.Ioc L U, 1 / (k : ℝ)) =
        ∑ k ∈ Finset.Ioc L U, (1 / (k : ℝ)) * (f k - D) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hrewrite]
  have hleft :
      ‖∑ k ∈ Finset.Ioc L U, ((1 / (k : ℝ) : ℝ) : ℂ) *
          (((f k - D : ℝ) : ℝ) : ℂ)‖ =
        |∑ k ∈ Finset.Ioc L U, (1 / (k : ℝ)) * (f k - D)| := by
    have hcast :
        (∑ k ∈ Finset.Ioc L U, ((1 / (k : ℝ) : ℝ) : ℂ) *
            (((f k - D : ℝ) : ℝ) : ℂ)) =
          (((∑ k ∈ Finset.Ioc L U, (1 / (k : ℝ)) * (f k - D)) : ℝ) : ℂ) := by
      norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [hleft] at habel
  simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc, one_mul]
    using habel

end

end RHTower.Sieve
