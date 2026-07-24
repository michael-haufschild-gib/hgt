import GaloisForLFunctions.RHTower.SelbergSecondInequality
import GaloisForLFunctions.HTGeometry.DiscreteSignCrossing

/-!
# Small values of the remainder at sign changes

The remainder `R = ψ − id` steps by `R(j+1) − R(j) = Λ(j+1) − 1`: down-steps
are at most `1`, up-steps at most `log(j+1)`.  Hence at any sign change a
point with `|R| ≤ log b + 1` appears:

* a downward crossing lands within `1` of zero;
* an upward crossing starts within `log(m+1) − 1` of zero.

Also records the summatory cancellation
`|∑_{n ≤ N} R(⌊N/n⌋) + 2γN| ≤ 24√N`, the `2γ`-shift of the `ψ`-defect
bound — the reservoir forcing the sign changes the contraction feeds on.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The exact step `R(j+1) − R(j) = Λ(j+1) − 1`. -/
theorem psiRemainder_succ_sub (j : ℕ) :
    psiRemainder (j + 1) - psiRemainder j = vonMangoldt (j + 1) - 1 := by
  simp only [psiRemainder, chebyshevPsi]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
  push_cast
  ring

/-- **Small remainder at a sign change**: if `R` has opposite (or zero)
signs at `1 ≤ a ≤ b`, some `m ∈ [a, b]` has `|R(m)| ≤ log b + 1`. -/
theorem exists_abs_psiRemainder_le_of_sign_change {a b : ℕ}
    (h1 : 1 ≤ a) (hab : a ≤ b)
    (hsign : psiRemainder a * psiRemainder b ≤ 0) :
    ∃ m ∈ Finset.Icc a b, |psiRemainder m| ≤ Real.log b + 1 := by
  have hlogb0 : 0 ≤ Real.log b :=
    Real.log_nonneg (by exact_mod_cast le_trans h1 hab)
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · -- a = b: the product is a square, so `R(a) = 0`
    have hz : psiRemainder a = 0 := by
      nlinarith [hsign, sq_nonneg (psiRemainder a)]
    exact ⟨a, Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩, by
      rw [hz, abs_zero]
      linarith⟩
  obtain ⟨m, ham, hmb, hcross⟩ :=
    HTGeometry.exists_mul_succ_nonpos psiRemainder hlt hsign
  have hstep := psiRemainder_succ_sub m
  have hΛ0 : 0 ≤ vonMangoldt (m + 1) := vonMangoldt_nonneg
  have hΛlog : vonMangoldt (m + 1) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    vonMangoldt_le_log
  have hlogm : Real.log ((m + 1 : ℕ) : ℝ) ≤ Real.log b := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < m + 1))
    exact_mod_cast (by omega : m + 1 ≤ b)
  rcases mul_nonpos_iff.1 hcross with ⟨hm0, hm10⟩ | ⟨hm0, hm10⟩
  · -- downward crossing: `R(m) ≥ 0 ≥ R(m+1)`, so `|R(m+1)| ≤ 1`
    refine ⟨m + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [abs_of_nonpos hm10]
    linarith
  · -- upward crossing: `R(m) ≤ 0 ≤ R(m+1)`, so `|R(m)| ≤ log(m+1) − 1`
    refine ⟨m, Finset.mem_Icc.2 ⟨ham, by omega⟩, ?_⟩
    rw [abs_of_nonpos hm0]
    linarith

/-- **Summatory cancellation of the remainder**:
`|∑_{n ≤ N} R(⌊N/n⌋) + 2γN| ≤ 24√N`. -/
theorem abs_floorSummatory_psiRemainder_add_le (N : ℕ) (hN : 1 ≤ N) :
    |floorSummatory psiRemainder N
        + 2 * Real.eulerMascheroniConstant * N| ≤ 24 * Real.sqrt N := by
  have hsplit : floorSummatory psiDefect N
      = floorSummatory psiRemainder N
        + 2 * Real.eulerMascheroniConstant * N := by
    simp only [floorSummatory]
    have hcard : ∀ d ∈ Finset.Icc 1 N,
        psiDefect (N / d)
          = psiRemainder (N / d) + 2 * Real.eulerMascheroniConstant := by
      intro d _
      rw [psiDefect_eq_psiRemainder_add]
    rw [Finset.sum_congr rfl hcard, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc,
      show N + 1 - 1 = N from by omega, nsmul_eq_mul]
    ring
  have := abs_floorSummatory_psiDefect_le N hN
  rw [hsplit] at this
  exact this

end RHTower
