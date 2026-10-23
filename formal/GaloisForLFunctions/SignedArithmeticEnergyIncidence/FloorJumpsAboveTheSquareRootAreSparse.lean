import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Floor jumps above the square root are sparse

For `K² > N` consecutive quotients differ by at most one, `⌊N/K⌋ − ⌊N/(K+1)⌋ ∈ {0, 1}`, and a jump
at `K` determines `K` from the quotient `m = ⌊N/K⌋`: `K` is the largest index with that quotient
(`floorJump_injOn`).  The quotients of jumps lie in `[1, √N]` and `K ≤ N/m`, so any increasing
weight summed over the jumps is dominated by its values at `N/m` (`sum_floorJump_le`).  This is
the sparsity that makes the floor part of the damping chain square summable.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- The jump indices above the square root among `1, …, M`. -/
def floorJumps (N M : ℕ) : Finset ℕ :=
  (Icc 1 M).filter fun K => N < K * K ∧ N / (K + 1) < N / K

/-- Above the square root consecutive quotients differ by at most one. -/
theorem div_sub_div_succ_le_one {N K : ℕ} (hK : N < K * K) : N / K - N / (K + 1) ≤ 1 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK0
  · simp
  have h1 : N / K < K := (Nat.div_lt_iff_lt_mul hK0).2 hK
  -- `N/K ≤ N/(K+1) + 1` since `(N/(K+1) + 1)(K+1) > N`
  have h2 : N / K ≤ N / (K + 1) + 1 := by
    have hlt : N < (N / (K + 1) + 1) * (K + 1) := by
      have := Nat.lt_div_mul_add (a := N) (b := K + 1) (by omega); nlinarith
    by_contra hcon
    push Not at hcon
    have h3 : (N / (K + 1) + 2) * K ≤ N := by
      have := Nat.div_mul_le_self N K
      nlinarith
    nlinarith
  omega

/-- A jump index is determined by its quotient. -/
theorem floorJump_injOn (N M : ℕ) : Set.InjOn (fun K => N / K) (floorJumps N M : Set ℕ) := by
  intro K₁ h₁ K₂ h₂ he
  simp only [floorJumps, coe_filter, mem_Icc, Set.mem_setOf_eq] at h₁ h₂
  simp only at he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : N / K₂ ≤ N / (K₁ + 1) := Nat.div_le_div_left (by omega) (by omega)
    omega
  · have : N / K₁ ≤ N / (K₂ + 1) := Nat.div_le_div_left (by omega) (by omega)
    omega

/-- The quotient of a jump lies in `[1, √N]`, and the jump index is at most `N/m`. -/
theorem floorJump_quotient {N M K : ℕ} (hK : K ∈ floorJumps N M) :
    1 ≤ N / K ∧ N / K ≤ Nat.sqrt N ∧ (K : ℝ) ≤ (N : ℝ) / ((N / K : ℕ) : ℝ) := by
  simp only [floorJumps, mem_filter, mem_Icc] at hK
  obtain ⟨⟨hK1, -⟩, hsq, hjump⟩ := hK
  have hm1 : 1 ≤ N / K := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hjump)
  refine ⟨hm1, ?_, ?_⟩
  · rw [Nat.le_sqrt]
    have h1 : N / K < K := (Nat.div_lt_iff_lt_mul (by omega)).2 hsq
    calc N / K * (N / K) ≤ N / K * K := Nat.mul_le_mul_left _ h1.le
      _ ≤ N := Nat.div_mul_le_self N K
  · have hm0 : (0 : ℝ) < ((N / K : ℕ) : ℝ) := by exact_mod_cast hm1
    rw [le_div_iff₀ hm0]
    exact_mod_cast (by rw [mul_comm]; exact Nat.div_mul_le_self N K : K * (N / K) ≤ N)

/-- **Sparse floor jumps**: `Σ_{jumps K} K^p ≤ Σ_{m ≤ √N} (N/m)^p` for `p ≥ 0`. -/
theorem sum_floorJump_le (N M : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ∑ K ∈ floorJumps N M, (K : ℝ) ^ p ≤ ∑ m ∈ Icc 1 (Nat.sqrt N), ((N : ℝ) / m) ^ p := by
  calc ∑ K ∈ floorJumps N M, (K : ℝ) ^ p
      ≤ ∑ K ∈ floorJumps N M, ((N : ℝ) / ((N / K : ℕ) : ℝ)) ^ p :=
        sum_le_sum fun K hK => Real.rpow_le_rpow (Nat.cast_nonneg _)
          (floorJump_quotient hK).2.2 hp
    _ = ∑ m ∈ (floorJumps N M).image (fun K => N / K), ((N : ℝ) / m) ^ p :=
        (sum_image (f := fun m : ℕ => ((N : ℝ) / m) ^ p) (floorJump_injOn N M)).symm
    _ ≤ ∑ m ∈ Icc 1 (Nat.sqrt N), ((N : ℝ) / m) ^ p := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by positivity
        intro m hm
        obtain ⟨K, hK, rfl⟩ := mem_image.1 hm
        have := floorJump_quotient hK
        exact mem_Icc.2 ⟨this.1, this.2.1⟩

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
