import Mathlib

/-!
# A power lands in every multiplicative window at least as wide as the base
-/

namespace RHTower.Sieve

/-- **Power-window selection.**  If the window `[A,B]` is multiplicatively at least as wide as `M`,
some power `M^ℓ` with `ℓ ≥ 1` lies in it.  This is the choice of `ℓ` in Matomäki--Teräväinen's
Proposition 4.2: `M₁^ℓ ∈ [T^{5/6−ε}, T^{1−ε/2}]` is possible because consecutive powers of `M₁`
differ by the factor `M₁`, which is below the window's multiplicative width. -/
theorem exists_pow_mem_window {M A B : ℝ} (hM : 1 < M) (hA : 1 < A) (hAB : A * M ≤ B) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ A ≤ M ^ ℓ ∧ M ^ ℓ ≤ B := by
  classical
  have hex : ∃ n : ℕ, A ≤ M ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt A hM
    exact ⟨n, hn.le⟩
  have hspec : A ≤ M ^ (Nat.find hex) := Nat.find_spec hex
  have hℓ1 : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero] at hspec
      linarith
    · exact hpos
  have hprev : ¬ (A ≤ M ^ (Nat.find hex - 1)) := Nat.find_min hex (by omega)
  have hlt : M ^ (Nat.find hex - 1) < A := not_le.mp hprev
  have hM0 : (0 : ℝ) < M := by linarith
  have hstep : M ^ (Nat.find hex) = M ^ (Nat.find hex - 1) * M := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨Nat.find hex, hℓ1, hspec, ?_⟩
  rw [hstep]
  nlinarith [hlt, hM0, hAB]

/-- **Matomäki--Teräväinen power-window selection on the full Type-II range.**
The generic consecutive-power argument covers
`M ≤ T^(1/6 + ε/2)`. Above that threshold the fixed choice `ℓ = 5` lands in the required
window; its upper edge follows from `M ≤ T^(2/11 + ε)` and `ε ≤ 1/1000`.

This two-branch statement repairs the tempting but false claim that the full Type-II range follows
from the generic window-width criterion alone: `2/11` is larger than `1/6`. -/
theorem exists_pow_mem_matomakiTeravainen_window
    {T M eps : ℝ} (hT : 1 < T) (hM : 1 < M)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 1000)
    (hMupper : M ≤ T ^ ((2 : ℝ) / 11 + eps)) :
    ∃ ell : ℕ, 1 ≤ ell ∧
      T ^ ((5 : ℝ) / 6 - eps) ≤ M ^ ell ∧
      M ^ ell ≤ T ^ (1 - eps / 2) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hLowerExp : 0 < (5 : ℝ) / 6 - eps := by linarith
  by_cases hsmall : M ≤ T ^ ((1 : ℝ) / 6 + eps / 2)
  · have hA : 1 < T ^ ((5 : ℝ) / 6 - eps) :=
      Real.one_lt_rpow hT hLowerExp
    have hAB :
        T ^ ((5 : ℝ) / 6 - eps) * M ≤ T ^ (1 - eps / 2) := by
      calc
        T ^ ((5 : ℝ) / 6 - eps) * M ≤
            T ^ ((5 : ℝ) / 6 - eps) * T ^ ((1 : ℝ) / 6 + eps / 2) :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hT0.le _)
        _ = T ^ (((5 : ℝ) / 6 - eps) + ((1 : ℝ) / 6 + eps / 2)) := by
          rw [← Real.rpow_add hT0]
        _ = T ^ (1 - eps / 2) := by
          congr 1
          ring
    exact exists_pow_mem_window hM hA hAB
  · have hlarge : T ^ ((1 : ℝ) / 6 + eps / 2) < M := lt_of_not_ge hsmall
    refine ⟨5, by norm_num, ?_, ?_⟩
    · calc
        T ^ ((5 : ℝ) / 6 - eps) ≤
            T ^ (5 * ((1 : ℝ) / 6 + eps / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
        _ = (T ^ ((1 : ℝ) / 6 + eps / 2)) ^ (5 : ℕ) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hT0.le]
          congr 1
          ring
        _ ≤ M ^ (5 : ℕ) := by gcongr
    · calc
        M ^ (5 : ℕ) ≤ (T ^ ((2 : ℝ) / 11 + eps)) ^ (5 : ℕ) := by gcongr
        _ = T ^ (5 * ((2 : ℝ) / 11 + eps)) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hT0.le]
          congr 1
          ring
        _ ≤ T ^ (1 - eps / 2) :=
          Real.rpow_le_rpow_of_exponent_le hT.le (by nlinarith)

end RHTower.Sieve
