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

end RHTower.Sieve
