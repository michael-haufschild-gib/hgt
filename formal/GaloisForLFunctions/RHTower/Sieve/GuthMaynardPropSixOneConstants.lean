import GaloisForLFunctions.RHTower.Sieve.GuthMaynardHeathBrownBlocks
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOneLifted

/-!
# The `T^{o(1)}` constants of the lifted Heath-Brown bound

The all-lengths Heath-Brown constant `hbBlockConst T δ L` and the divisor bound
`d(u) ≤ divisorBoundConst δ · u^δ` both enter Guth–Maynard's (6.3) at block lengths and
coefficient indices of size `≤ a T^b`.  One choice of `δ`, namely `δ = ε/(20(b+1))`, makes both
`O_{ε,a,b}(T^ε)`: the block constant contributes `T^{10bδ} ≤ T^{ε/2}` and the reflection and dual
factors `T^{ε/2}` (`exists_hbReflFactor_add_hbDualFactor_le`), while the squared divisor factor
contributes `T^{2bδ} ≤ T^ε`.
-/

set_option autoImplicit false

namespace RHTower.GuthMaynard

open RHTower.Sieve

noncomputable section

/-- **One `δ` for the block constant and the divisor bound.**  For block lengths and coefficient
indices below `a T^b` both are `O(T^ε)`. -/
theorem exists_blockConst_divisor_le {ε a b : ℝ} (hε : 0 < ε) (ha : 4 ≤ a) (hb : 2 / 3 ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∀ L : ℕ, (L : ℝ) ≤ a * T ^ b → hbBlockConst T δ L ≤ C * T ^ ε) ∧
      (∀ u : ℕ, (u : ℝ) ≤ a * T ^ b → (divisorBoundConst δ * (u : ℝ) ^ δ) ^ 2 ≤ C * T ^ ε) := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  set δ : ℝ := ε / (20 * (b + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨K, hK, hKb⟩ := exists_hbReflFactor_add_hbDualFactor_le (η := ε / 2) (by positivity)
  set D : ℝ := divisorBoundConst δ with hDdef
  have hD : 0 ≤ D := (divisorBoundConst_pos hδ).le
  -- the two exponent budgets
  have hratio : b / (b + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hratio0 : 0 ≤ b / (b + 1) := by positivity
  have hexp1 : 10 * b * δ ≤ ε / 2 := by
    rw [hδdef]
    have he : 10 * b * (ε / (20 * (b + 1))) = (b / (b + 1)) * (ε / 2) := by
      field_simp; ring
    rw [he]
    nlinarith
  have hexpδ : b * δ ≤ ε / 20 := by
    rw [hδdef]
    have he : b * (ε / (20 * (b + 1))) = (b / (b + 1)) * (ε / 20) := by
      field_simp
    rw [he]
    nlinarith
  have hexp2 : 2 * b * δ ≤ ε := by
    have : 2 * b * δ = 2 * (b * δ) := by ring
    rw [this]
    nlinarith
  refine ⟨δ, hδ, max (3584 * (D ^ 10 * (8 * a) ^ (10 * δ) + 1) * K) (D ^ 2 * a ^ (2 * δ)),
    le_trans (by positivity) (le_max_right _ _), fun T hT => ⟨?_, ?_⟩⟩
  · -- the all-lengths block constant
    intro L hL
    have hT0 : (0 : ℝ) < T := by linarith
    have hTb : (0 : ℝ) ≤ T ^ b := Real.rpow_nonneg hT0.le _
    have h8L : ((8 * L : ℕ) : ℝ) ≤ 8 * a * T ^ b := by push_cast; linarith
    have hstep : ((8 * L : ℕ) : ℝ) ^ δ ≤ (8 * a) ^ δ * T ^ (b * δ) := by
      calc ((8 * L : ℕ) : ℝ) ^ δ ≤ (8 * a * T ^ b) ^ δ :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) h8L hδ.le
        _ = (8 * a) ^ δ * (T ^ b) ^ δ := Real.mul_rpow (by positivity) hTb
        _ = (8 * a) ^ δ * T ^ (b * δ) := by rw [← Real.rpow_mul hT0.le]
    have hbd : (0 : ℝ) ≤ (8 * a) ^ δ := Real.rpow_nonneg (by positivity) _
    have hten : (D * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 ≤ D ^ 10 * (8 * a) ^ (10 * δ) * T ^ (ε / 2) := by
      have hmul : D * ((8 * L : ℕ) : ℝ) ^ δ ≤ D * ((8 * a) ^ δ * T ^ (b * δ)) :=
        mul_le_mul_of_nonneg_left hstep hD
      have h0 : (0 : ℝ) ≤ D * ((8 * L : ℕ) : ℝ) ^ δ := by positivity
      have e1 : ((8 * a : ℝ) ^ δ) ^ 10 = (8 * a) ^ (10 * δ) := by
        rw [← Real.rpow_natCast ((8 * a : ℝ) ^ δ) 10, ← Real.rpow_mul (by positivity)]
        congr 1; push_cast; ring
      have e2 : ((T ^ (b * δ)) : ℝ) ^ 10 = T ^ (10 * (b * δ)) := by
        rw [← Real.rpow_natCast (T ^ (b * δ)) 10, ← Real.rpow_mul hT0.le]
        congr 1; push_cast; ring
      have hle : T ^ (10 * (b * δ)) ≤ T ^ (ε / 2) :=
        Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      have h0' : (0 : ℝ) ≤ D ^ 10 * (8 * a) ^ (10 * δ) := by positivity
      calc (D * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 ≤ (D * ((8 * a) ^ δ * T ^ (b * δ))) ^ 10 :=
            pow_le_pow_left₀ h0 hmul 10
        _ = D ^ 10 * ((8 * a : ℝ) ^ δ) ^ 10 * ((T ^ (b * δ)) : ℝ) ^ 10 := by ring
        _ = D ^ 10 * (8 * a) ^ (10 * δ) * T ^ (10 * (b * δ)) := by rw [e1, e2]
        _ ≤ D ^ 10 * (8 * a) ^ (10 * δ) * T ^ (ε / 2) := mul_le_mul_of_nonneg_left hle h0'
    have hTe2 : (1 : ℝ) ≤ T ^ (ε / 2) := Real.one_le_rpow hT (by positivity)
    have hfirst : (D * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1 ≤
        (D ^ 10 * (8 * a) ^ (10 * δ) + 1) * T ^ (ε / 2) := by
      have : (0 : ℝ) ≤ D ^ 10 * (8 * a) ^ (10 * δ) := by positivity
      nlinarith
    have hsecond := hKb T hT
    have hsplit : T ^ ε = T ^ (ε / 2) * T ^ (ε / 2) := by
      rw [← Real.rpow_add hT0]; ring_nf
    have h0 : 0 ≤ hbReflFactor T + hbDualFactor T + 1 := by
      have := one_le_hbReflFactor hT
      have := hbDualFactor_nonneg T
      linarith
    have hmain : hbBlockConst T δ L ≤ 3584 * (D ^ 10 * (8 * a) ^ (10 * δ) + 1) * K * T ^ ε := by
      rw [hbBlockConst, hsplit, ← hDdef]
      calc 3584 * ((D * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
            (hbReflFactor T + hbDualFactor T + 1)
          ≤ 3584 * ((D ^ 10 * (8 * a) ^ (10 * δ) + 1) * T ^ (ε / 2)) * (K * T ^ (ε / 2)) := by
            gcongr
        _ = _ := by ring
    refine hmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact Real.rpow_nonneg hT0.le _
  · -- the squared divisor factor
    intro u hu
    have hT0 : (0 : ℝ) < T := by linarith
    have hTb : (0 : ℝ) ≤ T ^ b := Real.rpow_nonneg hT0.le _
    have hstep : ((u : ℕ) : ℝ) ^ δ ≤ a ^ δ * T ^ (b * δ) := by
      calc ((u : ℕ) : ℝ) ^ δ ≤ (a * T ^ b) ^ δ :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hu hδ.le
        _ = a ^ δ * (T ^ b) ^ δ := Real.mul_rpow ha0.le hTb
        _ = a ^ δ * T ^ (b * δ) := by rw [← Real.rpow_mul hT0.le]
    have hmul : D * ((u : ℕ) : ℝ) ^ δ ≤ D * (a ^ δ * T ^ (b * δ)) :=
      mul_le_mul_of_nonneg_left hstep hD
    have h0 : (0 : ℝ) ≤ D * ((u : ℕ) : ℝ) ^ δ := by positivity
    have hsq := pow_le_pow_left₀ h0 hmul 2
    have e1 : ((a : ℝ) ^ δ) ^ 2 = a ^ (2 * δ) := by
      rw [← Real.rpow_natCast ((a : ℝ) ^ δ) 2, ← Real.rpow_mul ha0.le]
      congr 1; push_cast; ring
    have e2 : ((T ^ (b * δ)) : ℝ) ^ 2 = T ^ (2 * (b * δ)) := by
      rw [← Real.rpow_natCast (T ^ (b * δ)) 2, ← Real.rpow_mul hT0.le]
      congr 1; push_cast; ring
    have hexpand : (D * (a ^ δ * T ^ (b * δ))) ^ 2 = D ^ 2 * a ^ (2 * δ) * T ^ (2 * (b * δ)) := by
      rw [show (D * (a ^ δ * T ^ (b * δ))) ^ 2 = D ^ 2 * ((a : ℝ) ^ δ) ^ 2 * (T ^ (b * δ)) ^ 2 by
        ring, e1, e2]
    rw [hexpand] at hsq
    have hle : T ^ (2 * (b * δ)) ≤ T ^ ε :=
      Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    have h0' : (0 : ℝ) ≤ D ^ 2 * a ^ (2 * δ) := by positivity
    refine hsq.trans ((mul_le_mul_of_nonneg_left hle h0').trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hT0.le _)

end

end RHTower.GuthMaynard
