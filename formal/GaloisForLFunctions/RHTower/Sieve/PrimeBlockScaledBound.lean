import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistScaledEnvelope
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange

/-!
# The prime polynomial of a ladder block at a free smoothing width

The prime polynomial of a ladder step is a difference of two initial twisted prime sums, so the
scaled Route-T envelope bounds it.  Both boundary terms are dominated by the envelope at the block's
right endpoint, and the summation-by-parts factor is at most `2/log 2`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The prime polynomial of a block, at a free smoothing width.** -/
theorem exists_norm_primeBlockPoly_scaled_le :
    ∃ A delta Ctot τ₀ : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (B : Finset ℕ) (a b : ℕ) (D w : ℝ), 1 ≤ a → a ≤ b →
        (∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b)) → 1 ≤ D → τ₀ ≤ |(-(2 * Real.pi * w))| →
        ‖primeBlockPoly B w‖
          ≤ (4 / Real.log 2)
            * (scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max (b : ℝ) 1)
              + 7 * Real.exp 9) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hbound⟩ := exists_norm_sum_primeTwist_scaled_le
  refine ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, ?_⟩
  intro B a b D w ha hab hB hD hτ
  have hτ1 : (1 : ℝ) ≤ |(-(2 * Real.pi * w))| := by linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmaxa : (1 : ℝ) ≤ max (a : ℝ) 1 := le_max_right _ _
  have hmaxb : (1 : ℝ) ≤ max (b : ℝ) 1 := le_max_right _ _
  have hmaxab : max (a : ℝ) 1 ≤ max (b : ℝ) 1 := by
    have hcast : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    exact max_le_max hcast le_rfl
  set Ea : ℝ := scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max (a : ℝ) 1)
    + 7 * Real.exp 9 with hEa
  set Eb : ℝ := scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) (max (b : ℝ) 1)
    + 7 * Real.exp 9 with hEb
  have hEab : Ea ≤ Eb := by
    have := scaledTwistEnvelope_mono (A := A) (delta := delta) (Ctot := Ctot) (D := D)
      (τ := -(2 * Real.pi * w)) hCtot.le hD0 hτ1 hmaxa hmaxab
    rw [hEa, hEb]
    linarith
  have hEa0 : (0 : ℝ) ≤ Ea := by
    have hnn := scaledTwistEnvelope_nonneg (A := A) (delta := delta) (Ctot := Ctot) (D := D)
      (τ := -(2 * Real.pi * w)) hCtot.le hD0 hτ1 hmaxa
    have : (0 : ℝ) ≤ 7 * Real.exp 9 := by positivity
    rw [hEa]
    linarith
  have hfac : ∀ m : ℕ, 1 ≤ m →
      1 / Real.log 2 + 1 / Real.log ((m + 1 : ℕ) : ℝ) ≤ 2 / Real.log 2 := by
    intro m hm
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlog : Real.log 2 ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
      rw [hcast]
      exact Real.log_le_log (by norm_num) (by linarith)
    have hinv : 1 / Real.log ((m + 1 : ℕ) : ℝ) ≤ 1 / Real.log 2 :=
      one_div_le_one_div_of_le hlog2 hlog
    have : (2 : ℝ) / Real.log 2 = 1 / Real.log 2 + 1 / Real.log 2 := by ring
    linarith
  have hb1 : 1 ≤ b := le_trans ha hab
  have hbase := hbound b D (-(2 * Real.pi * w)) hD hτ
  have hbasea := hbound a D (-(2 * Real.pi * w)) hD hτ
  have hsplit := norm_primeBlockPoly_le_of_range hab hB w
  have hcomb : ‖primeBlockPoly B w‖ ≤ Eb * (2 / Real.log 2) + Ea * (2 / Real.log 2) := by
    refine hsplit.trans (add_le_add ?_ ?_)
    · refine hbase.trans ?_
      exact mul_le_mul_of_nonneg_left (hfac b hb1) (le_trans hEa0 hEab)
    · refine hbasea.trans ?_
      exact mul_le_mul_of_nonneg_left (hfac a ha) hEa0
  have hfin : Eb * (2 / Real.log 2) + Ea * (2 / Real.log 2) ≤ (4 / Real.log 2) * Eb := by
    have h2 : (0 : ℝ) < 2 / Real.log 2 := by positivity
    have hkey : (0 : ℝ) ≤ (Eb - Ea) * (2 / Real.log 2) :=
      mul_nonneg (by linarith) h2.le
    have hexp : (4 / Real.log 2) * Eb = Eb * (2 / Real.log 2) + Eb * (2 / Real.log 2) := by
      field_simp
      ring
    rw [hexp]
    linarith [hkey]
  linarith [hcomb, hfin]

end

end RHTower.Sieve
