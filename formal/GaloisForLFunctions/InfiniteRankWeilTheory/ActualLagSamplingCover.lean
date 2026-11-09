import GaloisForLFunctions.InfiniteRankWeilTheory.ActualLagCellCurvature
import GaloisForLFunctions.RHTower.WildSaddleAdaptiveDepthRelocation

/-!
# Finite covers for small actual Weil-lag samples

At level `n` and on a bounded positive interval of bases, at most exponentially many arithmetic
cells occur. Each contributes two sublevel balls. Clipping their centers to `[1, infinity)` and
applying logarithm transfers the covers to bases without increasing their radii.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The universal radius factor from the order-two cell cover. -/
def lagSamplingCoverConstant : ℝ :=
  2 * (12 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ)

theorem lagSamplingCoverConstant_pos : 0 < lagSamplingCoverConstant := by
  unfold lagSamplingCoverConstant
  positivity

private theorem lagCellCover_radius_eq {R : ℝ} (hR : 0 < R) (t : ℝ) :
    derivativeCoverConstant 2 (1 / (2 * R)) *
        (2 * R * Real.exp (-t)) ^ ((2 : ℝ)⁻¹) =
      lagSamplingCoverConstant * R * Real.exp (-t / 2) := by
  simp only [derivativeCoverConstant, show (2 + 1).factorial = 6 by rfl, Nat.cast_ofNat]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
  have hden : (6 : ℝ) / (1 / (2 * R)) = 12 * R := by field_simp; ring
  have hA : (12 * R) ^ (1 / 2 : ℝ) = (12 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) :=
    Real.mul_rpow (by norm_num) hR.le
  have hE : (2 * R * Real.exp (-t)) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) * Real.exp (-t / 2) := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      Real.mul_rpow (by norm_num) hR.le, ← Real.exp_mul]
    congr 2
    ring
  have hRpow : R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) = R := by
    rw [← Real.rpow_add hR]
    norm_num
  rw [hden, hA, hE]
  calc _ = lagSamplingCoverConstant *
      (R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) * Real.exp (-t / 2) := by
        unfold lagSamplingCoverConstant
        ring
    _ = _ := by rw [hRpow]

/-- On `[0,U]`, the level-`n` bases with accuracy `exp(-(m+1)n)` have at most `4 exp(nU)`
covering balls, with radii decreasing at rate `(m+1)/2-U`. The restrictions `n≥1` and
`exp(n ell)≥2` discard only finitely many levels at every positive base. -/
theorem exists_actualLag_sampled_cover {U : ℝ} (hU : 0 ≤ U) (m n : ℕ) :
    ∃ T : Finset ℝ, (T.card : ℝ) ≤ 4 * Real.exp ((n : ℝ) * U) ∧
      ∀ ℓ ∈ Icc 0 U, 1 ≤ n → 2 ≤ Real.exp ((n : ℝ) * ℓ) →
        |RHTower.weilLagFunctionReal ((n : ℝ) * ℓ)| ≤
          Real.exp (-((m : ℝ) + 1) * (n : ℝ)) →
        ∃ z ∈ T, |ℓ - z| ≤ lagSamplingCoverConstant *
          Real.exp (-(((m : ℝ) + 1) / 2 - U) * (n : ℝ)) := by
  classical
  by_cases hn : 1 ≤ n
  swap
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨∅, by simp, fun _ _ h => ?_⟩
    omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  let R : ℝ := Real.exp ((n : ℝ) * U)
  let t : ℝ := ((m : ℝ) + 1) * (n : ℝ)
  let ε : ℝ := 2 * R * Real.exp (-t)
  let A : ℕ → ℝ := fun j => 1 + Real.eulerMascheroniConstant + RHTower.mertensSum j
  let B : ℕ → ℝ := fun j => -Chebyshev.psi (j : ℝ) - Real.log (2 * Real.pi)
  have hR : 0 < R := Real.exp_pos _
  have hR1 : 1 ≤ R := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n) hU)
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose V hV using (fun j : ℕ => exists_lagCellModel_sublevel_cover (A j) (B j) hR hε)
  let N : ℕ := ⌊R⌋₊ + 1
  let C : Finset ℝ := (Finset.range N).biUnion V
  let T : Finset ℝ := C.image fun z => Real.log (max 1 z) / (n : ℝ)
  have hC : C.card ≤ 2 * N := by
    calc C.card ≤ ∑ j ∈ Finset.range N, (V j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.range N, 2 := Finset.sum_le_sum fun j _ => (hV j).1
      _ = 2 * N := by simp [mul_comm]
  have hNc : (N : ℝ) ≤ 2 * R := by
    have hfloor := Nat.floor_le hR.le
    dsimp [N]
    push_cast
    linarith only [hfloor, hR1]
  refine ⟨T, ?_, fun ℓ hℓ _ hx2 hsmall => ?_⟩
  · have hT : T.card ≤ 2 * N := Finset.card_image_le.trans hC
    have hTc : (T.card : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hT
    change (T.card : ℝ) ≤ 4 * R
    linarith only [hTc, hNc]
  · let x : ℝ := Real.exp ((n : ℝ) * ℓ)
    let j : ℕ := ⌊x⌋₊
    have hxR : x ≤ R := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hℓ.2 (Nat.cast_nonneg n))
    have hx0 : 0 < x := Real.exp_pos _
    have hx1 : 1 ≤ x := by change 2 ≤ x at hx2; linarith only [hx2]
    have hj2 : 2 ≤ j := Nat.le_floor hx2
    have hjN : j ∈ Finset.range N := by
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.floor_le_floor hxR)
    have hcell : x ∈ Ico (j : ℝ) ((j : ℝ) + 1) :=
      ⟨Nat.floor_le hx0.le, Nat.lt_floor_add_one x⟩
    have hvalue : |lagCellModel (A j) (B j) x| < ε := by
      rw [← scaledActualLag_eq_cellModel hj2 hcell, scaledActualLag]
      dsimp only [x]
      rw [Real.log_exp, abs_mul, abs_of_pos (Real.exp_pos _)]
      have htime : 0 ≤ (n : ℝ) * ℓ := mul_nonneg (Nat.cast_nonneg n) hℓ.1
      have htimeU := mul_le_mul_of_nonneg_left hℓ.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have hscale : Real.exp (((n : ℝ) * ℓ) / 2) ≤ R :=
        Real.exp_le_exp.mpr (by linarith only [htime, htimeU])
      have hsmall' : |RHTower.weilLagFunctionReal ((n : ℝ) * ℓ)| ≤ Real.exp (-t) := by
        simpa only [t, neg_mul] using hsmall
      calc Real.exp (((n : ℝ) * ℓ) / 2) *
          |RHTower.weilLagFunctionReal ((n : ℝ) * ℓ)| ≤ R * Real.exp (-t) :=
            mul_le_mul hscale hsmall' (abs_nonneg _) hR.le
        _ < ε := by
          have hp := mul_pos hR (Real.exp_pos (-t))
          dsimp [ε]
          linarith only [hp]
    obtain ⟨z, hz, hdist⟩ := (hV j).2 x ⟨hx2, hxR⟩ hvalue
    change |x - z| ≤ derivativeCoverConstant 2 (1 / (2 * R)) *
      (2 * R * Real.exp (-t)) ^ ((2 : ℝ)⁻¹) at hdist
    rw [lagCellCover_radius_eq hR t] at hdist
    refine ⟨Real.log (max 1 z) / (n : ℝ), Finset.mem_image.mpr
      ⟨z, Finset.mem_biUnion.mpr ⟨j, hjN, hz⟩, rfl⟩, ?_⟩
    have hclip : |x - max 1 z| ≤ |x - z| := by
      have h := abs_max_sub_max_le_abs x z 1
      rwa [max_eq_left hx1, max_comm z 1] at h
    have hlog : |Real.log x - Real.log (max 1 z)| ≤ |x - max 1 z| := by
      have h := RHTower.abs_log_sub_log_le (L := 2) (x := x) (y := max 1 z) (by norm_num)
        (by simpa using hx1) (by simpa using le_max_left (1 : ℝ) z)
      simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul] using h
    have heq : ℓ - Real.log (max 1 z) / (n : ℝ) =
        (Real.log x - Real.log (max 1 z)) / (n : ℝ) := by
      dsimp only [x]
      rw [Real.log_exp]
      field_simp
    rw [heq, abs_div, abs_of_pos hn0]
    calc |Real.log x - Real.log (max 1 z)| / (n : ℝ)
        ≤ (lagSamplingCoverConstant * R * Real.exp (-t / 2)) / (n : ℝ) :=
          div_le_div_of_nonneg_right (hlog.trans (hclip.trans hdist)) hn0.le
      _ ≤ lagSamplingCoverConstant * R * Real.exp (-t / 2) := by
        apply (div_le_iff₀ hn0).mpr
        exact le_mul_of_one_le_right
          (mul_pos (mul_pos lagSamplingCoverConstant_pos hR) (Real.exp_pos _)).le hn1
      _ = lagSamplingCoverConstant *
          Real.exp (-(((m : ℝ) + 1) / 2 - U) * (n : ℝ)) := by
        dsimp only [R, t]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

#print axioms exists_actualLag_sampled_cover

end GaloisForLFunctions.InfiniteRankWeilTheory
