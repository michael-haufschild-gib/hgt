import GaloisForLFunctions.RHTower.Sieve.RamareLadderHMRecip
import GaloisForLFunctions.RHTower.Sieve.LadderAggregates

/-!
# The large half's ladder group

The exceptional half carries the Kuzmin–Landau Halász–Montgomery mass instead of the mean value
theorem's.  Its dependence on the block data is through the same three aggregates, so
`Sieve/LadderGroupBudget.ladderGroup_hm_inner_le` applies once the kernel's far constant is made
uniform over the ladder — which it is, because that constant grows only through `log₂` of the
cofactor length, and the cofactor is longest at the bottom of the range.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The kernel's far constant grows with the length of the polynomial. -/
theorem plainKernelFarConst_mono {N N' : ℕ} (h : N ≤ N') (T : ℝ) :
    plainKernelFarConst N T ≤ plainKernelFarConst N' T := by
  have hlog : (Nat.log 2 N : ℝ) ≤ (Nat.log 2 N' : ℝ) := by
    exact_mod_cast Nat.log_mono_right h
  rw [plainKernelFarConst, plainKernelFarConst]
  linarith

/-- The cofactor is longest at the bottom of the range. -/
theorem floor_div_le_bottom (M : ℕ) {R η : ℝ} (hR : 0 < R) (hη : 0 ≤ η) (j : ℕ) :
    ⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ ≤ ⌊(M : ℝ) / R⌋₊ := by
  refine Nat.floor_le_floor ?_
  have h1 : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ (by linarith)
  have hRj : R ≤ R * (1 + η) ^ j := by nlinarith [hR.le, h1]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg M) hR hRj

/-- **The large half's ladder group.** -/
theorem largeLadderGroup_le {P : Finset ℕ} (M : ℕ) {R η W ρ volE : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    (hW : 1 ≤ W) (hvol : 0 ≤ volE) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, R < (p : ℝ) ∧ (p : ℝ) ≤ R * (1 + η) ^ L) :
    2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (ρ * ((geomBlock P R (1 + η) j).card : ℝ)) ^ (2 : ℕ)
          * ladderHMBoundRecip M R η W volE j
      ≤ 2 * (L : ℝ) * (2 * Real.pi)⁻¹
          * (ρ ^ (2 : ℕ) * ((2 + 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)))
                * (((1 + η) * (M : ℝ) * rangeHarmonic P) ^ (2 : ℕ)
                  + (R * (1 + η) ^ L * η + 1) * ((1 + η) * (M : ℝ) * rangeHarmonic P))
              + plainKernelFarConst ⌊(M : ℝ) / R⌋₊ (2 * Real.pi * W)
                  * (2 * Real.pi * volE)
                  * ((R * (1 + η) ^ L * η + 1) * ((1 + η) * (M : ℝ) * rangeHarmonic P)
                    + (R * (1 + η) ^ L * η + 1) * (P.card : ℝ)))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hW0 : (0 : ℝ) ≤ 2 * Real.pi * W := by positivity
  have hΛ : (0 : ℝ) ≤ Real.log (2 + 2 * (2 * Real.pi * W)) :=
    Real.log_nonneg (by linarith)
  have hBmax0 : (0 : ℝ) ≤ R * (1 + η) ^ L * η + 1 := by positivity
  have hH : (0 : ℝ) ≤ rangeHarmonic P := Finset.sum_nonneg fun p _ => by positivity
  have hS0 : (0 : ℝ) ≤ (1 + η) * (M : ℝ) * rangeHarmonic P := by
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    rw [rangeHarmonic] at hH ⊢
    positivity
  have hFC0 : (0 : ℝ) ≤ plainKernelFarConst ⌊(M : ℝ) / R⌋₊ (2 * Real.pi * W) := by
    refine plainKernelFarConst_nonneg _ ?_
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hW, h3]
  have hrw : ∀ j : ℕ,
      (ρ * ((geomBlock P R (1 + η) j).card : ℝ)) ^ (2 : ℕ) * ladderHMBoundRecip M R η W volE j
        = (2 * Real.pi)⁻¹
            * ((ρ * ((geomBlock P R (1 + η) j).card : ℝ)) ^ (2 : ℕ)
              * ((2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
                    + plainKernelFarConst ⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ (2 * Real.pi * W)
                        * (2 * Real.pi * volE)
                    + 48 * Real.pi * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
                        * Real.log (2 + 2 * (2 * Real.pi * W)))
                * ((geomCofactorBlock M R η j).card : ℝ))) := by
    intro j
    rw [ladderHMBoundRecip, hmMassRecip]
    ring
  rw [Finset.sum_congr rfl fun j _ => hrw j, ← Finset.mul_sum]
  have hinner := ladderGroup_hm_inner_le (L := L) (ρ := ρ)
    (S := (1 + η) * (M : ℝ) * rangeHarmonic P)
    (Bmax := R * (1 + η) ^ L * η + 1) (PP := (P.card : ℝ))
    (FCmax := plainKernelFarConst ⌊(M : ℝ) / R⌋₊ (2 * Real.pi * W))
    (v := 2 * Real.pi * volE) (Λ := Real.log (2 + 2 * (2 * Real.pi * W)))
    (B := fun j => ((geomBlock P R (1 + η) j).card : ℝ))
    (Cc := fun j => ((geomCofactorBlock M R η j).card : ℝ))
    (Nn := fun j => ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
    (FC := fun j => plainKernelFarConst ⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ (2 * Real.pi * W))
    hBmax0 (fun j => Nat.cast_nonneg _) (fun j => Nat.cast_nonneg _) (fun j => Nat.cast_nonneg _)
    (fun j _ => card_geomCofactorBlock_le M R η j)
    (fun j hj => card_geomBlock_le_top P hR hη hj)
    (fun j _ => plainKernelFarConst_mono (floor_div_le_bottom M hR hη j) (2 * Real.pi * W))
    hFC0 (by positivity) hΛ
    (by rw [rangeHarmonic]; exact sum_card_geomBlock_mul_floor_le M hR hη hL hP)
    (sum_card_geomBlock_le_card hR hη hL hP)
  have hL0 : (0 : ℝ) ≤ 2 * (L : ℝ) * (2 * Real.pi)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left hinner hL0
  calc 2 * (L : ℝ) * ((2 * Real.pi)⁻¹ * ∑ j ∈ Finset.range L,
          (ρ * ((geomBlock P R (1 + η) j).card : ℝ)) ^ (2 : ℕ)
            * ((2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
                  + plainKernelFarConst ⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ (2 * Real.pi * W)
                      * (2 * Real.pi * volE)
                  + 48 * Real.pi * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
                      * Real.log (2 + 2 * (2 * Real.pi * W)))
              * ((geomCofactorBlock M R η j).card : ℝ)))
      = 2 * (L : ℝ) * (2 * Real.pi)⁻¹ * ∑ j ∈ Finset.range L,
          (ρ * ((geomBlock P R (1 + η) j).card : ℝ)) ^ (2 : ℕ)
            * ((2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
                  + plainKernelFarConst ⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ (2 * Real.pi * W)
                      * (2 * Real.pi * volE)
                  + 48 * Real.pi * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
                      * Real.log (2 + 2 * (2 * Real.pi * W)))
              * ((geomCofactorBlock M R η j).card : ℝ)) := by ring
    _ ≤ _ := this

end

end RHTower.Sieve
