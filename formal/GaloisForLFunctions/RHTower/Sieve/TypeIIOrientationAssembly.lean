import GaloisForLFunctions.RHTower.Sieve.TypeIISwapExplicit

/-!
# Exhaustive type-II dyadic orientation assembly

When the global transition-range curvature inequality holds, every dyadic block satisfies the
threshold for at least one explicit Cauchy--Schwarz orientation.  This theorem performs that split
with the actual Vaughan coefficients and no analytic callback.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- Every relevant dyadic block obeys one of the two fully explicit coefficient-energy bounds. -/
theorem exists_typeII_orientation_block_bound :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {T r : ℝ} {A B L U V P Q : ℕ},
        0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ P → 2 ≤ Q →
        Q ≤ 2 * P → Q ≤ L + 1 → B - 1 ≤ L → P < B → 8 * r ≤ (A : ℝ) →
        2 * T * r ≤ 9 * Real.pi * A ^ (2 : ℕ) →
        (‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
              (fun m => typeIIShort V m)‖ ^ (2 : ℕ)
            ≤ (C₁ * (Q : ℝ) * Real.log L)
              * (((Q - P : ℕ) : ℝ) * typeIIShortEnergyEnvelope (effHigh B P)
                + typeIIShortEnergyEnvelope (effHigh B P)
                  * (2 * typeIIUnswapGapEnvelope T r A B P)))
          ∨
        (‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
              (fun m => typeIIShort V m)‖ ^ (2 : ℕ)
            ≤ typeIIShortEnergyEnvelope (effHigh B P)
              * ((((effHigh B P + 1 - effLow A Q : ℕ) : ℝ)
                    * (C₂ * (Q : ℝ) * Real.log L))
                + (C₂ * (Q : ℝ) * Real.log L)
                  * (2 * typeIISwapGapEnvelope T r A B P))) := by
  obtain ⟨C₁, hC₁, hunswap⟩ := exists_norm_maskedBlockSum_sq_le_unswap_explicit
  obtain ⟨C₂, hC₂, hswap⟩ := exists_norm_maskedBlockSum_sq_le_swap_explicit
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hP hQ hQ2P hQL hBL hPB h8 hglobal
  rcases typeII_orientation_cover hT hr hA hglobal with hlarge | hsmall
  · left
    exact hunswap hT hr hA hB hL hP hQ hQ2P hQL hPB h8 hlarge
  · right
    exact hswap hT hr hA hB hL hP hQ hQ2P hQL hBL hPB.le h8 hsmall

end

end RHTower.Sieve
