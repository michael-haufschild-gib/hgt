import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22Identity
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanBoundarySupport

/-!
# Support of the complete Proposition 2.2 error
-/

namespace RHTower.Sieve

open ArithmeticFunction

noncomputable section

/-- Interval-restricted source errors and the complete product boundary share `(Y/4,8Y]`. -/
theorem mtHarmanProposition22ErrorAF_support_four_eight
    {outerQ outerD : ℕ} {delta : ℝ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D E : ℕ)
    (hendpointQ : ∀ i, 2 ≤ endpointQ i)
    (hbandQ : ∀ i, mtAdjacentBlockUpperScale endpointQ i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpointQ i)
    (hendpointD : ∀ i, 2 ≤ endpointD i)
    (hbandD : ∀ i, mtAdjacentBlockUpperScale endpointD i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpointD i)
    (z0 Dtrunc recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 Dtrunc recStart delta recRoot hdelta hz0 hroot).block)
    (hz0Data : data.z₀ = z0) (hDData : data.D = Dtrunc)
    (maxDepth : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta + 1))
    (N Y : ℕ) (hYNat : 1 ≤ Y) {eta : ℝ} (heta : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta)
    {n : ℕ}
    (hn : mtHarmanProposition22ErrorAF (outerD := outerD)
      endpointD z Q D E data maxDepth j Y
      (mtHarmanProductBoundaryErrorAF (outerQ := outerQ) (outerD := outerD)
        endpointQ endpointD z Q D (E : ℝ) data maxDepth j delta N recStart (Y : ℝ)) n ≠ 0) :
    (Y : ℝ) / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * (Y : ℝ) := by
  have hY : 0 < (Y : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hYNat)
  have hboundary : ∀ {m : ℕ},
      mtHarmanProductBoundaryErrorAF (outerQ := outerQ) (outerD := outerD)
        endpointQ endpointD z Q D (E : ℝ) data maxDepth j delta N recStart (Y : ℝ) m ≠ 0 →
      (Y : ℝ) / 4 < (m : ℝ) ∧ (m : ℝ) ≤ 8 * (Y : ℝ) := by
    intro m hm
    exact mtHarmanProductBoundaryErrorAF_support_four_eight
      (outerQ := outerQ) (outerD := outerD) endpointQ endpointD z Q D (E : ℝ)
      hendpointQ hbandQ hendpointD hbandD z0 Dtrunc recStart hdelta hz0 hroot
      data hblocks hz0Data hDData maxDepth j N hY heta hetaOne hdilation hm
  exact mtHarmanProposition22ErrorAF_support endpointD z Q D E data maxDepth j Y _
    hYNat hboundary hn

end

end RHTower.Sieve
