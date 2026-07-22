import GaloisForLFunctions.RHTower.VonMangoldtGammaJetBoundaryConvergence

/-!
# Universal two-boundary Gram collapse

Four different finite balancing mechanisms annihilate both Mellin boundary characters `+1/2`
and `-1/2`: orthogonal boundary projection, affine residual balance, arbitrary positive jet order,
and depth-matched growing jet order.  Consequently the entire two-node boundary Gram—not merely
its determinant—is zero for every finite source cutoff and depth.  The same total collapse
survives the genuine cofinal von Mangoldt limit.
-/

open scoped BigOperators ComplexOrder Topology
open Filter

namespace RHTower

noncomputable section

/-- Canonical pair of positive and negative Mellin boundary characters. -/
def vonMangoldtTwoBoundaryPacket : Fin 2 → ℂ := ![1 / 2, -1 / 2]

@[simp] theorem finiteVonMangoldtAllDepthBalancedCauchyVector_twoBoundary_eq_zero
    (M N : ℕ) (i : Fin 2) :
    finiteVonMangoldtAllDepthBalancedCauchyVector M N (vonMangoldtTwoBoundaryPacket i) = 0 := by
  fin_cases i
  · exact finiteVonMangoldtAllDepthBalancedCauchyVector_plus_half_eq_zero M N
  · exact finiteVonMangoldtAllDepthBalancedCauchyVector_neg_half_eq_zero M N

@[simp] theorem finiteVonMangoldtAllDepthAffineBalancedCauchyVector_twoBoundary_eq_zero
    (M N : ℕ) (i : Fin 2) :
    finiteVonMangoldtAllDepthAffineBalancedCauchyVector M N
      (vonMangoldtTwoBoundaryPacket i) = 0 := by
  fin_cases i
  · exact finiteVonMangoldtAllDepthAffineBalancedCauchyVector_plus_eq_zero M N
  · exact finiteVonMangoldtAllDepthAffineBalancedCauchyVector_minus_eq_zero M N

@[simp] theorem finiteVonMangoldtAllDepthJetBalancedCauchyVector_twoBoundary_eq_zero
    (M N k : ℕ) (i : Fin 2) :
    finiteVonMangoldtAllDepthJetBalancedCauchyVector M N (k + 1)
      (vonMangoldtTwoBoundaryPacket i) = 0 := by
  fin_cases i
  · exact finiteVonMangoldtAllDepthJetBalancedCauchyVector_succ_plus_eq_zero M N k
  · exact finiteVonMangoldtAllDepthJetBalancedCauchyVector_succ_minus_eq_zero M N k

@[simp] theorem finiteVonMangoldtAllDepthOrderGrowingCauchyVector_twoBoundary_eq_zero
    (M N : ℕ) (i : Fin 2) :
    finiteVonMangoldtAllDepthOrderGrowingCauchyVector M N
      (vonMangoldtTwoBoundaryPacket i) = 0 := by
  fin_cases i
  · exact finiteVonMangoldtAllDepthOrderGrowingCauchyVector_plus_eq_zero M N
  · exact finiteVonMangoldtAllDepthOrderGrowingCauchyVector_minus_eq_zero M N

theorem finiteVonMangoldtAllDepthBalancedCauchyGram_twoBoundary_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthBalancedCauchyGram M N vonMangoldtTwoBoundaryPacket = 0 := by
  ext i j
  simp [finiteVonMangoldtAllDepthBalancedCauchyGram, Matrix.gram_apply]

theorem finiteVonMangoldtAllDepthAffineBalancedCauchyGram_twoBoundary_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthAffineBalancedCauchyGram M N vonMangoldtTwoBoundaryPacket = 0 := by
  ext i j
  simp [finiteVonMangoldtAllDepthAffineBalancedCauchyGram, Matrix.gram_apply]

theorem finiteVonMangoldtAllDepthJetBalancedCauchyGram_twoBoundary_eq_zero
    (M N k : ℕ) :
    finiteVonMangoldtAllDepthJetBalancedCauchyGram M N (k + 1)
      vonMangoldtTwoBoundaryPacket = 0 := by
  ext i j
  simp [finiteVonMangoldtAllDepthJetBalancedCauchyGram, Matrix.gram_apply]

theorem finiteVonMangoldtAllDepthOrderGrowingCauchyGram_twoBoundary_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N vonMangoldtTwoBoundaryPacket = 0 := by
  ext i j
  simp [finiteVonMangoldtAllDepthOrderGrowingCauchyGram, Matrix.gram_apply]

theorem infiniteVonMangoldtAllDepthOrderGrowingCauchyGram_twoBoundary_eq_zero
    (N : ℕ) :
    infiniteVonMangoldtAllDepthOrderGrowingCauchyGram N vonMangoldtTwoBoundaryPacket = 0 := by
  ext i j
  have hlim := finiteVonMangoldtAllDepthOrderGrowingCauchyGram_tendsto
    N vonMangoldtTwoBoundaryPacket i j
  have heq :
      (fun M => finiteVonMangoldtAllDepthOrderGrowingCauchyGram
        M N vonMangoldtTwoBoundaryPacket i j) = fun _ => 0 := by
    funext M
    rw [finiteVonMangoldtAllDepthOrderGrowingCauchyGram_twoBoundary_eq_zero]
    rfl
  have hzero : Tendsto
      (fun M => finiteVonMangoldtAllDepthOrderGrowingCauchyGram
        M N vonMangoldtTwoBoundaryPacket i j)
      atTop (𝓝 0) := by
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzero

/-- **Universal two-boundary collapse law.**  Projection, affine, positive jet, growing jet, and
cofinal growing-jet Grams all annihilate the complete canonical boundary packet. -/
theorem vonMangoldtAllDepthTwoBoundaryGramCollapseLaw (M N k : ℕ) :
    finiteVonMangoldtAllDepthBalancedCauchyGram M N vonMangoldtTwoBoundaryPacket = 0 ∧
    finiteVonMangoldtAllDepthAffineBalancedCauchyGram M N vonMangoldtTwoBoundaryPacket = 0 ∧
    finiteVonMangoldtAllDepthJetBalancedCauchyGram M N (k + 1)
      vonMangoldtTwoBoundaryPacket = 0 ∧
    finiteVonMangoldtAllDepthOrderGrowingCauchyGram M N vonMangoldtTwoBoundaryPacket = 0 ∧
    infiniteVonMangoldtAllDepthOrderGrowingCauchyGram N vonMangoldtTwoBoundaryPacket = 0 :=
  ⟨finiteVonMangoldtAllDepthBalancedCauchyGram_twoBoundary_eq_zero M N,
    finiteVonMangoldtAllDepthAffineBalancedCauchyGram_twoBoundary_eq_zero M N,
    finiteVonMangoldtAllDepthJetBalancedCauchyGram_twoBoundary_eq_zero M N k,
    finiteVonMangoldtAllDepthOrderGrowingCauchyGram_twoBoundary_eq_zero M N,
    infiniteVonMangoldtAllDepthOrderGrowingCauchyGram_twoBoundary_eq_zero N⟩

end


end RHTower
