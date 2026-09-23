import GaloisForLFunctions.HTGeometry.ConservativeHankelRigidity
import GaloisForLFunctions.RHTower.VonMangoldtAdditiveLogJetPointedNoGo
import GaloisForLFunctions.RHTower.VonMangoldtGammaPointedWardReconstruction

/-!
# Hankel curvature of the von Mangoldt successor Dirichlet carrier

The successor Dirichlet Gram is not merely different from the completed prime--Gamma moment
matrix.  Its first Hankel curvature is strictly negative.  Every additive ordinary Hankel
boundary has zero curvature and therefore cannot repair it.  Any viable Gamma/polar Green--Schur
completion must contain genuinely non-Hankel pointed or cross terms carrying the exact opposite
curvature.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The resolved von Mangoldt conductance at the prime atom `2` is strictly positive. -/
theorem finiteVonMangoldtRealWeight_two_pos :
    0 < finiteVonMangoldtRealWeight 2 := by
  rw [finiteVonMangoldtRealWeight,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  positivity

/-- The order-one successor logarithmic difference is already strict on the edge `2 -> 3`. -/
theorem vonMangoldtAdditiveLogJetDifference_one_two_pos :
    0 < vonMangoldtAdditiveLogJetDifference 1 2 := by
  simp only [vonMangoldtAdditiveLogJetDifference,
    vonMangoldtAdditiveLogJet, pow_one, Nat.cast_ofNat]
  exact sub_pos.mpr (Real.strictMonoOn_log
    (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (3 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (2 : ℝ) < 3))

/-- The actual prime atom `2` supplies a strictly positive order-one edge energy. -/
theorem vonMangoldtAdditiveLogJetEnergy_one_two_pos :
    0 < vonMangoldtAdditiveLogJetEnergy 1 2 := by
  rw [vonMangoldtAdditiveLogJetEnergy]
  exact mul_pos finiteVonMangoldtRealWeight_two_pos
    (sq_pos_of_pos vonMangoldtAdditiveLogJetDifference_one_two_pos)

/-- The total order-one successor Dirichlet energy is strictly positive. -/
theorem tsum_vonMangoldtAdditiveLogJetEnergy_one_pos :
    0 < ∑' n, vonMangoldtAdditiveLogJetEnergy 1 n := by
  exact (summable_vonMangoldtAdditiveLogJetEnergy 1).tsum_pos
    (vonMangoldtAdditiveLogJetEnergy_nonneg 1) 2
    vonMangoldtAdditiveLogJetEnergy_one_two_pos

/-- The first nonconstant diagonal entry of the actual successor Gram is strictly positive. -/
theorem vonMangoldtAdditiveLogJetGram_three_one_one_pos :
    0 < vonMangoldtAdditiveLogJetGram 3 1 1 := by
  rw [vonMangoldtAdditiveLogJetGram_diagonal]
  exact tsum_vonMangoldtAdditiveLogJetEnergy_one_pos

/-- Conservativity kills the transposed `(2,0)` entry. -/
theorem vonMangoldtAdditiveLogJetGram_three_two_zero_eq_zero :
    vonMangoldtAdditiveLogJetGram 3 2 0 = 0 := by
  rw [vonMangoldtAdditiveLogJetGram_apply]
  simp [vonMangoldtAdditiveLogJetFeature_zero]

/-- Exact first Hankel curvature of the actual successor carrier. -/
theorem vonMangoldtAdditiveLogJetGram_firstHankelCurvature_eq :
    vonMangoldtAdditiveLogJetGram 3 2 0 -
        vonMangoldtAdditiveLogJetGram 3 1 1 =
      -(∑' n, vonMangoldtAdditiveLogJetEnergy 1 n) := by
  rw [vonMangoldtAdditiveLogJetGram_three_two_zero_eq_zero,
    vonMangoldtAdditiveLogJetGram_diagonal]
  norm_num

/-- **Actual strict curvature law.** The successor carrier lies strictly on the anti-Hankel side
at its first nonconstant jet. -/
theorem vonMangoldtAdditiveLogJetGram_firstHankelCurvature_neg :
    vonMangoldtAdditiveLogJetGram 3 2 0 -
        vonMangoldtAdditiveLogJetGram 3 1 1 < 0 := by
  rw [vonMangoldtAdditiveLogJetGram_firstHankelCurvature_eq]
  exact neg_neg_of_pos tsum_vonMangoldtAdditiveLogJetEnergy_one_pos

/-- Adding any boundary with the first Hankel shift relation leaves the strict curvature
unchanged. -/
theorem vonMangoldtAdditiveLogJetGram_add_hankelCorrection_curvature_neg
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B 2 0 = B 1 1) :
    (vonMangoldtAdditiveLogJetGram 3 + B) 2 0 -
        (vonMangoldtAdditiveLogJetGram 3 + B) 1 1 < 0 := by
  simp only [Matrix.add_apply]
  rw [hB]
  simpa only [add_sub_add_right_eq_sub] using
    vonMangoldtAdditiveLogJetGram_firstHankelCurvature_neg

/-- **Additive Hankel-boundary no-go.** No boundary and target which both obey the first Hankel
shift relation can satisfy a completed additive identity with the successor Gram. -/
theorem vonMangoldtAdditiveLogJetGram_add_hankelCorrection_ne_hankelTarget
    (B T : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B 2 0 = B 1 1) (hT : T 2 0 = T 1 1) :
    vonMangoldtAdditiveLogJetGram 3 + B ≠ T := by
  intro h
  have h20 := congrFun (congrFun h (2 : Fin 3)) (0 : Fin 3)
  have h11 := congrFun (congrFun h (1 : Fin 3)) (1 : Fin 3)
  have hneg := vonMangoldtAdditiveLogJetGram_add_hankelCorrection_curvature_neg B hB
  rw [h20, h11, hT] at hneg
  rw [sub_self] at hneg
  exact (lt_irrefl 0) hneg

/-- In particular, adding an arbitrary moment-Hankel boundary cannot produce any moment-Hankel
target, independently of what either moment sequence is. -/
theorem vonMangoldtAdditiveLogJetGram_add_momentHankel_ne_momentHankel
    (boundary target : ℕ → ℝ) :
    vonMangoldtAdditiveLogJetGram 3 +
        HTGeometry.momentHankelMatrix boundary 3 ≠
      HTGeometry.momentHankelMatrix target 3 := by
  apply vonMangoldtAdditiveLogJetGram_add_hankelCorrection_ne_hankelTarget
  · simp [HTGeometry.momentHankelMatrix]
  · simp [HTGeometry.momentHankelMatrix]

/-! ### All-order strict anti-Hankel curvature -/

/-- Infinite successor Gram kernel without a finite jet-index wrapper. -/
def vonMangoldtAdditiveLogJetKernel (r s : ℕ) : ℝ :=
  ∑' n, vonMangoldtAdditiveLogJetFeature r n *
    vonMangoldtAdditiveLogJetFeature s n

/-- Positive density whose total is the magnitude of adjacent Hankel curvature at order `s`. -/
def vonMangoldtAdditiveLogJetAdjacentHankelCost (s n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n *
    (Real.log (n + 1 : ℝ) - Real.log (n : ℝ)) ^ (2 : ℕ) *
      (Real.log (n + 1 : ℝ) * Real.log (n : ℝ)) ^ s

theorem vonMangoldtAdditiveLogJetAdjacentHankelCost_nonneg (s n : ℕ) :
    0 ≤ vonMangoldtAdditiveLogJetAdjacentHankelCost s n := by
  rcases n with _ | n
  · simp [vonMangoldtAdditiveLogJetAdjacentHankelCost]
  · apply mul_nonneg (mul_nonneg (finiteVonMangoldtRealWeight_nonneg _)
      (sq_nonneg _))
    apply pow_nonneg
    apply mul_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 + 1 by omega))
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))

/-- The prime atom `2` makes every order of the curvature density strict. -/
theorem vonMangoldtAdditiveLogJetAdjacentHankelCost_two_pos (s : ℕ) :
    0 < vonMangoldtAdditiveLogJetAdjacentHankelCost s 2 := by
  unfold vonMangoldtAdditiveLogJetAdjacentHankelCost
  have hdiff : 0 < Real.log (2 + 1 : ℝ) - Real.log (2 : ℝ) := by
    norm_num
    exact Real.strictMonoOn_log
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (3 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2 : ℝ) < 3)
  exact mul_pos
    (mul_pos finiteVonMangoldtRealWeight_two_pos (sq_pos_of_pos hdiff))
    (pow_pos (mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))) s)

/-- Exact local all-order curvature law. -/
theorem vonMangoldtAdditiveLogJetFeature_adjacentHankelCurvature_eq
    (s n : ℕ) :
    vonMangoldtAdditiveLogJetFeature (s + 2) n *
          vonMangoldtAdditiveLogJetFeature s n -
        vonMangoldtAdditiveLogJetFeature (s + 1) n ^ (2 : ℕ) =
      -vonMangoldtAdditiveLogJetAdjacentHankelCost s n := by
  unfold vonMangoldtAdditiveLogJetFeature
  calc
    (Real.sqrt (finiteVonMangoldtRealWeight n) *
          vonMangoldtAdditiveLogJetDifference (s + 2) n) *
        (Real.sqrt (finiteVonMangoldtRealWeight n) *
          vonMangoldtAdditiveLogJetDifference s n) -
        (Real.sqrt (finiteVonMangoldtRealWeight n) *
          vonMangoldtAdditiveLogJetDifference (s + 1) n) ^ (2 : ℕ) =
        (Real.sqrt (finiteVonMangoldtRealWeight n) *
          Real.sqrt (finiteVonMangoldtRealWeight n)) *
        (vonMangoldtAdditiveLogJetDifference (s + 2) n *
          vonMangoldtAdditiveLogJetDifference s n -
          vonMangoldtAdditiveLogJetDifference (s + 1) n ^ (2 : ℕ)) := by ring
    _ = finiteVonMangoldtRealWeight n *
        (vonMangoldtAdditiveLogJetDifference (s + 2) n *
          vonMangoldtAdditiveLogJetDifference s n -
          vonMangoldtAdditiveLogJetDifference (s + 1) n ^ (2 : ℕ)) := by
      rw [Real.mul_self_sqrt (finiteVonMangoldtRealWeight_nonneg n)]
    _ = -vonMangoldtAdditiveLogJetAdjacentHankelCost s n := by
      unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
      simp only [Nat.cast_add, Nat.cast_one]
      rw [HTGeometry.monomialEdge_adjacent_hankelCurvature_eq
        (Real.log (n + 1 : ℝ)) (Real.log (n : ℝ)) s]
      unfold vonMangoldtAdditiveLogJetAdjacentHankelCost
      ring

/-- Every adjacent curvature density is summable, despite its strict source sign. -/
theorem summable_vonMangoldtAdditiveLogJetAdjacentHankelCost (s : ℕ) :
    Summable (vonMangoldtAdditiveLogJetAdjacentHankelCost s) := by
  have hleft := summable_vonMangoldtAdditiveLogJetFeature_mul (s + 2) s
  have hright := summable_sq_vonMangoldtAdditiveLogJetFeature (s + 1)
  have hdiff := hleft.sub hright
  apply hdiff.neg.congr
  intro n
  have hcurv := vonMangoldtAdditiveLogJetFeature_adjacentHankelCurvature_eq s n
  linarith

theorem tsum_vonMangoldtAdditiveLogJetAdjacentHankelCost_pos (s : ℕ) :
    0 < ∑' n, vonMangoldtAdditiveLogJetAdjacentHankelCost s n := by
  exact (summable_vonMangoldtAdditiveLogJetAdjacentHankelCost s).tsum_pos
    (vonMangoldtAdditiveLogJetAdjacentHankelCost_nonneg s) 2
    (vonMangoldtAdditiveLogJetAdjacentHankelCost_two_pos s)

/-- **All-order exact anti-Hankel law.** Adjacent shift curvature is the negative of an explicit
strictly positive source sum at every order. -/
theorem vonMangoldtAdditiveLogJetKernel_adjacentHankelCurvature_eq (s : ℕ) :
    vonMangoldtAdditiveLogJetKernel (s + 2) s -
        vonMangoldtAdditiveLogJetKernel (s + 1) (s + 1) =
      -(∑' n, vonMangoldtAdditiveLogJetAdjacentHankelCost s n) := by
  rw [vonMangoldtAdditiveLogJetKernel, vonMangoldtAdditiveLogJetKernel,
    ← (summable_vonMangoldtAdditiveLogJetFeature_mul (s + 2) s).tsum_sub
      (summable_vonMangoldtAdditiveLogJetFeature_mul (s + 1) (s + 1))]
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  calc
    vonMangoldtAdditiveLogJetFeature (s + 2) n *
          vonMangoldtAdditiveLogJetFeature s n -
        vonMangoldtAdditiveLogJetFeature (s + 1) n *
          vonMangoldtAdditiveLogJetFeature (s + 1) n =
        vonMangoldtAdditiveLogJetFeature (s + 2) n *
          vonMangoldtAdditiveLogJetFeature s n -
        vonMangoldtAdditiveLogJetFeature (s + 1) n ^ (2 : ℕ) := by ring
    _ = -vonMangoldtAdditiveLogJetAdjacentHankelCost s n :=
      vonMangoldtAdditiveLogJetFeature_adjacentHankelCurvature_eq s n

/-- The anti-Hankel curvature is strict at every adjacent order. -/
theorem vonMangoldtAdditiveLogJetKernel_adjacentHankelCurvature_neg (s : ℕ) :
    vonMangoldtAdditiveLogJetKernel (s + 2) s -
        vonMangoldtAdditiveLogJetKernel (s + 1) (s + 1) < 0 := by
  rw [vonMangoldtAdditiveLogJetKernel_adjacentHankelCurvature_eq]
  exact neg_neg_of_pos (tsum_vonMangoldtAdditiveLogJetAdjacentHankelCost_pos s)

/-- Positive-depth successor Gram, aligned with the admissible positive depths of the pointed
Gamma--Bianchi reconstruction. -/
def vonMangoldtAdditivePositiveLogJetGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (fun i : Fin N =>
    vonMangoldtAdditiveLogJetVector ((i : ℕ) + 1))

theorem vonMangoldtAdditivePositiveLogJetGram_apply
    (N : ℕ) (i j : Fin N) :
    vonMangoldtAdditivePositiveLogJetGram N i j =
      vonMangoldtAdditiveLogJetKernel ((i : ℕ) + 1) ((j : ℕ) + 1) := by
  rw [vonMangoldtAdditivePositiveLogJetGram, Matrix.gram_apply, lp.inner_eq_tsum]
  simp [vonMangoldtAdditiveLogJetVector, vonMangoldtAdditiveLogJetKernel, mul_comm]

theorem vonMangoldtAdditivePositiveLogJetGram_posSemidef (N : ℕ) :
    (vonMangoldtAdditivePositiveLogJetGram N).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

theorem vonMangoldtAdditivePositiveLogJetGram_firstHankelCurvature_neg :
    vonMangoldtAdditivePositiveLogJetGram 3 2 0 -
        vonMangoldtAdditivePositiveLogJetGram 3 1 1 < 0 := by
  rw [vonMangoldtAdditivePositiveLogJetGram_apply,
    vonMangoldtAdditivePositiveLogJetGram_apply]
  norm_num
  exact sub_neg.mp (vonMangoldtAdditiveLogJetKernel_adjacentHankelCurvature_neg 1)

/-- An aligned ordinary Hankel boundary also cannot repair the positive-depth successor tower. -/
theorem vonMangoldtAdditivePositiveLogJetGram_add_hankelCorrection_ne_hankelTarget
    (B T : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B 2 0 = B 1 1) (hT : T 2 0 = T 1 1) :
    vonMangoldtAdditivePositiveLogJetGram 3 + B ≠ T := by
  intro h
  have h20 := congrFun (congrFun h (2 : Fin 3)) (0 : Fin 3)
  have h11 := congrFun (congrFun h (1 : Fin 3)) (1 : Fin 3)
  have hneg := vonMangoldtAdditivePositiveLogJetGram_firstHankelCurvature_neg
  simp only [Matrix.add_apply] at h20 h11
  linarith [hB, hT]

/-! ### The actual pointed Ward/Bianchi boundary is in the excluded additive class -/

/-- Positive jet depth used to extract a `3 x 3` pointed Bianchi boundary block. -/
def pointedWardHankelDepth (i : Fin 3) : ℕ := (i : ℕ) + 1

/-- Actual finite von Mangoldt--Gamma adjacent-depth Bianchi boundary on the first three positive
jet depths. -/
def finiteVonMangoldtGammaPointedBianchiHankelBoundary
    (M : ℕ) (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteVonMangoldtGammaAnomalyBianchiMixedGram M x
    pointedWardHankelDepth (fun _ ↦ 0) (by
      intro i j
      simp only [pointedWardHankelDepth]
      omega)

/-- Pointed Ward reconstruction identifies the actual Bianchi boundary with the shifted raw
von Mangoldt moment Gram. -/
theorem finiteVonMangoldtGammaPointedBianchiHankelBoundary_eq_rawGram
    (M : ℕ) (x : ℝ) :
    finiteVonMangoldtGammaPointedBianchiHankelBoundary M x =
      finiteVonMangoldtGammaRawGram M x pointedWardHankelDepth := by
  rw [finiteVonMangoldtGammaPointedBianchiHankelBoundary]
  apply finiteVonMangoldtGammaAnomalyBianchiMixedGram_eq_rawGram

/-- The actual pointed Bianchi boundary has zero first Hankel curvature. -/
theorem finiteVonMangoldtGammaPointedBianchiHankelBoundary_firstShift
    (M : ℕ) (x : ℝ) :
    finiteVonMangoldtGammaPointedBianchiHankelBoundary M x 2 0 =
      finiteVonMangoldtGammaPointedBianchiHankelBoundary M x 1 1 := by
  rw [finiteVonMangoldtGammaPointedBianchiHankelBoundary_eq_rawGram,
    finiteVonMangoldtGammaRawGram_apply,
    finiteVonMangoldtGammaRawGram_apply]
  rfl

/-- **Direct-sum Bianchi no-go.** Adding the actual positive pointed Ward/Bianchi boundary to the
positive successor carrier still cannot produce any moment-Hankel target.  The missing data are
necessarily non-Hankel coupling/cross terms. -/
theorem vonMangoldtAdditivePositiveLogJetGram_add_pointedBianchiBoundary_ne_momentHankel
    (M : ℕ) (x : ℝ) (target : ℕ → ℝ) :
    vonMangoldtAdditivePositiveLogJetGram 3 +
        finiteVonMangoldtGammaPointedBianchiHankelBoundary M x ≠
      HTGeometry.momentHankelMatrix target 3 := by
  apply vonMangoldtAdditivePositiveLogJetGram_add_hankelCorrection_ne_hankelTarget
  · exact finiteVonMangoldtGammaPointedBianchiHankelBoundary_firstShift M x
  · simp [HTGeometry.momentHankelMatrix]

/-- In particular, the direct sum of the two proved positive source legs is not the normalized
prime--archimedean Hankel section. -/
theorem vonMangoldtAdditivePositiveLogJetGram_add_pointedBianchiBoundary_ne_primeArchSourceMomentHankel
    (M : ℕ) (x : ℝ) :
    vonMangoldtAdditivePositiveLogJetGram 3 +
        finiteVonMangoldtGammaPointedBianchiHankelBoundary M x ≠
      primeArchSourceMomentHankelMatrix 3 := by
  apply vonMangoldtAdditivePositiveLogJetGram_add_hankelCorrection_ne_hankelTarget
  · exact finiteVonMangoldtGammaPointedBianchiHankelBoundary_firstShift M x
  · rw [primeArchSourceMomentHankelMatrix_apply,
      primeArchSourceMomentHankelMatrix_apply]
    rfl

end

end RHTower
