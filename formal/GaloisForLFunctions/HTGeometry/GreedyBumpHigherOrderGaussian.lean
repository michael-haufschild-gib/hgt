import GaloisForLFunctions.HTGeometry.QuasiFreeWickExpansion

/-!
# Higher-order Gaussian greedy-bump coefficients

Appendix A's one-dimensional correction coefficients are evaluated with the
corpus's Isserlis/Wick recursion.  The derivative labels and their covariance
kernel are concrete, so no Gaussian-moment assumptions remain in theorem
statements.
-/

namespace GaloisForLFunctions.HTGeometry

inductive GreedyBumpGaussianJetLabel
  | X | A | B | C | D4 | E5
  deriving DecidableEq

open GreedyBumpGaussianJetLabel

/-- Nonzero two-point contractions of the Gaussian location-model jet. -/
def greedyBumpGaussianJetContraction :
    GreedyBumpGaussianJetLabel → GreedyBumpGaussianJetLabel → ℝ
  | A, A => 1
  | A, C => -3
  | C, A => -3
  | A, E5 => 15
  | E5, A => 15
  | B, B => 3
  | B, D4 => -15
  | D4, B => -15
  | C, C => 15
  | X, B => -1
  | B, X => -1
  | X, D4 => 3
  | D4, X => 3
  | _, _ => 0

/-- Four-field Isserlis expansion from the recursive Wick moment. -/
theorem greedyBump_wickMoment_four_expansion {ι R : Type*} [CommRing R]
    (W : ι → ι → R) (a b c d : ι) :
    wickMoment W [a, b, c, d] =
      W a b * W c d + W a c * W b d + W a d * W b c := by
  rw [wickMoment_cons]
  change (∑ k : Fin 3, W a [b, c, d][k] *
    wickMoment W ([b, c, d].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_three]
  simp [List.eraseIdx, wickMoment]

/-- `E[A⁴]=3`. -/
theorem greedyBumpGaussianJet_wick_A4 :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, A] = 3 := by
  rw [greedyBump_wickMoment_four_expansion]
  norm_num [greedyBumpGaussianJetContraction]

/-- `E[A³C]=-9`. -/
theorem greedyBumpGaussianJet_wick_A3C :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, C] = -9 := by
  rw [greedyBump_wickMoment_four_expansion]
  norm_num [greedyBumpGaussianJetContraction]

/-- `E[A²B²]=3`. -/
theorem greedyBumpGaussianJet_wick_A2B2 :
    wickMoment greedyBumpGaussianJetContraction [A, A, B, B] = 3 := by
  rw [greedyBump_wickMoment_four_expansion]
  norm_num [greedyBumpGaussianJetContraction]

/-- `E[XA²B]=-1`, the radial/local coupling entering profile gain. -/
theorem greedyBumpGaussianJet_wick_XA2B :
    wickMoment greedyBumpGaussianJetContraction [X, A, A, B] = -1 := by
  rw [greedyBump_wickMoment_four_expansion]
  norm_num [greedyBumpGaussianJetContraction]

/-- The odd cubic contraction `E[A²B]` vanishes. -/
theorem greedyBumpGaussianJet_wick_A2B :
    wickMoment greedyBumpGaussianJetContraction [A, A, B] = 0 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 2, greedyBumpGaussianJetContraction A [A, B][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A, B].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_two]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction, wickMoment]

/-- `E[A⁶]=15`. -/
theorem greedyBumpGaussianJet_wick_A6 :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, A, A, A] = 15 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,A,A,A,A][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,A,A,A,A].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- `E[A⁵C]=-45`. -/
theorem greedyBumpGaussianJet_wick_A5C :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, A, A, C] = -45 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,A,A,A,C][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,A,A,A,C].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- `E[A⁵E₅]=225`. -/
theorem greedyBumpGaussianJet_wick_A5E5 :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, A, A, E5] = 225 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,A,A,A,E5][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,A,A,A,E5].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- `E[A⁴B²]=9`. -/
theorem greedyBumpGaussianJet_wick_A4B2 :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, A, B, B] = 9 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,A,A,B,B][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,A,A,B,B].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- `E[A⁴BD₄]=-45`. -/
theorem greedyBumpGaussianJet_wick_A4BD4 :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, A, B, D4] = -45 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,A,A,B,D4][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,A,A,B,D4].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- `E[A⁴C²]=153`. -/
theorem greedyBumpGaussianJet_wick_A4C2 :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, A, C, C] = 153 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,A,A,C,C][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,A,A,C,C].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- `E[A³B²C]=-27`. -/
theorem greedyBumpGaussianJet_wick_A3B2C :
    wickMoment greedyBumpGaussianJetContraction [A, A, A, B, B, C] = -27 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,A,B,B,C][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,A,B,B,C].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- `E[A²B⁴]=27`. -/
theorem greedyBumpGaussianJet_wick_A2B4 :
    wickMoment greedyBumpGaussianJetContraction [A, A, B, B, B, B] = 27 := by
  rw [wickMoment_cons]
  change (∑ k : Fin 5, greedyBumpGaussianJetContraction A [A,B,B,B,B][k] *
    wickMoment greedyBumpGaussianJetContraction
      ([A,B,B,B,B].eraseIdx (k : ℕ))) = _
  rw [Fin.sum_univ_five]
  norm_num [List.get, List.eraseIdx, greedyBumpGaussianJetContraction,
    greedyBump_wickMoment_four_expansion]

/-- Leading one-dimensional amplitude-bias coefficient `E[δ₁]=1/2`. -/
theorem greedyBumpGaussianLocation_biasCoefficient_one :
    (1 / 2 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A, A] = 1 / 2 := by
  norm_num [wickMoment, greedyBumpGaussianJetContraction]

/-- Odd one-dimensional amplitude-bias coefficient `E[δ₂]=0`. -/
theorem greedyBumpGaussianLocation_biasCoefficient_two :
    (1 / 2 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A, A, B] = 0 := by
  rw [greedyBumpGaussianJet_wick_A2B]
  norm_num

/-- First curvature correction `E[δ₃]=3/8`. -/
theorem greedyBumpGaussianLocation_biasCoefficient_three :
    (1 / 8 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A, A, A, A] +
    (1 / 6 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A, A, A, C] +
    (1 / 2 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A, A, B, B] =
      3 / 8 := by
  rw [greedyBumpGaussianJet_wick_A4, greedyBumpGaussianJet_wick_A3C,
    greedyBumpGaussianJet_wick_A2B2]
  norm_num

/-- Fifth-order curvature correction `E[δ₅]=25/16`. -/
theorem greedyBumpGaussianLocation_biasCoefficient_five :
    (5 / 48 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A,A,A,A,A,A] +
    (1 / 4 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A,A,A,A,A,C] +
    (1 / 120 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A,A,A,A,A,E5] +
    (5 / 4 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A,A,A,A,B,B] +
    (1 / 6 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A,A,A,A,B,D4] +
    (1 / 8 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A,A,A,A,C,C] +
    wickMoment greedyBumpGaussianJetContraction [A,A,A,B,B,C] +
    (1 / 2 : ℝ) * wickMoment greedyBumpGaussianJetContraction [A,A,B,B,B,B] =
      25 / 16 := by
  rw [greedyBumpGaussianJet_wick_A6, greedyBumpGaussianJet_wick_A5C,
    greedyBumpGaussianJet_wick_A5E5, greedyBumpGaussianJet_wick_A4B2,
    greedyBumpGaussianJet_wick_A4BD4, greedyBumpGaussianJet_wick_A4C2,
    greedyBumpGaussianJet_wick_A3B2C, greedyBumpGaussianJet_wick_A2B4]
  norm_num

/-- First localization-radius correction is `3/Q⁴`. -/
theorem greedyBumpGaussianLocation_localizationCoefficient_four :
    wickMoment greedyBumpGaussianJetContraction [A, A, B, B] +
      wickMoment greedyBumpGaussianJetContraction [A, A, A, A] +
      wickMoment greedyBumpGaussianJetContraction [A, A, A, C] +
      2 * wickMoment greedyBumpGaussianJetContraction [A, A, B, B] = 3 := by
  rw [greedyBumpGaussianJet_wick_A2B2, greedyBumpGaussianJet_wick_A4,
    greedyBumpGaussianJet_wick_A3C]
  norm_num

/-- First profile-likelihood correction is `1/(2Q²)`. -/
theorem greedyBumpGaussianLocation_profileGainCoefficient_two :
    2 * (3 / 8 : ℝ) +
      2 * ((1 / 2 : ℝ) *
        wickMoment greedyBumpGaussianJetContraction [X, A, A, B]) +
      (1 / 4 : ℝ) *
        wickMoment greedyBumpGaussianJetContraction [A, A, A, A] = 1 / 2 := by
  rw [greedyBumpGaussianJet_wick_XA2B, greedyBumpGaussianJet_wick_A4]
  norm_num

end GaloisForLFunctions.HTGeometry
