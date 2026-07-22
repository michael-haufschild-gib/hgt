import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureTangentLoewnerLimit

/-!
# Strict dyadic innovation law for continuous Möbius apertures

The dyadic aperture-refinement increment was realized as an `ell²` Gram and hence shown positive
semidefinite.  Its explicit depth feature is a nonzero column weight times a geometric sequence.
For every finite packet of distinct positive apertures, the first `N` depth coordinates form a
weighted Vandermonde matrix.  They have full rank already at one prime, so both the one-prime and
completed all-prime innovation Grams are positive definite with positive determinant.
-/

open scoped BigOperators
open Matrix

namespace RHTower

noncomputable section

/-- First `N` depth coordinates of one prime's dyadic innovation feature packet. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun e j => xiMobiusPrimeContinuousApertureDyadicInnovationFeature
    h (aperture j) p e

/-- The finite innovation sampling matrix is a diagonally weighted Vandermonde on squared disk
nodes. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_factorization
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix h aperture p =
      (Matrix.vandermonde (fun j =>
        xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p ^ 2))ᵀ *
      Matrix.diagonal (fun j =>
        (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) *
        (1 - xiMobiusContinuousApertureDiskNode
          ((h / 2) * aperture j) p) ^ 2) := by
  classical
  ext e j
  rw [Matrix.mul_diagonal]
  simp [xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature,
    Matrix.vandermonde]
  ring

/-- Distinct positive apertures make the finite innovation sampling matrix invertible. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_det_ne_zero
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j)
    (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix
      h aperture p).det ≠ 0 := by
  let r : Fin N → ℝ := fun j =>
    xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p
  let z : Fin N → ℝ := fun j => r j ^ 2
  let d : Fin N → ℝ := fun j =>
    (xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) * (1 - r j) ^ 2
  have hrpos : ∀ j, 0 < r j := fun j =>
    xiMobiusContinuousApertureDiskNode_pos _ p
  have hr : Function.Injective r := by
    apply (xiMobiusContinuousApertureDiskNode_injective p).comp
    intro i j hij
    have hh2 : h / 2 ≠ 0 := (half_pos hh).ne'
    exact haperture (mul_left_cancel₀ hh2 hij)
  have hz : Function.Injective z := by
    intro i j hij
    apply hr
    dsimp [z] at hij
    nlinarith [hrpos i, hrpos j]
  have hd : ∀ j, d j ≠ 0 := by
    intro j
    have hq : 0 < xiTransversePrimeApertureDiskNode 1 p :=
      xiTransversePrimeApertureDiskNode_pos 1 p
    have hr1 : r j < 1 :=
      xiMobiusContinuousApertureDiskNode_lt_one
        (mul_pos (half_pos hh) (hpos j)) p
    dsimp only [d]
    positivity
  rw [xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hz
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun j _ => hd j

/-- The genuine one-prime `ell²` innovation features are linearly independent on every finite
injective positive aperture packet. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_linearIndependent
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j)
    (p : Nat.Primes) :
    LinearIndependent ℝ (fun j =>
      xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp
        h (aperture j) p hh (hpos j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let A := xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix h aperture p
  have hAc : A.mulVec c = 0 := by
    funext e
    have he := congrArg
      (fun v : lp (fun _ : ℕ => ℝ) 2 => (v : ℕ → ℝ) (e : ℕ)) hc
    simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, lp.coeFn_zero, Pi.zero_apply] at he
    simpa [A, xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix,
      Matrix.mulVec, dotProduct, mul_comm] using he
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_det_ne_zero
      hh haperture hpos p
  have hc0 : c = 0 :=
    (Matrix.mulVec_injective_of_isUnit hunit)
      (hAc.trans (Matrix.mulVec_zero A).symm)
  exact fun i => congrFun hc0 i

/-- One prime already makes the dyadic innovation Gram positive definite. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationGram_posDef
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j)
    (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureDyadicInnovationGram h aperture p).PosDef := by
  have hgram :
      xiMobiusPrimeContinuousApertureDyadicInnovationGram h aperture p =
        Matrix.gram ℝ (fun i =>
          xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp
            h (aperture i) p hh (hpos i)) := by
    ext i j
    simp only [xiMobiusPrimeContinuousApertureDyadicInnovationGram, Matrix.gram]
    simpa only [Matrix.of_apply] using
      (inner_xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_eq
        hh (hpos i) (hpos j) p).symm
  rw [hgram]
  exact Matrix.posDef_gram_of_linearIndependent
    (xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_linearIndependent
      hh haperture hpos p)

/-- The completed direct-sum innovation features remain linearly independent because restriction
to the prime `2` recovers a linearly independent one-prime packet. -/
theorem xiMobiusContinuousApertureDyadicInnovationFeatureLp_linearIndependent
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j) :
    LinearIndependent ℝ (fun j =>
      xiMobiusContinuousApertureDyadicInnovationFeatureLp
        h (aperture j) hh (hpos j)) := by
  classical
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hprime :=
    xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_linearIndependent
      hh haperture hpos p
  rw [Fintype.linearIndependent_iff] at hprime ⊢
  intro c hc
  apply hprime c
  apply Subtype.ext
  funext e
  have he := congrArg
    (fun v : lp (fun _ : Nat.Primes × ℕ => ℝ) 2 =>
      (v : Nat.Primes × ℕ → ℝ) (p, e)) hc
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, lp.coeFn_zero, Pi.zero_apply] at he ⊢
  simpa [xiMobiusContinuousApertureDyadicInnovationFeatureLp,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp] using he

/-- **Universal strict dyadic innovation law.**  The completed all-prime refinement increment is
positive definite on every finite packet of distinct positive apertures. -/
theorem xiMobiusContinuousApertureDyadicInnovationGram_posDef
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j) :
    (xiMobiusContinuousApertureDyadicInnovationGram h aperture).PosDef := by
  have hgram : xiMobiusContinuousApertureDyadicInnovationGram h aperture =
      Matrix.gram ℝ (fun i =>
        xiMobiusContinuousApertureDyadicInnovationFeatureLp
          h (aperture i) hh (hpos i)) := by
    ext i j
    simp only [xiMobiusContinuousApertureDyadicInnovationGram, Matrix.gram]
    simpa only [Matrix.of_apply] using
      (inner_xiMobiusContinuousApertureDyadicInnovationFeatureLp_eq
        hh (hpos i) (hpos j)).symm
  rw [hgram]
  exact Matrix.posDef_gram_of_linearIndependent
    (xiMobiusContinuousApertureDyadicInnovationFeatureLp_linearIndependent
      hh haperture hpos)

/-- Determinant form of strict dyadic refinement. -/
theorem det_xiMobiusContinuousApertureDyadicInnovationGram_pos
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j) :
    0 < (xiMobiusContinuousApertureDyadicInnovationGram h aperture).det :=
  (xiMobiusContinuousApertureDyadicInnovationGram_posDef
    hh haperture hpos).det_pos

end

end RHTower
