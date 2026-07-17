import GaloisForLFunctions.RHTower.VonMangoldtGammaFactorialNormalizationNoGo
import GaloisForLFunctions.RHTower.CompletedPrimeGammaMomentFarRightAsymptotic
import GaloisForLFunctions.RHTower.GammaRealConnectionSpectralHankel

/-!
# Exact prime--Gamma--polar resolution of the completed odd moment

The factorially normalized Euler moment is not positive semidefinite by itself.  The completed
source does not perform that normalization in isolation: the logarithmic derivative of `xi`
canonically couples the Euler leg to the half-argument Gamma leg and the rational polar pair.

This file resolves that coupling exactly on the real half-plane `x > 1`.  The three real source
terms are

* the factorially normalized cofinal von Mangoldt--Gamma moment;
* the positive Gamma/Bose spectral moment at the half-shift `x / 2`;
* the two polar atoms at inverse-square nodes `x⁻²` and `(x-1)⁻²`, with negative incidence.

Their signed sum is precisely the analytic odd logarithmic-derivative moment of `xi`.  Entrywise,
the corresponding completed Hankel matrix is a diagonal sign congruence of the resolved real
Hankel matrix.  Thus the correction forced by completion is not an ad hoc repair of the Euler
normalization: it is the unique decomposition already present in `xi'/xi`.
-/

open scoped BigOperators Matrix
open Complex Filter Topology LSeries

namespace RHTower

noncomputable section

/-- The cofinal Euler source after the odd factorial normalization used by the completed trace. -/
def completedPrimeFactorialMoment (x : ℝ) (k : ℕ) : ℝ :=
  infiniteVonMangoldtGammaRawMoment (x - 1) (2 * k + 1) /
    ((2 * k + 1).factorial : ℝ)

/-- The half-argument Gamma leg as a positive even Gamma/Bose spectral moment. -/
def completedGammaSpectralMoment (x : ℝ) (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (2 * k + 2) *
    HTGeometry.gammaBoseMoment (x / 2) (2 * k)

/-- The completed rational leg as the moment sequence of the two inverse-square polar atoms. -/
def completedPolarPairMoment (x : ℝ) (k : ℕ) : ℝ :=
  (x ^ (2 * k + 2))⁻¹ + ((x - 1) ^ (2 * k + 2))⁻¹

/-- Canonical real source colligation: prime plus Gamma minus the polar pair. -/
def completedPrimeGammaResolvedMoment (x : ℝ) (k : ℕ) : ℝ :=
  completedPrimeFactorialMoment x k +
    completedGammaSpectralMoment x k - completedPolarPairMoment x k

/-- Exact source resolution of every completed odd logarithmic-derivative moment on `x > 1`. -/
theorem completedOddLogDerivMoment_ofReal_eq_resolved
    {x : ℝ} (hx : 1 < x) (k : ℕ) :
    completedOddLogDerivMoment (x : ℂ) k =
      (((-1 : ℝ) ^ k * completedPrimeGammaResolvedMoment x k : ℝ) : ℂ) := by
  let j : ℕ := 2 * k + 1
  have hj : 0 < j := by dsimp [j]; omega
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx))
  have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hx)
  have hs : 1 < (x : ℂ).re := by simpa using hx
  have heuler :
      LSeries (LSeries.logMul^[j]
          (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))) (x : ℂ) =
        (infiniteVonMangoldtGammaRawMoment (x - 1) j : ℂ) := by
    symm
    simpa [vonMangoldtLogCoeff, j] using
      (infiniteVonMangoldtGammaRawMoment_ofReal_eq_weightedLSeries
        (x := x - 1) (by linarith) j)
  have hgamma :
      iteratedDeriv j Complex.digamma ((x : ℂ) / 2) =
        (j.factorial : ℂ) *
          (HTGeometry.gammaBoseMoment (x / 2) (2 * k) : ℂ) := by
    have h := HTGeometry.iteratedDeriv_digamma_eq_gammaBoseMoment
      (a := x / 2) (by linarith) (2 * k)
    have hsign : (-1 : ℂ) ^ (2 * k + 2) = 1 := by
      rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
      norm_num
    rw [hsign, one_mul] at h
    simpa [j] using h
  rw [completedOddLogDerivMoment,
    show logDeriv xi = xiLogDeriv by
      funext s
      rw [logDeriv_apply, xiLogDeriv],
    iteratedDeriv_xiLogDeriv_split j hs,
    iteratedDeriv_completedRationalLeg j hj hx0 hx1,
    hgamma, heuler]
  have hfac : ((j.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hjodd : (-1 : ℂ) ^ j = -1 := by
    rw [show j = 2 * k + 1 by dsimp [j], pow_add, pow_mul]
    norm_num
  have hjeven : (-1 : ℂ) ^ (j + 1) = 1 := by
    rw [show j + 1 = 2 * (k + 1) by dsimp [j]; omega, pow_mul]
    norm_num
  have hnormalize (sign fac polar scale gamma prime : ℂ) (hfac0 : fac ≠ 0) :
      sign * (-fac * polar + scale * (fac * gamma) + prime) / fac =
        sign * (prime / fac + scale * gamma - polar) := by
    field_simp [hfac0]
    ring
  rw [hjodd, hjeven]
  rw [show 2 * k + 1 = j by rfl]
  simp only [one_mul, neg_one_mul]
  rw [hnormalize _ _ _ _ _ _ hfac]
  push_cast
  norm_num [completedPrimeGammaResolvedMoment, completedPrimeFactorialMoment,
    completedGammaSpectralMoment, completedPolarPairMoment, j]

/-- The real Hankel matrix of the canonically resolved completed source. -/
def completedPrimeGammaResolvedHankelMatrix (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  HTGeometry.momentHankelMatrix (completedPrimeGammaResolvedMoment x) n

/-- Hankel matrix of the factorially normalized cofinal Euler leg. -/
def completedPrimeFactorialHankelMatrix (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  HTGeometry.momentHankelMatrix (completedPrimeFactorialMoment x) n

/-- Hankel matrix of the Gamma/Bose completion leg. -/
def completedGammaSpectralHankelMatrix (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  HTGeometry.momentHankelMatrix (completedGammaSpectralMoment x) n

/-- The Gamma completion leg remains strictly positive definite after the forced even-order and
half-argument rescaling. -/
theorem completedGammaSpectralHankelMatrix_posDef
    {x : ℝ} (hx : 1 < x) (n : ℕ) :
    (completedGammaSpectralHankelMatrix n x).PosDef := by
  classical
  let N : ℕ := 2 * n + 1
  let e : Fin n → Fin N := fun i ↦ ⟨2 * (i : ℕ), by
    dsimp [N]
    omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp [e] at hval
    omega
  let H : Matrix (Fin N) (Fin N) ℝ :=
    HTGeometry.momentHankelMatrix (HTGeometry.gammaBoseMoment (x / 2)) N
  have hH : H.PosDef := by
    exact HTGeometry.gammaBoseHankel_posDef (by linarith) N
  have hsub : (H.submatrix e e).PosDef := hH.submatrix he
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal fun i ↦ (1 / 2 : ℝ) ^ (2 * (i : ℕ) + 1)
  have hDpos : D.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    positivity
  have hcong := hsub.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hDpos.isUnit)
  convert hcong using 1
  ext i j
  simp only [completedGammaSpectralHankelMatrix,
    HTGeometry.momentHankelMatrix, completedGammaSpectralMoment]
  simp [H, D, e, HTGeometry.momentHankelMatrix,
    Matrix.mul_apply, Matrix.diagonal_apply]
  rw [show 2 * ((i : ℕ) + (j : ℕ)) + 2 =
      (2 * (i : ℕ) + 1) + (2 * (j : ℕ) + 1) by omega, pow_add]
  ring

/-- The two inverse-square nodes carried by the rational polar pair. -/
def completedPolarPairNode (x : ℝ) (p : Fin 2) : ℝ :=
  if (p : ℕ) = 0 then (x ^ 2)⁻¹ else ((x - 1) ^ 2)⁻¹

/-- The polar moment is exactly the sum of the two node powers, each node also serving as its
positive atomic weight. -/
theorem completedPolarPairMoment_eq_twoAtomMoment (x : ℝ) (k : ℕ) :
    completedPolarPairMoment x k =
      completedPolarPairNode x 0 ^ (k + 1) +
        completedPolarPairNode x 1 ^ (k + 1) := by
  rw [completedPolarPairMoment, completedPolarPairNode, completedPolarPairNode]
  norm_num
  rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul, pow_mul]

/-- Hankel matrix of the rational polar pair. -/
def completedPolarPairHankelMatrix (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  HTGeometry.momentHankelMatrix (completedPolarPairMoment x) n

/-- Literal two-atom Gram realizing the polar Hankel matrix. -/
def completedPolarPairRawGram (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  finiteExponentialGammaRawGram (completedPolarPairNode x)
    (completedPolarPairNode x) 0 (fun i ↦ (i : ℕ))

/-- The polar Hankel matrix is the literal two-atom source Gram. -/
theorem completedPolarPairHankelMatrix_eq_rawGram (n : ℕ) (x : ℝ) :
    completedPolarPairHankelMatrix n x = completedPolarPairRawGram n x := by
  ext i j
  rw [completedPolarPairHankelMatrix, HTGeometry.momentHankelMatrix,
    completedPolarPairRawGram,
    finiteExponentialGammaRawGram_apply]
  · rw [finiteExponentialGammaRawMoment, Fin.sum_univ_two]
    rw [completedPolarPairMoment_eq_twoAtomMoment]
    norm_num
    ring
  · intro p
    dsimp [completedPolarPairNode]
    split <;> positivity

/-- The rational polar pair is positive semidefinite before its forced negative incidence in the
completed source. -/
theorem completedPolarPairHankelMatrix_posSemidef (n : ℕ) (x : ℝ) :
    (completedPolarPairHankelMatrix n x).PosSemidef := by
  rw [completedPolarPairHankelMatrix_eq_rawGram]
  exact finiteExponentialGammaRawGram_posSemidef _ _ _ _

/-- Exact matrix incidence of the three canonically completed source legs. -/
theorem completedPrimeGammaResolvedHankelMatrix_eq_incidence
    (n : ℕ) (x : ℝ) :
    completedPrimeGammaResolvedHankelMatrix n x =
      completedPrimeFactorialHankelMatrix n x +
        completedGammaSpectralHankelMatrix n x -
          completedPolarPairHankelMatrix n x := by
  ext i j
  rfl

/-- Alternating diagonal implementing the harmless parity sign of the analytic odd jet. -/
def completedAlternatingSignMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i ↦ (-1 : ℝ) ^ (i : ℕ)

/-- The alternating diagonal sign congruence of the resolved real Hankel matrix. -/
def completedPrimeGammaSignedHankelMatrix (n : ℕ) (x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (-1 : ℝ) ^ (i : ℕ) *
    completedPrimeGammaResolvedHankelMatrix n x i j * (-1 : ℝ) ^ (j : ℕ)

/-- Literal matrix-congruence form of the alternating sign transform. -/
theorem completedPrimeGammaSignedHankelMatrix_eq_congruence
    (n : ℕ) (x : ℝ) :
    completedPrimeGammaSignedHankelMatrix n x =
      (completedAlternatingSignMatrix n)ᴴ *
        completedPrimeGammaResolvedHankelMatrix n x *
          completedAlternatingSignMatrix n := by
  classical
  ext i j
  simp [completedPrimeGammaSignedHankelMatrix, completedAlternatingSignMatrix,
    Matrix.mul_apply, Matrix.diagonal_apply]

/-- Applying the alternating sign congruence twice recovers the resolved matrix. -/
theorem completedPrimeGammaResolvedHankelMatrix_eq_signedCongruence
    (n : ℕ) (x : ℝ) :
    completedPrimeGammaResolvedHankelMatrix n x =
      (completedAlternatingSignMatrix n)ᴴ *
        completedPrimeGammaSignedHankelMatrix n x *
          completedAlternatingSignMatrix n := by
  classical
  ext i j
  simp [completedPrimeGammaSignedHankelMatrix, completedAlternatingSignMatrix,
    Matrix.mul_apply, Matrix.diagonal_apply]
  have hi : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
    rw [← pow_add]
    norm_num
  have hj : (-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← pow_add]
    norm_num
  calc
    completedPrimeGammaResolvedHankelMatrix n x i j =
        ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) *
          completedPrimeGammaResolvedHankelMatrix n x i j *
            ((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) := by
              rw [hi, hj]
              ring
    _ = _ := by ring

/-- Alternating parity signs neither create nor destroy positive semidefiniteness. -/
theorem completedPrimeGammaSignedHankelMatrix_posSemidef_iff
    (n : ℕ) (x : ℝ) :
    (completedPrimeGammaSignedHankelMatrix n x).PosSemidef ↔
      (completedPrimeGammaResolvedHankelMatrix n x).PosSemidef := by
  constructor
  · intro h
    rw [completedPrimeGammaResolvedHankelMatrix_eq_signedCongruence]
    exact h.conjTranspose_mul_mul_same _
  · intro h
    rw [completedPrimeGammaSignedHankelMatrix_eq_congruence]
    exact h.conjTranspose_mul_mul_same _

/-- The analytic completed Hankel matrix is exactly the complexification of the resolved signed
real Hankel matrix. -/
theorem completedOddLogDerivHankelMatrix_ofReal_eq_resolvedSignCongruence
    {x : ℝ} (hx : 1 < x) (n : ℕ) :
    completedOddLogDerivHankelMatrix n (x : ℂ) =
      (completedPrimeGammaSignedHankelMatrix n x).map (algebraMap ℝ ℂ) := by
  ext i j
  rw [completedOddLogDerivHankelMatrix,
    completedOddLogDerivMoment_ofReal_eq_resolved hx]
  simp only [completedPrimeGammaSignedHankelMatrix,
    completedPrimeGammaResolvedHankelMatrix, HTGeometry.momentHankelMatrix,
    Matrix.map_apply, map_mul, map_pow, map_neg, map_one]
  rw [pow_add]
  push_cast
  ring_nf
  norm_num

end

end RHTower
