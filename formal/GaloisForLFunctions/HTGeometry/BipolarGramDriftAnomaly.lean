import GaloisForLFunctions.HilbertMetric.FanoCommutator

/-!
# Bipolar Gram drift anomaly

Two normalized source polarizations with real cross-Gram coefficient `r` have Gram matrix
`[[1, r], [r, 1]]`.  A reflection-odd real drift has diagonal matrix `diag(a, -a)`.
Although the drift is self-adjoint in the orthogonal direct-sum metric, it is self-adjoint for
the source Gram metric only when its commutator with that Gram vanishes.

This file proves the exact local anomaly and its Hilbert--Schmidt energy.  For the projective
prime producer/reporter pair, `r = -1 / p`, so every nonzero reflected drift has local energy
`8 * a^2 / p^2`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix
open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Gram matrix of two normalized real source polarizations with cross coefficient `r`. -/
def bipolarSourceGram (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, r; r, 1]

/-- Reflection-odd centered drift: the two polarizations carry opposite real weights. -/
def reflectionOddDrift (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 0; 0, -a]

/-- Failure of reflection-odd drift to be self-adjoint for the source Gram metric. -/
def bipolarGramDriftAnomaly (a r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  reflectionOddDrift a * bipolarSourceGram r -
    bipolarSourceGram r * reflectionOddDrift a

/-- Exact two-channel form of the source-Gram adjoint anomaly. -/
theorem bipolarGramDriftAnomaly_eq (a r : ℝ) :
    bipolarGramDriftAnomaly a r =
      !![0, 2 * a * r; -(2 * a * r), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bipolarGramDriftAnomaly, reflectionOddDrift, bipolarSourceGram] <;>
    ring

/-- A nonorthogonal source seam makes Gram-adjointability equivalent to zero drift. -/
theorem bipolarGramDriftAnomaly_eq_zero_iff
    {a r : ℝ} (hr : r ≠ 0) :
    bipolarGramDriftAnomaly a r = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h01 := congrFun₂ h 0 1
    simp [bipolarGramDriftAnomaly_eq] at h01
    exact h01.resolve_right hr
  · rintro rfl
    rw [bipolarGramDriftAnomaly_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Exact squared Hilbert--Schmidt energy of the local source-Gram adjoint anomaly. -/
theorem matrixHilbertSchmidtEnergy_bipolarGramDriftAnomaly
    (a r : ℝ) :
    matrixHilbertSchmidtEnergy (bipolarGramDriftAnomaly a r) =
      8 * a ^ 2 * r ^ 2 := by
  rw [bipolarGramDriftAnomaly_eq]
  simp [matrixHilbertSchmidtEnergy, Fin.sum_univ_two]
  ring

/-- At projective-prime cross coefficient `-1/p`, anomaly energy is `8 a²/p²`. -/
theorem matrixHilbertSchmidtEnergy_projectivePrimeBipolarGramDriftAnomaly
    (a p : ℝ) (hp : p ≠ 0) :
    matrixHilbertSchmidtEnergy
        (bipolarGramDriftAnomaly a (-1 / p)) =
      8 * a ^ 2 / p ^ 2 := by
  rw [matrixHilbertSchmidtEnergy_bipolarGramDriftAnomaly]
  field_simp

/-- Every nonzero projective-prime seam detects zero drift exactly. -/
theorem projectivePrime_bipolarGramDriftAnomaly_eq_zero_iff
    {a p : ℝ} (hp : p ≠ 0) :
    bipolarGramDriftAnomaly a (-1 / p) = 0 ↔ a = 0 :=
  bipolarGramDriftAnomaly_eq_zero_iff (by simp [hp])

end

end GaloisForLFunctions.HTGeometry
