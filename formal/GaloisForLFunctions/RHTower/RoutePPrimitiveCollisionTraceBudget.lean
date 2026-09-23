import GaloisForLFunctions.RHTower.RoutePCriticalCollisionSchurTrace
import GaloisForLFunctions.RHTower.XiWardCubicLogMomentEulerSource

/-!
# Route P: primitive Euler collision-trace budget

P-G173 proves that the full critical ordinate-collision kernel is positive and has diagonal
`115 / (864 a^(3 : ℕ))`.  This module places that complete, non-diagonal kernel on the literal primitive
Euler carrier.  Its radial parameter is the prime-power log frequency and its congruence weight is
the positive square root of the resolved von Mangoldt mass.

The resulting matrix is positive semidefinite for arbitrary collision frequencies.  Its diagonal
is exactly the already-proved cubic Euler source weight, not merely a majorant.  Consequently every
finite packet of distinct primitive cells has trace bounded by one global summable budget,
independent of packet size and all collision frequencies.  Thus critical clustering is compatible
with the complete cubic Euler source.  This is a source trace-class envelope, not the still-missing
completed source-to-zero transport theorem.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Diagonal congruence by the positive square root of resolved von Mangoldt mass. -/
def routePPrimitiveCollisionScalingMatrix {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i =>
    finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (pe i))

/-- Full critical collision kernel on a finite primitive Euler packet. -/
def routePPrimitiveCollisionCubicKernelMatrix {N : ℕ}
    (R : ℝ) (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  routePPrimitiveCollisionScalingMatrix pe *
    routePCollisionCubicKernelMatrix R
      (fun i => xiGammaEulerPrimitiveLogFrequency (pe i)) kappa *
    (routePPrimitiveCollisionScalingMatrix pe)ᴴ

/-- Arbitrary prime-depth collision packets remain positive, with no frequency-gap hypothesis. -/
theorem routePPrimitiveCollisionCubicKernelMatrix_posSemidef
    {N : ℕ} {R : ℝ} {pe : Fin N → Nat.Primes × ℕ} {kappa : Fin N → ℝ}
    (hR : 0 < R) :
    (routePPrimitiveCollisionCubicKernelMatrix R pe kappa).PosSemidef := by
  exact (routePCollisionCubicKernelMatrix_posSemidef hR
    (fun i => xiGammaEulerPrimitiveLogFrequency_pos (pe i))).mul_mul_conjTranspose_same
      (routePPrimitiveCollisionScalingMatrix pe)

/-- Entrywise form of the primitive collision congruence. -/
theorem routePPrimitiveCollisionCubicKernelMatrix_apply
    {N : ℕ} (R : ℝ) (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) :
    routePPrimitiveCollisionCubicKernelMatrix R pe kappa i j =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (pe i)) *
        routePCollisionCubicKernel R
          (xiGammaEulerPrimitiveLogFrequency (pe i))
          (xiGammaEulerPrimitiveLogFrequency (pe j))
          (kappa j - kappa i) *
        star (finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat (pe j))) := by
  simp [routePPrimitiveCollisionCubicKernelMatrix,
    routePPrimitiveCollisionScalingMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, routePCollisionCubicKernelMatrix]

/-- Exact seam: collision diagonal times von Mangoldt mass is the existing cubic Euler weight. -/
theorem routePPrimitiveCollisionCubicKernelMatrix_diagonal
    {N : ℕ} {R : ℝ} (hR : 0 < R)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (i : Fin N) :
    routePPrimitiveCollisionCubicKernelMatrix R pe kappa i i =
      (xiGammaEulerPrimitiveCubicLogMomentWeight (pe i) : ℂ) := by
  rw [routePPrimitiveCollisionCubicKernelMatrix_apply]
  rw [sub_self, routePCollisionCubicKernel_diagonal hR
    (xiGammaEulerPrimitiveLogFrequency_pos (pe i))]
  rw [← xiGammaEulerPrimitiveCubicLogMomentDiagonal_eq_weight 0 (pe i)]
  rw [xiGammaEulerPrimitiveCubicLogMomentDiagonal,
    xiGammaEulerPrimitiveBalancedReflectionCoeff_eq]
  rw [cubicLogMomentHellingerHorizontalKernel_self
    (xiGammaEulerPrimitiveLogFrequency_pos (pe i))]
  have hn : xiGammaEulerValuationNat (pe i) ≠ 0 := by
    unfold xiGammaEulerValuationNat
    exact pow_ne_zero _ (pe i).1.property.ne_zero
  rw [← finiteVonMangoldtDepthOneAmplitude_sq hn]
  simp [finiteVonMangoldtDepthOneAmplitude]
  ring

/-- Exact trace of every finite primitive collision packet. -/
theorem trace_routePPrimitiveCollisionCubicKernelMatrix
    {N : ℕ} {R : ℝ} (hR : 0 < R)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveCollisionCubicKernelMatrix R pe kappa).trace =
      ∑ i : Fin N, (xiGammaEulerPrimitiveCubicLogMomentWeight (pe i) : ℂ) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact routePPrimitiveCollisionCubicKernelMatrix_diagonal hR pe kappa i

/-- Total primitive Euler collision-trace budget. -/
def routePPrimitiveCollisionCubicTraceBudget : ℝ :=
  ∑' pe : Nat.Primes × ℕ, xiGammaEulerPrimitiveCubicLogMomentWeight pe

theorem routePPrimitiveCollisionCubicTraceBudget_nonneg :
    0 ≤ routePPrimitiveCollisionCubicTraceBudget := by
  exact tsum_nonneg xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg

/-- Every finite packet of distinct primitive Euler cells has trace bounded by one global,
frequency-independent summable budget. -/
theorem re_trace_routePPrimitiveCollisionCubicKernelMatrix_le_budget
    {N : ℕ} {R : ℝ} (hR : 0 < R)
    (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (routePPrimitiveCollisionCubicKernelMatrix R pe kappa).trace.re ≤
      routePPrimitiveCollisionCubicTraceBudget := by
  rw [trace_routePPrimitiveCollisionCubicKernelMatrix hR pe kappa]
  have hsub :=
    (summable_xiGammaEulerPrimitiveCubicLogMomentWeight.comp_injective hpe).tsum_le_tsum_of_inj
      pe hpe
      (fun q hq => xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg q)
      (fun i => le_rfl)
      summable_xiGammaEulerPrimitiveCubicLogMomentWeight
  simpa [routePPrimitiveCollisionCubicTraceBudget] using hsub

end

end RHTower
