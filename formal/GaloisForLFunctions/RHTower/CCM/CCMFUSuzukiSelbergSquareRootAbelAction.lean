import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSelbergRemainderBridge
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainder

/-!
# Square-root Abel action of the CCM-FU Suzuki source

The event-weighted Suzuki curvature is not merely asymptotic to a Selberg-remainder current.
Finite summation by parts gives a coefficient-faithful three-term law: terminal normalized
Chebyshev error, an interior half-order Abel action, and the already-controlled archimedean
remainder.  The terminal and interior terms occur with opposite signs, so estimating either one
separately destroys the cancellation required by CCM-FU.

This module also rationalizes the Abel kernel exactly as
`1 / (sqrt (k+1) + sqrt k)`.  Thus the surviving arithmetic action lives at half order, not at the
harmonic order controlled by the existing Selberg harmonic estimate.  Every statement below is
finite and unconditional.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Interior half-order Abel action of the discrete Selberg remainder. -/
def suzukiCheckpointSelbergSquareRootAbelMoment (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (N + 1),
    (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiRemainder k

/-- Exact rationalization of the square-root Abel kernel. -/
theorem sqrt_nat_succ_sub_eq_inv_add (k : ℕ) :
    Real.sqrt (k + 1 : ℕ) - Real.sqrt k =
      (Real.sqrt (k + 1 : ℕ) + Real.sqrt k)⁻¹ := by
  have hkp1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hden : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ) := by
    positivity
  rw [inv_eq_one_div]
  apply (eq_div_iff hden.ne').2
  have hs1 := Real.sq_sqrt hkp1.le
  have hs0 := Real.sq_sqrt (show (0 : ℝ) ≤ k by positivity)
  push_cast at hs1 hs0 ⊢
  nlinarith

/-- The interior action is literally the Selberg remainder against a positive half-order
kernel. -/
theorem suzukiCheckpointSelbergSquareRootAbelMoment_eq_rationalized (N : ℕ) :
    suzukiCheckpointSelbergSquareRootAbelMoment N =
      ∑ k ∈ Finset.Ico 3 (N + 1),
        psiRemainder k /
          (Real.sqrt (k + 1 : ℕ) + Real.sqrt k) := by
  rw [suzukiCheckpointSelbergSquareRootAbelMoment]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sqrt_nat_succ_sub_eq_inv_add]
  ring

private theorem natCast_div_sqrt_eq_sqrt {k : ℕ} (hk : 0 < k) :
    (k : ℝ) / Real.sqrt k = Real.sqrt k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  apply (div_eq_iff hsqrt.ne').2
  rw [← pow_two]
  exact (Real.sq_sqrt hkR.le).symm

private theorem natCast_mul_neg_div_sqrt_eq {k : ℕ} (hk : 0 < k) (x : ℝ) :
    (k : ℝ) * (-x / Real.sqrt k) = -Real.sqrt k * x := by
  calc
    (k : ℝ) * (-x / Real.sqrt k) = -((k : ℝ) / Real.sqrt k) * x := by ring
    _ = -Real.sqrt k * x := by rw [natCast_div_sqrt_eq_sqrt hk]

/-- Exact finite Abel law for the event-weighted Selberg increment current.  Terminal remainder
and interior Abel action retain their relative sign. -/
theorem weightedSelbergIncrement_eq_boundary_add_squareRootAbel
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointWeightedSelbergIncrementPrefix N =
      Real.sqrt 3 * psiRemainder 2 -
        Real.sqrt (N + 1 : ℕ) * psiRemainder (N + 1) +
        suzukiCheckpointSelbergSquareRootAbelMoment N := by
  induction N, hN using Nat.le_induction with
  | base =>
      have h34 : Finset.Ico 3 4 = {3} := by
        ext k
        simp
      have h33 : Finset.Ico 3 3 = ∅ := by simp
      rw [suzukiCheckpointWeightedSelbergIncrementPrefix,
        suzukiCheckpointSelbergSquareRootAbelMoment, h34, h33]
      simp only [sum_singleton, sum_empty, add_zero, Nat.reduceAdd, Nat.cast_ofNat]
      have hterm : (3 : ℝ) * suzukiCheckpointSelbergIncrementCell 3 =
          -Real.sqrt 3 * (psiRemainder 3 - psiRemainder 2) := by
        unfold suzukiCheckpointSelbergIncrementCell
        simpa only [Nat.cast_ofNat, Nat.reduceSub] using
          natCast_mul_neg_div_sqrt_eq (k := 3)
            (by norm_num : 0 < 3) (psiRemainder 3 - psiRemainder 2)
      rw [hterm]
      ring
  | succ N hN ih =>
      rw [suzukiCheckpointWeightedSelbergIncrementPrefix,
        show N + 1 + 2 = (N + 2) + 1 by omega,
        Finset.sum_Ico_succ_top (by omega : 3 ≤ N + 2)]
      rw [suzukiCheckpointWeightedSelbergIncrementPrefix] at ih
      rw [ih]
      unfold suzukiCheckpointSelbergSquareRootAbelMoment
      rw [show N + 1 + 1 = (N + 1) + 1 by omega,
        Finset.sum_Ico_succ_top (by omega : 3 ≤ N + 1)]
      have hterm : ((N + 2 : ℕ) : ℝ) *
          suzukiCheckpointSelbergIncrementCell (N + 2) =
          -Real.sqrt (N + 2 : ℕ) *
            (psiRemainder (N + 2) - psiRemainder (N + 1)) := by
        unfold suzukiCheckpointSelbergIncrementCell
        rw [show N + 2 - 1 = N + 1 by omega,
          natCast_mul_neg_div_sqrt_eq (by omega : 0 < N + 2)]
      rw [show N + 1 + 1 = N + 2 by omega, hterm]
      ring

/-- At every positive integer aperture, normalized completed Chebyshev error is exactly the
square-root-normalized discrete Selberg remainder. -/
theorem normalizedChebyshevError_log_nat_eq_psiRemainder_div_sqrt
    {M : ℕ} (hM : 0 < M) :
    criticalMellinNormalizedChebyshevError (Real.log (M : ℝ)) =
      psiRemainder M / Real.sqrt M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have herr := criticalMellinNormalizedChebyshevError_eq_discrete_add_floor
    (Real.log (M : ℝ))
  rw [Real.exp_log hMR, Nat.floor_natCast] at herr
  simp only [sub_self, mul_zero, add_zero] at herr
  have hexp : Real.exp (-Real.log (M : ℝ) / 2) =
      1 / Real.sqrt (M : ℝ) := by
    have hsqrt : Real.sqrt (M : ℝ) =
        Real.exp (Real.log (M : ℝ) / 2) := by
      symm
      rw [← Real.log_sqrt hMR.le,
        Real.exp_log (Real.sqrt_pos.mpr hMR)]
    rw [hsqrt, one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hexp] at herr
  simpa [div_eq_mul_inv, mul_comm] using herr

/-- Boundary-normalized Abel law.  This is the cancellation-preserving form needed by the
coherent boundary transport: terminal critical error is subtracted before the interior action is
read out. -/
theorem weightedSelbergIncrement_eq_normalizedErrorBoundary_add_squareRootAbel
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointWeightedSelbergIncrementPrefix N =
      Real.sqrt 3 * psiRemainder 2 -
        (N + 1 : ℕ) * criticalMellinNormalizedChebyshevError
          (Real.log ((N + 1 : ℕ) : ℝ)) +
        suzukiCheckpointSelbergSquareRootAbelMoment N := by
  rw [weightedSelbergIncrement_eq_boundary_add_squareRootAbel hN,
    normalizedChebyshevError_log_nat_eq_psiRemainder_div_sqrt
      (by omega : 0 < N + 1)]
  have hcancel := natCast_div_sqrt_eq_sqrt (by omega : 0 < N + 1)
  have hprod : ((N + 1 : ℕ) : ℝ) *
      (psiRemainder (N + 1) / Real.sqrt (N + 1 : ℕ)) =
      Real.sqrt (N + 1 : ℕ) * psiRemainder (N + 1) := by
    calc
      _ = (((N + 1 : ℕ) : ℝ) / Real.sqrt (N + 1 : ℕ)) *
          psiRemainder (N + 1) := by ring
      _ = _ := by rw [hcancel]
  rw [hprod]

/-- Exact CCM-FU/Suzuki source law: literal weighted signed curvature equals terminal normalized
Chebyshev error, interior half-order Selberg action, and the source-free archimedean remainder.
No prime, polar, or Gamma channel has been bounded separately. -/
theorem weightedSignedCurvature_eq_normalizedErrorBoundary_add_squareRootAbel_arch
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N =
      Real.sqrt 3 * psiRemainder 2 -
        (N + 1 : ℕ) * criticalMellinNormalizedChebyshevError
          (Real.log ((N + 1 : ℕ) : ℝ)) +
        suzukiCheckpointSelbergSquareRootAbelMoment N +
        suzukiCheckpointWeightedSelbergArchRemainderPrefix N := by
  rw [weightedSignedCurvaturePrefix_eq_selbergIncrement_add_arch,
    weightedSelbergIncrement_eq_normalizedErrorBoundary_add_squareRootAbel hN]

end RHTower
