import GaloisForLFunctions.HTGeometry.PositiveObserverCovarianceLaw
import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse
import GaloisForLFunctions.RHTower.SuzukiDiagonalResolventInstantiation

/-!
# Positive observer compact-resolvent and escaping-lift law

This file supplies a literal Hilbert-space model for the compact-resolvent and recurrence clauses
of the positive-observer card.  The observed coordinate is period two, while the hidden coordinate
runs through the canonical orthonormal sequence in `ℓ²(ℕ)`.  The positive generator is the closed
inverse of the compact injective harmonic diagonal `diag (1 / (n + 1))`; its hidden eigenvalues are
`n + 1`, so the action escapes to infinity although observation closes exactly.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- Hidden covariance Hilbert space for the explicit observer model. -/
abbrev PositiveObserverHiddenL2 := _root_.RHTower.EllTwo

/-- Canonical hidden coordinate mode. -/
def positiveObserverHiddenMode (n : ℕ) : PositiveObserverHiddenL2 :=
  lp.single 2 n (1 : ℂ)

theorem positiveObserverHiddenMode_norm (n : ℕ) :
    ‖positiveObserverHiddenMode n‖ = 1 := by
  simp [positiveObserverHiddenMode,
    lp.norm_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num)]

/-- Distinct hidden modes stay a fixed positive distance apart. -/
theorem one_le_dist_positiveObserverHiddenMode_of_ne {m n : ℕ} (hmn : m ≠ n) :
    1 ≤ dist (positiveObserverHiddenMode m) (positiveObserverHiddenMode n) := by
  rw [dist_eq_norm]
  have hcoord := lp.norm_apply_le_norm (p := (2 : ENNReal)) (by norm_num)
    (positiveObserverHiddenMode m - positiveObserverHiddenMode n) m
  simpa [positiveObserverHiddenMode, lp.single_apply, hmn] using hcoord

/-- No subsequence selected by a strictly increasing index map can be Cauchy. -/
theorem positiveObserverHiddenMode_subsequence_not_cauchy
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ¬ CauchySeq (fun n => positiveObserverHiddenMode (φ n)) := by
  intro hc
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc 1 zero_lt_one
  have hne : φ N ≠ φ (N + 1) := ne_of_lt (hφ (Nat.lt_succ_self N))
  have hlower := one_le_dist_positiveObserverHiddenMode_of_ne hne
  have hupper := hN N le_rfl (N + 1) (Nat.le_succ N)
  linarith

/-- Exact period-two observed phase. -/
def positiveObserverPhase (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n

/-- Closed observer coordinate paired with an escaping hidden coordinate. -/
def positiveObserverPeriodicEscapingLift (n : ℕ) :
    ℂ × PositiveObserverHiddenL2 :=
  (positiveObserverPhase n, positiveObserverHiddenMode n)

theorem positiveObserverPhase_period_two (n : ℕ) :
    positiveObserverPhase (n + 2) = positiveObserverPhase n := by
  simp [positiveObserverPhase, pow_add]

theorem positiveObserverPeriodicEscapingLift_observer_period_two (n : ℕ) :
    (positiveObserverPeriodicEscapingLift (n + 2)).1 =
      (positiveObserverPeriodicEscapingLift n).1 :=
  positiveObserverPhase_period_two n

/-- Although its observed projection is periodic, the lifted history has no convergent
subsequence. -/
theorem positiveObserverPeriodicEscapingLift_no_convergent_subsequence
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x : ℂ × PositiveObserverHiddenL2) :
    ¬ Tendsto (fun n => positiveObserverPeriodicEscapingLift (φ n)) atTop (nhds x) := by
  intro hconv
  apply positiveObserverHiddenMode_subsequence_not_cauchy φ hφ
  have hhidden : Tendsto (fun n => positiveObserverHiddenMode (φ n)) atTop (nhds x.2) := by
    simpa [Function.comp_def, positiveObserverPeriodicEscapingLift] using
      (continuous_snd.tendsto x |>.comp hconv)
  exact hhidden.cauchySeq

open GaloisForLFunctions.RHTower

/-- Positive compact-resolvent generator: closed inverse of the compact harmonic diagonal. -/
abbrev positiveObserverCompactGenerator :
    PositiveObserverHiddenL2 →ₗ.[ℂ] PositiveObserverHiddenL2 :=
  closedDenseInverse harmonicDiagonalOperator

theorem positiveObserverCompactGenerator_hasCompactResolvent :
    LinearPMap.HasCompactResolventAt positiveObserverCompactGenerator 0 :=
  closedDenseInverse_hasCompactResolventAt_zero harmonicDiagonalOperator
    injective_harmonicDiagonalOperator isCompactOperator_harmonicDiagonalOperator

theorem positiveObserverCompactGenerator_isSelfAdjoint :
    IsSelfAdjoint positiveObserverCompactGenerator :=
  closedDenseInverse_isSelfAdjoint harmonicDiagonalOperator
    injective_harmonicDiagonalOperator denseRange_harmonicDiagonalOperator
    isSelfAdjoint_harmonicDiagonalOperator

theorem harmonicDiagonalOperator_smul_positiveObserverHiddenMode (n : ℕ) :
    harmonicDiagonalOperator
        (((n + 1 : ℕ) : ℂ) • positiveObserverHiddenMode n) =
      positiveObserverHiddenMode n := by
  ext k
  simp only [map_smul, harmonicDiagonalOperator, positiveObserverHiddenMode,
    lp.single_apply, Pi.single_apply]
  by_cases hk : k = n
  · subst k
    simp only [lp.coeFn_smul, Pi.smul_apply, _root_.RHTower.diagonalOperator_apply,
      lp.single_apply_self, smul_eq_mul, harmonicMultiplier]
    push_cast
    rw [mul_one, div_eq_mul_inv]
    have hnR : ((n : ℝ) + 1) ≠ 0 := ne_of_gt
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one)
    have hnC : ((n : ℂ) + 1) ≠ 0 := by
      simpa using Complex.ofReal_ne_zero.mpr hnR
    simpa only [one_mul] using mul_inv_cancel₀ hnC
  · simp [hk]

/-- Canonical hidden mode as a vector in the closed generator domain. -/
def positiveObserverCompactGeneratorEigenvector (n : ℕ) :
    positiveObserverCompactGenerator.domain :=
  ⟨positiveObserverHiddenMode n, by
    rw [closedDenseInverse_domain]
    exact ⟨((n + 1 : ℕ) : ℂ) • positiveObserverHiddenMode n,
      harmonicDiagonalOperator_smul_positiveObserverHiddenMode n⟩⟩

/-- Exact hidden eigenvalue `n + 1`. -/
theorem positiveObserverCompactGenerator_eigenvector (n : ℕ) :
    positiveObserverCompactGenerator
        (positiveObserverCompactGeneratorEigenvector n) =
      ((n + 1 : ℕ) : ℂ) • positiveObserverHiddenMode n := by
  let y : PositiveObserverHiddenL2 :=
    ((n + 1 : ℕ) : ℂ) • positiveObserverHiddenMode n
  have happ := (closedDenseInverse_apply_C harmonicDiagonalOperator
    injective_harmonicDiagonalOperator y).2
  have heq : positiveObserverCompactGeneratorEigenvector n =
      ⟨harmonicDiagonalOperator y,
        (closedDenseInverse_apply_C harmonicDiagonalOperator
          injective_harmonicDiagonalOperator y).1⟩ := by
    apply Subtype.ext
    exact (harmonicDiagonalOperator_smul_positiveObserverHiddenMode n).symm
  simpa [positiveObserverCompactGenerator, y, heq] using happ

/-- Closed quadratic action associated with the positive generator. -/
def positiveObserverCompactGeneratorAction
    (x : positiveObserverCompactGenerator.domain) : ℝ :=
  (inner ℂ (positiveObserverCompactGenerator x)
    (x : PositiveObserverHiddenL2)).re

theorem positiveObserverCompactGeneratorAction_eigenvector (n : ℕ) :
    positiveObserverCompactGeneratorAction
        (positiveObserverCompactGeneratorEigenvector n) = n + 1 := by
  rw [positiveObserverCompactGeneratorAction,
    positiveObserverCompactGenerator_eigenvector, inner_smul_left]
  change ((star (((n + 1 : ℕ) : ℂ)) *
    inner ℂ (positiveObserverHiddenMode n) (positiveObserverHiddenMode n)).re) =
      (n : ℝ) + 1
  rw [inner_self_eq_norm_sq_to_K, positiveObserverHiddenMode_norm]
  simp

/-- Action of the escaping lift tends to infinity. -/
theorem positiveObserverCompactGeneratorAction_tendsto_atTop :
    Tendsto
      (fun n => positiveObserverCompactGeneratorAction
        (positiveObserverCompactGeneratorEigenvector n)) atTop atTop := by
  simp only [positiveObserverCompactGeneratorAction_eigenvector]
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- Global phase leaves the positive quadratic action unchanged. -/
theorem positiveObserverCompactGeneratorAction_phase_invariant
    (x : positiveObserverCompactGenerator.domain) (z : ℂ) (hz : ‖z‖ = 1) :
    positiveObserverCompactGeneratorAction (z • x) =
      positiveObserverCompactGeneratorAction x := by
  change (inner ℂ (positiveObserverCompactGenerator (z • x))
      (z • (x : PositiveObserverHiddenL2))).re =
    (inner ℂ (positiveObserverCompactGenerator x)
      (x : PositiveObserverHiddenL2)).re
  have hmap : positiveObserverCompactGenerator (z • x) =
      z • positiveObserverCompactGenerator x :=
    positiveObserverCompactGenerator.toFun.map_smul z x
  rw [hmap, inner_smul_left, inner_smul_right, ← mul_assoc]
  have hzz : (starRingEnd ℂ) z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
    norm_num
  rw [hzz]
  simp

end


end GaloisForLFunctions.HTGeometry
