import GaloisForLFunctions.CompletedArithmeticForms.NativeGaussianHorizon
import GaloisForLFunctions.CompletedArithmeticForms.SuccessorComparison

/-!
# Explicit relative bounds for the complete native successor

The full-form Gaussian error controls the actual mixed Schur reserve with the
same relative cost. The resulting source horizon depends explicitly on rank and
shift and includes the complete infinite theta remainder.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Exact successor of the shifted Gaussian comparison. -/
theorem gaussianShifted_successorSchur (N s : ℕ) :
    finiteHankelSuccessorSchur (fun k => gaussianMoment (k + s)) N =
      nativeGammaReserve N s := by
  have hg : 0 < gaussianMoment s :=
    mul_pos (pow_pos (by positivity) s) (gammaShapeMoment_pos (by positivity) s)
  have he : (fun k => gaussianMoment (k + s)) =
      scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) := by
    funext k
    rw [Nat.add_comm k s]
    simp only [gaussianMoment, scaledGammaMoment, pow_add, gammaShapeMoment_add]
    rw [add_comm (1 / 2 : ℝ) (s : ℝ)]
    ring
  rw [he, scaledGamma_successorSchur hg (by positivity) (by positivity)]
  rfl

/-- The same full-form relative error pays the exact native successor, without
an additional inverse perturbation loss. -/
theorem nativeBalancedSuccessor_relative_error_le (N s : ℕ) {x : ℝ}
    (hq : ((2 * (s + 2 * (N + 1)) : ℕ) : ℝ) + 6 ≤
      thetaCuspSingleAtomReflectionScale 1 x)
    (hcost : nativeMixedErrorNumerator (N + 1) s < thetaCuspSingleAtomReflectionScale 1 x) :
    |nativeBalancedSuccessor N s x - nativeGammaReserve N s| ≤
      (nativeMixedErrorNumerator (N + 1) s / thetaCuspSingleAtomReflectionScale 1 x) *
        nativeGammaReserve N s := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη : 0 ≤ nativeMixedErrorNumerator (N + 1) s /
      thetaCuspSingleAtomReflectionScale 1 x :=
    div_nonneg (nativeMixedErrorNumerator_nonneg _ _) hqp.le
  have hη1 : nativeMixedErrorNumerator (N + 1) s /
      thetaCuspSingleAtomReflectionScale 1 x < 1 := (div_lt_one hqp).mpr hcost
  have h := successorSchur_relative_error (gaussianShiftedHead_posDef (N + 1) s)
    hη hη1 (nativeBalancedHead_relative_error_le (N + 1) s hq)
  rw [gaussianShifted_successorSchur N s] at h
  exact h

/-- One explicit scale pays the analytic domain and half the complete successor error. -/
def nativeSuccessorScale (N s : ℕ) : ℝ :=
  ((2 * (s + 2 * (N + 1)) + 6 : ℕ) : ℝ) + 2 * nativeMixedErrorNumerator (N + 1) s

theorem nativeSuccessorScale_base_le (N s : ℕ) :
    ((2 * (s + 2 * (N + 1)) + 6 : ℕ) : ℝ) ≤ nativeSuccessorScale N s := by
  unfold nativeSuccessorScale
  linarith only [nativeMixedErrorNumerator_nonneg (N + 1) s]

/-- Explicit simultaneous rank, shift, and center bounds for the literal native reserve. -/
theorem nativeBalancedSuccessor_half_bounds_of_scale (N s : ℕ) {x : ℝ}
    (hq : nativeSuccessorScale N s ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 := by
  have hbase := (nativeSuccessorScale_base_le N s).trans hq
  have hdomain : ((2 * (s + 2 * (N + 1)) : ℕ) : ℝ) + 6 ≤
      thetaCuspSingleAtomReflectionScale 1 x := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hbase
  have hbpos : (0 : ℝ) < ((2 * (s + 2 * (N + 1)) + 6 : ℕ) : ℝ) := by positivity
  have hscale : 2 * nativeMixedErrorNumerator (N + 1) s <
      thetaCuspSingleAtomReflectionScale 1 x := by
    unfold nativeSuccessorScale at hq
    linarith only [hq, hbpos]
  have hcost : nativeMixedErrorNumerator (N + 1) s <
      thetaCuspSingleAtomReflectionScale 1 x := by
    linarith only [hscale, nativeMixedErrorNumerator_nonneg (N + 1) s]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη : nativeMixedErrorNumerator (N + 1) s /
      thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hqp).mpr
    linarith only [hscale]
  have he := nativeBalancedSuccessor_relative_error_le N s hdomain hcost
  have hstrict := mul_lt_mul_of_pos_right hη (nativeGammaReserve_pos N s)
  have habs := he.trans_lt hstrict
  obtain ⟨hl, hu⟩ := abs_lt.mp habs
  constructor <;> linarith only [hl, hu]

/-- Explicit center horizon for a native successor of the given rank and shift. -/
def nativeSuccessorHorizon (N s : ℕ) : ℝ :=
  max 0 (Real.log (nativeSuccessorScale N s / Real.pi) / 2)

/-- Every source center beyond the stated horizon has the exact half-Gamma successor reserve. -/
theorem nativeBalancedSuccessor_half_bounds_of_horizon (N s : ℕ) {x : ℝ}
    (hx : nativeSuccessorHorizon N s ≤ x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 := by
  have hQ : 0 < nativeSuccessorScale N s :=
    lt_of_lt_of_le (by positivity) (nativeSuccessorScale_base_le N s)
  have hxlog : Real.log (nativeSuccessorScale N s / Real.pi) ≤ 2 * x := by
    have h := (le_max_right 0 (Real.log (nativeSuccessorScale N s / Real.pi) / 2)).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_log (div_pos hQ Real.pi_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  apply nativeBalancedSuccessor_half_bounds_of_scale N s
  simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
    mul_div_cancel₀ _ Real.pi_ne_zero] using hm

#print axioms gaussianShifted_successorSchur
#print axioms nativeBalancedSuccessor_relative_error_le
#print axioms nativeBalancedSuccessor_half_bounds_of_scale
#print axioms nativeBalancedSuccessor_half_bounds_of_horizon

end GaloisForLFunctions.CompletedArithmeticForms
