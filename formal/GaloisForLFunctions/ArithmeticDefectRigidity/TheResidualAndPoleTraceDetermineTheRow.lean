import GaloisForLFunctions.ArithmeticDefectRigidity.ThePoleTraceDefinesALinearCofactorRenormalization
import GaloisForLFunctions.RHTower.FloorTransformPowerThreshold

/-!
# Exact reconstruction from the renormalized residual and its boundary trace

Möbius floor inversion reconstructs every row in the trace domain from its renormalized
residual and one scalar trace. Thus the residual map is injective on each fixed-trace slice;
its kernel is contained in one explicit inverse-power line. This is exact algebraic rigidity,
not a bounded inverse theorem. Membership or energy admission of the inverse-power row is
not assumed or asserted.
-/

open Finset RHTower

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The row plus its linear, power-subtracted proper cofactor sum. -/
def renormalizedResidualOperator (ε : SubcriticalDamping) :
    poleTraceDomain ε →ₗ[ℝ] (ℕ → ℝ) :=
  (poleTraceDomain ε).subtype + renormalizedCofactorOperator ε

/-- The exact Möbius floor inverse of the pole power, as a row without a domain assertion. -/
def inversePolePower (ε : SubcriticalDamping) : ℕ → ℝ :=
  floorTransform (moebiusPowerWeight ε) (fun n => (n : ℝ) ^ (1 - (ε : ℝ)))

private theorem totalCofactor_eq (ε : SubcriticalDamping) (v : poleTraceDomain ε) (n : ℕ) :
    floorTransform (powerWeight ε) v n = v n + finiteCofactorOperator ε v n := by
  change (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-(ε : ℝ)) * v (n / j)) =
    v n + ∑ j ∈ Icc 2 n, (j : ℝ) ^ (-(ε : ℝ)) * v (n / j)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0),
      Icc_eq_empty (by omega : ¬(2 : ℕ) ≤ 0), sum_empty, v.property.1, zero_add]
  · have hIcc : Icc 1 n = insert 1 (Icc 2 n) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [hIcc, sum_insert (by simp only [mem_Icc]; omega), Nat.cast_one,
      Real.one_rpow, Nat.div_one, one_mul]

/-- Exact floor inversion preserves the scalar boundary coordinate explicitly. -/
theorem poleTrace_reconstruction (ε : SubcriticalDamping) (v : poleTraceDomain ε) (n : ℕ) :
    v n = floorTransform (moebiusPowerWeight ε) (renormalizedResidualOperator ε v) n +
      poleTrace ε v * inversePolePower ε n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [v.property.1, floorTransform, inversePolePower,
      Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0), sum_empty, mul_zero, add_zero]
  · have htotal : floorTransform (powerWeight ε) v = fun m =>
        renormalizedResidualOperator ε v m + poleTrace ε v * (m : ℝ) ^ (1 - (ε : ℝ)) := by
      funext m
      rw [totalCofactor_eq]
      change v m + finiteCofactorOperator ε v m =
        (v m + (finiteCofactorOperator ε v m -
          poleTrace ε v * (m : ℝ) ^ (1 - (ε : ℝ)))) +
            poleTrace ε v * (m : ℝ) ^ (1 - (ε : ℝ))
      ring
    calc
      v n = floorTransform (moebiusPowerWeight ε) (floorTransform (powerWeight ε) v) n :=
        (floorTransform_moebiusPower_power ε v hn).symm
      _ = floorTransform (moebiusPowerWeight ε) (fun m =>
          renormalizedResidualOperator ε v m + poleTrace ε v * (m : ℝ) ^ (1 - (ε : ℝ))) n := by
        rw [htotal]
      _ = _ := by
        simp only [floorTransform, inversePolePower, mul_add, sum_add_distrib, mul_sum]
        congr 1
        exact sum_congr rfl fun j _ => by ring

/-- Every possible kernel row lies on the same explicit inverse-power line. -/
theorem residual_zero_implies_inversePolePower (ε : SubcriticalDamping)
    (v : poleTraceDomain ε) :
    renormalizedResidualOperator ε v = 0 →
      (v : ℕ → ℝ) = fun n => poleTrace ε v * inversePolePower ε n := by
  intro hv
  funext n
  rw [poleTrace_reconstruction ε v n, hv]
  simp only [floorTransform, Pi.zero_apply, mul_zero, sum_const_zero, zero_add]

/-- No nonzero row in the residual kernel can have zero boundary trace. -/
theorem residual_and_trace_zero_iff (ε : SubcriticalDamping) (v : poleTraceDomain ε) :
    (renormalizedResidualOperator ε v = 0 ∧ poleTrace ε v = 0) ↔ v = 0 := by
  constructor
  · rintro ⟨hr, ht⟩
    apply Subtype.ext
    funext n
    have h := congrFun (residual_zero_implies_inversePolePower ε v hr) n
    simpa only [ht, zero_mul, Submodule.coe_zero, Pi.zero_apply] using h
  · rintro rfl
    simp only [map_zero, and_self]

/-- The residual and the trace together are an injective source coordinate. -/
theorem residual_and_trace_injective (ε : SubcriticalDamping) :
    Function.Injective (fun v : poleTraceDomain ε =>
      (renormalizedResidualOperator ε v, poleTrace ε v)) := by
  intro v w h
  have hr : renormalizedResidualOperator ε v = renormalizedResidualOperator ε w :=
    congrArg Prod.fst h
  have ht : poleTrace ε v = poleTrace ε w := congrArg Prod.snd h
  apply Subtype.ext
  funext n
  rw [poleTrace_reconstruction ε v n, poleTrace_reconstruction ε w n, hr, ht]

/-- The actual source residual is the already paid forcing remainder at every cell. -/
theorem renormalizedResidualOperator_actualTraceVector (ε : SubcriticalDamping) :
    renormalizedResidualOperator ε (actualTraceVector ε) = forcingRemainder ε := by
  funext n
  change actualTraceVector ε n +
    renormalizedCofactorOperator ε (actualTraceVector ε) n = forcingRemainder ε n
  rw [renormalizedCofactorOperator_actualTraceVector]
  change pmPowerDampedCenteredDivisorPrefix ε n + renormalizedCofactor ε n = forcingRemainder ε n
  cases n with
  | zero =>
    have hα : 1 - (ε : ℝ) ≠ 0 := by linarith [ε.property.2]
    have hIcc : (Icc 2 0 : Finset ℕ) = ∅ := Icc_eq_empty (by omega)
    rw [ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      forcingRemainder_zero]
    simp only [renormalizedCofactor,
      ArithmeticContinuationAndCriticalEnergy.offDiagonalUnitDilation, forcingPower,
      hIcc, sum_empty, Nat.cast_zero, Real.zero_rpow hα, mul_zero, sub_self, zero_add]
  | succ n => exact receiver_add_renormalizedCofactor_eq ε n

/-- Actual reconstruction retains the unestimated inverse-power direction separately. -/
theorem actual_receiver_reconstruction (ε : SubcriticalDamping) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      floorTransform (moebiusPowerWeight ε) (forcingRemainder ε) n +
        forcingPowerCoefficient ε * inversePolePower ε n := by
  have h := poleTrace_reconstruction ε (actualTraceVector ε) n
  rw [renormalizedResidualOperator_actualTraceVector, poleTrace_actualTraceVector] at h
  exact h

end GaloisForLFunctions.ArithmeticDefectRigidity
