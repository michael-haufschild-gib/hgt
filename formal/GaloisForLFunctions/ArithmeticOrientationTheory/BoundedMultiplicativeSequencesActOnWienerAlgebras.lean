import GaloisForLFunctions.ArithmeticOrientationTheory.TheCriticalWienerAlgebraIsABanachAlgebra

/-!
# Bounded multiplicative sequences act on Wiener algebras

A multiplicative sequence in a complete normed algebra, bounded by the Wiener
weight, extends uniquely to a contractive algebra homomorphism. The extension
is its absolutely convergent coefficient series. Multiplication follows by
continuity from the point-mass multiplication law.
-/

noncomputable section
set_option autoImplicit false

open LSeries

namespace GaloisForLFunctions.ArithmeticOrientationTheory
namespace WienerAlgebraAt

variable {σ : ℝ} {B : Type*}

section Linear

variable [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable (V : ℕ → B) (hV0 : V 0 = 0)
variable (hV : ∀ n : ℕ, n ≠ 0 → ‖V n‖ ≤ (n : ℝ) ^ (-σ))

include hV0 hV

/-- The Wiener summand norm dominates the operator-series summand norm. -/
theorem norm_coefficient_smul_le (a : WienerAlgebraAt σ) (n : ℕ) :
    ‖a.toFn n • V n‖ ≤ ‖LSeries.term (⇑a.toFn) σ n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hV0]
  · calc
      ‖a.toFn n • V n‖ = ‖a.toFn n‖ * ‖V n‖ := norm_smul _ _
      _ ≤ ‖a.toFn n‖ * (n : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_left (hV n hn) (norm_nonneg _)
      _ = ‖LSeries.term (⇑a.toFn) σ n‖ := by
        rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re,
          Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The target coefficient series is absolutely summable in norm. -/
theorem summable_norm_coefficient_smul (a : WienerAlgebraAt σ) :
    Summable (fun n => ‖a.toFn n • V n‖) :=
  a.summable_norm.of_nonneg_of_le (fun n => norm_nonneg _)
    (norm_coefficient_smul_le V hV0 hV a)

/-- Completeness turns absolute norm summability into convergence. -/
theorem summable_coefficient_smul (a : WienerAlgebraAt σ) :
    Summable (fun n => a.toFn n • V n) :=
  (summable_norm_coefficient_smul V hV0 hV a).of_norm

/-- The coefficient series is contractive for the Wiener norm. -/
theorem norm_tsum_coefficient_smul_le (a : WienerAlgebraAt σ) :
    ‖∑' n, a.toFn n • V n‖ ≤ ‖a‖ := by
  refine (norm_tsum_le_tsum_norm
    (summable_norm_coefficient_smul V hV0 hV a)).trans ?_
  exact (summable_norm_coefficient_smul V hV0 hV a).tsum_le_tsum
    (norm_coefficient_smul_le V hV0 hV a) a.summable_norm

/-- The bounded linear extension of a sequence with the Wiener weight bound. -/
def sequenceExtension : WienerAlgebraAt σ →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' n, a.toFn n • V n
      map_add' := fun a b => by
        simp only [toFn_add, ArithmeticFunction.add_apply, add_smul]
        exact (summable_coefficient_smul V hV0 hV a).tsum_add
          (summable_coefficient_smul V hV0 hV b)
      map_smul' := fun z a => by
        simp only [toFn_smul, ArithmeticFunction.smul_map, smul_smul]
        exact (HasSum.const_smul z
          (summable_coefficient_smul V hV0 hV a).hasSum).tsum_eq } 1
    (fun a => by simpa only [one_mul] using norm_tsum_coefficient_smul_le V hV0 hV a)

theorem sequenceExtension_apply (a : WienerAlgebraAt σ) :
    sequenceExtension V hV0 hV a = ∑' n, a.toFn n • V n := rfl

/-- The extension takes each point mass to its prescribed value. -/
theorem sequenceExtension_pointMass (n : ℕ) :
    sequenceExtension V hV0 hV (pointMass n) = V n := by
  rw [sequenceExtension_apply, tsum_eq_single n]
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [hV0]
    · simp only [toFn_pointMass, pointMassFn_apply, if_pos ⟨hn, rfl⟩, one_smul]
  · intro m hm
    simp only [toFn_pointMass, pointMassFn_apply]
    rw [if_neg (fun h => hm h.2), zero_smul]

theorem norm_sequenceExtension_le : ‖sequenceExtension V hV0 hV‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun a => by simpa only [one_mul] using norm_tsum_coefficient_smul_le V hV0 hV a)

/-- A continuous linear extension is determined by its point-mass values. -/
theorem sequenceExtension_unique (L : WienerAlgebraAt σ →L[ℂ] B)
    (hL : ∀ n, L (pointMass n) = V n) : L = sequenceExtension V hV0 hV := by
  ext a
  have h := L.hasSum (hasSum_pointMass a)
  simp only [map_smul, hL] at h
  exact h.tsum_eq.symm

end Linear

section Algebra

variable [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
variable (V : ℕ → B) (hV0 : V 0 = 0)
variable (hV : ∀ n : ℕ, n ≠ 0 → ‖V n‖ ≤ (n : ℝ) ^ (-σ))
variable (hV1 : V 1 = 1) (hVmul : ∀ m n, V (m * n) = V m * V n)

include hVmul

/-- Multiplication by a point mass is respected by the extension. -/
theorem sequenceExtension_mul_pointMass (a : WienerAlgebraAt σ) (n : ℕ) :
    sequenceExtension V hV0 hV (a * pointMass n) =
      sequenceExtension V hV0 hV a * V n := by
  have hleft := (sequenceExtension V hV0 hV).hasSum
    ((hasSum_pointMass a).mul_right (pointMass n))
  have hright := ((sequenceExtension V hV0 hV).hasSum
    (hasSum_pointMass a)).mul_right (V n)
  apply HasSum.unique hleft
  convert hright using 1
  ext m
  simp only [smul_mul_assoc, map_smul, pointMass_mul, sequenceExtension_pointMass,
    hVmul]

/-- Absolute convergence extends multiplicativity from point masses to all kernels. -/
theorem sequenceExtension_mul (a b : WienerAlgebraAt σ) :
    sequenceExtension V hV0 hV (a * b) =
      sequenceExtension V hV0 hV a * sequenceExtension V hV0 hV b := by
  have hleft := (sequenceExtension V hV0 hV).hasSum
    ((hasSum_pointMass b).mul_left a)
  have hright := ((sequenceExtension V hV0 hV).hasSum
    (hasSum_pointMass b)).mul_left (sequenceExtension V hV0 hV a)
  apply HasSum.unique hleft
  convert hright using 1
  ext n
  simp only [mul_smul_comm, map_smul, sequenceExtension_pointMass,
    sequenceExtension_mul_pointMass V hV0 hV hVmul]

/-- The contractive algebra representation associated with a multiplicative sequence. -/
def sequenceRepresentation : WienerAlgebraAt σ →ₐ[ℂ] B where
  toFun := sequenceExtension V hV0 hV
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by rw [← pointMass_one, sequenceExtension_pointMass, hV1]
  map_mul' := sequenceExtension_mul V hV0 hV hVmul
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← pointMass_one,
      sequenceExtension_pointMass, hV1, Algebra.algebraMap_eq_smul_one]


end Algebra

end WienerAlgebraAt
end GaloisForLFunctions.ArithmeticOrientationTheory
