import GaloisForLFunctions.BiScaleUncertainty.FiniteGridRunLength
import GaloisForLFunctions.BiScaleUncertainty.IntegerHatTraceExtension

/-!
# Actual union data for finite divisor families

The coordinate-mask fixed space counts each positive integer node once. It is
closed and complete. Its physical extension realizes every integer trace,
including zeros outside the union, with exact adjacent energy and mismatch.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def finiteGridDataSpace (d : ℕ) (D : Finset ℕ) : Submodule ℝ TraceData :=
  (sequenceMask ℝ (finiteGridActive d D) - ContinuousLinearMap.id ℝ TraceData).ker

abbrev FiniteGridData (d : ℕ) (D : Finset ℕ) := finiteGridDataSpace d D

theorem mem_finiteGridDataSpace_iff (d : ℕ) (D : Finset ℕ) (v : TraceData) :
    v ∈ finiteGridDataSpace d D ↔ ∀ k, ¬ finiteGridActive d D k → v k = 0 := by
  change sequenceMask ℝ (finiteGridActive d D) v - v = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h k hk
    have he := congrArg (fun w : TraceData => w k) h
    simpa [sequenceMask_apply, hk] using he.symm
  · intro h
    apply lp.ext
    funext k
    rw [sequenceMask_apply]
    split_ifs with hk
    · rfl
    · exact (h k hk).symm

theorem finiteGridData_off (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D)
    {k : ℕ} (hk : ¬ finiteGridActive d D k) : v.1 k = 0 :=
  (mem_finiteGridDataSpace_iff d D v.1).mp v.2 k hk

instance finiteGridData_completeSpace (d : ℕ) (D : Finset ℕ) :
    CompleteSpace (FiniteGridData d D) :=
  (sequenceMask ℝ (finiteGridActive d D) -
    ContinuousLinearMap.id ℝ TraceData).isClosed_ker.completeSpace_coe

/-- Masking arbitrary ℓ² data constructs union data without an admission premise. -/
def finiteGridData (d : ℕ) (D : Finset ℕ) (v : TraceData) : FiniteGridData d D :=
  ⟨sequenceMask ℝ (finiteGridActive d D) v, by
    change sequenceMask ℝ (finiteGridActive d D)
      (sequenceMask ℝ (finiteGridActive d D) v) -
        sequenceMask ℝ (finiteGridActive d D) v = 0
    rw [sequenceMask_idempotent, sub_self]⟩

theorem finiteGridData_apply (d : ℕ) (D : Finset ℕ) (v : TraceData) (k : ℕ) :
    (finiteGridData d D v).1 k = if finiteGridActive d D k then v k else 0 :=
  sequenceMask_apply ℝ (finiteGridActive d D) v k

def finiteGridExtension (d : ℕ) (D : Finset ℕ) : FiniteGridData d D →L[ℝ] Velocity :=
  integerExtension ∘L (finiteGridDataSpace d D).subtypeL

theorem finiteGridExtension_apply (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D) :
    finiteGridExtension d D v = integerExtension v.1 := rfl

theorem hasSum_finiteGridExtension (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D) :
    HasSum (fun k => v.1 k • integerHat k) (finiteGridExtension d D v) :=
  hasSum_integerExtension v.1

theorem primitive_finiteGridExtension (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D)
    (n : ℕ) : primitive (finiteGridExtension d D v) (n + 1) = v.1 n :=
  primitive_integerExtension_succ n v.1

theorem primitive_finiteGridExtension_nat (d : ℕ) (D : Finset ℕ)
    (v : FiniteGridData d D) (n : ℕ) :
    primitive (finiteGridExtension d D v) n = if n = 0 then 0 else v.1 (n-1) := by
  cases n with
  | zero => simp [primitive]
  | succ n =>
      simpa only [Nat.cast_succ, Nat.succ_ne_zero, if_false, Nat.succ_sub_one] using
        primitive_finiteGridExtension d D v n

theorem primitive_finiteGridExtension_off (d : ℕ) (D : Finset ℕ)
    (v : FiniteGridData d D) (n : ℕ) (hn : ¬ finiteGridActive d D n) :
    primitive (finiteGridExtension d D v) (n + 1) = 0 := by
  rw [primitive_finiteGridExtension, finiteGridData_off d D v hn]

theorem log_finiteGridExtension (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D)
    (n : ℕ) : logPrimitive (finiteGridExtension d D v) (Real.log ((n : ℝ) + 1)) = v.1 n :=
  log_integerExtension n v.1

theorem finiteGridExtension_energy (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D) :
    ‖finiteGridExtension d D v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * ∑' k, v.1 k * v.1 (k + 1) :=
  integerExtension_energy v.1

theorem finiteGridExtension_mass (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D) :
    ‖v‖ ^ 2 = ∑' k, (v.1 k) ^ 2 := norm_sq_traceData v.1

theorem finiteGrid_competitor_energy (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D)
    (q : Velocity) :
    ‖q‖ ^ 2 = ‖finiteGridExtension d D v‖ ^ 2 + ‖q - finiteGridExtension d D v‖ ^ 2 +
      2 * ∑' k, v.1 k * integerTraceCurvature (q - finiteGridExtension d D v) k :=
  integerExtension_competitor_energy v.1 q

theorem finiteGrid_minimum_energy_defect (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D)
    (q : Velocity) (h : ∀ k : ℕ, primitive q k = primitive (finiteGridExtension d D v) k) :
    ‖q‖ ^ 2 = ‖finiteGridExtension d D v‖ ^ 2 + ‖q - finiteGridExtension d D v‖ ^ 2 :=
  integerExtension_minimum_energy_defect v.1 q h

theorem finiteGrid_minimum_energy_eq_iff (d : ℕ) (D : Finset ℕ)
    (v : FiniteGridData d D) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (finiteGridExtension d D v) k) :
    ‖q‖ ^ 2 = ‖finiteGridExtension d D v‖ ^ 2 ↔ q = finiteGridExtension d D v :=
  integerExtension_minimum_energy_eq_iff v.1 q h

theorem finiteGrid_minimum_energy (d : ℕ) (D : Finset ℕ)
    (v : FiniteGridData d D) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (finiteGridExtension d D v) k) :
    ‖finiteGridExtension d D v‖^2 ≤ ‖q‖^2 :=
  integerExtension_minimum_energy v.1 q h

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
