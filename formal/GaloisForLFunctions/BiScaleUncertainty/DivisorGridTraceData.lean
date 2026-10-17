import GaloisForLFunctions.BiScaleUncertainty.IntegerHatTraceExtension

/-!
# Actual union data for arbitrary divisor families

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

/-- Active positive nodes of a nonempty, possibly infinite divisor family. -/
def divisorGridActive (d : ℕ) (D : Set ℕ) (k : ℕ) : Prop :=
  ∃ e ∈ insert d D, e + 2 ∣ k + 1

theorem divisorGridActive_seed (d : ℕ) (D : Set ℕ) :
    divisorGridActive d D (d + 1) := ⟨d, Set.mem_insert d D, dvd_rfl⟩

def divisorGridDataSpace (d : ℕ) (D : Set ℕ) : Submodule ℝ TraceData :=
  (sequenceMask ℝ (divisorGridActive d D) - ContinuousLinearMap.id ℝ TraceData).ker

abbrev DivisorGridData (d : ℕ) (D : Set ℕ) := divisorGridDataSpace d D

theorem mem_divisorGridDataSpace_iff (d : ℕ) (D : Set ℕ) (v : TraceData) :
    v ∈ divisorGridDataSpace d D ↔ ∀ k, ¬ divisorGridActive d D k → v k = 0 := by
  change sequenceMask ℝ (divisorGridActive d D) v - v = 0 ↔ _
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

theorem divisorGridData_off (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D)
    {k : ℕ} (hk : ¬ divisorGridActive d D k) : v.1 k = 0 :=
  (mem_divisorGridDataSpace_iff d D v.1).mp v.2 k hk

instance divisorGridData_completeSpace (d : ℕ) (D : Set ℕ) :
    CompleteSpace (DivisorGridData d D) :=
  (sequenceMask ℝ (divisorGridActive d D) -
    ContinuousLinearMap.id ℝ TraceData).isClosed_ker.completeSpace_coe

/-- Masking arbitrary ℓ² data constructs union data without an admission premise. -/
def divisorGridData (d : ℕ) (D : Set ℕ) (v : TraceData) : DivisorGridData d D :=
  ⟨sequenceMask ℝ (divisorGridActive d D) v, by
    change sequenceMask ℝ (divisorGridActive d D)
      (sequenceMask ℝ (divisorGridActive d D) v) -
        sequenceMask ℝ (divisorGridActive d D) v = 0
    rw [sequenceMask_idempotent, sub_self]⟩

theorem divisorGridData_apply (d : ℕ) (D : Set ℕ) (v : TraceData) (k : ℕ) :
    (divisorGridData d D v).1 k = if divisorGridActive d D k then v k else 0 :=
  sequenceMask_apply ℝ (divisorGridActive d D) v k

def divisorGridExtension (d : ℕ) (D : Set ℕ) : DivisorGridData d D →L[ℝ] Velocity :=
  integerExtension ∘L (divisorGridDataSpace d D).subtypeL

theorem divisorGridExtension_apply (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D) :
    divisorGridExtension d D v = integerExtension v.1 := rfl

theorem hasSum_divisorGridExtension (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D) :
    HasSum (fun k => v.1 k • integerHat k) (divisorGridExtension d D v) :=
  hasSum_integerExtension v.1

theorem primitive_divisorGridExtension (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D)
    (n : ℕ) : primitive (divisorGridExtension d D v) (n + 1) = v.1 n :=
  primitive_integerExtension_succ n v.1

theorem primitive_divisorGridExtension_nat (d : ℕ) (D : Set ℕ)
    (v : DivisorGridData d D) (n : ℕ) :
    primitive (divisorGridExtension d D v) n = if n = 0 then 0 else v.1 (n-1) := by
  cases n with
  | zero => simp [primitive]
  | succ n =>
      simpa only [Nat.cast_succ, Nat.succ_ne_zero, if_false, Nat.succ_sub_one] using
        primitive_divisorGridExtension d D v n

theorem primitive_divisorGridExtension_off (d : ℕ) (D : Set ℕ)
    (v : DivisorGridData d D) (n : ℕ) (hn : ¬ divisorGridActive d D n) :
    primitive (divisorGridExtension d D v) (n + 1) = 0 := by
  rw [primitive_divisorGridExtension, divisorGridData_off d D v hn]

theorem log_divisorGridExtension (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D)
    (n : ℕ) : logPrimitive (divisorGridExtension d D v) (Real.log ((n : ℝ) + 1)) = v.1 n :=
  log_integerExtension n v.1

theorem divisorGridExtension_energy (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D) :
    ‖divisorGridExtension d D v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * ∑' k, v.1 k * v.1 (k + 1) :=
  integerExtension_energy v.1

theorem divisorGridExtension_mass (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D) :
    ‖v‖ ^ 2 = ∑' k, (v.1 k) ^ 2 := norm_sq_traceData v.1

theorem divisorGrid_competitor_energy (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D)
    (q : Velocity) :
    ‖q‖ ^ 2 = ‖divisorGridExtension d D v‖ ^ 2 + ‖q - divisorGridExtension d D v‖ ^ 2 +
      2 * ∑' k, v.1 k * integerTraceCurvature (q - divisorGridExtension d D v) k :=
  integerExtension_competitor_energy v.1 q

theorem divisorGrid_minimum_energy_defect (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D)
    (q : Velocity) (h : ∀ k : ℕ, primitive q k = primitive (divisorGridExtension d D v) k) :
    ‖q‖ ^ 2 = ‖divisorGridExtension d D v‖ ^ 2 + ‖q - divisorGridExtension d D v‖ ^ 2 :=
  integerExtension_minimum_energy_defect v.1 q h

theorem divisorGrid_minimum_energy_eq_iff (d : ℕ) (D : Set ℕ)
    (v : DivisorGridData d D) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (divisorGridExtension d D v) k) :
    ‖q‖ ^ 2 = ‖divisorGridExtension d D v‖ ^ 2 ↔ q = divisorGridExtension d D v :=
  integerExtension_minimum_energy_eq_iff v.1 q h

theorem divisorGrid_minimum_energy (d : ℕ) (D : Set ℕ)
    (v : DivisorGridData d D) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (divisorGridExtension d D v) k) :
    ‖divisorGridExtension d D v‖^2 ≤ ‖q‖^2 :=
  integerExtension_minimum_energy v.1 q h

theorem divisorGridExtension_injective (d : ℕ) (D : Set ℕ) :
    Function.Injective (divisorGridExtension d D) := by
  intro v w h
  apply Subtype.ext
  apply lp.ext
  funext k
  have he := congrArg (fun q => primitive q ((k : ℝ) + 1)) h
  simpa only [primitive_divisorGridExtension] using he

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
