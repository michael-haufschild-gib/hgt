import GaloisForLFunctions.HTGeometry.EventComplementaryRecord

/-!
# A complementary record completes a noninvertible event

A linear event `T : V → W` separates into its transmitted range and its created cokernel.
If `V` and `W` have equal finite dimension, any cokernel-valued record `R` for which `(T, R)`
is faithful makes the combined map

`V → range T × coker T`

an equivalence.  Thus the visible event may be noninvertible while the transmitted-plus-recorded
completion is invertible.

This is unconditional finite-dimensional linear algebra.  It does not select the record, identify
the cokernel with spacetime, or derive any physical dynamics.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- Pair the transmitted value of an event with its complementary cokernel record. -/
def eventRangeRecordCompletion
    (T : V →ₗ[K] W) (R : V →ₗ[K] (W ⧸ LinearMap.range T)) :
    V →ₗ[K] (LinearMap.range T × (W ⧸ LinearMap.range T)) :=
  T.rangeRestrict.prod R

/-- Corestricting the visible event to its range does not change whether event plus record is
faithful. -/
theorem eventRangeRecordCompletion_injective_iff
    (T : V →ₗ[K] W) (R : V →ₗ[K] (W ⧸ LinearMap.range T)) :
    Function.Injective (eventRangeRecordCompletion T R) ↔
      Function.Injective (T.prod R) := by
  constructor
  · intro h x y hxy
    apply h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hxy
    · exact congrArg (fun z : W × (W ⧸ LinearMap.range T) => z.2) hxy
  · intro h x y hxy
    apply h
    apply Prod.ext
    · exact congrArg (fun z : LinearMap.range T => (z : W))
        (congrArg Prod.fst hxy)
    · exact congrArg
        (fun z : LinearMap.range T × (W ⧸ LinearMap.range T) => z.2) hxy

section FiniteDimensional

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- For equal-dimensional source and target, transmitted range plus created cokernel has exactly
the source dimension. -/
theorem eventRangeRecordCompletion_finrank
    (T : V →ₗ[K] W)
    (hdim : Module.finrank K V = Module.finrank K W) :
    Module.finrank K V =
      Module.finrank K (LinearMap.range T × (W ⧸ LinearMap.range T)) := by
  rw [Module.finrank_prod]
  have hcoker := Submodule.finrank_quotient_add_finrank (LinearMap.range T)
  omega

/-- A faithful cokernel record completes an equal-dimensional noninvertible event to a bijection
onto its transmitted and recorded faces. -/
theorem eventRangeRecordCompletion_bijective
    (T : V →ₗ[K] W) (R : V →ₗ[K] (W ⧸ LinearMap.range T))
    (hdim : Module.finrank K V = Module.finrank K W)
    (hTR : Function.Injective (T.prod R)) :
    Function.Bijective (eventRangeRecordCompletion T R) := by
  have hinj : Function.Injective (eventRangeRecordCompletion T R) :=
    (eventRangeRecordCompletion_injective_iff T R).2 hTR
  exact
    ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (eventRangeRecordCompletion_finrank T hdim)).mp hinj⟩

/-- The linear equivalence supplied by a faithful complementary record. -/
def eventRangeRecordCompletionEquiv
    (T : V →ₗ[K] W) (R : V →ₗ[K] (W ⧸ LinearMap.range T))
    (hdim : Module.finrank K V = Module.finrank K W)
    (hTR : Function.Injective (T.prod R)) :
    V ≃ₗ[K] (LinearMap.range T × (W ⧸ LinearMap.range T)) :=
  LinearEquiv.ofBijective (eventRangeRecordCompletion T R)
    (eventRangeRecordCompletion_bijective T R hdim hTR)

end FiniteDimensional

/-- At the ten-to-ten rank-six interface, the completion has a six-dimensional transmitted face
and a four-dimensional complementary record face. -/
theorem rankSixEvent_rangeRecordCompletion_dimensions
    (T : Matrix (Fin 10) (Fin 10) ℂ)
    (hrange : Module.finrank ℂ (LinearMap.range T.toLin') = 6) :
    Module.finrank ℂ (LinearMap.range T.toLin') = 6 ∧
      Module.finrank ℂ ((Fin 10 → ℂ) ⧸ LinearMap.range T.toLin') = 4 :=
  ⟨hrange, (rank_six_map_has_four_kernel_and_cokernel T hrange).2⟩

/-- A faithful record completes the rank-six ten-to-ten event to an exact `6 + 4`
linear equivalence. -/
def rankSixEventRangeRecordCompletionEquiv
    (T : Matrix (Fin 10) (Fin 10) ℂ)
    (R : (Fin 10 → ℂ) →ₗ[ℂ] ((Fin 10 → ℂ) ⧸ LinearMap.range T.toLin'))
    (hTR : Function.Injective (T.toLin'.prod R)) :
    (Fin 10 → ℂ) ≃ₗ[ℂ]
      (LinearMap.range T.toLin' ×
        ((Fin 10 → ℂ) ⧸ LinearMap.range T.toLin')) :=
  eventRangeRecordCompletionEquiv T.toLin' R (by simp) hTR

end GaloisForLFunctions.HTGeometry
