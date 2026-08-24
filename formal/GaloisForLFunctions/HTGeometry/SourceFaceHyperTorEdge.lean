import GaloisForLFunctions.HTGeometry.SourceFaceBaseChangeTransmutation
import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal

/-!
# One-face hyper-Tor edge sequence

For a two-term observation complex, regular one-parameter specialization yields the collapsed
hyper-Tor edge sequence.  Its terminal map sends a boundary cycle to the degree-one Tor class of
the generic cokernel.  Exactness states that precisely inherited generic cycles and discarded
source-layer cycles die; every Tor class occurs.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/-! ## Common-kernel no-go witness -/

/-- Smallest source ring distinguishing a unit observation from a coordinate observation. -/
abbrev sourceFaceNoGoRing (R : Type*) [CommRing R] := MvPolynomial (Fin 1) R

/-- The coordinate layer in the one-variable polynomial witness. -/
abbrev sourceFaceNoGoLayer (R : Type*) [CommRing R] :
    Submodule (sourceFaceNoGoRing R) (sourceFaceNoGoRing R) :=
  sourceFaceScalarLayer (MvPolynomial.X 0) (sourceFaceNoGoRing R)

/-- The coordinate layer is proper: its elements have zero constant term. -/
theorem one_not_mem_sourceFaceNoGoLayer [IsDomain A] :
    (1 : sourceFaceNoGoRing A) ∉ sourceFaceNoGoLayer A := by
  rintro ⟨p, hp⟩
  have h := congrArg
    (eval₂Hom (RingHom.id A) (fun _ : Fin 1 => 0)) hp
  simp [sourceFaceScalarMul] at h

/-- Multiplication by the coordinate is injective before specialization. -/
theorem sourceFaceNoGo_coordinate_injective [IsDomain A] :
    Function.Injective (sourceFaceScalarMul
      (MvPolynomial.X 0 : sourceFaceNoGoRing A) (sourceFaceNoGoRing A)) := by
  intro p q hpq
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := A) (0 : Fin 1)) hpq

/-- Unit and coordinate observations have the same zero generic kernel. -/
theorem sourceFaceNoGo_generic_kernels_equal [IsDomain A] :
    LinearMap.ker (LinearMap.id : sourceFaceNoGoRing A →ₗ[sourceFaceNoGoRing A]
      sourceFaceNoGoRing A) =
    LinearMap.ker (sourceFaceScalarMul
      (MvPolynomial.X 0 : sourceFaceNoGoRing A) (sourceFaceNoGoRing A)) := by
  rw [LinearMap.ker_eq_bot.mpr (fun _ _ h => h),
    LinearMap.ker_eq_bot.mpr sourceFaceNoGo_coordinate_injective]

/-- The unit observation remains injective on the coordinate face. -/
theorem sourceFaceNoGo_identity_boundary_injective [IsDomain A] :
    Function.Injective (sourceFaceQuotientObservation
      (LinearMap.id : sourceFaceNoGoRing A →ₗ[sourceFaceNoGoRing A]
        sourceFaceNoGoRing A)
      (sourceFaceNoGoLayer A) (sourceFaceNoGoLayer A)
      (sourceFaceScalarLayer_le_comap
        (MvPolynomial.X 0 : sourceFaceNoGoRing A) LinearMap.id)) := by
  rw [sourceFaceQuotientObservation_injective_iff]
  intro p hp
  exact hp

/-- The coordinate observation loses injectivity on the same face despite having the same generic
kernel as the unit observation. -/
theorem sourceFaceNoGo_coordinate_boundary_not_injective [IsDomain A] :
    ¬ Function.Injective (sourceFaceQuotientObservation
      (sourceFaceScalarMul (MvPolynomial.X 0 : sourceFaceNoGoRing A)
        (sourceFaceNoGoRing A))
      (sourceFaceNoGoLayer A) (sourceFaceNoGoLayer A)
      (sourceFaceScalarLayer_le_comap
        (MvPolynomial.X 0 : sourceFaceNoGoRing A)
        (sourceFaceScalarMul (MvPolynomial.X 0 : sourceFaceNoGoRing A)
          (sourceFaceNoGoRing A)))) := by
  rw [sourceFaceQuotientObservation_injective_iff]
  intro hle
  apply one_not_mem_sourceFaceNoGoLayer (A := A)
  apply hle
  change sourceFaceScalarMul (MvPolynomial.X 0 : sourceFaceNoGoRing A)
    (sourceFaceNoGoRing A) 1 ∈ sourceFaceNoGoLayer A
  exact ⟨1, rfl⟩

/-- Edge map from boundary cycles, represented upstairs, to the first Tor correction. -/
def sourceFaceHyperTorEdgeBoundary
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    sourceFaceObservationPreimage f (sourceFaceScalarLayer x N) →ₗ[A]
      regularFaceTor x (sourceFaceObservationCokernel f) 1 :=
  (sourceFaceBornGaugeEquivRegularFaceTorOne x f hx).toLinearMap.comp
    (sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
      (sourceFaceScalarLayer x N)).mkQ

/-- Kernel of the hyper-Tor edge map is exactly the inherited generic kernel plus the discarded
source layer. -/
theorem ker_sourceFaceHyperTorEdgeBoundary
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    LinearMap.ker (sourceFaceHyperTorEdgeBoundary x f hx) =
      sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N) := by
  ext y
  constructor
  · intro hy
    rw [LinearMap.mem_ker] at hy
    apply Submodule.Quotient.mk_eq_zero _ |>.1
    apply (sourceFaceBornGaugeEquivRegularFaceTorOne x f hx).injective
    change sourceFaceBornGaugeEquivRegularFaceTorOne x f hx
      ((sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N)).mkQ y) = 0 at hy
    simpa using hy
  · intro hy
    rw [LinearMap.mem_ker]
    change sourceFaceBornGaugeEquivRegularFaceTorOne x f hx
      ((sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N)).mkQ y) = 0
    have hyq : (sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N)).mkQ y = 0 :=
      Submodule.Quotient.mk_eq_zero _ |>.2 hy
    simpa only [hyq, map_zero]

/-- Every degree-one Tor correction is reached by a boundary cycle. -/
theorem sourceFaceHyperTorEdgeBoundary_surjective
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    Function.Surjective (sourceFaceHyperTorEdgeBoundary x f hx) := by
  intro t
  obtain ⟨q, rfl⟩ := (sourceFaceBornGaugeEquivRegularFaceTorOne x f hx).surjective t
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
    (sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
      (sourceFaceScalarLayer x N)) q
  exact ⟨y, rfl⟩

/-- Range of inclusion of inherited cycles. -/
theorem range_sourceFaceInheritedGauge_subtype
    (x : A) (f : M →ₗ[A] N) :
    LinearMap.range
        (sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
          (sourceFaceScalarLayer x N)).subtype =
      sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- Collapsed one-face hyper-Tor edge sequence: inherited cycles inject into all boundary cycles,
the edge map has exactly that range as kernel, and it surjects onto `Tor₁`. -/
theorem sourceFaceHyperTorEdge_exact
    (x : A) (f : M →ₗ[A] N)
    (hx : Function.Injective (sourceFaceScalarMul x N)) :
    LinearMap.range
        (sourceFaceInheritedGauge f (sourceFaceScalarLayer x M)
          (sourceFaceScalarLayer x N)).subtype =
      LinearMap.ker (sourceFaceHyperTorEdgeBoundary x f hx) ∧
    Function.Surjective (sourceFaceHyperTorEdgeBoundary x f hx) := by
  constructor
  · rw [range_sourceFaceInheritedGauge_subtype,
      ker_sourceFaceHyperTorEdgeBoundary]
  · exact sourceFaceHyperTorEdgeBoundary_surjective x f hx

/-- Degree-zero edge of the same collapsed spectral sequence. -/
def sourceFaceHyperTorDegreeZeroEdge
    (x : A) (f : M →ₗ[A] N) :
    sourceFaceBoundaryCokernel f (sourceFaceScalarLayer x M)
        (sourceFaceScalarLayer x N) (sourceFaceScalarLayer_le_comap x f) ≃ₗ[A]
      regularFaceTor x (sourceFaceObservationCokernel f) 0 :=
  sourceFaceBoundaryCokernelEquivRegularFaceTorZero x f

end

end GaloisForLFunctions.HTGeometry
