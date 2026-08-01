import GaloisForLFunctions.RHTower.DeningerArithmeticThreeTermCohomology
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The shifted residue fibre and its global sections

Two statements about the fibre of a residue map into a once-shifted boundary object.

Globally: taking sections is a right adjoint, so it preserves the limit that defines the fibre.
In the additive setting this is the statement that the sections of a kernel are the kernel of the
induced map, which is what the global-section equivalence asserts.

Locally: if the source has cohomology concentrated in degrees `0, 1` and the boundary object sits
in degree `0`, then a map into its `[-1]` shift has a single component `∂¹` subject to
`∂¹ ∘ d = 0`, and the fibre totalizes to the three-term complex `A⁰ → A¹ → D`.  Its cohomology is
`ker d`, `ker ∂¹ / im d` and `D / im ∂¹`, and it is concentrated in degrees `0, 1, 2` because the
totalization has no other terms.  The comparison with the source is exact: the middle cohomology
of the fibre is the kernel of the residue induced on the source cokernel, and the top cohomology is
its cokernel.  If the residue image is exactly the kernel of a surjective trace, the top cohomology
is the trace line.

* `deningerGlobalSectionsFiberIso` : sections preserve the fibre.
* `deningerShiftedFiberComplex` : the totalization `(9)`--`(10)`.
* `deningerShiftedFiber_cycles0_eq`, `_cycles1_eq`, `_boundaries1_eq`, `_boundaries2_eq` : `(11)`.
* `deningerShiftedFiber_inducedResidue_ker`, `_range` : the exact comparison with the source.
* `deningerShiftedFiber_H2Equiv_of_trace` : the trace-kernel endpoint.
-/

namespace RHTower

section GlobalSections

open CategoryTheory CategoryTheory.Limits

/-- **Sections preserve the fibre.**  Derived global sections are a right adjoint, and a fibre is a
finite limit, so the sections of the fibre are the fibre of the sections.  In the additive setting
the limit in question is a kernel. -/
noncomputable def deningerGlobalSectionsFiberIso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : D ⥤ C) (L : C ⥤ D) (adj : L ⊣ F)
    [F.PreservesZeroMorphisms] {X Y : D} (f : X ⟶ Y) [HasKernel f] [HasKernel (F.map f)] :
    F.obj (kernel f) ≅ kernel (F.map f) :=
  haveI := adj.rightAdjoint_preservesLimits
  PreservesKernel.iso F f

end GlobalSections

section ShiftedTotalization

variable {R A0 A1 D : Type*} [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup D] [Module R D]

/-- **The totalization of the shifted residue fibre.**  The target sits in degree two, so the fibre
of a residue map out of a two-term source is the three-term complex `A⁰ → A¹ → D`. -/
def deningerShiftedFiberComplex (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) : DeningerArithmeticThreeTermComplex R A0 A1 D where
  d0 := dA
  d1 := res
  d1_comp_d0 := h

@[simp]
theorem deningerShiftedFiber_d0 (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D) (h : res.comp dA = 0) :
    (deningerShiftedFiberComplex dA res h).d0 = dA := rfl

@[simp]
theorem deningerShiftedFiber_d1 (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D) (h : res.comp dA = 0) :
    (deningerShiftedFiberComplex dA res h).d1 = res := rfl

/-- Degree-zero cohomology of the fibre is the kernel of the source differential. -/
theorem deningerShiftedFiber_cycles0_eq (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) :
    (deningerShiftedFiberComplex dA res h).cycles0 = LinearMap.ker dA := rfl

/-- Degree-one cocycles of the fibre are the residue kernel. -/
theorem deningerShiftedFiber_cycles1_eq (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) :
    (deningerShiftedFiberComplex dA res h).cycles1 = LinearMap.ker res := rfl

/-- Degree-one boundaries of the fibre are the image of the source differential. -/
theorem deningerShiftedFiber_boundaries1_eq (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) :
    (deningerShiftedFiberComplex dA res h).boundaries1 = LinearMap.range dA := rfl

/-- Degree-two boundaries of the fibre are the residue image, so top cohomology is its cokernel. -/
theorem deningerShiftedFiber_boundaries2_eq (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) :
    (deningerShiftedFiberComplex dA res h).boundaries2 = LinearMap.range res := rfl

/-- The residue descends to the cokernel of the source differential. -/
def deningerInducedResidue (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D) (h : res.comp dA = 0) :
    (A1 ⧸ LinearMap.range dA) →ₗ[R] D :=
  (LinearMap.range dA).liftQ res (by
    rintro _ ⟨a, rfl⟩
    exact LinearMap.congr_fun h a)

@[simp]
theorem deningerInducedResidue_mk (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D) (h : res.comp dA = 0)
    (x : A1) :
    deningerInducedResidue dA res h (Submodule.Quotient.mk x) = res x := rfl

/-- **The middle comparison.**  The kernel of the induced residue on the source cokernel is the
image of the residue kernel, which is the middle cohomology of the fibre. -/
theorem deningerShiftedFiber_inducedResidue_ker (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) :
    LinearMap.ker (deningerInducedResidue dA res h)
      = Submodule.map (LinearMap.range dA).mkQ (LinearMap.ker res) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range dA) q
    refine ⟨x, ?_, rfl⟩
    exact hq
  · rintro _ ⟨x, hx, rfl⟩
    exact hx

/-- **The top comparison.**  The induced residue has the same image as the residue, so the top
cohomology of the fibre is its cokernel. -/
theorem deningerShiftedFiber_inducedResidue_range (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) :
    LinearMap.range (deningerInducedResidue dA res h) = LinearMap.range res :=
  Submodule.range_liftQ _ _ _

/-- **The trace-kernel endpoint.**  If the residue image is exactly the kernel of a surjective
trace, the top cohomology of the fibre is the trace line. -/
noncomputable def deningerShiftedFiber_H2Equiv_of_trace (dA : A0 →ₗ[R] A1) (res : A1 →ₗ[R] D)
    (h : res.comp dA = 0) (tr : D →ₗ[R] R) (hexact : Function.Exact res tr)
    (hsurj : Function.Surjective tr) :
    (deningerShiftedFiberComplex dA res h).H2 ≃ₗ[R] R :=
  hexact.linearEquivOfSurjective hsurj

end ShiftedTotalization

end RHTower
