import GaloisForLFunctions.RHTower.DeningerPolarizationAlmostProjection
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The completed Arakelov trace kernel

The finite-plus-real boundary of a Kummer unit and a mean-zero collar form is the pair consisting
of its valuation-plus-residue and of minus the weighted degree of its valuation.  The Arakelov
trace adds the weighted degree of the finite part to the real part.  The composite vanishes by
construction, and conversely every element of the trace kernel is hit: split the finite part into
its scalar and mean-zero components, take the unit with the prescribed valuation and a collar form
with the prescribed residue, and the real component is forced.

So the boundary has image exactly the trace kernel, the trace is onto, and the top cohomology of
the shifted residue fibre is the real orientation line.  The boundary is injective as soon as the
residue is, which is the case on the summand chosen by the collar section.

* `deningerCollarArakelovBoundary`, `deningerCollarArakelovTrace` : `(9)`--`(10)`.
* `deningerCollarArakelovTrace_comp_boundary` : the composite vanishes.
* `deningerCollarArakelovBoundary_exact` : the image is the trace kernel, `(11)`.
* `deningerCollarArakelovH2Equiv` : `(12)`, the top cohomology is the orientation line.
-/

namespace RHTower

section TraceKernel

variable {R U C Bval Bpkt : Type*} [CommRing R]
variable [AddCommGroup U] [Module R U] [AddCommGroup C] [Module R C]
variable [AddCommGroup Bval] [Module R Bval] [AddCommGroup Bpkt] [Module R Bpkt]

/-- **The finite-plus-real boundary `(9)`.**  A Kummer unit contributes its valuation and minus the
weighted degree of that valuation; a mean-zero collar form contributes its residue. -/
def deningerCollarArakelovBoundary (ord : U →ₗ[R] Bval) (rho : C →ₗ[R] Bpkt) (W : Bval →ₗ[R] R) :
    (U × C) →ₗ[R] ((Bval × Bpkt) × R) where
  toFun q := ((ord q.1, rho q.2), -W (ord q.1))
  map_add' q q' := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · show ord (q.1 + q'.1) = ord q.1 + ord q'.1
      rw [map_add]
    · show rho (q.2 + q'.2) = rho q.2 + rho q'.2
      rw [map_add]
    · show -W (ord (q.1 + q'.1)) = -W (ord q.1) + -W (ord q'.1)
      rw [map_add, map_add, neg_add]
  map_smul' c q := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · show ord (c • q.1) = c • ord q.1
      rw [map_smul]
    · show rho (c • q.2) = c • rho q.2
      rw [map_smul]
    · show -W (ord (c • q.1)) = c • -W (ord q.1)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_neg]

@[simp]
theorem deningerCollarArakelovBoundary_apply (ord : U →ₗ[R] Bval) (rho : C →ₗ[R] Bpkt)
    (W : Bval →ₗ[R] R) (u : U) (w : C) :
    deningerCollarArakelovBoundary ord rho W (u, w) = ((ord u, rho w), -W (ord u)) := rfl

/-- **The Arakelov trace `(10)`.**  The weighted degree of the finite scalar part plus the real
part. -/
def deningerCollarArakelovTrace (W : Bval →ₗ[R] R) : ((Bval × Bpkt) × R) →ₗ[R] R where
  toFun z := W z.1.1 + z.2
  map_add' z z' := by
    show W (z.1.1 + z'.1.1) + (z.2 + z'.2) = (W z.1.1 + z.2) + (W z'.1.1 + z'.2)
    rw [map_add]
    ring
  map_smul' c z := by
    show W (c • z.1.1) + c • z.2 = c • (W z.1.1 + z.2)
    rw [map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

@[simp]
theorem deningerCollarArakelovTrace_apply (W : Bval →ₗ[R] R) (d : Bval) (c : Bpkt) (x : R) :
    deningerCollarArakelovTrace (Bpkt := Bpkt) W ((d, c), x) = W d + x := rfl

/-- **The trace kills the boundary.** -/
theorem deningerCollarArakelovTrace_comp_boundary (ord : U →ₗ[R] Bval) (rho : C →ₗ[R] Bpkt)
    (W : Bval →ₗ[R] R) :
    (deningerCollarArakelovTrace (Bpkt := Bpkt) W).comp (deningerCollarArakelovBoundary ord rho W) = 0 := by
  refine LinearMap.ext fun q => ?_
  show W (ord q.1) + -W (ord q.1) = 0
  rw [add_neg_cancel]

/-- **`(11)`: the boundary image is exactly the trace kernel.**  Split the finite part into scalar
and mean-zero components, choose a unit with the prescribed valuation and a collar form with the
prescribed residue; the trace-kernel identity forces the real component. -/
theorem deningerCollarArakelovBoundary_exact {ord : U →ₗ[R] Bval} {rho : C →ₗ[R] Bpkt}
    (W : Bval →ₗ[R] R) (hord : Function.Surjective ord) (hrho : Function.Surjective rho) :
    Function.Exact (deningerCollarArakelovBoundary ord rho W) (deningerCollarArakelovTrace (Bpkt := Bpkt) W) := by
  intro z
  constructor
  · intro hz
    obtain ⟨⟨d, c⟩, x⟩ := z
    have hx : W d + x = 0 := hz
    obtain ⟨u, rfl⟩ := hord d
    obtain ⟨w, rfl⟩ := hrho c
    refine ⟨(u, w), ?_⟩
    refine Prod.ext rfl ?_
    show -W (ord u) = x
    exact neg_eq_of_add_eq_zero_right hx
  · rintro ⟨q, rfl⟩
    exact LinearMap.congr_fun (deningerCollarArakelovTrace_comp_boundary ord rho W) q

/-- **The trace is onto**: the real orientation line is realized by the real component alone. -/
theorem deningerCollarArakelovTrace_surjective (W : Bval →ₗ[R] R) :
    Function.Surjective (deningerCollarArakelovTrace (Bval := Bval) (Bpkt := Bpkt) W) := by
  intro x
  refine ⟨((0, 0), x), ?_⟩
  show W 0 + x = x
  rw [map_zero, zero_add]

/-- **The boundary is injective** as soon as the valuation and the residue are, which is the case
on the summand chosen by the collar section. -/
theorem deningerCollarArakelovBoundary_injective {ord : U →ₗ[R] Bval} {rho : C →ₗ[R] Bpkt}
    (W : Bval →ₗ[R] R) (hord : Function.Injective ord) (hrho : Function.Injective rho) :
    Function.Injective (deningerCollarArakelovBoundary ord rho W) := by
  intro q q' hq
  have h1 : ord q.1 = ord q'.1 := congrArg (fun z => z.1.1) hq
  have h2 : rho q.2 = rho q'.2 := congrArg (fun z => z.1.2) hq
  exact Prod.ext (hord h1) (hrho h2)

/-- **`(12)`: the top cohomology of the shifted residue fibre is the real orientation line.** -/
noncomputable def deningerCollarArakelovH2Equiv {ord : U →ₗ[R] Bval} {rho : C →ₗ[R] Bpkt}
    (W : Bval →ₗ[R] R) (hord : Function.Surjective ord) (hrho : Function.Surjective rho) :
    (((Bval × Bpkt) × R) ⧸ LinearMap.range (deningerCollarArakelovBoundary ord rho W)) ≃ₗ[R] R :=
  (deningerCollarArakelovBoundary_exact W hord hrho).linearEquivOfSurjective
    (deningerCollarArakelovTrace_surjective W)

end TraceKernel

section CollarSection

variable {R C Bpkt : Type*} [CommRing R]
variable [AddCommGroup C] [Module R C] [AddCommGroup Bpkt] [Module R Bpkt]

/-- **The collar section splits the residue `(4)`.**  A surjection with a linear right inverse has
complemented kernel; this is the algebraic content of strictness with closed kernel. -/
theorem deningerCollarSection_isCompl (s : Bpkt →ₗ[R] C) (rho : C →ₗ[R] Bpkt)
    (h : rho ∘ₗ s = LinearMap.id) :
    IsCompl (LinearMap.ker (deningerLeg s rho)) (LinearMap.range s) :=
  deningerExactLeg_isCompl h

/-- On the chosen collar summand the residue is injective, which is what makes the boundary
injective. -/
theorem deningerCollarSection_injective (s : Bpkt →ₗ[R] C) (rho : C →ₗ[R] Bpkt)
    (h : rho ∘ₗ s = LinearMap.id) : Function.Injective (rho ∘ₗ s) := by
  rw [h]
  exact fun _ _ hxy => hxy

end CollarSection

end RHTower
