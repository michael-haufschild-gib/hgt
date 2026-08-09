import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.IncompatDerived

/-!
# Ordinary versus derived specialisation at the identity wall

At the identity fibre the ordinary image of the minimal stable boundary is zero, while the derived
fibre retains the full normal defect.  Both halves are proved here:

* `tensor_subtype_minStableBoundary_eq_zero` — the map `B_min ⊗ R⧸I → U ⊗ R⧸I` induced by the
  inclusion is zero, so ordinary specialisation sees no boundary at the identity;
* `boundaryTensorEquiv` — nevertheless `B_min ⊗ R⧸I ≅ (R⧸I)²`, the conormal module `I⧸I²` twice;
* `boundaryTensorIsoTorOne` — and this module is exactly `Tor₁(Q, R⧸I)`.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory Limits Opposite TensorProduct

universe u

section Boundary

variable {R : Type u} [CommRing R] {q c : R}

/-- **Corollary 4.2 (4.5), vanishing half.**  Tensoring the inclusion of the minimal stable
boundary with the identity fibre gives the zero map: the ordinary special fibre of the boundary
maps to zero. -/
theorem tensor_subtype_minStableBoundary_eq_zero (hc : IsUnit c) :
    TensorProduct.map ((minStableBoundary q c).subtype)
        (LinearMap.id : (R ⧸ (Ideal.span {q - 1} : Ideal R)) →ₗ[R] _) = 0 := by
  refine TensorProduct.ext' fun b y => ?_
  have hb : (b : R × R) ∈ LinearMap.range ((q - 1) • LinearMap.id : (R × R) →ₗ[R] (R × R)) := by
    rw [range_smul_id_eq_minStableBoundary hc]
    exact b.2
  obtain ⟨w, hw⟩ := hb
  have hw' : (b : R × R) = (q - 1) • w := hw.symm
  rw [TensorProduct.map_tmul, LinearMap.zero_apply, Submodule.subtype_apply, hw',
    TensorProduct.smul_tmul, LinearMap.id_apply, quotient_smul_eq_zero (q - 1) y,
    TensorProduct.tmul_zero]

variable (hc : IsUnit c) (hreg : IsSMulRegular R (q - 1))
include hc hreg

/-- The free presentation identifies the minimal stable boundary with `R²`. -/
noncomputable def freeBoundaryEquiv : (R × R) ≃ₗ[R] ↥(minStableBoundary q c) :=
  (LinearEquiv.ofInjective ((q - 1) • LinearMap.id : (R × R) →ₗ[R] (R × R))
      (fun _ _ h => isSMulRegular_prod hreg h)).trans
    (LinearEquiv.ofEq _ _ (range_smul_id_eq_minStableBoundary hc))

/-- **Corollary 4.2 (4.5), nonvanishing half.**  The derived special fibre of the boundary is the
squared conormal module `(I ⧸ I²)² ≅ (R ⧸ I)²`. -/
noncomputable def boundaryTensorEquiv :
    (↥(minStableBoundary q c) ⊗[R] (R ⧸ (Ideal.span {q - 1} : Ideal R))) ≃ₗ[R]
      ((R ⧸ (Ideal.span {q - 1} : Ideal R)) × (R ⧸ (Ideal.span {q - 1} : Ideal R))) :=
  (TensorProduct.congr (freeBoundaryEquiv hc hreg).symm (LinearEquiv.refl R _)).trans
    (((TensorProduct.prodLeft R R R R (R ⧸ (Ideal.span {q - 1} : Ideal R)))).trans
      ((TensorProduct.lid R _).prodCongr (TensorProduct.lid R _)))

/-- **Corollary 4.2 (4.5), identification.**  The special fibre of the boundary is exactly the
first derived fibre of the incompatibility module. -/
noncomputable def boundaryTensorIsoTorOne :
    ModuleCat.of R (↥(minStableBoundary q c) ⊗[R] (R ⧸ (Ideal.span {q - 1} : Ideal R))) ≅
      (((Tor' (ModuleCat.{u} R) 1).obj (ModuleCat.of R (incompatModule q c))).obj
        (ModuleCat.of R (R ⧸ (Ideal.span {q - 1} : Ideal R)))) :=
  (boundaryTensorEquiv hc hreg).toModuleIso ≪≫ (torOneIncompatIso hc hreg).symm

end Boundary

end GaloisForLFunctions.HTGeometry.DerivedSelection
