import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionScalarChange
import Mathlib.Algebra.BigOperators.Pi

/-! Global section coordinates are linear over the base ring. A basis of
global sections gives unique simultaneous expansions on the bundle charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Spec (.of R)) {L : LB Y}

/-- A global section's coefficient in a fixed chart is linear in base scalars. -/
def globalChartLinearMap (i : L.ι) :
    letI := sectionBaseModule g (toMod L) ⊤
    letI := sectionAlgebra g (L.U i)
    Γ(toMod L, ⊤) →ₗ[R] Γ(Y, L.U i) := by
  letI := sectionBaseModule g (toMod L) ⊤
  letI := sectionAlgebra g (L.U i)
  let j : L.U i ≤ (⊤ : Y.Opens) ⊓ L.U i := le_inf le_top le_rfl
  refine
    { toFun := fun x => (globalCoordinates x).f i
      map_add' := fun x y => (congrArg (resG Y j) (coord_add x y i)).trans (map_add _ _ _)
      map_smul' := fun r x => ?_ }
  letI := sectionAlgebra g (⊤ : Y.Opens)
  change resG Y j (coord ((algebraMap R Γ(Y, ⊤) r) • x) i) =
    (algebraMap R Γ(Y, L.U i) r) * resG Y j (coord x i)
  rw [coord_smul, map_mul, resG_resG]
  exact congrArg (· * resG Y j (coord x i)) ((sectionRes g (homOfLE le_top)).commutes r)

private theorem coordinates_injective {s t : L.Sec} (h : s.f = t.f) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- The same unique coefficient vector expands a section in every chart. -/
theorem existsUnique_chart_coefficients {m : ℕ} :
    letI := sectionBaseModule g (toMod L) ⊤
    ∀ (E : (Fin m → R) ≃ₗ[R] Γ(toMod L, ⊤)) (s : L.Sec),
      ∃! a : Fin m → R, ∀ i,
        letI := sectionAlgebra g (L.U i)
        s.f i = ∑ k, algebraMap R Γ(Y, L.U i) (a k) * (globalCoordinates (E (Pi.single k 1))).f i := by
  letI := sectionBaseModule g (toMod L) ⊤
  intro E s
  let b := E.symm (globalCoordinates.symm s)
  have hb : globalCoordinates (E b) = s :=
    (congrArg globalCoordinates (E.apply_symm_apply _)).trans (Equiv.apply_symm_apply _ _)
  have hcoord (a : Fin m → R) (i : L.ι) :
      letI := sectionAlgebra g (L.U i)
      (globalCoordinates (E a)).f i =
        ∑ k, algebraMap R Γ(Y, L.U i) (a k) * (globalCoordinates (E (Pi.single k 1))).f i := by
    letI := sectionAlgebra g (L.U i)
    let A := globalChartLinearMap g i
    have he := congrArg (fun v => A (E v)) (pi_eq_sum_univ' a)
    simp only [map_sum] at he
    refine he.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact (congrArg A (E.map_smul (a k) (Pi.single k 1))).trans
      ((A.map_smul (a k) (E (Pi.single k 1))).trans (Algebra.smul_def _ _))
  refine ⟨b, fun i => (congrArg (fun t : L.Sec => t.f i) hb).symm.trans (hcoord b i), fun a ha => ?_⟩
  apply E.injective
  apply globalCoordinates.injective
  exact (coordinates_injective (funext fun i => (hcoord a i).trans (ha i).symm)).trans hb.symm

end GlobalTheory.LineBundleSections
