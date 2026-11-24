import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginFormCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginDifferentialRows
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! On the exterior powers, the entries of the pullback matrix in
origin coordinates are the corresponding ordered minors. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GaloisForLFunctions.HTGeometry
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E L : Type} [Field k] [CharZero k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k F L]
  {d p : ℕ} {x : Fin (d + 1) → F}

local notation "P" => Set.powersetCard (Fin d) p

/-- An entry of the exterior matrix is the minor with the selected
source rows and target columns. -/
def originExteriorEntry {R : Type*} [CommRing R] (A : Matrix (Fin d) (Fin d) R)
    (I J : P) : R :=
  (A.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)).det

theorem map_originExteriorEntry {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin d) (Fin d) R) (I J : P) :
    f (originExteriorEntry A I J) = originExteriorEntry (A.map f) I J := f.map_det _

/-- Each affine coordinate basis wedge pulls back through the first map
to the same basis wedge in the extension. -/
theorem pullbackDR_originCoordinateForm [Algebra E L] [IsScalarTower k E L]
    [IsScalarTower F E L] (I : P) :
    pullbackDR (IsScalarTower.toAlgHom k E L) (originCoordinateForm k E x I : DR k E) =
      (originCoordinateForm k L x I : DR k L) := by
  simp only [originCoordinateForm, exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe,
    pullbackDR_wedge, Function.comp_apply, algHomKaehlerMap_D, IsScalarTower.coe_toAlgHom',
    ← IsScalarTower.algebraMap_apply]
  rfl

omit [CharZero k] [IsScalarTower k F E] in
/-- The coefficients of the pulled-back wedge are the minors of the
matrix of the pulled-back one-forms. -/
theorem IsFinCover.pullbackDR_originCoordinateForm_eq_sum
    (h : IsFinCover k L x) (f : E →ₐ[k] L) (A : Matrix (Fin d) (Fin d) L)
    (hA : ∀ j, D k L (f (algebraMap F E (x j.succ / x 0))) =
      ∑ l, A j l • D k L (algebraMap F L (x l.succ / x 0))) (I : P) :
    pullbackDR f (originCoordinateForm k E x I : DR k E) =
      ∑ J : P, originExteriorEntry A I J • (originCoordinateForm k L x J : DR k L) := by
  let r := Set.powersetCard.ofFinEmbEquiv.symm I
  let v (i : Fin p) := D k L (f (algebraMap F E (x (r i).succ / x 0)))
  obtain ⟨b, hb⟩ := h.exists_coordinateDifferentialBasis
  have hbv (i : Fin p) : v i = ∑ l, A (r i) l • b l := by
    simpa only [v, hb] using hA (r i)
  let e := b.exteriorPower p
  have hcoef (J : P) : e.repr (exteriorPower.ιMulti L p v) J = originExteriorEntry A I J := by
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    change b.coord (J.1.orderEmbOfFin J.2 j) (v i) = A (r i) (J.1.orderEmbOfFin J.2 j)
    rw [hbv, map_sum]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, mul_ite]
  have hbJ (J : P) : e J = originCoordinateForm k L x J := by
    rw [exteriorPower.basis_apply, originCoordinateForm]
    exact congrArg (fun w : Fin d → Ω[L⁄k] => exteriorPower.ιMulti_family L p w J) (funext hb)
  have he : exteriorPower.ιMulti L p v =
      ∑ J : P, originExteriorEntry A I J • originCoordinateForm k L x J := by
    simpa only [hcoef, hbJ] using (e.sum_repr (exteriorPower.ιMulti L p v)).symm
  have hpull : pullbackDR f (originCoordinateForm k E x I : DR k E) =
      (exteriorPower.ιMulti L p v : DR k L) := by
    simp only [originCoordinateForm, exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe,
      pullbackDR_wedge, Function.comp_apply, algHomKaehlerMap_D, v, r]
  rw [hpull, he]
  simp only [Submodule.coe_sum, Submodule.coe_smul]

omit [CharZero k] [Field F] [Field E] [Field L] [Algebra k F] [Algebra k E]
    [Algebra k L] [Algebra F E] [Algebra F L] [IsScalarTower k F E] [IsScalarTower k F L] in
/-- The sum of the diagonal entries of the exterior matrix is the
coefficient of the determinant polynomial in its exterior degree. -/
theorem sum_originExteriorEntry_eq_coeff {R : Type*} [CommRing R]
    (A : Matrix (Fin d) (Fin d) R) :
    (∑ I : P, originExteriorEntry A I I) =
      (1 + (Polynomial.X : Polynomial R) • A.map Polynomial.C).det.coeff p := by
  classical
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.sum_subtype (p := fun I : Finset (Fin d) => I.card = p) _
      (fun I => by simp [Finset.mem_powersetCard])]
  refine Finset.sum_congr rfl fun I _ => ?_
  exact Matrix.det_submatrix_equiv_self (I.1.orderIsoOfFin I.2).toEquiv
    (A.submatrix (Subtype.val : I.1 → Fin d) Subtype.val)

end GlobalTheory.PD
