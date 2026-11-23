import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FinitePullbackNormalization
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Transitivity of normalization along a tower of function fields. -/

noncomputable section

open GlobalTheory.PD

namespace GlobalTheory.SchemeCohomology

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]

/-- Normalizing the image of an already normalized chart gives the
normalization in the upper function field. -/
theorem pullbackChartAlgebra_rB {d : ℕ} (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) :
    pullbackChartAlgebra (IsScalarTower.toAlgHom k E L) (rB k E x I) = rB k L x I := by
  let A := rA k x I
  let B := rB k E x I
  let j := IsScalarTower.toAlgHom k E L
  let S := B.map j
  let j' : E →ₐ[A] L := {
    toRingHom := j.toRingHom
    commutes' := fun a => (IsScalarTower.algebraMap_apply F E L (a : F)).symm }
  let i : A →+* S := (algebraMap A L).codRestrict S (fun a => by
    refine ⟨algebraMap A E a, isIntegral_algebraMap, ?_⟩
    exact j'.commutes a)
  letI : Algebra A S := i.toAlgebra
  letI : IsScalarTower A S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let v : S →ₐ[A] L := { toRingHom := S.val.toRingHom, commutes' := fun _ => rfl }
  letI : Algebra.IsIntegral A S := ⟨fun z => by
    have hz : (z : L) ∈ B.map j := z.2
    obtain ⟨b, hb, e⟩ := Subalgebra.mem_map.mp hz
    apply (isIntegral_algHom_iff v Subtype.val_injective).mp
    change IsIntegral A (z : L)
    rw [← e]
    exact (hb : IsIntegral A b).map j'⟩
  apply SetLike.ext
  intro z
  change IsIntegral S z ↔ IsIntegral A z
  exact ⟨isIntegral_trans z, fun h => h.tower_top⟩

end GlobalTheory.SchemeCohomology
