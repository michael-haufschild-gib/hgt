import GaloisForLFunctions.HTGeometry.MilnorSectionMap
import GaloisForLFunctions.HTGeometry.MilnorTotalResidueKernel
import GaloisForLFunctions.HTGeometry.RatFuncProjectiveNormalForm

/-!
# The residue at the place at infinity

The inversion `t ↦ 1/t` is an automorphism of `F(t)` over `F` carrying the place at infinity to the
place `X`, so the residue at infinity is the residue at `X` read through it.  What the norm map
needs from it is that it kills the constants, which is immediate: the inversion fixes them, and a
symbol of constants lies at the bottom of the degree filtration.

* `milnorKDegMap_comp` : functoriality of Milnor `K`-theory is composable.
* `milnorResidueInfty` : **the residue at infinity.**
* `milnorResidueInfty_const` : **it kills the constants.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- Functoriality of Milnor `K`-theory is composable. -/
theorem milnorKDegMap_comp {A B C : Type*} [Field A] [Field B] [Field C]
    (f : A →+* B) (g : B →+* C) (n : ℕ) :
    (milnorKDegMap g n).comp (milnorKDegMap f n) = milnorKDegMap (g.comp f) n := by
  refine milnorKDeg_hom_ext (F := A) fun s => ?_
  show milnorKDegMap g n (milnorKDegMap f n (milnorClassDeg A n s)) = _
  rw [milnorKDegMap_class, milnorKDegMap_class, milnorKDegMap_class]
  refine congrArg (milnorClassDeg C n) (Subtype.ext ?_)
  simp only [milnorSymbolDegMap_val, List.map_map]
  rfl

/-- The inversion `t ↦ 1/t` of the rational function field. -/
noncomputable def ratFuncInv (F : Type*) [Field F] : RatFunc F ≃ₐ[F] RatFunc F :=
  ratFuncFixedPointToInfinityEquiv (0 : F)

theorem ratFuncConstHom_eq_algebraMap (a : F) :
    ratFuncConstHom (F := F) a = algebraMap F (RatFunc F) a := rfl

theorem ratFuncInv_comp_const :
    ((ratFuncInv F).toRingEquiv.toRingHom).comp (ratFuncConstHom (F := F))
      = ratFuncConstHom (F := F) := by
  refine RingHom.ext fun a => ?_
  show ratFuncInv F (ratFuncConstHom (F := F) a) = ratFuncConstHom (F := F) a
  rw [ratFuncConstHom_eq_algebraMap]
  exact (ratFuncInv F).commutes a

/-- A symbol of constants lies at the bottom of the degree filtration. -/
theorem range_milnorKDegMap_const_le (n : ℕ) :
    AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n)
      ≤ degreeFiltration (F := F) 0 n := by
  rintro x ⟨y, rfl⟩
  have hcom : y ∈ AddSubgroup.comap (milnorKDegMap (ratFuncConstHom (F := F)) n)
      (degreeFiltration (F := F) 0 n) := by
    refine milnorKDeg_mem_of_gen _ (fun s => ?_) y
    show milnorKDegMap (ratFuncConstHom (F := F)) n (milnorClassDeg F n s)
      ∈ degreeFiltration (F := F) 0 n
    rw [milnorKDegMap_class]
    refine AddSubgroup.subset_closure ⟨_, ?_, rfl⟩
    intro a ha
    rw [milnorSymbolDegMap_val] at ha
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 ha
    refine ⟨Polynomial.C (c : F), ?_, by simp, ?_⟩
    · simp
    · exact Units.ext rfl
  exact hcom

/-- **The residue at the place at infinity**, read through the inversion `t ↦ 1/t`. -/
noncomputable def milnorResidueInfty (n : ℕ) :
    MilnorKDeg (RatFunc F) (n + 1) →+ MilnorKDeg F n :=
  (milnorKDegMap (polyPlaceXResidueEquiv (F := F) : _ →+* F) n).comp
    ((milnorResidue (polyResidueData (Polynomial.irreducible_X (R := F))) (n + 1)).comp
      (milnorKDegMap ((ratFuncInv F).toRingEquiv.toRingHom) (n + 1)))

/-- **The residue at infinity kills the constants.** -/
theorem milnorResidueInfty_const (n : ℕ) (z : MilnorKDeg F (n + 1)) :
    milnorResidueInfty n (milnorKDegMap (ratFuncConstHom (F := F)) (n + 1) z) = 0 := by
  have hσ : milnorKDegMap ((ratFuncInv F).toRingEquiv.toRingHom) (n + 1)
      (milnorKDegMap (ratFuncConstHom (F := F)) (n + 1) z)
      = milnorKDegMap (ratFuncConstHom (F := F)) (n + 1) z := by
    have := milnorKDegMap_comp (ratFuncConstHom (F := F))
      ((ratFuncInv F).toRingEquiv.toRingHom) (n + 1)
    have h2 := congrArg (fun f : MilnorKDeg F (n + 1) →+ MilnorKDeg (RatFunc F) (n + 1) => f z) this
    rw [ratFuncInv_comp_const] at h2
    exact h2
  show (milnorKDegMap (polyPlaceXResidueEquiv (F := F) : _ →+* F) n)
    ((milnorResidue (polyResidueData (Polynomial.irreducible_X (R := F))) (n + 1))
      (milnorKDegMap ((ratFuncInv F).toRingEquiv.toRingHom) (n + 1)
        (milnorKDegMap (ratFuncConstHom (F := F)) (n + 1) z))) = 0
  rw [hσ]
  have hzero : milnorResidue (polyResidueData (Polynomial.irreducible_X (R := F))) (n + 1)
      (milnorKDegMap (ratFuncConstHom (F := F)) (n + 1) z) = 0 := by
    refine polyResidue_degreeFiltration_eq_zero (Polynomial.irreducible_X (R := F))
      (d := 0) (by rw [Polynomial.natDegree_X]; omega) _ ?_
    exact range_milnorKDegMap_const_le (n + 1) ⟨z, rfl⟩
  rw [hzero]
  exact map_zero _

end GaloisForLFunctions.HTGeometry
