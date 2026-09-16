import GaloisForLFunctions.RHTower.SelbergMaassMackeyTraceComposition

/-!
# Mackey product formula for rational Maass traces

The composition of two source-attached rational principal traces is a finite
Mackey sum.  The inner trace base-changes through the second rational pullback,
and the resulting outer trace decomposes over the relevant double cosets.
The source group of those blocks is the conjugate by the product matrix, by
`rationalPullbackConjugateGroup_mul`.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- The composition of two rational principal traces is the Mackey sum of the
finite blocks induced by the base-changed inner trace. -/
theorem rationalPrincipalTrace_mackey_baseChange
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let f0 := rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f
    let fG := rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h f0
    let J := (principalCongruenceGL N).subgroupOf H
    let T := J.map H.subtype
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI : G.IsFiniteRelIndex H :=
      rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g)
        (principalCongruenceGL N) h
    letI : H.IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N h
    letI : T.IsFiniteRelIndex (principalCongruenceGL N) := by
      rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
      have hsub : T.subgroupOf (principalCongruenceGL N) =
          H.subgroupOf (principalCongruenceGL N) := by
        apply (Subgroup.map_subtype_inj).mp
        rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        simp only [T, J, Subgroup.subgroupOf_map_subtype]
        rw [inf_comm (principalCongruenceGL N) H, inf_assoc, inf_idem]
      rw [hsub]
      exact Subgroup.finiteIndex_of_finite_quotient
    let Ω := Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))
    letI : Fintype Ω := maassTraceDoubleCosetOrbitFintype G H J
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) h
        (maassTraceInvariant (H := principalCongruenceGL N) f0)) =
      ∑ q : Ω,
        (maassDoubleCosetBlockTraceToInvariant G H (principalCongruenceGL N) J q.out.out
          (by
            rintro x ⟨j, hj, rfl⟩
            exact hj) fG).1 := by
  dsimp only
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let f0 : glUpperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) :=
    rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f
  let fG : glUpperHalfPlaneInvariantFunctions G :=
    rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h f0
  let J : Subgroup H := (principalCongruenceGL N).subgroupOf H
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g)
      (principalCongruenceGL N) h
  letI : H.IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N h
  have hsub : T.subgroupOf (principalCongruenceGL N) =
      H.subgroupOf (principalCongruenceGL N) := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [T, J, Subgroup.subgroupOf_map_subtype]
    rw [inf_comm (principalCongruenceGL N) H, inf_assoc, inf_idem]
  letI : T.IsFiniteRelIndex (principalCongruenceGL N) := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : Fintype (Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :=
    maassTraceDoubleCosetOrbitFintype G H J
  have hbase : maassTraceFunction (H := H) fG =
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) h
        (maassTraceInvariant (H := principalCongruenceGL N) f0)).1 := by
    simpa only [H, G, fG, f0] using
      (maassTrace_rationalPullback_baseChange (rationalConjugateGroup N g)
        (principalCongruenceGL N) h f0)
  have hbaseInv : maassTraceInvariant (H := H) fG =
      rationalMaassPullbackInvariant_general (principalCongruenceGL N) h
        (maassTraceInvariant (H := principalCongruenceGL N) f0) := by
    apply Subtype.ext
    exact hbase
  calc
    maassTraceFunction (H := principalCongruenceGL N)
        (rationalMaassPullbackInvariant_general (principalCongruenceGL N) h
          (maassTraceInvariant (H := principalCongruenceGL N) f0)) =
        maassTraceFunction (H := principalCongruenceGL N)
          (maassTraceInvariant (H := H) fG) := by
      rw [hbaseInv]
    _ = _ := maassTrace_mackey_compose_subgroupOf G H (principalCongruenceGL N) fG

end

end GaloisForLFunctions.RHTower
