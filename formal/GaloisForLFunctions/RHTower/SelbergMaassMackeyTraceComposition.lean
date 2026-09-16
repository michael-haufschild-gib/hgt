import GaloisForLFunctions.RHTower.SelbergMaassDoubleCosetOperator

/-!
# Mackey composition for finite Maass traces

A trace from `G` to `H`, restricted to a subgroup of `H`, decomposes into
its double-coset blocks.  A second trace to an outer target flattens every
block by nested trace transitivity.  This gives the exact finite Mackey
composition formula needed to compose rational Maass correspondences.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- Restrict an invariant function along a subgroup inclusion. -/
def maassInvariantRestrict
    {G H : Subgroup (GL (Fin 2) ℝ)} (hGH : G ≤ H)
    (f : glUpperHalfPlaneInvariantFunctions H) :
    glUpperHalfPlaneInvariantFunctions G :=
  ⟨f.1, fun γ z => f.2 ⟨γ.val, hGH γ.2⟩ z⟩

/-- The image in the ambient matrix group of a subgroup of `H` lies in `H`. -/
theorem maassDoubleCosetTarget_le
    {H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H) :
    J.map H.subtype ≤ H := by
  rintro x ⟨j, hj, rfl⟩
  exact j.2

/-- A relative-coset trace summand evaluates an invariant function at the
canonical outer representative. -/
theorem maassTraceQuotientFunc_eq_out
    {T K : Subgroup (GL (Fin 2) ℝ)}
    (F : glUpperHalfPlaneInvariantFunctions T)
    [T.IsFiniteRelIndex K] (q : K ⧸ T.subgroupOf K) (z : ℍ) :
    maassTraceQuotientFunc (G := T) (H := K) F q z = F.1 (q.out.val⁻¹ • z) := by
  induction q using Quotient.inductionOn with
  | h k =>
    rw [maassTraceQuotientFunc_mk]
    let q0 : K := (QuotientGroup.mk k : K ⧸ T.subgroupOf K).out
    have hq_mem : q0⁻¹ * k ∈ T.subgroupOf K := by
      apply QuotientGroup.eq.mp
      exact Quotient.out_eq' (QuotientGroup.mk k)
    let hq : T.subgroupOf K := ⟨q0⁻¹ * k, hq_mem⟩
    let hqT : T := ⟨hq.1, hq.2⟩
    let hqK : K := ⟨hq.1, hq.1.2⟩
    have hq_eq : k = q0 * hqK := by
      apply Subtype.ext
      simp [hqK, hq]
    change F.1 (k.val⁻¹ • z) = F.1 (q0.val⁻¹ • z)
    rw [hq_eq]
    change F.1 ((q0.val * hqK.val)⁻¹ • z) = F.1 (q0.val⁻¹ • z)
    rw [_root_.mul_inv_rev, mul_smul]
    exact F.2 ⟨hqT⁻¹, T.inv_mem hqT.2⟩ _

/-- **Mackey trace composition.** First trace from `G` to `H`, restrict the result to the
image of `J`, then trace to `K`.  The result is the finite sum of the direct outer traces of
all stabilized double-coset pullbacks. -/
theorem maassTrace_mackey_compose
    (G H K : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (hTK : J.map H.subtype ≤ K) [(J.map H.subtype).IsFiniteRelIndex K]
    (f : glUpperHalfPlaneInvariantFunctions G) :
    let Ω := Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))
    letI : Fintype Ω := maassTraceDoubleCosetOrbitFintype G H J
    maassTraceFunction (H := K)
      (maassInvariantRestrict (maassDoubleCosetTarget_le J)
        (maassTraceInvariant (H := H) f)) =
      ∑ q : Ω, (maassDoubleCosetBlockTraceToInvariant G H K J q.out.out hTK f).1 := by
  dsimp only
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  letI : Fintype (Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :=
    maassTraceDoubleCosetOrbitFintype G H J
  letI : Fintype (K ⧸ T.subgroupOf K) := Fintype.ofFinite _
  funext z
  unfold maassTraceFunction
  calc
    (∑ p : K ⧸ T.subgroupOf K,
        maassTraceQuotientFunc
          (maassInvariantRestrict (maassDoubleCosetTarget_le J)
            (maassTraceInvariant (H := H) f)) p z) =
        ∑ p : K ⧸ T.subgroupOf K,
          maassTraceFunction (H := H) f (p.out.val⁻¹ • z) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [maassTraceQuotientFunc_eq_out
        (maassInvariantRestrict (maassDoubleCosetTarget_le J)
          (maassTraceInvariant (H := H) f)) p z]
      rfl
    _ =
        ∑ p : K ⧸ T.subgroupOf K,
          ∑ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
            maassDoubleCosetBlockTraceFunction G H J q.out.out f
              (p.out.val⁻¹ • z) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact maassTraceFunction_eq_sum_doubleCosetBlockTraceFunctions G H J f
        (p.out.val⁻¹ • z)
    _ =
        ∑ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
          ∑ p : K ⧸ T.subgroupOf K,
            maassDoubleCosetBlockTraceFunction G H J q.out.out f
              (p.out.val⁻¹ • z) := by
      exact Finset.sum_comm
    _ =
        ∑ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
          maassTraceFunction (H := K)
            (maassDoubleCosetBlockTraceInvariant G H J q.out.out f) z := by
      apply Finset.sum_congr rfl
      intro q hq
      symm
      unfold maassTraceFunction
      apply Finset.sum_congr rfl
      intro p hp
      rw [maassTraceQuotientFunc_eq_out
        (maassDoubleCosetBlockTraceInvariant G H J q.out.out f) p z]
      rfl
    _ =
        ∑ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
          (maassDoubleCosetBlockTraceToInvariant G H K J q.out.out hTK f).1 z := by
      apply Finset.sum_congr rfl
      intro q hq
      exact congrFun (maassTrace_block_then_outer_eq_direct G H K J q.out.out hTK f) z
    _ = _ := by
      simp only [Finset.sum_apply]

/-- The relative-coset quotient depends only on its subgroup of the target. -/
noncomputable def maassRelativeCosetEquivOfEq
    {G H K : Subgroup (GL (Fin 2) ℝ)}
    (hGH : G.subgroupOf K = H.subgroupOf K) :
    K ⧸ (G.subgroupOf K) ≃ K ⧸ (H.subgroupOf K) :=
  Quotient.congr (Equiv.refl K) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hGH]
    rfl)

@[simp] theorem maassRelativeCosetEquivOfEq_mk
    {G H K : Subgroup (GL (Fin 2) ℝ)}
    (hGH : G.subgroupOf K = H.subgroupOf K) (k : K) :
    maassRelativeCosetEquivOfEq hGH (QuotientGroup.mk k) = QuotientGroup.mk k :=
  rfl

/-- A finite trace only depends on the source subgroup as seen inside its target,
provided its underlying function is unchanged. -/
theorem maassTraceFunction_congr_source
    {G H K : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex K] [H.IsFiniteRelIndex K]
    (hGH : G.subgroupOf K = H.subgroupOf K)
    (fG : glUpperHalfPlaneInvariantFunctions G)
    (fH : glUpperHalfPlaneInvariantFunctions H)
    (hfun : fG.1 = fH.1) :
    maassTraceFunction (H := K) fG = maassTraceFunction (H := K) fH := by
  letI : Fintype (K ⧸ (G.subgroupOf K)) := Fintype.ofFinite _
  letI : Fintype (K ⧸ (H.subgroupOf K)) := Fintype.ofFinite _
  let e := maassRelativeCosetEquivOfEq hGH
  funext z
  unfold maassTraceFunction
  rw [← Equiv.sum_comp e (fun q => maassTraceQuotientFunc fH q z)]
  apply Finset.sum_congr rfl
  intro q hq
  induction q using Quotient.inductionOn with
  | h k =>
    rw [maassRelativeCosetEquivOfEq_mk, maassTraceQuotientFunc_mk,
      maassTraceQuotientFunc_mk]
    exact congrFun hfun _

/-- Restricting a source function to the subgroup visible in the target does not
change its finite trace. -/
theorem maassTrace_restrict_subgroupOf_eq
    (H K : Subgroup (GL (Fin 2) ℝ)) [H.IsFiniteRelIndex K]
    (f : glUpperHalfPlaneInvariantFunctions H) :
    let J := K.subgroupOf H
    let T := J.map H.subtype
    letI : T.IsFiniteRelIndex K := by
      rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
      have hsub : T.subgroupOf K = H.subgroupOf K := by
        apply (Subgroup.map_subtype_inj).mp
        rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        simp only [T, J, Subgroup.subgroupOf_map_subtype, inf_comm, inf_left_comm, inf_idem]
      rw [hsub]
      exact Subgroup.finiteIndex_of_finite_quotient
    maassTraceFunction (H := K)
      (maassInvariantRestrict (maassDoubleCosetTarget_le J) f) =
      maassTraceFunction (H := K) f := by
  dsimp only
  let J : Subgroup H := K.subgroupOf H
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  have hsub : T.subgroupOf K = H.subgroupOf K := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [T, J, Subgroup.subgroupOf_map_subtype, inf_comm, inf_left_comm, inf_idem]
  letI : T.IsFiniteRelIndex K := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  apply maassTraceFunction_congr_source hsub
  rfl

/-- Mackey composition with the literal outer finite trace. The acting subgroup is
the intersection of the intermediate and outer target groups. -/
theorem maassTrace_mackey_compose_subgroupOf
    (G H K : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H]
    [H.IsFiniteRelIndex K] (f : glUpperHalfPlaneInvariantFunctions G) :
    let J := K.subgroupOf H
    let T := J.map H.subtype
    letI : T.IsFiniteRelIndex K := by
      rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
      have hsub : T.subgroupOf K = H.subgroupOf K := by
        apply (Subgroup.map_subtype_inj).mp
        rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        simp only [T, J, Subgroup.subgroupOf_map_subtype, inf_comm, inf_left_comm, inf_idem]
      rw [hsub]
      exact Subgroup.finiteIndex_of_finite_quotient
    let Ω := Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))
    letI : Fintype Ω := maassTraceDoubleCosetOrbitFintype G H J
    maassTraceFunction (H := K) (maassTraceInvariant (H := H) f) =
      ∑ q : Ω,
        (maassDoubleCosetBlockTraceToInvariant G H K J q.out.out
          (by
            rintro x ⟨j, hj, rfl⟩
            exact hj) f).1 := by
  dsimp only
  let J : Subgroup H := K.subgroupOf H
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  have hsub : T.subgroupOf K = H.subgroupOf K := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [T, J, Subgroup.subgroupOf_map_subtype, inf_comm, inf_left_comm, inf_idem]
  have hTK : T ≤ K := by
    rintro x ⟨j, hj, rfl⟩
    exact hj
  letI : T.IsFiniteRelIndex K := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : Fintype (Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :=
    maassTraceDoubleCosetOrbitFintype G H J
  calc
    maassTraceFunction (H := K) (maassTraceInvariant (H := H) f) =
        maassTraceFunction (H := K)
          (maassInvariantRestrict (maassDoubleCosetTarget_le J)
            (maassTraceInvariant (H := H) f)) := by
      exact (maassTrace_restrict_subgroupOf_eq H K
        (maassTraceInvariant (H := H) f)).symm
    _ = _ := maassTrace_mackey_compose G H K J hTK f

end

end GaloisForLFunctions.RHTower
