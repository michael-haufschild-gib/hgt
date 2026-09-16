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

end

end GaloisForLFunctions.RHTower
