import GaloisForLFunctions.HTGeometry.MilnorKTwoBruhatTransitions

/-!
# Milnor's rank-four Bruhat-pair fibers

This file constructs Milnor's pair space `X = SL₄(F) ×_M W` and identifies every fixed-matrix
fiber as a principal homogeneous space for Milnor `K₂`.  This is the kernel-torsor core used in
the transitivity half of Milnor's Lemma 12.8.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MilnorDiagonalExtension

variable {F : Type*} [Field F]

noncomputable def milnorWCentralToKernel :
    Multiplicative (MilnorKDeg F 2) →*
      (milnorWProjection (F := F)).ker :=
  (milnorWCentralIncl (F := F)).codRestrict
    (milnorWProjection (F := F)).ker (fun z => by
      rw [milnorWProjection_ker]
      exact ⟨z, rfl⟩)

theorem milnorWCentralToKernel_bijective :
    Function.Bijective (milnorWCentralToKernel (F := F)) := by
  constructor
  · intro x y hxy
    exact milnorWCentralIncl_injective (congrArg Subtype.val hxy)
  · intro k
    have hk : k.1 ∈ MonoidHom.range (milnorWCentralIncl (F := F)) := by
      rw [← milnorWProjection_ker]
      exact k.2
    obtain ⟨z, hz⟩ := hk
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz

noncomputable def milnorWKernelEquiv :
    Multiplicative (MilnorKDeg F 2) ≃*
      (milnorWProjection (F := F)).ker :=
  MulEquiv.ofBijective (milnorWCentralToKernel (F := F))
    milnorWCentralToKernel_bijective

/-- Milnor's pair space `X = SL₄(F) ×_M W`. -/
@[ext]
structure Fin4BruhatPair where
  matrix : elementaryGroup F (Fin 4)
  lift : MilnorW F
  compatible : fin4BruhatProjection matrix = milnorWProjection lift

noncomputable instance :
    SMul (Multiplicative (MilnorKDeg F 2)) (Fin4BruhatPair (F := F)) where
  smul z x :=
    { matrix := x.matrix
      lift := milnorWCentralIncl z * x.lift
      compatible := by
        have hz : milnorWProjection (milnorWCentralIncl (F := F) z) = 1 :=
          (milnorWCentralToKernel (F := F) z).2
        rw [map_mul, hz, one_mul]
        exact x.compatible }

@[simp] theorem bruhatPair_smul_matrix
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    (z • x).matrix = x.matrix := rfl

@[simp] theorem bruhatPair_smul_lift
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    (z • x).lift = milnorWCentralIncl z * x.lift := rfl

noncomputable instance :
    MulAction (Multiplicative (MilnorKDeg F 2)) (Fin4BruhatPair (F := F)) where
  one_smul x := by
    ext <;> simp
  mul_smul z z' x := by
    ext
    · rfl
    · simp [map_mul, mul_assoc]

theorem exists_fin4BruhatPair_over (s : elementaryGroup F (Fin 4)) :
    ∃ x : Fin4BruhatPair (F := F), x.matrix = s := by
  obtain ⟨w, hw⟩ := milnorWProjection_surjective (fin4BruhatProjection s)
  exact ⟨⟨s, w, hw.symm⟩, rfl⟩

theorem existsUnique_milnorKTwo_smul_bruhatPair
    {x y : Fin4BruhatPair (F := F)} (hxy : x.matrix = y.matrix) :
    ∃! z : Multiplicative (MilnorKDeg F 2), z • x = y := by
  have hk : y.lift * x.lift⁻¹ ∈ (milnorWProjection (F := F)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← x.compatible, ← y.compatible, ← hxy]
    exact mul_inv_cancel _
  let k : (milnorWProjection (F := F)).ker := ⟨y.lift * x.lift⁻¹, hk⟩
  let z := (milnorWKernelEquiv (F := F)).symm k
  have hzval : milnorWCentralIncl (F := F) z = y.lift * x.lift⁻¹ := by
    have hz := (milnorWKernelEquiv (F := F)).apply_symm_apply k
    exact congrArg Subtype.val hz
  refine ⟨z, ?_, ?_⟩
  · apply Fin4BruhatPair.ext
    · exact hxy
    · rw [bruhatPair_smul_lift, hzval]
      group
  · intro z' hz'
    apply milnorWCentralIncl_injective
    have hlift := congrArg Fin4BruhatPair.lift hz'
    simp only [bruhatPair_smul_lift] at hlift
    rw [hzval]
    exact (eq_mul_inv_iff_mul_eq).2 hlift

end GaloisForLFunctions.HTGeometry
