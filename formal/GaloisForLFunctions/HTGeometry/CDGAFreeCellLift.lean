import GaloisForLFunctions.HTGeometry.CDGAFreeCellTwist
import GaloisForLFunctions.HTGeometry.CDGATwistedExtend

/-!
# Extending a comparison across a free cell attached along cocycles

A cell attached to a module along cocycles can be carried by a comparison as soon as the images of
those cocycles are coboundaries, and a choice of primitives is exactly the extra datum which extends
the comparison across the attachment.

* `HTGeometry.freeCellTwistedLift` : the extension datum from a choice of primitives.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {L : ℕ → Type w} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {V : Type w} [AddCommGroup V] [Module R V]

variable (S : CDGAModuleStructure A L) (P : CDGAModuleStructure A M)
  (ε : CDGAModuleHom S P) (k : ℕ) (w : V →ₗ[R] L (k + 1)) (hw : ∀ v, S.d (k + 1) (w v) = 0)
  (g : V →ₗ[R] M k) (hgw : ∀ v, P.d k (g v) = ε.toFun (k + 1) (w v))

include hw hgw

/-- **A choice of primitives extends a comparison across a cell attached along cocycles.** -/
noncomputable def freeCellTwistedLift :
    CDGATwistedLift (freeCellTwist S k w hw) P ε where
  η n z := freeCellExtendₗ P k g n z
  η_add n z z' := map_add (freeCellExtendₗ P k g n) z z'
  η_smul n c z := map_smul (freeCellExtendₗ P k g n) c z
  η_act h x z := freeCellExtendₗ_act P k g h x z
  η_d := by
    intro n z
    by_cases hn : k ≤ n
    · obtain ⟨a, ha⟩ : ∃ a, a + k = n := ⟨n - k, by omega⟩
      have ha' : a + 1 + k = n + 1 := by omega
      have haw : a + (k + 1) = n + 1 := by omega
      rw [freeCellExtendₗ_apply P k g ha z,
        show (freeCellTwist S k w hw).τ n z
          = ((-1 : R)) ^ a • TensorProduct.lift (freeCellBil S (k + 1) w haw) (z ⟨a, ha⟩) from
          freeCellTwistₗ_apply S k w ha z,
        freeCellExtendₗ_apply P k g ha' ((freeCellModule A V k).d n z),
        show (freeCellModule A V k).d n z ⟨a + 1, ha'⟩
          = TensorProduct.map (A.dₗ a) LinearMap.id (z ⟨a, ha⟩) from rfl]
      induction (z ⟨a, ha⟩) using TensorProduct.induction_on with
      | zero =>
          simp only [map_zero, smul_zero, add_zero, zero_add,
            show ∀ m : ℕ, P.d m (0 : M m) = 0 from fun m => (P.dₗ m).map_zero,
            show ∀ m : ℕ, ε.toFun m (0 : L m) = 0 from fun m => (ε.mapₗ m).map_zero]
      | tmul x v =>
          rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul,
            TensorProduct.lift.tmul, freeCellBil_apply, freeCellBil_apply, freeCellBil_apply,
            P.d_act ha x (g v), hgw v, ε.map_smul, ε.map_act haw x (w v)]
          exact add_comm _ _
      | add y y' hy hy' =>
          rw [map_add, map_add, map_add, map_add, smul_add, ε.map_add, P.d_add, hy, hy']
          abel
    · haveI := freeCell_subsingleton (R := R) (X := X) (V := V) (k := k) (n := n) (by omega)
      rw [show z = 0 from Subsingleton.elim _ _,
        show (freeCellModule A V k).d n (0 : FreeCellCarrier (R := R) X V k n) = 0 from
          ((freeCellModule A V k).dₗ n).map_zero,
        (freeCellExtendₗ P k g n).map_zero, (freeCellExtendₗ P k g (n + 1)).map_zero,
        show (freeCellTwist S k w hw).τ n (0 : FreeCellCarrier (R := R) X V k n) = 0 from
          (freeCellTwistₗ S k w n).map_zero,
        show ε.toFun (n + 1) (0 : L (n + 1)) = 0 from (ε.mapₗ (n + 1)).map_zero,
        show P.d n (0 : M n) = 0 from (P.dₗ n).map_zero, add_zero]

/-- **The comparison extended across the attachment.** -/
noncomputable def freeCellAttachExtend :
    CDGAModuleHom (CDGAModuleStructure.twisted S (freeCellModule A V k) (freeCellTwist S k w hw))
      P :=
  twistedExtend ε (freeCellTwistedLift S P ε k w hw g hgw)

end GaloisForLFunctions.HTGeometry
