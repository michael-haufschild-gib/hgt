import GaloisForLFunctions.HTGeometry.CDGATwistedExtend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The free cell on the cocycles of a degree

Every cocycle of a differential graded module is the image of a generator of the free cell on the
free module spanned by the cocycles of that degree.  This is the covering step of a relative cell
construction: it makes the comparison surjective on cocycles, hence on cohomology, in that degree.

* `HTGeometry.CDGATwist.zero` : the trivial twist, which makes a cell attachment a direct sum.
* `HTGeometry.cocycleCover` : the comparison from the free cell on the cocycles of a degree.
* `HTGeometry.cocycleCover_gen` : it hits every cocycle.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {K : ℕ → Type w} [∀ n, AddCommGroup (K n)] [∀ n, Module R (K n)]

/-- **The trivial twist.**  Attaching a cell along it is the direct sum. -/
def CDGATwist.zero (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) :
    CDGATwist P Q where
  τ _ _ := 0
  τ_add _ _ _ := (add_zero (0 : M _)).symm
  τ_smul _ _ _ := (smul_zero _).symm
  τ_act h x c := by
    show (0 : M _) = ((-1 : R)) ^ _ • P.act (show _ + (_ + 1) = _ + 1 by omega) x (0 : M _)
    rw [show P.act (show _ + (_ + 1) = _ + 1 by omega) x (0 : M _) = 0 from
      (P.actₗ (show _ + (_ + 1) = _ + 1 by omega) x).map_zero, smul_zero]
  τ_d n c := by
    show P.d (n + 1) (0 : M (n + 1)) + (0 : M (n + 2)) = 0
    rw [show P.d (n + 1) (0 : M (n + 1)) = 0 from (P.dₗ (n + 1)).map_zero, add_zero]

/-- A morphism out of the cell is a lift across the trivial twist. -/
def CDGATwistedLift.ofHom {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N}
    {S : CDGAModuleStructure A K} (ε : CDGAModuleHom P S) (ζ : CDGAModuleHom Q S) :
    CDGATwistedLift (CDGATwist.zero P Q) S ε where
  η n c := ζ.toFun n c
  η_add := ζ.map_add
  η_smul := ζ.map_smul
  η_act h x c := ζ.map_act h x c
  η_d n c := by
    rw [show (CDGATwist.zero P Q).τ n c = (0 : M (n + 1)) from rfl,
      show ε.toFun (n + 1) (0 : M (n + 1)) = 0 from (ε.mapₗ (n + 1)).map_zero, zero_add]
    exact (ζ.map_d n c).symm

section Cover

variable (P : CDGAModuleStructure A M) (k : ℕ)

/-- The free module spanned by the cocycles of a degree. -/
abbrev cocycleCellCoeff : Type w := (P.cocycles k) →₀ R

/-- The linear combination of cocycles, valued in the cocycles. -/
noncomputable def cocycleCellLift : cocycleCellCoeff P k →ₗ[R] P.cocycles k :=
  Finsupp.linearCombination R fun z => z

/-- The linear combination of cocycles. -/
noncomputable def cocycleCellMap : cocycleCellCoeff P k →ₗ[R] M k :=
  (P.cocycles k).subtype.comp (cocycleCellLift P k)

theorem cocycleCellMap_d (v : cocycleCellCoeff P k) : P.d k (cocycleCellMap P k v) = 0 :=
  (cocycleCellLift P k v).2

@[simp] theorem cocycleCellMap_single (z : P.cocycles k) :
    cocycleCellMap P k (Finsupp.single z 1) = (z : M k) := by
  show ((Finsupp.linearCombination R fun z : P.cocycles k => z) (Finsupp.single z 1) : M k) = _
  rw [Finsupp.linearCombination_single, one_smul]

variable (u : CDGAUnit A) (hP : CDGAModuleUnital u P)

/-- **The free cell on the cocycles of a degree, mapping to the module.** -/
noncomputable def cocycleCover :
    CDGAModuleHom (freeCellModule A (cocycleCellCoeff P k) k) P :=
  freeCellExtend P k (cocycleCellMap P k) (cocycleCellMap_d P k)

include hP

/-- **Every cocycle is the image of a generator.** -/
theorem cocycleCover_gen (z : P.cocycles k) :
    (cocycleCover P k).toFun k
        (freeCellGen (R := R) (X := X) u k (Finsupp.single z 1)) = (z : M k) := by
  rw [cocycleCover, freeCellExtend_gen u k P hP (cocycleCellMap P k) (cocycleCellMap_d P k),
    cocycleCellMap_single]

end Cover

/-- The generator of a free cell is a cocycle: the unit is one. -/
theorem freeCellGen_mem_cocycles {V : Type w} [AddCommGroup V] [Module R V] (u : CDGAUnit A)
    (k : ℕ) (v : V) :
    freeCellGen (R := R) (X := X) u k v ∈ (freeCellModule A V k).cocycles k := by
  refine funext fun p => ?_
  obtain ⟨a, ha⟩ := p
  obtain rfl : a = 1 := by omega
  have h0 : (0 : ℕ) + k = k := Nat.zero_add k
  show (tensorConstModule (CDGAStructure.selfModule A) V).d 0
      (freeCellGen (R := R) (X := X) u k v ⟨0, h0⟩) = 0
  rw [show freeCellGen (R := R) (X := X) u k v ⟨0, h0⟩ = u.one ⊗ₜ[R] v from
    freeCellGen_apply u k v]
  show TensorProduct.map (A.dₗ 0) LinearMap.id (u.one ⊗ₜ[R] v) = 0
  rw [TensorProduct.map_tmul]
  show A.d 0 u.one ⊗ₜ[R] (v : V) = 0
  rw [u.d_one, TensorProduct.zero_tmul]

end GaloisForLFunctions.HTGeometry
