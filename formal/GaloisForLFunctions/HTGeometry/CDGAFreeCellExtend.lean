import GaloisForLFunctions.HTGeometry.CDGARelFreeCellInvariance

/-!
# Maps out of a free cell

A free cell `A[−k] ⊗ V` has zero differential on `V`, so a morphism out of it into a differential
graded module is exactly a linear map from `V` into the cocycles of degree `k`: the value on a
generator determines the value everywhere by equivariance, and the Leibniz rule is satisfied
precisely because the generator is a cocycle.

This is the free–forgetful adjunction of the layer, and it is what makes a relative cell
construction possible: a cell can be attached along any prescribed family of cocycles.

* `HTGeometry.freeCellExtend` : the morphism determined by a linear map on generators.
* `HTGeometry.freeCellExtend_gen` : its value on a generator.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {V : Type w} [AddCommGroup V] [Module R V]

section Extend

variable (P : CDGAModuleStructure A M) (k : ℕ) (g : V →ₗ[R] M k)

/-- The bilinear map behind the extension: act on the value of a generator. -/
noncomputable def freeCellBil {a n : ℕ} (h : a + k = n) : X a →ₗ[R] V →ₗ[R] M n where
  toFun x := (P.actₗ h x).comp g
  map_add' x x' := by
    refine LinearMap.ext fun v => ?_
    exact P.act_add_left h x x' (g v)
  map_smul' c x := by
    refine LinearMap.ext fun v => ?_
    exact P.act_smul_left h c x (g v)

@[simp] theorem freeCellBil_apply {a n : ℕ} (h : a + k = n) (x : X a) (v : V) :
    freeCellBil P k g h x v = P.act h x (g v) := rfl

/-- The underlying degreewise linear map of the extension. -/
noncomputable def freeCellExtendₗ (n : ℕ) : FreeCellCarrier (R := R) X V k n →ₗ[R] M n :=
  if h : k ≤ n then
    { toFun := fun z => TensorProduct.lift (freeCellBil P k g (show n - k + k = n by omega))
        (z ⟨n - k, by omega⟩)
      map_add' := fun z z' => by
        show TensorProduct.lift _ (z ⟨n - k, by omega⟩ + z' ⟨n - k, by omega⟩) = _
        rw [map_add]
      map_smul' := fun c z => by
        show TensorProduct.lift _ (c • z ⟨n - k, by omega⟩) = _
        rw [map_smul]
        rfl }
  else 0

theorem freeCellExtendₗ_apply {a n : ℕ} (h : a + k = n)
    (z : FreeCellCarrier (R := R) X V k n) :
    freeCellExtendₗ P k g n z = TensorProduct.lift (freeCellBil P k g h) (z ⟨a, h⟩) := by
  have hk : k ≤ n := by omega
  have ha : n - k = a := by omega
  subst ha
  rw [freeCellExtendₗ, dif_pos hk]
  rfl

theorem freeCellExtendₗ_of_lt {n : ℕ} (h : n < k) (z : FreeCellCarrier (R := R) X V k n) :
    freeCellExtendₗ P k g n z = 0 := by
  rw [freeCellExtendₗ, dif_neg (by omega)]
  rfl

/-- Below the shift the free cell is trivial. -/
theorem freeCell_subsingleton {n : ℕ} (h : n < k) :
    Subsingleton (FreeCellCarrier (R := R) X V k n) :=
  shiftCarrier_subsingleton (M := fun a => TensorProduct R (X a) V) h

variable (hg : ∀ v, P.d k (g v) = 0)

include hg

/-- **A linear map into the cocycles of degree `k` extends to a morphism out of the free cell.** -/
noncomputable def freeCellExtend : CDGAModuleHom (freeCellModule A V k) P where
  toFun n z := freeCellExtendₗ P k g n z
  map_add n z z' := map_add (freeCellExtendₗ P k g n) z z'
  map_smul n c z := map_smul (freeCellExtendₗ P k g n) c z
  map_act := by
    intro c b n h x z
    by_cases hb : k ≤ b
    · obtain ⟨a, ha⟩ : ∃ a, a + k = b := ⟨b - k, by omega⟩
      have hn : c + a + k = n := by omega
      rw [freeCellExtendₗ_apply P k g ha z, freeCellExtendₗ_apply P k g hn]
      have hz : (freeCellModule A V k).act h x z ⟨c + a, hn⟩
          = TensorProduct.map (A.mulₗ (rfl : c + a = c + a) x) LinearMap.id (z ⟨a, ha⟩) := by
        show shiftAct (tensorConstModule (CDGAStructure.selfModule A) V) k h x z ⟨c + a, hn⟩ = _
        rw [shiftAct_apply_add (tensorConstModule (CDGAStructure.selfModule A) V) k h x z ha hn]
        rfl
      rw [hz]
      induction (z ⟨a, ha⟩) using TensorProduct.induction_on with
      | zero =>
          rw [map_zero, map_zero, map_zero]
          exact ((P.actₗ h x).map_zero).symm
      | tmul y v =>
          rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
          exact P.act_assoc (rfl : c + a = c + a) hn ha h x y (g v)
      | add w w' hw hw' =>
          rw [map_add, map_add, map_add, hw, hw']
          exact ((P.actₗ h x).map_add _ _).symm
    · haveI := freeCell_subsingleton (R := R) (X := X) (V := V) (k := k) (n := b) (by omega)
      rw [show z = 0 from Subsingleton.elim _ _]
      rw [show (freeCellModule A V k).act h x (0 : FreeCellCarrier (R := R) X V k b) = 0 from
        ((freeCellModule A V k).actₗ h x).map_zero,
        (freeCellExtendₗ P k g n).map_zero, (freeCellExtendₗ P k g b).map_zero,
        (P.actₗ h x).map_zero]
  map_d := by
    intro n z
    by_cases hn : k ≤ n
    · obtain ⟨a, ha⟩ : ∃ a, a + k = n := ⟨n - k, by omega⟩
      have ha' : a + 1 + k = n + 1 := by omega
      rw [freeCellExtendₗ_apply P k g ha z, freeCellExtendₗ_apply P k g ha']
      have hz : (freeCellModule A V k).d n z ⟨a + 1, ha'⟩
          = TensorProduct.map (A.dₗ a) LinearMap.id (z ⟨a, ha⟩) := rfl
      rw [hz]
      induction (z ⟨a, ha⟩) using TensorProduct.induction_on with
      | zero =>
          rw [map_zero, map_zero, map_zero]
          exact ((P.dₗ n).map_zero).symm
      | tmul y v =>
          rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
          show P.act ha' (A.d a y) (g v) = P.d n (P.act ha y (g v))
          rw [P.d_act ha y (g v), hg v,
            show P.act (show a + (k + 1) = n + 1 by omega) y (0 : M (k + 1)) = 0 from
              (P.actₗ (show a + (k + 1) = n + 1 by omega) y).map_zero, smul_zero, add_zero]
      | add w w' hw hw' =>
          rw [map_add, map_add, map_add, hw, hw']
          exact ((P.dₗ n).map_add _ _).symm
    · haveI := freeCell_subsingleton (R := R) (X := X) (V := V) (k := k) (n := n) (by omega)
      rw [show z = 0 from Subsingleton.elim _ _,
        show (freeCellModule A V k).d n (0 : FreeCellCarrier (R := R) X V k n) = 0 from
          ((freeCellModule A V k).dₗ n).map_zero,
        (freeCellExtendₗ P k g (n + 1)).map_zero, (freeCellExtendₗ P k g n).map_zero,
        (P.dₗ n).map_zero]

@[simp] theorem freeCellExtend_toFun (n : ℕ) (z : FreeCellCarrier (R := R) X V k n) :
    (freeCellExtend P k g hg).toFun n z = freeCellExtendₗ P k g n z := rfl

end Extend

end GaloisForLFunctions.HTGeometry
