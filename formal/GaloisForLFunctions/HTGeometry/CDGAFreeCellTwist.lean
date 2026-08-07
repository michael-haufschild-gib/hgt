import GaloisForLFunctions.HTGeometry.CDGAFreeCover

/-!
# Attaching a free cell along prescribed cocycles

A twisting cochain on a free cell `A[−k] ⊗ V` is determined by its value on the generators, which
must be cocycles of degree `k+1`: the Koszul sign of the twist is forced by equivariance, and the
anticommutation with the differentials is exactly the statement that the values are cocycles.

* `HTGeometry.freeCellTwist` : the twist attached to a linear map into the cocycles.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {V : Type w} [AddCommGroup V] [Module R V]

section Twist

variable (S : CDGAModuleStructure A M) (k : ℕ) (w : V →ₗ[R] M (k + 1))

/-- The degreewise linear map behind the twist on a free cell. -/
noncomputable def freeCellTwistₗ (n : ℕ) : FreeCellCarrier (R := R) X V k n →ₗ[R] M (n + 1) :=
  if h : k ≤ n then
    { toFun := fun z => ((-1 : R)) ^ (n - k) •
        TensorProduct.lift (freeCellBil S (k + 1) w (show n - k + (k + 1) = n + 1 by omega))
          (z ⟨n - k, by omega⟩)
      map_add' := fun z z' => by
        have hnk : n - k + k = n := by omega
        show ((-1 : R)) ^ (n - k) • TensorProduct.lift _ (z ⟨n - k, hnk⟩ + z' ⟨n - k, hnk⟩) = _
        rw [map_add, smul_add]
      map_smul' := fun c z => by
        have hnk : n - k + k = n := by omega
        show ((-1 : R)) ^ (n - k) • TensorProduct.lift _ (c • z ⟨n - k, hnk⟩) = _
        rw [map_smul, smul_comm]
        rfl }
  else 0

theorem freeCellTwistₗ_apply {a n : ℕ} (h : a + k = n) (z : FreeCellCarrier (R := R) X V k n) :
    freeCellTwistₗ S k w n z = ((-1 : R)) ^ a •
      TensorProduct.lift (freeCellBil S (k + 1) w (show a + (k + 1) = n + 1 by omega))
        (z ⟨a, h⟩) := by
  have hk : k ≤ n := by omega
  have ha : n - k = a := by omega
  subst ha
  rw [freeCellTwistₗ, dif_pos hk]
  rfl

variable (hw : ∀ v, S.d (k + 1) (w v) = 0)

include hw

/-- **The twist on a free cell attached to a linear map into the cocycles of degree `k+1`.** -/
noncomputable def freeCellTwist : CDGATwist S (freeCellModule A V k) where
  τ n z := freeCellTwistₗ S k w n z
  τ_add n z z' := map_add (freeCellTwistₗ S k w n) z z'
  τ_smul n c z := map_smul (freeCellTwistₗ S k w n) c z
  τ_act := by
    intro c b n h x z
    by_cases hb : k ≤ b
    · obtain ⟨a, ha⟩ : ∃ a, a + k = b := ⟨b - k, by omega⟩
      have hn : c + a + k = n := by omega
      rw [freeCellTwistₗ_apply S k w hn, freeCellTwistₗ_apply S k w ha]
      have hz : (freeCellModule A V k).act h x z ⟨c + a, hn⟩
          = TensorProduct.map (A.mulₗ (rfl : c + a = c + a) x) LinearMap.id (z ⟨a, ha⟩) := by
        show shiftAct (tensorConstModule (CDGAStructure.selfModule A) V) k h x z ⟨c + a, hn⟩ = _
        rw [shiftAct_apply_add (tensorConstModule (CDGAStructure.selfModule A) V) k h x z ha hn]
        rfl
      rw [hz, S.act_smul_right, smul_smul, ← pow_add]
      refine congrArg (fun y : M (n + 1) => ((-1 : R)) ^ (c + a) • y) ?_
      induction (z ⟨a, ha⟩) using TensorProduct.induction_on with
      | zero =>
          rw [map_zero, map_zero]
          exact ((S.actₗ (show c + (b + 1) = n + 1 by omega) x).map_zero).symm
      | tmul y v =>
          rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
          exact S.act_assoc (rfl : c + a = c + a) (show c + a + (k + 1) = n + 1 by omega)
            (show a + (k + 1) = b + 1 by omega) (show c + (b + 1) = n + 1 by omega) x y (w v)
      | add y y' hy hy' =>
          rw [map_add, map_add, hy, hy', map_add]
          exact (S.act_add_right _ x _ _).symm
    · haveI := freeCell_subsingleton (R := R) (X := X) (V := V) (k := k) (n := b) (by omega)
      rw [show z = 0 from Subsingleton.elim _ _,
        show (freeCellModule A V k).act h x (0 : FreeCellCarrier (R := R) X V k b) = 0 from
          ((freeCellModule A V k).actₗ h x).map_zero,
        (freeCellTwistₗ S k w n).map_zero, (freeCellTwistₗ S k w b).map_zero,
        show S.act (show c + (b + 1) = n + 1 by omega) x (0 : M (b + 1)) = 0 from
          (S.actₗ (show c + (b + 1) = n + 1 by omega) x).map_zero, smul_zero]
  τ_d := by
    intro n z
    by_cases hn : k ≤ n
    · obtain ⟨a, ha⟩ : ∃ a, a + k = n := ⟨n - k, by omega⟩
      have ha' : a + 1 + k = n + 1 := by omega
      rw [freeCellTwistₗ_apply S k w ha z, freeCellTwistₗ_apply S k w ha']
      have hz : (freeCellModule A V k).d n z ⟨a + 1, ha'⟩
          = TensorProduct.map (A.dₗ a) LinearMap.id (z ⟨a, ha⟩) := rfl
      rw [hz]
      induction (z ⟨a, ha⟩) using TensorProduct.induction_on with
      | zero =>
          simp only [map_zero, smul_zero, add_zero, zero_add,
            show ∀ m : ℕ, S.d m (0 : M m) = 0 from fun m => (S.dₗ m).map_zero]
      | tmul y v =>
          rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul,
            S.d_smul, freeCellBil_apply, freeCellBil_apply,
            S.d_act (show a + (k + 1) = n + 1 by omega) y (w v), hw v,
            show S.act (show a + (k + 1 + 1) = n + 1 + 1 by omega) y (0 : M (k + 1 + 1)) = 0 from
              (S.actₗ (show a + (k + 1 + 1) = n + 1 + 1 by omega) y).map_zero,
            smul_zero, add_zero, pow_succ,
            show ((-1 : R)) ^ a * (-1 : R) = -(((-1 : R)) ^ a) by ring, neg_smul,
            ← sub_eq_add_neg]
          exact sub_eq_zero_of_eq rfl
      | add y y' hy hy' =>
          rw [map_add, map_add, map_add, smul_add, smul_add, S.d_add]
          rw [show ∀ p q r s : M (n + 1 + 1), p + q + (r + s) = p + r + (q + s) from
            fun p q r s => by abel, hy, hy', add_zero]
    · haveI := freeCell_subsingleton (R := R) (X := X) (V := V) (k := k) (n := n) (by omega)
      rw [show z = 0 from Subsingleton.elim _ _,
        show (freeCellModule A V k).d n (0 : FreeCellCarrier (R := R) X V k n) = 0 from
          ((freeCellModule A V k).dₗ n).map_zero,
        (freeCellTwistₗ S k w (n + 1)).map_zero, (freeCellTwistₗ S k w n).map_zero,
        show S.d (n + 1) (0 : M (n + 1)) = 0 from (S.dₗ (n + 1)).map_zero, add_zero]

end Twist

end GaloisForLFunctions.HTGeometry
