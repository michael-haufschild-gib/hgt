import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicLevi

/-! Independent choices of diagonal blocks assemble to a section of the
Levi projection of the list parabolic. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

abbrev listLeviGroup (L : List (Pc g)) := ∀ k : Fin L.length, Gn g (L.get k).1

private def diagonalInTail (p : Pc g) (L : List (Pc g)) :
    Gn g p.1 × listParabolic L →* tailParabolic p L where
  toFun x := by
    let q : twoBlockParabolic g p.1 (degL L) :=
      ⟨upperBlockUnit x.1 0 x.2.val, inPar_upperBlockMatrix x.1.val 0 x.2.val.val⟩
    have he : rightLevi q = x.2.val :=
      congrArg Prod.snd (twoBlockLevi_upperBlockUnit x.1 0 x.2.val)
    refine ⟨q, ?_⟩
    change rightLevi q ∈ listParabolic L
    rw [he]
    exact x.2.property
  map_one' := Subtype.ext (Subtype.ext upperBlockUnit_one)
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change upperBlockUnit (x.1 * y.1) 0 (x.2.val * y.2.val) =
      upperBlockUnit x.1 0 x.2.val * upperBlockUnit y.1 0 y.2.val
    rw [upperBlockUnit_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- Assemble a list of invertible blocks into a block diagonal element of the flag parabolic. -/
def listDiagonalUnit : (L : List (Pc g)) → listLeviGroup L →* listParabolic L
  | [] =>
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => (one_mul _).symm }
  | p :: L =>
    let ι : listLeviGroup (p :: L) →* Gn g p.1 × listParabolic L :=
      { toFun := fun x => (x 0, listDiagonalUnit L fun k => x k.succ)
        map_one' := Prod.ext rfl (map_one (listDiagonalUnit L))
        map_mul' := fun x y => by
          let u : listLeviGroup L := fun k => x k.succ
          let v : listLeviGroup L := fun k => y k.succ
          exact Prod.ext rfl (map_mul (listDiagonalUnit L) u v) }
    (listParabolicConsEquiv p L).toMonoidHom.comp ((diagonalInTail p L).comp ι)

theorem listDiagonalUnit_cons_val (p : Pc g) (L : List (Pc g)) (x : listLeviGroup (p :: L)) :
    (listDiagonalUnit (p :: L) x).val =
      upperBlockUnit (x 0) 0 (listDiagonalUnit L fun k => x k.succ).val := rfl

@[simp] theorem listBlockLevi_listDiagonalUnit (L : List (Pc g)) (x : listLeviGroup L)
    (k : Fin L.length) : listBlockLevi L k (listDiagonalUnit L x) = x k := by
  induction L with
  | nil => exact Fin.elim0 k
  | cons p L ih =>
    let D := listDiagonalUnit L (fun i => x i.succ)
    let q := diagonalInTail p L (x 0, D)
    let e := listParabolicConsEquiv p L
    have hq : e.symm (listDiagonalUnit (p :: L) x) = q := e.symm_apply_apply q
    have hL : twoBlockLevi q.val = (x 0, D.val) :=
      twoBlockLevi_upperBlockUnit (x 0) 0 D.val
    refine Fin.cases ?_ (fun k => ?_) k
    · change (twoBlockLevi (e.symm (listDiagonalUnit (p :: L) x)).val).1 = x 0
      rw [hq]
      exact congrArg Prod.fst hL
    · change listBlockLevi L k (tailLevi p L (e.symm (listDiagonalUnit (p :: L) x))) = x k.succ
      rw [hq]
      have he : tailLevi p L q = D := Subtype.ext (congrArg Prod.snd hL)
      rw [he]
      exact ih (fun i => x i.succ) k

/-- The assembled diagonal unit is zero between distinct blocks. -/
theorem listDiagonalUnit_eq_zero_offBlock (L : List (Pc g)) (x : listLeviGroup L)
    (i j : Fin (degL L)) (h : listBlockOf L i ≠ listBlockOf L j) :
    (listDiagonalUnit L x).val.val i j = 0 := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons p L ih =>
    let D := (listDiagonalUnit L fun k => x k.succ).val
    let A : Mt g (p.1 + degL L) := upperBlockMatrix (x 0).val 0 D.val
    have hA : (listDiagonalUnit (p :: L) x).val.val = A :=
      congrArg Units.val (listDiagonalUnit_cons_val p L x)
    have hzero : A i j = 0 := by
      revert h
      refine Fin.addCases (m := p.1) (n := degL L) (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (m := p.1) (n := degL L) (fun j => ?_) (fun j => ?_) j
      · intro h
        exact (h ((listBlockOf_left p L i).trans (listBlockOf_left p L j).symm)).elim
      · intro _
        dsimp only [A, upperBlockMatrix, Matrix.submatrix_apply]
        rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
        rfl
      · intro _
        dsimp only [A, upperBlockMatrix, Matrix.submatrix_apply]
        rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
        rfl
      · intro h
        have he : listBlockOf L i ≠ listBlockOf L j := fun e =>
          h ((listBlockOf_right p L i).trans ((congrArg Fin.succ e).trans (listBlockOf_right p L j).symm))
        have hd : D.val i j = 0 := ih (fun k => x k.succ) i j he
        dsimp only [A, upperBlockMatrix, Matrix.submatrix_apply]
        rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
        exact hd
    exact (congrArg (fun B : Mt g (p.1 + degL L) => B i j) hA).trans hzero

section CommonDimension

variable (L : List (Pc g)) {n : ℕ} (h : degL L = n)

def listDiagonalUnitAt : listLeviGroup L →* listParabolicAt L h := by
  subst n
  exact listDiagonalUnit L

theorem listBlockLeviAt_listDiagonalUnitAt (x : listLeviGroup L) (i : Fin L.length) :
    listBlockLeviAt L h i (listDiagonalUnitAt L h x) = x i := by
  subst n
  exact listBlockLevi_listDiagonalUnit L x i

theorem listDiagonalUnitAt_eq_zero_offBlock (x : listLeviGroup L) (i j : Fin n)
    (he : listBlockOfAt L h i ≠ listBlockOfAt L h j) :
    (listDiagonalUnitAt L h x).val.val i j = 0 := by
  subst n
  exact listDiagonalUnit_eq_zero_offBlock L x i j he

end CommonDimension

end GlobalTheory.GLq
