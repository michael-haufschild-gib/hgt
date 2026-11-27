import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicDoubleCosets

/-! A two-element block list gives the two-block parabolic and its
product of diagonal-block characters. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ}
variable (α : Gn g a → ℂ) (β : Gn g b → ℂ)

/-- Two characters viewed as an ordered list of blocks. -/
def blockPair : List (Pc g) := [⟨a, α⟩, ⟨b, β⟩]

@[simp] theorem degL_blockPair : degL (blockPair α β) = a + b := rfl

theorem listBlockOfAt_blockPair_val (i : Fin (a + b)) :
    (listBlockOfAt (blockPair α β) (degL_blockPair α β) i).val =
      if i.val < a then 0 else 1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change (listBlockOf (⟨a, α⟩ :: [⟨b, β⟩]) (Fin.castAdd b j)).val = _
    have h := listBlockOf_left (⟨a, α⟩ : Pc g) [⟨b, β⟩] j
    exact (congrArg (fun k : Fin 2 => k.val) h).trans (if_pos j.isLt).symm
  · change (listBlockOf (⟨a, α⟩ :: [⟨b, β⟩]) (Fin.natAdd a j)).val = _
    have h := listBlockOf_right (⟨a, α⟩ : Pc g) [⟨b, β⟩] j
    have h₀ : (listBlockOf ([⟨b, β⟩] : List (Pc g)) j : Fin 1) = (0 : Fin 1) :=
      Fin.ext (Nat.lt_one_iff.mp (listBlockOf ([⟨b, β⟩] : List (Pc g)) j).isLt)
    calc
      _ = (listBlockOf ([⟨b, β⟩] : List (Pc g)) j).val + 1 :=
        congrArg (fun k : Fin 2 => k.val) h
      _ = 1 := congrArg (fun k : Fin 1 => k.val + 1) h₀
      _ = _ := (if_neg (Nat.not_lt_of_ge (Nat.le_add_right a j.val))).symm

variable [Fact g.Prime]

theorem listParabolicAt_blockPair :
    listParabolicAt (blockPair α β) (degL_blockPair α β) = twoBlockParabolic g a b := by
  ext x
  rw [mem_listParabolicAt_iff]
  change (∀ i j, _ → x.val i j = 0) ↔ InPar a x.val
  constructor
  · intro h i j hj hi
    apply h i j
    change (listBlockOfAt _ _ j).val < (listBlockOfAt _ _ i).val
    rw [listBlockOfAt_blockPair_val, listBlockOfAt_blockPair_val, if_pos hj, if_neg (not_lt_of_ge hi)]
    exact Nat.zero_lt_one
  · intro h i j hij
    change (listBlockOfAt _ _ j).val < (listBlockOfAt _ _ i).val at hij
    rw [listBlockOfAt_blockPair_val, listBlockOfAt_blockPair_val] at hij
    have he : j.val < a ∧ a ≤ i.val := by split_ifs at hij <;> omega
    exact h i j he.1 he.2

/-- The two inducing functions agree under the identification of parabolics. -/
theorem listParabolicCharacterAt_blockPair
    (u : listParabolicAt (blockPair α β) (degL_blockPair α β)) :
    let v : twoBlockParabolic g a b := ⟨u.val, listParabolicAt_blockPair α β ▸ u.property⟩
    listParabolicCharacterAt (blockPair α β) (degL_blockPair α β) u =
      α (twoBlockLevi v).1 * β (twoBlockLevi v).2 := by
  let M := blockPair α β
  let hM := degL_blockPair α β
  let v : twoBlockParabolic g a b := ⟨u.val, listParabolicAt_blockPair α β ▸ u.property⟩
  have hleft : listBlockLeviAt M hM (0 : Fin 2) u = (twoBlockLevi v).1 := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    rw [listBlockLeviAt_apply]
    change u.val.val (Fin.castAdd b i) (Fin.castAdd b j) = tl a u.val.val i j
    exact (tl_apply_add _ _ _).symm
  have hright : listBlockLeviAt M hM (1 : Fin 2) u = (twoBlockLevi v).2 := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    rw [listBlockLeviAt_apply]
    change u.val.val (Fin.natAdd a i) (Fin.natAdd a j) = br a b u.val.val i j
    exact (br_apply_add _ _ _).symm
  let f (i : Fin 2) := (M.get i).2 (listBlockLeviAt M hM i u)
  have h := listParabolicCharacterAt_eq_prod M hM u
  change listParabolicCharacterAt M hM u = ∏ i : Fin 2, f i at h
  exact h.trans ((Fin.prod_univ_two f).trans (congrArg₂ (· * ·) (congrArg α hleft) (congrArg β hright)))

private theorem doubleCosetPairing_transport_right
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) {K K' : Subgroup G}
    (e : K = K') (f : H → ℂ) (h : K' → ℂ) (x : G) :
    doubleCosetPairing H K f (fun u => h ⟨u.val, e ▸ u.property⟩) x =
      doubleCosetPairing H K' f h x := by
  subst K'
  rfl

theorem doubleCosetPairing_blockPair (P : Subgroup (Gn g (a + b))) (f : P → ℂ)
    (x : Gn g (a + b)) :
    doubleCosetPairing P (listParabolicAt (blockPair α β) (degL_blockPair α β))
      f (listParabolicCharacterAt (blockPair α β) (degL_blockPair α β)) x =
    doubleCosetPairing P (twoBlockParabolic g a b) f
      (fun v => α (twoBlockLevi v).1 * β (twoBlockLevi v).2) x := by
  let Q := listParabolicAt (blockPair α β) (degL_blockPair α β)
  let K := twoBlockParabolic g a b
  let e : Q = K := listParabolicAt_blockPair α β
  let h (v : K) := α (twoBlockLevi v).1 * β (twoBlockLevi v).2
  have he : listParabolicCharacterAt (blockPair α β) (degL_blockPair α β) =
      (fun u : Q => h ⟨u.val, e ▸ u.property⟩) := funext (listParabolicCharacterAt_blockPair α β)
  exact (congrArg (fun z : Q → ℂ => doubleCosetPairing P Q f z x) he).trans
    (doubleCosetPairing_transport_right P e f h x)

end GlobalTheory.GLq
