import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMonomialCharacter

/-! A Whittaker-compatible permutation begins with an increasing block
whose image is the final interval. Its column entries are constant there. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

/-- The data of a monomial matrix compatible with the Whittaker character. -/
@[ext] structure WhittakerMonomialData (g n : ℕ) [Fact g.Prime] where
  perm : Equiv.Perm (Fin n)
  scale : Fin n → (ZMod g)ˣ
  compatible : WhittakerMonomialCompatible perm scale

namespace WhittakerMonomialData

variable {g n : ℕ} [Fact g.Prime]

/-- The first block starts at the value of the first column and continues
consecutively until the maximal value. -/
theorem first_block (D : WhittakerMonomialData g (n + 1))
    (i : Fin (n + 1)) (hi : i.val < n + 1 - (D.perm 0).val) :
    (D.perm i).val = (D.perm 0).val + i.val ∧ D.scale i = D.scale 0 := by
  let a := (D.perm 0).val
  have h : ∀ (k : ℕ) (hk : k < n + 1), k < n + 1 - a →
      (D.perm ⟨k, hk⟩).val = a + k ∧ D.scale ⟨k, hk⟩ = D.scale 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk ha
      cases k with
      | zero =>
        have hzero : (⟨0, hk⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp)
        rw [hzero]
        exact ⟨(Nat.add_zero a).symm, rfl⟩
      | succ k =>
        have hkn : k < n + 1 := by omega
        have hka : k < n + 1 - a := by omega
        let u : Fin (n + 1) := ⟨k, hkn⟩
        let w : Fin (n + 1) := ⟨a + k + 1, by omega⟩
        let j := D.perm.symm w
        have hu : (D.perm u).val = a + k ∧ D.scale u = D.scale 0 := ih k (Nat.lt_succ_self k) hkn hka
        have hj : (D.perm j).val = a + k + 1 := congrArg Fin.val (D.perm.apply_symm_apply w)
        have hlt : u < j := by
          by_contra hn
          have hjk : j.val ≤ k := le_of_not_gt hn
          have e := (ih j.val (by omega) j.isLt (by omega)).1
          change (D.perm j).val = a + j.val at e
          omega
        have hσ : D.perm u < D.perm j := by
          change (D.perm u).val < (D.perm j).val
          rw [hu.1, hj]
          exact Nat.lt_succ_self _
        have hσ' : Adjacent (D.perm u) (D.perm j) := by
          change (D.perm u).val + 1 = (D.perm j).val
          rw [hu.1, hj]
        have he := (D.compatible hlt hσ).1.mpr hσ'
        have hj' : (⟨k + 1, hk⟩ : Fin (n + 1)) = j := Fin.ext he
        exact ⟨(congrArg (fun i => (D.perm i).val) hj').trans (hj.trans (Nat.add_succ a k).symm),
          (congrArg D.scale hj').trans (((D.compatible hlt hσ).2 he).symm.trans hu.2)⟩
  exact h i.val i.isLt hi

/-- Beyond the first block, all images lie in the initial interval. -/
theorem value_lt_first_of_outside (D : WhittakerMonomialData g (n + 1))
    (i : Fin (n + 1)) (hi : n + 1 - (D.perm 0).val ≤ i.val) :
    (D.perm i).val < (D.perm 0).val := by
  let a := (D.perm 0).val
  let x := (D.perm i).val
  by_contra hn
  have hax : a ≤ x := le_of_not_gt hn
  have hx : x < n + 1 := (D.perm i).isLt
  let j : Fin (n + 1) := ⟨x - a, by omega⟩
  have hja : j.val < n + 1 - a := by
    change x - a < n + 1 - a
    omega
  have e := (D.first_block j hja).1
  have hj : D.perm j = D.perm i := Fin.ext (e.trans (Nat.add_sub_of_le hax))
  exact (not_le_of_gt hja) ((congrArg Fin.val (D.perm.injective hj)).symm ▸ hi)

private def tailIndex (a : Fin (n + 1)) (i : Fin a.val) : Fin (n + 1) :=
  ⟨n + 1 - a.val + i.val, by
    have ha := a.isLt
    have hi := i.isLt
    omega⟩

private theorem tailIndex_val (a : Fin (n + 1)) (i : Fin a.val) :
    (tailIndex a i).val = n + 1 - a.val + i.val := rfl

private theorem tailIndex_injective (a : Fin (n + 1)) : Function.Injective (tailIndex a) := by
  intro i j h
  have e := congrArg Fin.val h
  apply Fin.ext
  exact Nat.add_left_cancel e

/-- Deleting the first block leaves compatible data on the smaller interval. -/
def tail (D : WhittakerMonomialData g (n + 1)) (a : Fin (n + 1)) (ha : D.perm 0 = a) :
    WhittakerMonomialData g a.val := by
  let f (i : Fin a.val) : Fin a.val := ⟨(D.perm (tailIndex a i)).val, by
    have e : (D.perm 0).val = a.val := congrArg Fin.val ha
    have h : n + 1 - (D.perm 0).val ≤ (tailIndex a i).val := by
      rw [e, tailIndex_val]
      exact Nat.le_add_right _ _
    exact (D.value_lt_first_of_outside (tailIndex a i) h).trans_le e.le⟩
  have hf : Function.Injective f := by
    intro i j e
    have hval : (D.perm (tailIndex a i)).val = (D.perm (tailIndex a j)).val :=
      congrArg (fun y : Fin a.val => y.val) e
    exact tailIndex_injective a (D.perm.injective (Fin.ext hval))
  let E := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨E, fun i => D.scale (tailIndex a i), ?_⟩
  intro i j hij hE
  have hlt : tailIndex a i < tailIndex a j := by
    change n + 1 - a.val + i.val < n + 1 - a.val + j.val
    exact Nat.add_lt_add_left hij _
  have hσ : D.perm (tailIndex a i) < D.perm (tailIndex a j) := hE
  have e := D.compatible hlt hσ
  have e' : Adjacent (tailIndex a i) (tailIndex a j) ↔ Adjacent i j := by
    change n + 1 - a.val + i.val + 1 = n + 1 - a.val + j.val ↔ i.val + 1 = j.val
    omega
  exact ⟨e'.symm.trans e.1, fun hab => e.2 (e'.mpr hab)⟩


private def tailSlot (a : Fin (n + 1)) (i : Fin (n + 1))
    (h : ¬ i.val < n + 1 - a.val) : Fin a.val :=
  ⟨i.val - (n + 1 - a.val), by
    have hi := i.isLt
    have ha := a.isLt
    omega⟩

private theorem tailIndex_tailSlot (a : Fin (n + 1)) (i : Fin (n + 1))
    (h : ¬ i.val < n + 1 - a.val) : tailIndex a (tailSlot a i h) = i :=
  Fin.ext (Nat.add_sub_of_le (le_of_not_gt h))

private theorem tailSlot_tailIndex (a : Fin (n + 1)) (i : Fin a.val)
    (h : ¬ (tailIndex a i).val < n + 1 - a.val) : tailSlot a (tailIndex a i) h = i :=
  Fin.ext (Nat.add_sub_cancel_left _ _)

private def prependMap (a : Fin (n + 1)) (D : WhittakerMonomialData g a.val)
    (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val < n + 1 - a.val then ⟨a.val + i.val, by omega⟩ else
    ⟨(D.perm (tailSlot a i h)).val, (D.perm (tailSlot a i h)).isLt.trans a.isLt⟩

private theorem prependMap_first (a : Fin (n + 1)) (D : WhittakerMonomialData g a.val)
    (i : Fin (n + 1)) (h : i.val < n + 1 - a.val) :
    (prependMap a D i).val = a.val + i.val := by
  rw [prependMap, dif_pos h]

private theorem prependMap_rest (a : Fin (n + 1)) (D : WhittakerMonomialData g a.val)
    (i : Fin (n + 1)) (h : ¬ i.val < n + 1 - a.val) :
    (prependMap a D i).val = (D.perm (tailSlot a i h)).val := by
  rw [prependMap, dif_neg h]

private theorem prependMap_injective (a : Fin (n + 1)) (D : WhittakerMonomialData g a.val) :
    Function.Injective (prependMap a D) := by
  intro i j h
  have e := congrArg Fin.val h
  by_cases hi : i.val < n + 1 - a.val
  · by_cases hj : j.val < n + 1 - a.val
    · rw [prependMap_first a D i hi, prependMap_first a D j hj] at e
      exact Fin.ext (Nat.add_left_cancel e)
    · rw [prependMap_first a D i hi, prependMap_rest a D j hj] at e
      have hlt := (D.perm (tailSlot a j hj)).isLt
      omega
  · by_cases hj : j.val < n + 1 - a.val
    · rw [prependMap_rest a D i hi, prependMap_first a D j hj] at e
      have hlt := (D.perm (tailSlot a i hi)).isLt
      omega
    · rw [prependMap_rest a D i hi, prependMap_rest a D j hj] at e
      exact (tailIndex_tailSlot a i hi).symm.trans
        ((congrArg (tailIndex a) (D.perm.injective (Fin.ext e))).trans (tailIndex_tailSlot a j hj))

private def prependScale (a : Fin (n + 1)) (c : (ZMod g)ˣ) (D : WhittakerMonomialData g a.val)
    (i : Fin (n + 1)) : (ZMod g)ˣ :=
  if h : i.val < n + 1 - a.val then c else D.scale (tailSlot a i h)

private def prepend (a : Fin (n + 1)) (c : (ZMod g)ˣ) (D : WhittakerMonomialData g a.val) :
    WhittakerMonomialData g (n + 1) := by
  have hinj := prependMap_injective a D
  let E := Equiv.ofBijective (prependMap a D) ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨E, prependScale a c D, ?_⟩
  intro i j hij he
  change i.val < j.val at hij
  change (prependMap a D i).val < (prependMap a D j).val at he
  by_cases hj : j.val < n + 1 - a.val
  · have hi : i.val < n + 1 - a.val := hij.trans hj
    refine ⟨?_, fun _ => ?_⟩
    · change i.val + 1 = j.val ↔ (prependMap a D i).val + 1 = (prependMap a D j).val
      rw [prependMap_first a D i hi, prependMap_first a D j hj]
      omega
    · simp only [prependScale, dif_pos hi, dif_pos hj]
  · have hi : ¬ i.val < n + 1 - a.val := by
      intro hi
      rw [prependMap_first a D i hi, prependMap_rest a D j hj] at he
      have hlast := (D.perm (tailSlot a j hj)).isLt
      omega
    rw [prependMap_rest a D i hi, prependMap_rest a D j hj] at he
    let i' := tailSlot a i hi
    let j' := tailSlot a j hj
    have hlt : i' < j' := by
      change i.val - (n + 1 - a.val) < j.val - (n + 1 - a.val)
      omega
    have h₀ : Adjacent i j ↔ Adjacent i' j' := by
      change i.val + 1 = j.val ↔ i.val - (n + 1 - a.val) + 1 = j.val - (n + 1 - a.val)
      omega
    have h₁ : Adjacent (E i) (E j) ↔ Adjacent (D.perm i') (D.perm j') := by
      change (prependMap a D i).val + 1 = (prependMap a D j).val ↔
        (D.perm i').val + 1 = (D.perm j').val
      rw [prependMap_rest a D i hi, prependMap_rest a D j hj]
    have h := D.compatible hlt he
    refine ⟨h₀.trans (h.1.trans h₁.symm), fun e => ?_⟩
    unfold prependScale
    rw [dif_neg hi, dif_neg hj]
    exact h.2 (h₀.mp e)

private theorem zero_mem_first (a : Fin (n + 1)) : (0 : Fin (n + 1)).val < n + 1 - a.val := by
  rw [Fin.val_zero]
  exact Nat.sub_pos_of_lt a.isLt

/-- At fixed first column image, compatible data are equivalent to one
nonzero entry for the first block and compatible data on the smaller interval. -/
def firstBlockEquiv (a : Fin (n + 1)) :
    {D : WhittakerMonomialData g (n + 1) // D.perm 0 = a} ≃
      (ZMod g)ˣ × WhittakerMonomialData g a.val where
  toFun D := ⟨D.val.scale 0, D.val.tail a D.property⟩
  invFun p := ⟨prepend a p.1 p.2, Fin.ext
    ((prependMap_first a p.2 0 (zero_mem_first a)).trans (by rw [Fin.val_zero, add_zero]))⟩
  left_inv x := by
    let D := x.val
    let T := D.tail a x.property
    have he : (D.perm 0).val = a.val := congrArg Fin.val x.property
    apply Subtype.ext
    apply WhittakerMonomialData.ext
    · ext i
      change (prependMap a T i).val = (D.perm i).val
      by_cases hi : i.val < n + 1 - a.val
      · rw [prependMap_first a T i hi]
        exact ((D.first_block i (he.symm ▸ hi)).1.trans (congrArg (· + i.val) he)).symm
      · rw [prependMap_rest a T i hi]
        change (D.perm (tailIndex a (tailSlot a i hi))).val = _
        rw [tailIndex_tailSlot]
    · funext i
      change prependScale a (D.scale 0) T i = D.scale i
      by_cases hi : i.val < n + 1 - a.val
      · rw [prependScale, dif_pos hi]
        exact (D.first_block i (he.symm ▸ hi)).2.symm
      · rw [prependScale, dif_neg hi]
        change D.scale (tailIndex a (tailSlot a i hi)) = _
        rw [tailIndex_tailSlot]
  right_inv x := by
    obtain ⟨c, D⟩ := x
    apply Prod.ext
    · change prependScale a c D 0 = c
      rw [prependScale, dif_pos (zero_mem_first a)]
    · apply WhittakerMonomialData.ext
      · ext i
        change (prependMap a D (tailIndex a i)).val = (D.perm i).val
        have hi : ¬ (tailIndex a i).val < n + 1 - a.val := by
          rw [tailIndex_val]
          exact not_lt_of_ge (Nat.le_add_right _ _)
        rw [prependMap_rest a D _ hi, tailSlot_tailIndex]
      · funext i
        change prependScale a c D (tailIndex a i) = D.scale i
        have hi : ¬ (tailIndex a i).val < n + 1 - a.val := by
          rw [tailIndex_val]
          exact not_lt_of_ge (Nat.le_add_right _ _)
        rw [prependScale, dif_neg hi, tailSlot_tailIndex]

end WhittakerMonomialData

end GlobalTheory.GLq
