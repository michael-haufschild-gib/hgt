import GaloisForLFunctions.HTGeometry.SteinbergWeylRootAction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : Type*} [DecidableEq n]

def steinbergWeylWordGens : Set (SteinbergGroup F n) :=
  {x | ∃ (i j : n) (hij : i ≠ j) (u : Fˣ), x = steinbergWeyl hij u}

def steinbergWeylWordSubgroup : Subgroup (SteinbergGroup F n) :=
  Subgroup.closure (steinbergWeylWordGens (F := F) (n := n))

namespace SteinbergWeylWord

def append : SteinbergWeylWord F n → SteinbergWeylWord F n → SteinbergWeylWord F n
  | w, .one => w
  | w, .snoc v i j hij u => (append w v).snoc i j hij u

theorem eval_append (w v : SteinbergWeylWord F n) :
    (append w v).eval = w.eval * v.eval := by
  induction v generalizing w with
  | one => simp [append, eval]
  | snoc v i j hij u ih =>
      simp only [append, eval, ih]
      group

def inv : SteinbergWeylWord F n → SteinbergWeylWord F n
  | .one => .one
  | .snoc w i j hij u => append (.snoc .one i j hij (-u)) w.inv

theorem eval_inv (w : SteinbergWeylWord F n) :
    w.inv.eval = w.eval⁻¹ := by
  induction w with
  | one => simp [inv, eval]
  | snoc w i j hij u ih =>
      rw [inv, eval_append, eval, ih]
      simp only [eval, one_mul, steinbergWeyl_neg]
      group

theorem eval_mem_subgroup (w : SteinbergWeylWord F n) :
    w.eval ∈ steinbergWeylWordSubgroup (F := F) (n := n) := by
  induction w with
  | one =>
      simp only [eval]
      exact Subgroup.one_mem _
  | snoc w i j hij u ih =>
      simp only [eval]
      exact (steinbergWeylWordSubgroup (F := F) (n := n)).mul_mem ih
        (Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩)

theorem exists_of_mem_subgroup {x : SteinbergGroup F n}
    (hx : x ∈ steinbergWeylWordSubgroup (F := F) (n := n)) :
    ∃ w : SteinbergWeylWord F n, w.eval = x := by
  apply Subgroup.closure_induction (p := fun x _ => ∃ w : SteinbergWeylWord F n, w.eval = x)
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, j, hij, u, rfl⟩
    exact ⟨.snoc .one i j hij u, by simp [eval]⟩
  · exact ⟨.one, by simp [eval]⟩
  · intro x y _ _ ⟨wx, hwx⟩ ⟨wy, hwy⟩
    exact ⟨append wx wy, by rw [eval_append, hwx, hwy]⟩
  · intro x _ ⟨w, hw⟩
    exact ⟨w.inv, by rw [eval_inv, hw]⟩

end SteinbergWeylWord

/-- Every element of the Weyl-word subgroup has a signed permutation action on all root groups. -/
theorem exists_signed_root_action_of_mem {x : SteinbergGroup F n}
    (hspare : ∀ i j : n, i ≠ j → ∃ m : n, i ≠ m ∧ j ≠ m)
    (hx : x ∈ steinbergWeylWordSubgroup (F := F) (n := n)) :
    ∃ (σ : Equiv.Perm n) (c : n → Fˣ), ∀ (p q : n) (hpq : p ≠ q) (a : F),
      x * steinbergX hpq a * x⁻¹
        = steinbergX (σ.injective.ne_iff.mpr hpq) ((c p : F) * ((c q)⁻¹ : F) * a) := by
  obtain ⟨w, hw⟩ := SteinbergWeylWord.exists_of_mem_subgroup hx
  refine ⟨w.perm, w.scale, ?_⟩
  intro p q hpq a
  rw [← hw]
  exact w.conj_root hspare hpq a

end GaloisForLFunctions.HTGeometry
