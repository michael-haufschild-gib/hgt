import GaloisForLFunctions.HTGeometry.SteinbergTWTAbsorption

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : Type*} [DecidableEq n] [LinearOrder n]

/-- A Weyl word evaluating to the inverse torus element. -/
def steinbergTorusInverseWord (i j : n) (hij : i ≠ j) (u : Fˣ) : SteinbergWeylWord F n :=
  .snoc (.snoc .one i j hij (1 : Fˣ)) i j hij (-u)

omit [LinearOrder n] in
theorem steinbergTorusInverseWord_eval (i j : n) (hij : i ≠ j) (u : Fˣ) :
    (steinbergTorusInverseWord i j hij u).eval = (steinbergTorus hij u)⁻¹ := by
  change 1 * steinbergWeyl hij (1 : Fˣ) * steinbergWeyl hij (-u) = (steinbergTorus hij u)⁻¹
  rw [one_mul, steinbergTorus, steinbergWeyl_neg hij (1 : Fˣ), steinbergWeyl_neg hij u]
  group

omit [LinearOrder n] in
theorem steinbergTorusInverseWord_perm_apply (i j : n) (hij : i ≠ j) (u : Fˣ) (p : n) :
    (steinbergTorusInverseWord i j hij u).perm p = p := by
  simp only [steinbergTorusInverseWord, SteinbergWeylWord.perm, Equiv.trans_apply,
    Equiv.refl_apply]
  exact Equiv.swap_apply_self i j p

/-- Inverse torus conjugation preserves the positive-root subgroup. -/
theorem steinbergTorus_inv_conj_upper_mem
    (hspare : ∀ i j : n, i ≠ j → ∃ m : n, i ≠ m ∧ j ≠ m)
    {i j : n} (hij : i ≠ j) (u : Fˣ) {t : SteinbergGroup F n}
    (ht : t ∈ upperSteinbergSubgroup (F := F) n) :
    (steinbergTorus hij u)⁻¹ * t * steinbergTorus hij u
      ∈ upperSteinbergSubgroup (F := F) n := by
  let word := steinbergTorusInverseWord i j hij u
  have hword : word.eval = (steinbergTorus hij u)⁻¹ :=
    steinbergTorusInverseWord_eval i j hij u
  change t ∈ Subgroup.closure (upperSteinbergGens (F := F) (n := n)) at ht
  apply Subgroup.closure_induction (p := fun x _ =>
    (steinbergTorus hij u)⁻¹ * x * steinbergTorus hij u ∈ upperSteinbergSubgroup (F := F) n)
    ?_ ?_ ?_ ?_ ht
  · rintro x ⟨p, q, hpq, a, hpq_upper, rfl⟩
    have hword_inv : word.eval⁻¹ = steinbergTorus hij u := by rw [hword, inv_inv]
    rw [← hword, ← hword_inv]
    have h := word.conj_root hspare hpq a
    rw [h]
    have hperm_p : word.perm p = p := by
      simpa [word] using steinbergTorusInverseWord_perm_apply i j hij u p
    have hperm_q : word.perm q = q := by
      simpa [word] using steinbergTorusInverseWord_perm_apply i j hij u q
    have hmem : steinbergX hpq ((word.scale p : F) * ((word.scale q)⁻¹ : F) * a)
        ∈ upperSteinbergSubgroup (F := F) n := Subgroup.subset_closure
      ⟨p, q, hpq, ((word.scale p : F) * ((word.scale q)⁻¹ : F) * a), hpq_upper, rfl⟩
    simpa only [hperm_p, hperm_q] using hmem
  · simp
  · intro x y _ _ hx hy
    rw [show (steinbergTorus hij u)⁻¹ * (x * y) * steinbergTorus hij u
      = ((steinbergTorus hij u)⁻¹ * x * steinbergTorus hij u)
          * ((steinbergTorus hij u)⁻¹ * y * steinbergTorus hij u) by group]
    exact (upperSteinbergSubgroup (F := F) n).mul_mem hx hy
  · intro x _ hx
    rw [show (steinbergTorus hij u)⁻¹ * x⁻¹ * steinbergTorus hij u
      = ((steinbergTorus hij u)⁻¹ * x * steinbergTorus hij u)⁻¹ by group]
    exact (upperSteinbergSubgroup (F := F) n).inv_mem hx

omit [DecidableEq n] [LinearOrder n] in
theorem steinbergTorus_mem_weylWordSubgroup {i j : n} (hij : i ≠ j) (u : Fˣ) :
    steinbergTorus hij u ∈ steinbergWeylWordSubgroup (F := F) (n := n) := by
  rw [steinbergTorus]
  exact (steinbergWeylWordSubgroup (F := F) (n := n)).mul_mem
    (Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩)
    (Subgroup.subset_closure ⟨i, j, hij, -1, rfl⟩)

omit [DecidableEq n] in
theorem steinbergTWT_mul_upper {g : SteinbergGroup F n}
    (hg : g ∈ steinbergTWT (F := F) (n := n)) {t : SteinbergGroup F n}
    (ht : t ∈ upperSteinbergSubgroup (F := F) n) :
    g * t ∈ steinbergTWT (F := F) (n := n) := by
  rcases hg with ⟨t₁, w, t₂, ht₁, hw, ht₂, rfl⟩
  refine ⟨t₁, w, t₂ * t, ht₁, hw,
    (upperSteinbergSubgroup (F := F) n).mul_mem ht₂ ht, ?_⟩
  group

/-- Right multiplication by every torus factor preserves `TWT`. -/
theorem steinbergTWT_mul_torus
    (hspare : ∀ i j : n, i ≠ j → ∃ m : n, i ≠ m ∧ j ≠ m)
    {g : SteinbergGroup F n} (hg : g ∈ steinbergTWT (F := F) (n := n))
    {i j : n} (hij : i ≠ j) (u : Fˣ) :
    g * steinbergTorus hij u ∈ steinbergTWT (F := F) (n := n) := by
  rcases hg with ⟨t₁, w, t₂, ht₁, hw, ht₂, rfl⟩
  have hconj := steinbergTorus_inv_conj_upper_mem hspare hij u ht₂
  refine ⟨t₁, w * steinbergTorus hij u,
    (steinbergTorus hij u)⁻¹ * t₂ * steinbergTorus hij u, ht₁,
    (steinbergWeylWordSubgroup (F := F) (n := n)).mul_mem hw
      (steinbergTorus_mem_weylWordSubgroup hij u), hconj, ?_⟩
  group

end GaloisForLFunctions.HTGeometry
