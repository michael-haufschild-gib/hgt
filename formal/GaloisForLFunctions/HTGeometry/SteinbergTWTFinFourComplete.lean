import GaloisForLFunctions.HTGeometry.SteinbergTWTClosureFinFourWeyl

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- A finite word in the root generators of the rank-four Steinberg group. -/
inductive FinFourSteinbergRootWord (F : Type*) [Field F] where
  | one : FinFourSteinbergRootWord F
  | snoc : FinFourSteinbergRootWord F → (i j : Fin 4) → (hij : i ≠ j) → F → FinFourSteinbergRootWord F

namespace FinFourSteinbergRootWord

def eval : FinFourSteinbergRootWord F → SteinbergGroup F (Fin 4)
  | .one => 1
  | .snoc w _ _ hij a => w.eval * steinbergX hij a

def append : FinFourSteinbergRootWord F → FinFourSteinbergRootWord F → FinFourSteinbergRootWord F
  | w, .one => w
  | w, .snoc v i j hij a => (append w v).snoc i j hij a

theorem eval_append (w v : FinFourSteinbergRootWord F) :
    (append w v).eval = w.eval * v.eval := by
  induction v generalizing w with
  | one => simp [append, eval]
  | snoc v i j hij a ih =>
      simp only [append, eval, ih]
      group

def inv : FinFourSteinbergRootWord F → FinFourSteinbergRootWord F
  | .one => .one
  | .snoc w i j hij a => append (.snoc .one i j hij (-a)) w.inv

theorem eval_inv (w : FinFourSteinbergRootWord F) :
    w.inv.eval = w.eval⁻¹ := by
  induction w with
  | one => simp [inv, eval]
  | snoc w i j hij a ih =>
      rw [inv, eval_append, eval, ih]
      rw [eval, one_mul, steinbergX_neg]
      change (steinbergX hij a)⁻¹ * w.eval⁻¹ = (w.eval * steinbergX hij a)⁻¹
      group

/-- Every rank-four Steinberg element has a finite root-word representative. -/
theorem exists_eval (x : SteinbergGroup F (Fin 4)) :
    ∃ w : FinFourSteinbergRootWord F, w.eval = x := by
  have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of : SteinbergGen F (Fin 4)
      → SteinbergGroup F (Fin 4))) := by
    rw [PresentedGroup.closure_range_of (steinbergRels F (Fin 4))]
    exact Subgroup.mem_top x
  apply Subgroup.closure_induction (p := fun x _ => ∃ w : FinFourSteinbergRootWord F, w.eval = x)
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨g, rfl⟩
    exact ⟨.snoc .one g.i g.j g.hij g.a, rfl⟩
  · exact ⟨.one, rfl⟩
  · intro x y _ _ ⟨wx, hwx⟩ ⟨wy, hwy⟩
    exact ⟨append wx wy, by rw [eval_append, hwx, hwy]; rfl⟩
  · intro x _ ⟨w, hw⟩
    exact ⟨w.inv, by rw [eval_inv, hw]; rfl⟩

end FinFourSteinbergRootWord

/-- Right multiplication by every root generator preserves `TWT` in rank four. -/
theorem fin4_steinbergTWT_mul_root {g : SteinbergGroup F (Fin 4)}
    (hg : g ∈ steinbergTWT (F := F) (n := Fin 4))
    {i j : Fin 4} (hij : i ≠ j) (a : F) :
    g * steinbergX hij a ∈ steinbergTWT (F := F) (n := Fin 4) := by
  rcases lt_or_gt_of_ne hij with hupper | hlower
  · exact steinbergTWT_mul_upper hg
      (Subgroup.subset_closure ⟨i, j, hij, a, hupper, rfl⟩)
  · by_cases ha : a = 0
    · rw [ha, steinbergX_zero, mul_one]
      exact hg
    · let b : Fˣ := Units.mk0 a ha
      have hu : (steinbergX (Ne.symm hij) ((-b⁻¹ : Fˣ) : F))⁻¹
          ∈ upperSteinbergSubgroup (F := F) (Fin 4) :=
        (upperSteinbergSubgroup (F := F) (Fin 4)).inv_mem
          (Subgroup.subset_closure ⟨j, i, Ne.symm hij, ((-b⁻¹ : Fˣ) : F), hlower, rfl⟩)
      rw [← show (b : F) = a by simp [b], steinbergX_lower_eq_upper_weyl_upper hij b]
      have h1 := steinbergTWT_mul_upper hg hu
      have h2 := fin4_steinbergTWT_mul_weyl h1 (Ne.symm hij) (-b⁻¹)
      simpa only [mul_assoc] using steinbergTWT_mul_upper h2 hu

theorem FinFourSteinbergRootWord.eval_mem_TWT (w : FinFourSteinbergRootWord F) :
    w.eval ∈ steinbergTWT (F := F) (n := Fin 4) := by
  induction w with
  | one => exact upper_mem_steinbergTWT (Subgroup.one_mem _)
  | snoc w i j hij a ih =>
      simp only [FinFourSteinbergRootWord.eval]
      exact fin4_steinbergTWT_mul_root ih hij a

/-- **Rank-four Matsumoto/Bruhat normal form.** Every Steinberg element over a field is an
upper--Weyl--upper product. -/
theorem fin4_steinbergTWT_eq_top : steinbergTWT (F := F) (n := Fin 4) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨w, hw⟩ := FinFourSteinbergRootWord.exists_eval x
  rw [← hw]
  exact w.eval_mem_TWT

end GaloisForLFunctions.HTGeometry
