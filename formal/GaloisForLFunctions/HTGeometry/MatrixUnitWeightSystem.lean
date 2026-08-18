import GaloisForLFunctions.HTGeometry.MatrixUnitCasimir

/-!
# The spectral gap of a weighted matrix-unit Casimir

A matrix-unit family with a compatible integer weight system has a Casimir whose nonzero spectrum
starts at twice the alphabet size.  An eigenvector splits into weight components, each of which is
again an eigenvector because the Casimir preserves weights; among the weights realized in one
eigenspace there is one maximal for a strictly antitone linear functional, and a vector there is
annihilated by every raising generator.  The bracket relations then evaluate the Casimir energy of
that vector as the weight's own Casimir value, and the ordered differences of the weight are the
energies of the lowering generators, so the weight is decreasing.  The combinatorial weight gap
finishes the argument.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Weights

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One raising step of a weight. -/
def shiftWeight (a b : α) (nu : α → ℤ) : α → ℤ :=
  fun c => nu c + (if c = a then 1 else 0) - (if c = b then 1 else 0)

theorem shiftWeight_involutive (a b : α) (nu : α → ℤ) :
    shiftWeight a b (shiftWeight b a nu) = nu := by
  funext c
  rw [shiftWeight, shiftWeight]
  ring

/-- A weight system for a matrix-unit family. -/
structure IsWeightSystem (gen : α → α → Matrix I I ℂ) (wt : I → α → ℤ) : Prop where
  diag : ∀ (a : α) (i j : I), gen a a i j = if i = j then ((wt i a : ℤ) : ℂ) else 0
  shift : ∀ (a b : α) (i j : I), gen a b i j ≠ 0 → wt i = shiftWeight a b (wt j)
  zerosum : ∀ i : I, ∑ a, wt i a = 0

/-- A vector supported on a single weight. -/
def HasWeight (wt : I → α → ℤ) (nu : α → ℤ) (X : I → ℂ) : Prop :=
  ∀ i, wt i ≠ nu → X i = 0

/-- The weight component of a vector. -/
def wproj (wt : I → α → ℤ) (nu : α → ℤ) (X : I → ℂ) : I → ℂ :=
  fun i => if wt i = nu then X i else 0

/-- The weights realized by the coordinates. -/
def weightSet (wt : I → α → ℤ) : Finset (α → ℤ) :=
  Finset.image wt (Finset.univ : Finset I)

theorem hasWeight_wproj (wt : I → α → ℤ) (nu : α → ℤ) (X : I → ℂ) :
    HasWeight wt nu (wproj wt nu X) := by
  intro i hi
  rw [wproj, if_neg hi]

theorem wproj_of_hasWeight {wt : I → α → ℤ} {nu : α → ℤ} {X : I → ℂ}
    (h : HasWeight wt nu X) : wproj wt nu X = X := by
  funext i
  rw [wproj]
  by_cases hi : wt i = nu
  · rw [if_pos hi]
  · rw [if_neg hi, h i hi]

theorem wproj_of_hasWeight_ne {wt : I → α → ℤ} {mu nu : α → ℤ} {X : I → ℂ}
    (h : HasWeight wt mu X) (hne : mu ≠ nu) : wproj wt nu X = 0 := by
  funext i
  rw [wproj]
  by_cases hi : wt i = nu
  · rw [if_pos hi, h i (by rw [hi]; exact fun hh => hne hh.symm)]
    rfl
  · rw [if_neg hi]
    rfl

theorem wproj_add (wt : I → α → ℤ) (nu : α → ℤ) (X Y : I → ℂ) :
    wproj wt nu (X + Y) = wproj wt nu X + wproj wt nu Y := by
  funext i
  simp only [wproj, Pi.add_apply]
  by_cases hi : wt i = nu <;> simp [hi]

theorem wproj_smul (wt : I → α → ℤ) (nu : α → ℤ) (c : ℂ) (X : I → ℂ) :
    wproj wt nu (c • X) = c • wproj wt nu X := by
  funext i
  simp only [wproj, Pi.smul_apply]
  by_cases hi : wt i = nu <;> simp [hi]

theorem wproj_sum {ι : Type*} (wt : I → α → ℤ) (nu : α → ℤ) (s : Finset ι) (F : ι → I → ℂ) :
    wproj wt nu (∑ k ∈ s, F k) = ∑ k ∈ s, wproj wt nu (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext i; rw [wproj]; by_cases hi : wt i = nu <;> simp [hi]
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, wproj_add, ih]

theorem sum_wproj (wt : I → α → ℤ) (X : I → ℂ) :
    (∑ nu ∈ weightSet wt, wproj wt nu X) = X := by
  classical
  funext i
  rw [Finset.sum_apply]
  have hterm : ∀ nu ∈ weightSet wt, wproj wt nu X i = if wt i = nu then X i else 0 := by
    intro nu _
    rfl
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq (weightSet wt) (wt i) (fun _ => X i)]
  have hmem : wt i ∈ weightSet wt := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rw [if_pos hmem]

theorem hasWeight_zero (wt : I → α → ℤ) (nu : α → ℤ) : HasWeight wt nu (0 : I → ℂ) :=
  fun _ _ => rfl

theorem hasWeight_add {wt : I → α → ℤ} {nu : α → ℤ} {X Y : I → ℂ}
    (hX : HasWeight wt nu X) (hY : HasWeight wt nu Y) : HasWeight wt nu (X + Y) := by
  intro i hi
  show X i + Y i = 0
  rw [hX i hi, hY i hi, add_zero]

theorem hasWeight_sum {ι : Type*} {wt : I → α → ℤ} {nu : α → ℤ} (s : Finset ι)
    (F : ι → I → ℂ) (h : ∀ k ∈ s, HasWeight wt nu (F k)) :
    HasWeight wt nu (∑ k ∈ s, F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasWeight_zero wt nu
  | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact hasWeight_add (h k (Finset.mem_insert_self k s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- A generator moves a pure weight by one step. -/
theorem hasWeight_mulVec {gen : α → α → Matrix I I ℂ} {wt : I → α → ℤ}
    (hws : IsWeightSystem gen wt) (a b : α) {nu : α → ℤ} {X : I → ℂ}
    (hX : HasWeight wt nu X) : HasWeight wt (shiftWeight a b nu) (gen a b *ᵥ X) := by
  intro i hi
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : wt j = nu
  · by_cases hg : gen a b i j = 0
    · rw [hg, zero_mul]
    · exact absurd (by rw [hws.shift a b i j hg, hj]) hi
  · rw [hX j hj, mul_zero]

/-- The Casimir preserves pure weights. -/
theorem hasWeight_casimir {gen : α → α → Matrix I I ℂ} {wt : I → α → ℤ}
    (hws : IsWeightSystem gen wt) {nu : α → ℤ} {X : I → ℂ} (hX : HasWeight wt nu X) :
    HasWeight wt nu (familyCasimir gen *ᵥ X) := by
  classical
  have hvec : familyCasimir gen *ᵥ X = ∑ a, ∑ b, (gen a b *ᵥ (gen b a *ᵥ X)) := by
    rw [familyCasimir]
    simp only [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact (Matrix.mulVec_mulVec X (gen a b) (gen b a)).symm
  rw [hvec]
  refine hasWeight_sum _ _ fun a _ => hasWeight_sum _ _ fun b _ => ?_
  have h1 := hasWeight_mulVec hws b a hX
  have h2 := hasWeight_mulVec hws a b h1
  rwa [shiftWeight_involutive] at h2

end Weights

end

end GaloisForLFunctions.HTGeometry
