import GaloisForLFunctions.HTGeometry.DbarPolydiscSolve

/-!
# Basic operations on `(0,q)`-forms

A `(0,q)`-form is a coefficient family indexed by `q`-tuples of coordinate directions, and the
Dolbeault operator is the alternating sum of the antiholomorphic partial derivatives over the slots.
The operations the Dolbeault induction needs in every degree are collected here: smoothness of a
form, the difference of two forms, the smoothness and locality of the Dolbeault operator, and the
predicate that a form uses only the directions below a given index — the predicate the induction
decreases.

* `HTGeometry.SmoothForm` : all coefficients are smooth.
* `HTGeometry.dbarOp_smooth` : the Dolbeault operator preserves smoothness.
* `HTGeometry.dbarOp_sub` : it is subtractive.
* `HTGeometry.FormBelow` : the form uses only directions below an index.
-/

namespace HTGeometry

open Complex

section Forms

variable {n : ℕ}

/-- A form is smooth when all its coefficients are. -/
def SmoothForm {q : ℕ} (f : DbarForm n q) : Prop :=
  ∀ J : Fin q → Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f J)

/-- The difference of two forms. -/
def formSub {q : ℕ} (f g : DbarForm n q) : DbarForm n q := fun J z => f J z - g J z

@[simp] theorem formSub_apply {q : ℕ} (f g : DbarForm n q) (J : Fin q → Fin n)
    (z : Fin n → ℂ) : formSub f g J z = f J z - g J z := rfl

theorem SmoothForm.sub {q : ℕ} {f g : DbarForm n q} (hf : SmoothForm f) (hg : SmoothForm g) :
    SmoothForm (formSub f g) := fun J => (hf J).sub (hg J)

theorem SmoothForm.differentiable {q : ℕ} {f : DbarForm n q} (hf : SmoothForm f)
    (J : Fin q → Fin n) : Differentiable ℝ (f J) := (hf J).differentiable (by simp)

/-- **The Dolbeault operator preserves smoothness.** -/
theorem dbarOp_smooth {q : ℕ} {f : DbarForm n q} (hf : SmoothForm f) : SmoothForm (dbarOp f) := by
  intro J
  have heq : (dbarOp f) J = fun z => ∑ k : Fin (q + 1),
      (-1 : ℂ) ^ (k : ℕ) * dzbarAt (f fun i => J (k.succAbove i)) (J k) z := rfl
  rw [heq]
  refine ContDiff.sum fun k _ => ?_
  exact contDiff_const.mul (contDiff_infty_dzbarAt (hf _) (J k))

/-- **The Dolbeault operator is subtractive.** -/
theorem dbarOp_sub {q : ℕ} {f g : DbarForm n q} (hf : SmoothForm f) (hg : SmoothForm g)
    (J : Fin (q + 1) → Fin n) (z : Fin n → ℂ) :
    dbarOp (formSub f g) J z = dbarOp f J z - dbarOp g J z := by
  show (∑ k : Fin (q + 1), (-1 : ℂ) ^ (k : ℕ) *
      dzbarAt (formSub f g fun i => J (k.succAbove i)) (J k) z) = _
  have hterm : ∀ k : Fin (q + 1),
      (-1 : ℂ) ^ (k : ℕ) * dzbarAt (formSub f g fun i => J (k.succAbove i)) (J k) z
        = (-1 : ℂ) ^ (k : ℕ) * dzbarAt (f fun i => J (k.succAbove i)) (J k) z
          - (-1 : ℂ) ^ (k : ℕ) * dzbarAt (g fun i => J (k.succAbove i)) (J k) z := by
    intro k
    have hsub : dzbarAt (formSub f g fun i => J (k.succAbove i)) (J k) z
        = dzbarAt (f fun i => J (k.succAbove i)) (J k) z
          - dzbarAt (g fun i => J (k.succAbove i)) (J k) z :=
      dzbarAt_sub (hf.differentiable _) (hg.differentiable _) (J k) z
    rw [hsub, mul_sub]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib]
  rfl

/-- A form uses only the directions below an index. -/
def FormBelow {q : ℕ} (m : ℕ) (f : DbarForm n q) (P : Set (Fin n → ℂ)) : Prop :=
  ∀ J : Fin q → Fin n, (∃ i, m ≤ (J i : ℕ)) → ∀ z ∈ P, f J z = 0

theorem FormBelow.mono {q : ℕ} {m m' : ℕ} (hmm' : m ≤ m') {f : DbarForm n q}
    {P : Set (Fin n → ℂ)} (hf : FormBelow m f P) : FormBelow m' f P := by
  intro J hJ z hz
  obtain ⟨i, hi⟩ := hJ
  exact hf J ⟨i, le_trans hmm' hi⟩ z hz

end Forms

section ConsFaces

variable {n : ℕ}

/-- The zeroth face of a tuple with a prepended index is the tuple itself. -/
theorem consFace_zero {q : ℕ} (k : Fin n) (J : Fin q → Fin n) :
    (fun i => (Fin.cons k J : Fin (q + 1) → Fin n) ((0 : Fin (q + 1)).succAbove i)) = J := by
  funext i
  simp

/-- The later faces of a tuple with a prepended index keep the prepended index. -/
theorem consFace_succ {q : ℕ} (k : Fin n) (J : Fin (q + 1) → Fin n) (t : Fin (q + 1)) :
    (fun i => (Fin.cons k J : Fin (q + 2) → Fin n) (t.succ.succAbove i))
      = Fin.cons k (fun i => J (t.succAbove i)) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.succ_succAbove_succ]

/-- **The Dolbeault operator on a tuple with a prepended index separates the zeroth slot.** -/
theorem dbarOp_cons {q : ℕ} (G : DbarForm n (q + 1)) (k : Fin n) (J : Fin (q + 1) → Fin n)
    (z : Fin n → ℂ) :
    dbarOp G (Fin.cons k J) z
      = dzbarAt (G J) k z
        + ∑ t : Fin (q + 1), (-1 : ℂ) ^ ((t : ℕ) + 1) *
            dzbarAt (G (Fin.cons k (fun i => J (t.succAbove i)))) (J t) z := by
  show (∑ l : Fin (q + 2), (-1 : ℂ) ^ (l : ℕ) *
      dzbarAt (G fun i => (Fin.cons k J : Fin (q + 2) → Fin n) (l.succAbove i))
        ((Fin.cons k J : Fin (q + 2) → Fin n) l) z) = _
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [consFace_zero k J]
    simp
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [consFace_succ k J t]
    simp [Fin.cons_succ]

end ConsFaces

end HTGeometry
