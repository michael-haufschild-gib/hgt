import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Quadratic equations for arbitrary polynomial values

Every integer polynomial admits finitely many auxiliary variables and
quadratic constraints whose linear output is its value. Constants require
no auxiliary variables. Addition joins two disjoint systems, and
multiplication by an input variable adds one quadratic gate. Polynomial
induction therefore constructs the system for every polynomial.
-/

namespace GaloisForLFunctions.HTGeometry.Polynomial

open MvPolynomial

universe u

/-- Evaluation of an integer polynomial at rational arguments. -/
abbrev rationalEval {σ : Type*} (x : σ → ℚ) : MvPolynomial σ ℤ →+* ℚ :=
  eval₂Hom (Int.castRingHom ℚ) x

/-- Rename auxiliary variables while leaving input variables fixed. -/
def auxiliaryRename {σ α β : Type*} (f : α → β) :
    MvPolynomial (σ ⊕ α) ℤ →+* MvPolynomial (σ ⊕ β) ℤ :=
  rename (Sum.map id f)

theorem rationalEval_auxiliaryRename {σ α β : Type*} (f : α → β)
    (p : MvPolynomial (σ ⊕ α) ℤ) (x : σ → ℚ) (w : β → ℚ) :
    rationalEval (Sum.elim x w) (auxiliaryRename f p) =
      rationalEval (Sum.elim x (w ∘ f)) p := by
  change eval₂ _ _ (rename _ p) = eval₂ _ _ p
  rw [eval₂_rename]
  rfl

theorem totalDegree_auxiliaryRename_le {σ α β : Type*} (f : α → β)
    (p : MvPolynomial (σ ⊕ α) ℤ) :
    (auxiliaryRename f p).totalDegree ≤ p.totalDegree :=
  totalDegree_rename_le _ _

theorem totalDegree_neg_le {σ : Type*} (p : MvPolynomial σ ℤ) :
    (-p).totalDegree ≤ p.totalDegree := by
  calc
    (-p).totalDegree = (C (-1 : ℤ) * p).totalDegree := by simp
    _ ≤ (C (-1 : ℤ) : MvPolynomial σ ℤ).totalDegree + p.totalDegree := totalDegree_mul _ _
    _ = p.totalDegree := by simp

theorem totalDegree_sub_le {σ : Type*} (p q : MvPolynomial σ ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  exact (totalDegree_add _ _).trans (max_le_max le_rfl (totalDegree_neg_le q))

/-- A finite quadratic system with a linear output, together with proofs
that all its solutions compute the polynomial and that every input has
a solution. -/
structure QuadraticLift {σ : Type u} (p : MvPolynomial σ ℤ) where
  Aux : Type
  finiteAux : Fintype Aux
  constraints : Aux → MvPolynomial (σ ⊕ Aux) ℤ
  output : MvPolynomial (σ ⊕ Aux) ℤ
  constraint_degree : ∀ a, (constraints a).totalDegree ≤ 2
  output_degree : output.totalDegree ≤ 1
  sound : ∀ (x : σ → ℚ) (w : Aux → ℚ),
    (∀ a, rationalEval (Sum.elim x w) (constraints a) = 0) →
      rationalEval (Sum.elim x w) output = rationalEval x p
  complete : ∀ x : σ → ℚ, ∃ w : Aux → ℚ,
    ∀ a, rationalEval (Sum.elim x w) (constraints a) = 0

attribute [instance] QuadraticLift.finiteAux

namespace QuadraticLift

variable {σ : Type u} {p q : MvPolynomial σ ℤ}

/-- Constants have no gates. -/
def constant (c : ℤ) : QuadraticLift (C c : MvPolynomial σ ℤ) where
  Aux := PEmpty
  finiteAux := inferInstance
  constraints := PEmpty.elim
  output := C c
  constraint_degree := fun a => PEmpty.elim a
  output_degree := by simp
  sound := by intros; simp
  complete := fun _ => ⟨PEmpty.elim, fun a => PEmpty.elim a⟩

/-- Addition joins two systems with disjoint auxiliary variables. -/
def add (L : QuadraticLift p) (R : QuadraticLift q) : QuadraticLift (p + q) where
  Aux := L.Aux ⊕ R.Aux
  finiteAux := inferInstance
  constraints := Sum.elim
    (fun a => auxiliaryRename Sum.inl (L.constraints a))
    (fun a => auxiliaryRename Sum.inr (R.constraints a))
  output := auxiliaryRename Sum.inl L.output + auxiliaryRename Sum.inr R.output
  constraint_degree := by
    rintro (a | a)
    · exact (totalDegree_auxiliaryRename_le _ _).trans (L.constraint_degree a)
    · exact (totalDegree_auxiliaryRename_le _ _).trans (R.constraint_degree a)
  output_degree := (totalDegree_add _ _).trans (max_le
    ((totalDegree_auxiliaryRename_le _ _).trans L.output_degree)
    ((totalDegree_auxiliaryRename_le _ _).trans R.output_degree))
  sound := by
    intro x w hw
    rw [map_add, rationalEval_auxiliaryRename, rationalEval_auxiliaryRename]
    rw [L.sound x (w ∘ Sum.inl), R.sound x (w ∘ Sum.inr), map_add]
    · intro a
      simpa only [Sum.elim_inr, rationalEval_auxiliaryRename] using hw (Sum.inr a)
    · intro a
      simpa only [Sum.elim_inl, rationalEval_auxiliaryRename] using hw (Sum.inl a)
  complete := by
    intro x
    obtain ⟨u, hu⟩ := L.complete x
    obtain ⟨v, hv⟩ := R.complete x
    refine ⟨Sum.elim u v, ?_⟩
    rintro (a | a)
    · simpa only [Sum.elim_inl, rationalEval_auxiliaryRename] using hu a
    · simpa only [Sum.elim_inr, rationalEval_auxiliaryRename] using hv a

/-- Multiplication by an input adds one output variable and one quadratic
equation. The older gates are unchanged after renaming. -/
def mul_X (L : QuadraticLift p) (i : σ) : QuadraticLift (p * X i) where
  Aux := Option L.Aux
  finiteAux := inferInstance
  constraints := fun a => a.elim
    (X (Sum.inr none) - auxiliaryRename some L.output * X (Sum.inl i))
    (fun a => auxiliaryRename some (L.constraints a))
  output := X (Sum.inr none)
  constraint_degree := by
    intro a
    cases a with
    | none =>
      apply (totalDegree_sub_le _ _).trans
      apply max_le
      · simp
      · have ho := (totalDegree_auxiliaryRename_le some L.output).trans L.output_degree
        have hm := totalDegree_mul (auxiliaryRename some L.output)
          (X (Sum.inl i) : MvPolynomial (σ ⊕ Option L.Aux) ℤ)
        simp only [totalDegree_X] at hm
        omega
    | some a => exact (totalDegree_auxiliaryRename_le _ _).trans (L.constraint_degree a)
  output_degree := by simp
  sound := by
    intro x w hw
    have hold : ∀ a, rationalEval (Sum.elim x (w ∘ some)) (L.constraints a) = 0 := by
      intro a
      simpa only [Option.elim_some, rationalEval_auxiliaryRename] using hw (some a)
    have hn := hw none
    simp only [Option.elim_none, map_sub, map_mul, eval₂Hom_X, Sum.elim_inl,
      Sum.elim_inr, rationalEval_auxiliaryRename] at hn ⊢
    rw [L.sound x (w ∘ some) hold] at hn
    exact sub_eq_zero.mp hn
  complete := by
    intro x
    obtain ⟨w, hw⟩ := L.complete x
    refine ⟨fun a => a.elim (rationalEval x (p * X i)) w, ?_⟩
    intro a
    cases a with
    | none =>
      simp only [Option.elim_none, map_sub, map_mul, eval₂Hom_X, Sum.elim_inl,
        Sum.elim_inr, rationalEval_auxiliaryRename]
      change rationalEval x p * x i - rationalEval (Sum.elim x w) L.output * x i = 0
      rw [L.sound x w hw, sub_self]
    | some a =>
      simpa only [Option.elim_some, rationalEval_auxiliaryRename] using hw a

end QuadraticLift

/-- Every integer polynomial has a finite quadratic lifting, with no
assumption on its coefficients, degree, or rational zeros. -/
theorem exists_quadraticLift {σ : Type u} (p : MvPolynomial σ ℤ) :
    Nonempty (QuadraticLift p) := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨QuadraticLift.constant c⟩
  | add p q hp hq =>
    obtain ⟨L⟩ := hp
    obtain ⟨R⟩ := hq
    exact ⟨L.add R⟩
  | mul_X p i hp =>
    obtain ⟨L⟩ := hp
    exact ⟨L.mul_X i⟩

#print axioms exists_quadraticLift

end GaloisForLFunctions.HTGeometry.Polynomial
