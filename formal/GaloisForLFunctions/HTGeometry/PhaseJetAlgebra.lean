import GaloisForLFunctions.HTGeometry.PolyannulusFunctionDomain
import GaloisForLFunctions.HTGeometry.TorusDerivationLeibniz

/-!
# Phase jets as elements of the algebra of holomorphic functions

Pointwise evaluation is a `ℂ`-algebra homomorphism on the algebra of
holomorphic functions on an open set, so a polynomial relation among elements
of that algebra is exactly a pointwise polynomial relation among the functions.

Algebraic independence of the phase jets is therefore the absence of a nonzero
polynomial vanishing identically on the polyannulus, which is the form in which
the differential-rank argument and the minimal-order argument both deliver
their conclusions.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Pointwise evaluation is an algebra homomorphism -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Pointwise evaluation on the algebra of holomorphic functions. -/
def analyticEvalHom {U : Set E} (z : ↥U) : ↥(analyticSubalgebra U) →ₐ[ℂ] ℂ where
  toFun f := (f : ↥U → ℂ) z
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem analyticEvalHom_apply {U : Set E} (z : ↥U)
    (f : ↥(analyticSubalgebra U)) : analyticEvalHom z f = (f : ↥U → ℂ) z := rfl

theorem analyticEvalHom_aeval {U : Set E} {ι : Type*}
    (x : ι → ↥(analyticSubalgebra U)) (P : MvPolynomial ι ℂ) (z : ↥U) :
    analyticEvalHom z (MvPolynomial.aeval x P)
      = MvPolynomial.eval (fun i => (x i : ↥U → ℂ) z) P := by
  have hcomp := MvPolynomial.comp_aeval (R := ℂ) x (analyticEvalHom (U := U) z)
  have happ := congrArg (fun φ : MvPolynomial ι ℂ →ₐ[ℂ] ℂ => φ P) hcomp
  simpa [MvPolynomial.aeval_eq_eval] using happ

/-- **A polynomial relation in the algebra is a pointwise polynomial
relation.** -/
theorem algebraicIndependent_analyticSubalgebra_iff {U : Set E} {ι : Type*}
    (x : ι → ↥(analyticSubalgebra U)) :
    AlgebraicIndependent ℂ x ↔
      ∀ P : MvPolynomial ι ℂ,
        (∀ z : ↥U, MvPolynomial.eval (fun i => (x i : ↥U → ℂ) z) P = 0) →
          P = 0 := by
  rw [algebraicIndependent_iff]
  constructor
  · intro h P hP
    refine h P (Subtype.ext (funext fun z => ?_))
    show analyticEvalHom z (MvPolynomial.aeval x P) = (0 : ↥U → ℂ) z
    rw [analyticEvalHom_aeval]
    exact hP z
  · intro h P hP
    refine h P fun z => ?_
    rw [← analyticEvalHom_aeval x P z, hP]
    rfl

/-! ### The phase jets -/

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The `k`-th phase jet as an element of the algebra of holomorphic functions
on the polyannulus. -/
def phaseJetElem {ρ : d → ℝ} (omega : d → ℝ) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) :
    ↥(analyticSubalgebra (polyannulus ρ)) :=
  analyticRestrict (phaseJet omega F k) (analyticOnNhd_phaseJet omega hF k)

@[simp] theorem phaseJetElem_apply {ρ : d → ℝ} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ)
    (z : ↥(polyannulus ρ)) :
    (phaseJetElem omega hF k : ↥(polyannulus ρ) → ℂ) z
      = phaseJet omega F k z.1 := rfl

/-- **Algebraic independence of phase jets is the absence of an identically
vanishing polynomial relation.** -/
theorem algebraicIndependent_phaseJetElem_iff {ρ : d → ℝ} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {ι : Type*}
    (k : ι → ℕ) :
    AlgebraicIndependent ℂ (fun i => phaseJetElem omega hF (k i)) ↔
      ∀ P : MvPolynomial ι ℂ,
        (∀ z ∈ polyannulus ρ,
            MvPolynomial.eval (fun i => phaseJet omega F (k i) z) P = 0) →
          P = 0 := by
  rw [algebraicIndependent_analyticSubalgebra_iff]
  constructor
  · intro h P hP
    exact h P fun z => hP z.1 z.2
  · intro h P hP
    exact h P fun z hz => hP ⟨z, hz⟩

/-! ### Comparing an independent family with a dependent one -/

/-- **A subfamily of an algebraically independent family is algebraically
independent.** -/
theorem algebraicIndependent_comp_of_injective {A : Type*} [CommRing A]
    [Algebra ℂ A] {ι ι' : Type*} {x : ι → A} (hx : AlgebraicIndependent ℂ x)
    (f : ι' → ι) (hf : Function.Injective f) :
    AlgebraicIndependent ℂ (x ∘ f) := hx.comp f hf

/-- **The counting step.**  If some family of `m` phase jets is algebraically
independent and every family of `n + 1` phase jets is algebraically dependent,
then `m ≤ n`. -/
theorem le_of_algebraicIndependent_of_not_algebraicIndependent {ρ : d → ℝ}
    (omega : d → ℝ) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {m n : ℕ} {k : Fin m → ℕ}
    (hind : AlgebraicIndependent ℂ (fun i => phaseJetElem omega hF (k i)))
    (hdep : ∀ l : Fin (n + 1) → ℕ,
      ¬ AlgebraicIndependent ℂ (fun i => phaseJetElem omega hF (l i))) :
    m ≤ n := by
  by_contra hlt
  have hle : n + 1 ≤ m := by omega
  let f : Fin (n + 1) → Fin m := fun i => ⟨(i : ℕ), lt_of_lt_of_le i.2 hle⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    exact Fin.ext (congrArg (fun w : Fin m => (w : ℕ)) hab)
  exact hdep (k ∘ f) (hind.comp f hfinj)

end

end GaloisForLFunctions.HTGeometry
