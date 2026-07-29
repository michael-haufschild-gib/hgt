import Mathlib

/-!
# Polynomial jet evaluation and hypertranscendence

The finite-resolution law-escape theorem of `wigner-smith-finite-resolution-law-escape` evaluates a
finite-dimensional space of polynomial laws `P(E, Y_0, …, Y_r)` on the jet
`(E, f(E), f'(E), …, f^{(r)}(E))` of a candidate scattering phase `(10)-(11)`.  This file gives the
algebraic layer: the evaluation `Ev_g : P ↦ (E ↦ P(g_0 E, …, g_{n-1} E))` is `ℝ`-linear, and its
**injectivity is exactly the hypertranscendence** of the jet — no nonzero polynomial law annihilates
it everywhere `(12)`.  The finite-dimensional normed / operator-norm layer that feeds
`injMod_pos_of_close_to_injective` sits on top of this.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- Jet evaluation: given jet-coordinate functions `g i : ℝ → ℝ` (e.g. `g 0 = id`, `g 1 = f`,
`g 2 = f'`, …, `g (r+1) = f^(r)`), the map sending a polynomial law `P` to the function
`E ↦ P(g 0 E, …, g (n-1) E)`.  Linear in `P`. -/
noncomputable def jetEval {n : ℕ} (g : Fin n → (ℝ → ℝ)) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] (ℝ → ℝ) where
  toFun P := fun E => MvPolynomial.eval (fun i => g i E) P
  map_add' P Q := by ext E; simp
  map_smul' c P := by ext E; simp

@[simp] theorem jetEval_apply {n : ℕ} (g : Fin n → (ℝ → ℝ)) (P : MvPolynomial (Fin n) ℝ) (E : ℝ) :
    jetEval g P E = MvPolynomial.eval (fun i => g i E) P := rfl

/-- **Evaluation injectivity is exactly the no-nonzero-relation (hypertranscendence) property.**
`Ev_g` is injective iff the only polynomial law annihilating the jet everywhere is zero. -/
theorem jetEval_injective_iff {n : ℕ} (g : Fin n → (ℝ → ℝ)) :
    Function.Injective (jetEval g) ↔
      ∀ P : MvPolynomial (Fin n) ℝ,
        (∀ E, MvPolynomial.eval (fun i => g i E) P = 0) → P = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h P hP
    exact h P (by ext E; simpa using hP E)
  · intro h P hP
    exact h P (fun E => by have := congrFun hP E; simpa using this)

/-- Finite measurement map `(16)`: sample the evaluated law at energies `E_1, …, E_m`,
`P ↦ (Ev_g(P)(E_1), …, Ev_g(P)(E_m))`.  Linear, into the finite-dimensional space `Fin m → ℝ`. -/
noncomputable def sampleEval {n m : ℕ} (g : Fin n → (ℝ → ℝ)) (E : Fin m → ℝ) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] (Fin m → ℝ) where
  toFun P := fun j => jetEval g P (E j)
  map_add' P Q := by ext j; simp
  map_smul' c P := by ext j; simp

@[simp] theorem sampleEval_apply {n m : ℕ} (g : Fin n → (ℝ → ℝ)) (E : Fin m → ℝ)
    (P : MvPolynomial (Fin n) ℝ) (j : Fin m) :
    sampleEval g E P j = jetEval g P (E j) := rfl

/-- If a finite energy packet already makes the measurement map injective, the underlying jet is
hypertranscendental: `sampleEval` factors through `jetEval`, so its injectivity forces
`jetEval`-injectivity `(15)→(12)`. -/
theorem injective_jetEval_of_injective_sampleEval {n m : ℕ} (g : Fin n → (ℝ → ℝ)) (E : Fin m → ℝ)
    (h : Function.Injective (sampleEval g E)) : Function.Injective (jetEval g) := by
  intro P Q hPQ
  exact h (by ext j; simp only [sampleEval_apply, hPQ])

/-- When the jet-coordinate functions are continuous, the evaluated law `Ev_g(P)` is a continuous
function — i.e. `jetEval` lands in `C(I)`, the sup-norm codomain of `(11)`. -/
theorem continuous_jetEval {n : ℕ} {g : Fin n → (ℝ → ℝ)} (hg : ∀ i, Continuous (g i))
    (P : MvPolynomial (Fin n) ℝ) : Continuous (jetEval g P) := by
  have hpt : Continuous (fun E => (fun i => g i E : Fin n → ℝ)) := continuous_pi hg
  have := (MvPolynomial.continuous_eval P).comp hpt
  rw [show jetEval g P =
    (fun x => MvPolynomial.eval x P) ∘ fun E i => g i E by rfl]
  exact this

end GaloisForLFunctions.HTGeometry
