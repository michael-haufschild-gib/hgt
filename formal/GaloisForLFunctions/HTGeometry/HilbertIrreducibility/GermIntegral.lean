/-
# Bivariate algebraic relations for germs of analytic functions

A function `y` defined near `s₀ ∈ ℂ` which is *integral over `ℚ[X]`* inside the germ ring
`Germ (𝓝 s₀) ℂ` satisfies a genuine bivariate polynomial relation `P(s, y s) = 0` near `s₀`, with
`P ∈ ℚ[X][Y]` monic in `Y` of positive degree.  This is how step 3 of Coleman--Zwald gets its
algebraic relation: the branch functions of an algebraic equation are integral, and integrality is
closed under sums and products, so every coefficient of every partial root product is integral.

Working in the germ ring rather than with functions on a fixed disc means every hypothesis is an
"eventually near `s₀`" statement, which is exactly the form the analytic input comes in.
-/
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial Filter Topology

variable {R : Type*} [CommRing R] [Algebra R ℂ]

/-- Bivariate evaluation of `P ∈ ℚ[X][Y]` at `(s, w)`. -/
noncomputable def bivEval (P : Polynomial (Polynomial R)) (s w : ℂ) : ℂ :=
  Polynomial.eval₂ (Polynomial.aeval s : Polynomial R →ₐ[R] ℂ).toRingHom w P

/-- Pointwise evaluation of `ℚ[X]` on complex numbers, as a ring hom into the function ring. -/
noncomputable def piEvalHom (R : Type*) [CommRing R] [Algebra R ℂ] : Polynomial R →+* (ℂ → ℂ) :=
  RingHom.pi fun s : ℂ => (Polynomial.aeval s : Polynomial R →ₐ[R] ℂ).toRingHom

@[simp]
theorem piEvalHom_apply (p : Polynomial R) (s : ℂ) :
    piEvalHom R p s = Polynomial.aeval s p := rfl

/-- Evaluation of `ℚ[X]` as a ring hom into the germ ring at `s₀`. -/
noncomputable def germEvalHom (R : Type*) [CommRing R] [Algebra R ℂ] (s₀ : ℂ) : Polynomial R →+* Germ (𝓝 s₀) ℂ :=
  (Germ.coeRingHom (𝓝 s₀)).comp (piEvalHom R)

/-- The germ ring at `s₀` is a `ℚ[X]`-algebra by evaluation. -/
noncomputable scoped instance germAlgebra {s₀ : ℂ} :
    Algebra (Polynomial R) (Germ (𝓝 s₀) ℂ) :=
  (germEvalHom R s₀).toAlgebra

theorem algebraMap_germ {s₀ : ℂ} (p : Polynomial R) :
    algebraMap (Polynomial R) (Germ (𝓝 s₀) ℂ) p = ((piEvalHom R p : ℂ → ℂ) : Germ (𝓝 s₀) ℂ) := rfl

/-- Evaluation of a bivariate polynomial in the germ ring is the germ of its pointwise
evaluation. -/
theorem aeval_germ_eq {s₀ : ℂ} (y : ℂ → ℂ) (P : Polynomial (Polynomial R)) :
    (Polynomial.aeval ((y : ℂ → ℂ) : Germ (𝓝 s₀) ℂ) P : Germ (𝓝 s₀) ℂ)
      = ((fun s => bivEval P s (y s) : ℂ → ℂ) : Germ (𝓝 s₀) ℂ) := by
  have hcomp : ∀ s : ℂ, (Pi.evalRingHom (fun _ : ℂ => ℂ) s).comp (piEvalHom R)
      = (Polynomial.aeval s : Polynomial R →ₐ[R] ℂ).toRingHom :=
    fun s => RingHom.ext fun p => rfl
  have hfun : (fun s => bivEval P s (y s)) = Polynomial.eval₂ (piEvalHom R) y P := by
    funext s
    have h := Polynomial.hom_eval₂ P (piEvalHom R) (Pi.evalRingHom (fun _ : ℂ => ℂ) s) y
    rw [hcomp s] at h
    exact h.symm
  rw [hfun]
  rw [Polynomial.aeval_def]
  exact (Polynomial.hom_eval₂ P (piEvalHom R) (Germ.coeRingHom (𝓝 s₀)) y).symm

/-- **From integrality to a bivariate relation.** -/
theorem exists_monic_bivariate_of_isIntegral {s₀ : ℂ} {y : ℂ → ℂ}
    (h : IsIntegral (Polynomial R) ((y : ℂ → ℂ) : Germ (𝓝 s₀) ℂ)) :
    ∃ P : Polynomial (Polynomial R), P.Monic ∧ 0 < P.natDegree ∧
      ∀ᶠ s in 𝓝 s₀, bivEval P s (y s) = 0 := by
  obtain ⟨P, hPmonic, hPeval⟩ := h
  have hdeg : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · exfalso
      have hP1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hPmonic h0
      rw [hP1] at hPeval
      simp at hPeval
    · exact h0
  refine ⟨P, hPmonic, hdeg, ?_⟩
  rw [← Polynomial.aeval_def] at hPeval
  have := aeval_germ_eq (s₀ := s₀) y P
  rw [hPeval] at this
  have hzero : ((fun s => bivEval P s (y s) : ℂ → ℂ) : Germ (𝓝 s₀) ℂ) = 0 := this.symm
  have := Germ.coe_eq.mp (by simpa using hzero : ((fun s => bivEval P s (y s) : ℂ → ℂ)
      : Germ (𝓝 s₀) ℂ) = ((0 : ℂ → ℂ) : Germ (𝓝 s₀) ℂ))
  filter_upwards [this] with s hs using hs

/-- **From a bivariate monic relation to integrality.** -/
theorem isIntegral_of_monic_bivariate {s₀ : ℂ} {y : ℂ → ℂ} {P : Polynomial (Polynomial R)}
    (hPmonic : P.Monic) (hrel : ∀ᶠ s in 𝓝 s₀, bivEval P s (y s) = 0) :
    IsIntegral (Polynomial R) ((y : ℂ → ℂ) : Germ (𝓝 s₀) ℂ) := by
  refine ⟨P, hPmonic, ?_⟩
  rw [← Polynomial.aeval_def, aeval_germ_eq]
  have hz : ((fun s => bivEval P s (y s) : ℂ → ℂ) : Germ (𝓝 s₀) ℂ)
      = ((0 : ℂ → ℂ) : Germ (𝓝 s₀) ℂ) :=
    Germ.coe_eq.mpr (by filter_upwards [hrel] with s hs using hs)
  simpa using hz

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
