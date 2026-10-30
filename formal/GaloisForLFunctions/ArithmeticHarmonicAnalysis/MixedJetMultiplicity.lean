import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Analytic mixed jets and point-ideal multiplicity

Centered Taylor coefficients identify full polynomial multiplicity with
ordinary analytic mixed derivatives. Coordinate relabeling preserves this
filtration, so finite prime coordinates may use the existing analytic jet API.
-/

open MvPolynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Point-ideal multiplicity is exactly the vanishing of all lower centered coefficients. -/
theorem mem_pointIdeal_pow_iff_centered_coeff {ι : Type*}
    (P : MvPolynomial ι ℂ) (x : ι → ℂ) (r : ℕ) :
    P ∈ vanishingIdeal ℂ {x} ^ r ↔
      ∀ a : ι →₀ ℕ, Finsupp.degree a < r →
        (mvPolynomialBaseTranslation x P).coeff a = 0 := by
  constructor
  · intro h
    exact (mem_pow_idealOfVars_iff' r _).mp
      (HTGeometry.mvPolynomialBaseTranslation_mem_idealOfVars_pow_of_mem_pointIdeal_pow x h)
  · intro h
    have hm := (mem_pow_idealOfVars_iff' r _).mpr h
    rw [← HTGeometry.map_vanishingIdeal_singleton_mvPolynomialBaseTranslation x,
      ← Ideal.map_pow] at hm
    obtain ⟨Q, hQ, heq⟩ := (Ideal.mem_map_iff_of_surjective
      (mvPolynomialBaseTranslation x).toRingHom
      (mvPolynomialBaseTranslation x).surjective).mp hm
    exact (mvPolynomialBaseTranslation x).injective heq ▸ hQ

/-- Ordinary analytic mixed derivatives and algebraic point multiplicity agree for polynomials. -/
theorem mem_pointIdeal_pow_iff_mixedJets {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) (r : ℕ) :
    P ∈ vanishingIdeal ℂ {x} ^ r ↔
      ∀ a : Fin d →₀ ℕ, Finsupp.degree a < r →
        HTGeometry.multiIndexJetEvalCLM x a (HTGeometry.mvPolynomialMultivariateEntire P) = 0 := by
  rw [mem_pointIdeal_pow_iff_centered_coeff]
  constructor
  · intro h a ha
    rw [HTGeometry.multiIndexJetEvalCLM_mvPolynomial_eq_centered_coeff, h a ha, zero_mul]
  · intro h a ha
    have hz := h a ha
    rw [HTGeometry.multiIndexJetEvalCLM_mvPolynomial_eq_centered_coeff] at hz
    exact (mul_eq_zero.mp hz).resolve_right (HTGeometry.multiIndexFactorial_ne_zero a)

/-- Relabeling coordinates preserves every point-ideal power. -/
theorem renameEquiv_mem_pointIdeal_pow_iff {ι κ : Type*} (e : ι ≃ κ)
    (P : MvPolynomial ι ℂ) (x : ι → ℂ) (r : ℕ) :
    renameEquiv ℂ e P ∈ vanishingIdeal ℂ {fun j => x (e.symm j)} ^ r ↔
      P ∈ vanishingIdeal ℂ {x} ^ r := by
  let E := renameEquiv ℂ e
  have hI : Ideal.map E (vanishingIdeal ℂ {x}) =
      vanishingIdeal ℂ {fun j => x (e.symm j)} := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨P, hP, rfl⟩ := (Ideal.mem_map_iff_of_surjective E E.surjective).mp hQ
      simpa only [mem_vanishingIdeal_singleton_iff, aeval_eq_eval, E,
        renameEquiv_apply, eval_rename, Function.comp_def, Equiv.symm_apply_apply] using hP
    · intro hQ
      have hP : E.symm Q ∈ vanishingIdeal ℂ {x} := by
        simpa only [mem_vanishingIdeal_singleton_iff, aeval_eq_eval, E,
          renameEquiv_symm, renameEquiv_apply, eval_rename, Function.comp_def] using hQ
      exact E.apply_symm_apply Q ▸ Ideal.mem_map_of_mem E hP
  rw [← hI, ← Ideal.map_pow]
  constructor
  · intro h
    obtain ⟨Q, hQ, heq⟩ := (Ideal.mem_map_iff_of_surjective E E.surjective).mp h
    exact E.injective heq ▸ hQ
  · exact Ideal.mem_map_of_mem E

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
