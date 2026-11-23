import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExteriorProductPairing
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLogarithmicForms
import Mathlib.RingTheory.Trace.Basic

/-! The trace of the top wedge pairs complementary rational form
degrees nondegenerately over the projective coordinate field. -/

noncomputable section

open GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- Trace separability and exterior multiplication detect every
rational form in a degree complementary to the testing degree. -/
theorem IsFinCover.trace_wedge_pairing_nondegenerate (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) {p q : ℕ} (hpq : p + q = d)
    {y : DR k E} (hy : y ∈ ⋀[E]^q Ω[E⁄k])
    (hz : ∀ a ∈ ⋀[E]^p Ω[E⁄k], Algebra.trace F E (τ (a * y)) = 0) :
    y = 0 := by
  letI := h.fin
  letI := h.sep
  subst d
  obtain ⟨b, hb⟩ := h.exists_coordinateDifferentialBasis
  have hb₀ : τ (ExteriorAlgebra.ιMulti E (p + q) b) ≠ 0 := by
    intro h₀
    have e : vol0 k E x =
        (∏ j : Fin (p + q), (algebraMap F E (x j.succ / x 0))⁻¹) • ExteriorAlgebra.ιMulti E (p + q) b := by
      rw [← AlternatingMap.map_smul_univ]
      simp only [vol0, hb]
    have h₁ := hτ.1
    rw [e, map_smul, h₀, smul_zero] at h₁
    exact zero_ne_one h₁
  refine wedge_pairing_sep b τ hb₀ y hy fun a ha => ?_
  refine (traceForm_nondegenerate F E).1 _ fun c => ?_
  rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc]
  exact hz _ (Submodule.smul_mem _ c ha)

/-- Complementary rational exterior degrees have the same dimension. -/
theorem IsFinCover.finrank_exteriorDifferentials_complement (h : IsFinCover k E x)
    {p q : ℕ} (hpq : p + q = d) :
    Module.finrank E (⋀[E]^p Ω[E⁄k]) = Module.finrank E (⋀[E]^q Ω[E⁄k]) := by
  obtain ⟨b, _⟩ := h.exists_coordinateDifferentialBasis
  letI : Module.Finite E Ω[E⁄k] := Module.Finite.of_basis b
  have e : Module.finrank E Ω[E⁄k] = d := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin _)
  rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq, e]
  exact Nat.choose_symm_of_eq_add hpq.symm

end GlobalTheory.PD
