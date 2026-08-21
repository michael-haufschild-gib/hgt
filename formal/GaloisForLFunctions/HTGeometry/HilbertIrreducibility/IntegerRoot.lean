/-
# Rational values of a monic integral relation are integers

If `Q ∈ ℤ[T][Y]` is monic in `Y` and a *rational* number `c` satisfies `Q(n, c) = 0` for an integer
`n`, then `c` is an integer: `c` is integral over `ℤ` and `ℤ` is integrally closed in `ℚ`.

This is `Exercise 2` of Coleman--Zwald, in the form used by step 3 of the proof of Hilbert's
irreducibility theorem.
-/
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.GermIntegral

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

theorem ringHom_comp_evalRingHom (n : ℤ) :
    (Int.castRingHom ℂ).comp (Polynomial.evalRingHom n)
      = (Polynomial.aeval ((n : ℤ) : ℂ) : Polynomial ℤ →ₐ[ℤ] ℂ).toRingHom := by
  refine RingHom.ext fun p => ?_
  have h := Polynomial.eval₂_at_apply (p := p) (Int.castRingHom ℂ) n
  have hn : (Int.castRingHom ℂ) n = ((n : ℤ) : ℂ) := rfl
  rw [hn] at h
  show (Int.castRingHom ℂ) (Polynomial.eval n p) = Polynomial.eval₂ _ _ p
  rw [← h]
  rfl

/-- **Rational roots of a monic integral relation are integers.** -/
theorem exists_int_of_bivEval {Q : Polynomial (Polynomial ℤ)} (hQ : Q.Monic) {n : ℤ} {c : ℚ}
    (h : bivEval Q ((n : ℤ) : ℂ) ((c : ℚ) : ℂ) = 0) : ∃ N : ℤ, c = (N : ℚ) := by
  classical
  set Qn : Polynomial ℤ := Q.map (Polynomial.evalRingHom n) with hQn
  have hQnMonic : Qn.Monic := hQ.map _
  have hcast : ((Polynomial.aeval c Qn : ℚ) : ℂ) = bivEval Q ((n : ℤ) : ℂ) ((c : ℚ) : ℂ) := by
    have h1 : (Rat.castHom ℂ) (Polynomial.eval₂ (Int.castRingHom ℚ) c Qn)
        = Polynomial.eval₂ ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) ((c : ℚ) : ℂ) Qn :=
      Polynomial.hom_eval₂ Qn (Int.castRingHom ℚ) (Rat.castHom ℂ) c
    have h2 : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
      refine RingHom.ext fun z => ?_
      simp
    rw [h2] at h1
    have h3 : Polynomial.eval₂ (Int.castRingHom ℂ) ((c : ℚ) : ℂ) Qn
        = Polynomial.eval₂ ((Int.castRingHom ℂ).comp (Polynomial.evalRingHom n))
            ((c : ℚ) : ℂ) Q := by
      rw [hQn, Polynomial.eval₂_map]
    rw [h3, ringHom_comp_evalRingHom n] at h1
    simpa [Polynomial.aeval_def, bivEval] using h1
  have hzero : Polynomial.aeval c Qn = 0 := by
    have : ((Polynomial.aeval c Qn : ℚ) : ℂ) = 0 := by rw [hcast, h]
    exact_mod_cast this
  have hint : IsIntegral ℤ c := ⟨Qn, hQnMonic, hzero⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨y, by simpa using hy.symm⟩

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
