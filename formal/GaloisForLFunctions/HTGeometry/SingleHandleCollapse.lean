import GaloisForLFunctions.HTGeometry.RationalPadeCollapse
import GaloisForLFunctions.HTGeometry.PRecursiveDFinite
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAntiderivative

/-!
# The single-handle collapse lemma, class (I)

Each DA-forcing finite handle — an algebraic addition theorem, a P-recursive coefficient sequence,
a stabilizing Padé table, a differentially algebraic derivative, or an algebraic relation — forces
differential algebraicity.  A hypertranscendental function therefore carries none of them: every
such handle is vacuous on the hypertranscendental class.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **C05.**  A differentially algebraic derivative forces differential algebraicity. -/
theorem hypertranscendental_deriv_of_hypertranscendental {f : ℂ → ℂ}
    (hHT : Hypertranscendental f) : Hypertranscendental (deriv f) :=
  fun hDA => hHT (differentiallyAlgebraic_of_deriv hDA)

/-- **Single-handle collapse, class (I).**  A hypertranscendental entire function carries none of
the DA-forcing finite handles. -/
theorem hypertranscendental_no_classI_handle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hHT : Hypertranscendental f) :
    (¬ ∃ P : Polynomial (Polynomial ℂ), ∀ x y : ℂ, f (x + y) = biEval P (f x) (f y)) ∧
    (¬ PRecursive (fun n => PowerSeries.coeff n (taylorSeries f))) ∧
    (¬ ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
        ∀ k : ℕ, iteratedDeriv k (fun z => Q.eval z * f z - P.eval z) 0 = 0) ∧
    (¬ ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ z : ℂ, Q.eval z * f z = P.eval z) ∧
    Hypertranscendental (deriv f) ∧
    (¬ ∃ P : Polynomial ℂ, P ≠ 0 ∧ ∀ z : ℂ, P.eval (f z) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, hypertranscendental_deriv_of_hypertranscendental hHT, ?_⟩
  · rintro ⟨P, hadd⟩
    exact hHT (differentiallyAlgebraic_of_additionTheorem hf hadd)
  · exact not_pRecursive_taylorSeries_of_hypertranscendental hf hHT
  · rintro ⟨P, Q, hQ, hjet⟩
    exact hHT (differentiallyAlgebraic_of_padeStabilization hf P Q hQ hjet)
  · rintro ⟨P, Q, hQ, hrep⟩
    exact hHT (differentiallyAlgebraic_of_rational P Q hQ hrep)
  · rintro ⟨P, hP, hroot⟩
    exact hHT (differentiallyAlgebraic_of_algebraic P hP hroot)

end

end GaloisForLFunctions.HTGeometry
