import GaloisForLFunctions.HTGeometry.LogDerivFullIndependence
import GaloisForLFunctions.HTGeometry.LogDerivFamilyRealization
import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge

/-!
# From carrier freeness to solution freeness

If a family `sigma` admits no algebraic differential relation on a connected open set, and `sol`
solves `sol i ' = sigma i * sol i` with `sol i` analytic and nonvanishing, then `sol` admits no
algebraic differential relation either.

This is the `r = 0` instance of `logDeriv_fullJet_independent`, glued to the truncation bridge.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Negating a family preserves relation-freeness.** -/
theorem not_familyDifferentiallyAlgebraicOn_neg {m : ℕ} {U : Set ℂ} {g : Fin m → ℂ → ℂ}
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : ¬ FamilyDifferentiallyAlgebraicOn g U) :
    ¬ FamilyDifferentiallyAlgebraicOn (fun i z => -(g i z)) U := by
  intro hcon
  refine h (familyDifferentiallyAlgebraicOn_of_mul_polynomial g (fun _ => -1) (by simp) hg ?_)
  have hfun : (fun i w => Polynomial.eval w ((-1 : Polynomial ℂ)) * g i w)
      = fun i z => -(g i z) := by
    funext i w
    simp
  rw [hfun]
  exact hcon

/-- **Solutions of `y' = sigma y` inherit relation-freeness from their carriers.** -/
theorem not_familyDifferentiallyAlgebraicOn_of_logDerivFamily {m : ℕ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {sigma sol : Fin m → ℂ → ℂ}
    (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U)
    (hsolA : ∀ i, AnalyticOnNhd ℂ (sol i) U)
    (hsolne : ∀ i, ∀ z ∈ U, sol i z ≠ 0)
    (hrel : ∀ i, ∀ z ∈ U, deriv (sol i) z = sigma i z * sol i z)
    (hind : ¬ FamilyDifferentiallyAlgebraicOn sigma U) :
    ¬ FamilyDifferentiallyAlgebraicOn sol U := by
  refine not_familyDifferentiallyAlgebraicOn_of_fullJet_independent (fun Q hQ => ?_)
  refine logDeriv_fullJet_independent (r := 0) hUo hUc hUne ?_ hs hsolA hsolne ?_
    (fun P hP => fullJet_independent_of_not_familyDifferentiallyAlgebraicOn hind P hP) Q hQ
  · intro n z₀ y hy
    obtain ⟨V, H, E, hVo, hz₀, hH, hE, _, hrel', hjet⟩ :=
      exists_logDerivFamily_realizing_jets n z₀ y hy
    exact ⟨V, H, E, hVo, hz₀, hH, hE, hrel', hjet⟩
  · intro i z hz
    rw [iteratedDeriv_zero]
    exact hrel i z hz

end

end GaloisForLFunctions.HTGeometry
