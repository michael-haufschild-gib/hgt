import GaloisForLFunctions.RHTower.LandauAbscissaRigidity

/-!
# The convergence abscissa exists

For a nonnegative measure the Laplace mass is antitone, so the set of exponents where it is finite is
an up-set; its infimum is the abscissa provided the set is nonempty and bounded below, which is
exactly the statement that the transform converges somewhere and diverges somewhere.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **The convergence abscissa exists.** -/
theorem exists_isAbscissa {ν : Measure ℝ}
    (hconv : ∃ σ : ℝ, laplaceMass ν σ ≠ ⊤) (hdiv : ∃ σ : ℝ, laplaceMass ν σ = ⊤) :
    ∃ c : ℝ, IsAbscissa ν c := by
  classical
  set S : Set ℝ := {σ : ℝ | laplaceMass ν σ ≠ ⊤} with hSdef
  obtain ⟨σ₁, hσ₁⟩ := hconv
  obtain ⟨σ₀, hσ₀⟩ := hdiv
  have hne : S.Nonempty := ⟨σ₁, hσ₁⟩
  have hbdd : BddBelow S := by
    refine ⟨σ₀, fun τ hτ => ?_⟩
    by_contra hcon
    have hcon' : τ < σ₀ := lt_of_not_ge hcon
    have hmono := laplaceMass_antitone ν (le_of_lt hcon')
    rw [hσ₀] at hmono
    exact hτ (top_le_iff.mp hmono)
  refine ⟨sInf S, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨τ, hτS, hτσ⟩ := exists_lt_of_csInf_lt hne hσ
    have hmono := laplaceMass_antitone ν (le_of_lt hτσ)
    exact fun htop => hτS (top_le_iff.mp (htop ▸ hmono))
  · intro σ hσ
    by_contra hcon
    have hmem : σ ∈ S := hcon
    exact absurd (csInf_le hbdd hmem) (not_le.mpr hσ)

end GaloisForLFunctions.RHTower
