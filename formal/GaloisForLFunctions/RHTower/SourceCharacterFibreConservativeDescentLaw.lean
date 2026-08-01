import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Source-character fibre conservation

A real source fibre carrying one exponential character cannot descend faithfully through an
equivariant norm-conservative target away from the neutral character.  The vector-level rigidity
law therefore upgrades to an operator classification: either the entire fibre is erased or the
real character rate is zero.
-/

noncomputable section
namespace RHTower

/-- **Source-character fibre conservation law.**  If a source action is the same real exponential
character on an entire fibre, every equivariant descent into a norm-conservative target either
annihilates that fibre or has neutral character rate. -/
theorem normConservative_sourceCharacterFibre_descent_dichotomy
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E →ₗ[ℝ] E) (V : F →ₗ[ℝ] F) (T : E →ₗ[ℝ] F)
    (nu : ℝ)
    (hsource : ∀ x : E, U x = Real.exp nu • x)
    (hintertwine : ∀ x : E, V (T x) = T (U x))
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    T = 0 ∨ nu = 0 := by
  by_cases hnu : nu = 0
  · exact Or.inr hnu
  · left
    apply LinearMap.ext
    intro x
    by_contra hx
    have hTx : T x ≠ 0 := by
      simpa only [LinearMap.zero_apply] using hx
    exact hnu
      (normConservative_equivariantDescent_forces_zero
        U V T x hTx nu (hsource x) hintertwine hconservative)

/-- Off the neutral horizon, equivariant norm-conservative descent erases the complete source
fibre, not merely one chosen vector. -/
theorem normConservative_sourceCharacterFibre_descent_eq_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E →ₗ[ℝ] E) (V : F →ₗ[ℝ] F) (T : E →ₗ[ℝ] F)
    (nu : ℝ) (hnu : nu ≠ 0)
    (hsource : ∀ x : E, U x = Real.exp nu • x)
    (hintertwine : ∀ x : E, V (T x) = T (U x))
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    T = 0 :=
  (normConservative_sourceCharacterFibre_descent_dichotomy
    U V T nu hsource hintertwine hconservative).resolve_right hnu

end RHTower
