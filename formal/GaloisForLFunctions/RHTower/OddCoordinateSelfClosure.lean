import GaloisForLFunctions.RHTower.CriticalLocusQuadrupleEvenness
import GaloisForLFunctions.RHTower.CriticalLocusHessianClassification

/-!
# Self-closure of landscape theories: no even theory outputs the odd sign

The off-line displacement coordinate is odd under the reflection that every configuration
observation is even under.  A landscape-level theory — any functional calculus whose inputs
are observations of the configuration — therefore produces only displacement-even outputs,
and an odd output (the RH sign) is possible only if it vanishes identically.  An input that
is not a function of the configuration (an arithmetic construction) is required to break
the parity: this is the mechanism's proved ceiling.
-/

namespace RHTower

/-- Every output of a landscape theory over a displacement-even configuration family is
even in the displacement — for arbitrary output sort, with no regularity. -/
theorem landscape_output_even {α : Sort*} (Z : ℂ → Multiset ℂ) (hZ : ∀ t, Z (-t) = Z t)
    (G : Multiset ℂ → α) (t : ℂ) : G (Z (-t)) = G (Z t) :=
  congrArg G (hZ t)

/-- **Self-closure (Law 6).**  A functional that factors through a displacement-even
configuration family and is odd in the displacement vanishes identically: no
landscape-level theory outputs the RH sign. -/
theorem odd_landscape_output_eq_zero (Z : ℂ → Multiset ℂ) (hZ : ∀ t, Z (-t) = Z t)
    (G : Multiset ℂ → ℝ) (ψ : ℂ → ℝ) (hfactor : ∀ t, ψ t = G (Z t))
    (hodd : ∀ t, ψ (-t) = -ψ t) : ∀ t, ψ t = 0 := by
  intro t
  have heven : ψ (-t) = ψ t := by
    rw [hfactor, hfactor, hZ t]
  have := hodd t
  linarith [heven.symm.trans this]

/-- **Self-closure at the splitting quadruple.**  No functional of the quadruple
configuration detects the sign of the off-line displacement: any odd factoring functional
is zero.  Instantiates Law 6 on the family whose evenness is the universal criticality
law. -/
theorem odd_quadruple_output_eq_zero (γ : ℂ) (G : Multiset ℂ → ℝ) (ψ : ℂ → ℝ)
    (hfactor : ∀ t, ψ t = G (criticalQuadruple γ t))
    (hodd : ∀ t, ψ (-t) = -ψ t) : ∀ t, ψ t = 0 :=
  odd_landscape_output_eq_zero _ (criticalQuadruple_neg γ) G ψ hfactor hodd

/-- **Self-closure at multi-splittings.**  The same for a finite multi-splitting family in
one common displacement parameter. -/
theorem odd_multiQuadruple_output_eq_zero {ι : Type*} (s : Finset ι) (gam t₀ : ι → ℂ)
    (G : Multiset ℂ → ℝ) (ψ : ℂ → ℝ)
    (hfactor : ∀ t, ψ t = G (multiQuadruple s gam (fun j => t₀ j * t)))
    (hodd : ∀ t, ψ (-t) = -ψ t) : ∀ t, ψ t = 0 := by
  refine odd_landscape_output_eq_zero
    (fun t => multiQuadruple s gam (fun j => t₀ j * t)) ?_ G ψ hfactor hodd
  intro t
  have : (fun j => t₀ j * -t) = fun j => -(t₀ j * t) := by
    funext j
    ring
  rw [this]
  exact multiQuadruple_neg s gam _

/-- **The detection corollary.**  A landscape functional that is genuinely odd somewhere
does not exist: sign detection requires an input that is not a function of the
configuration. -/
theorem no_odd_landscape_detector (Z : ℂ → Multiset ℂ) (hZ : ∀ t, Z (-t) = Z t)
    (G : Multiset ℂ → ℝ) (ψ : ℂ → ℝ) (hfactor : ∀ t, ψ t = G (Z t))
    (hodd : ∀ t, ψ (-t) = -ψ t) : ¬ ∃ t, ψ t ≠ 0 := by
  rintro ⟨t, ht⟩
  exact ht (odd_landscape_output_eq_zero Z hZ G ψ hfactor hodd t)

end RHTower
