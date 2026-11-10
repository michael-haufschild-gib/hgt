import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeilSymbolFromTheGeometricScatteringTower

/-!
# The finite scattering tower is a completed-zeta quotient

The geometric telescope is the logarithmic derivative of
`Λ(s)/Λ(s+N)`. Its normalization retains the Robin scalar and the
two original boundary poles. This identifies the literal quotient,
including its shifted derivative, before passing to packet energies.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
open _root_.RHTower

/-- The completed-zeta quotient belonging to a finite scattering height. -/
def completedZetaQuotient (N : ℕ) (s : ℂ) : ℂ :=
  reflectedCompletedLambda s / reflectedCompletedLambda (s + N)

private theorem completedLambda_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    reflectedCompletedLambda s ≠ 0 := by
  unfold reflectedCompletedLambda
  exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))
    (riemannZeta_ne_zero_of_one_lt_re hs)

/-- The height telescope is the actual logarithmic derivative of the completed quotient. -/
theorem geometricTower_eq_logDeriv_completedZetaQuotient {s : ℂ}
    (hs : 1 < s.re) (him : s.im ≠ 0) (N : ℕ) :
    geometricTower s N = logDeriv (completedZetaQuotient N) s := by
  have hsN : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hs, Nat.cast_nonneg (α := ℝ) N]
  have himN : (s + N).im ≠ 0 := by simpa only [Complex.add_im, Complex.natCast_im, add_zero] using him
  have hd := differentiableAt_reflectedCompletedLambda him
  have hdN := differentiableAt_reflectedCompletedLambda himN
  have hshift : HasDerivAt (fun z : ℂ => z + N) 1 s := (hasDerivAt_id s).add_const (N : ℂ)
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => reflectedCompletedLambda (z + N)) s :=
    DifferentiableAt.comp s (f := fun z : ℂ => z + N) (g := reflectedCompletedLambda)
      hdN hshift.differentiableAt
  have hc : logDeriv (fun z => reflectedCompletedLambda (z + N)) s =
      logDeriv reflectedCompletedLambda (s + N) := by
    have he := logDeriv_comp (g := fun z : ℂ => z + N) (x := s) hdN hshift.differentiableAt
    rw [hshift.deriv, mul_one] at he
    exact he
  change geometricTower s N = logDeriv
    (fun z => reflectedCompletedLambda z / reflectedCompletedLambda (z + N)) s
  rw [geometricTower_eq hs him N,
    logDeriv_div (f := reflectedCompletedLambda)
      (g := fun z : ℂ => reflectedCompletedLambda (z + N)) s
      (completedLambda_ne_zero_of_one_lt_re hs)
      (completedLambda_ne_zero_of_one_lt_re hsN) hd
      hcomp, hc]

/-- The Robin scalar and both polar residues remain in the normalized quotient formula. -/
theorem renormalizedTower_eq_completedZetaQuotient {s : ℂ}
    (hs : 1 < s.re) (him : s.im ≠ 0) (N : ℕ) :
    renormalizedTower s N = logDeriv (completedZetaQuotient N) s +
      robinCounterterm (s.re + N) + 1 / s + 1 / (s - 1) := by
  rw [renormalizedTower, geometricTower_eq_logDeriv_completedZetaQuotient hs him N]

#print axioms geometricTower_eq_logDeriv_completedZetaQuotient
#print axioms renormalizedTower_eq_completedZetaQuotient

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
