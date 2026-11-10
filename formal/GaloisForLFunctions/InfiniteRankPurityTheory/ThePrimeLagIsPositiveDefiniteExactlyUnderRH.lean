import GaloisForLFunctions.InfiniteRankPurityTheory.OnTheFlowCastelnuovoSeveriIsPurityAndEffectivity
import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta

/-!
# Positive definiteness of the prime-side lag

The central trace of the zero motive is the Weil lag function. Its explicit
formula gives an even function defined entirely by prime counts and the
archimedean correction. Positive definiteness of that function is RH.
-/

open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower InfiniteRankWeilTheory HTGeometry

/-- The prime-side lag, with its explicit diagonal value. -/
def primeLag (u : ℝ) : ℂ :=
  if u = 0 then (poleSharpConstant : ℂ)
  else (Real.exp (-|u| / 2) : ℂ) * primeDeviation (Real.exp |u|)

/-- The explicit formula identifies the prime expression at every real lag. -/
theorem primeLag_eq_weilLagFunction (u : ℝ) : primeLag u = weilLagFunction u := by
  by_cases hu : u = 0
  · subst u
    rw [primeLag, if_pos rfl, weilLagFunction_zero]
  · rw [primeLag, if_neg hu, ← weilLagFunction_eq_primeDeviation (abs_pos.mpr hu)]
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, weilLagFunction_neg]

/-- The central zero trace has exactly the lag normalization. -/
theorem centralTrace_zeroMotive_eq_weilLagFunction :
    centralTrace InfiniteRankWeilTheory.lagWeight (fun q : XiZeroCopy => (q.1 : ℂ)) =
      weilLagFunction := by
  funext u
  unfold centralTrace InfiniteRankWeilTheory.lagWeight weilLagFunction
  apply tsum_congr
  intro q
  ring

/-- The flow criterion expressed as positive definiteness of the lag. -/
theorem riemannHypothesis_iff_positiveDefinite_weilLagFunction :
    RiemannHypothesis ↔ PositiveDefiniteOnReal weilLagFunction := by
  have h := zeroMotive_castelnuovoSeveri_iff
  rw [castelnuovoSeveri_iff_positiveDefinite,
    centralTrace_zeroMotive_eq_weilLagFunction] at h
  exact h.symm

/-- RH is positive definiteness on the real line of the prime-count formula. -/
theorem riemannHypothesis_iff_positiveDefinite_primeLag :
    RiemannHypothesis ↔ PositiveDefiniteOnReal primeLag := by
  rw [show primeLag = weilLagFunction from funext primeLag_eq_weilLagFunction]
  exact riemannHypothesis_iff_positiveDefinite_weilLagFunction

#print axioms primeLag_eq_weilLagFunction
#print axioms riemannHypothesis_iff_positiveDefinite_weilLagFunction
#print axioms riemannHypothesis_iff_positiveDefinite_primeLag

end GaloisForLFunctions.InfiniteRankPurityTheory
