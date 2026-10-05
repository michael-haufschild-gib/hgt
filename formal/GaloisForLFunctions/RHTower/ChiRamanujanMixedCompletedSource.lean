import GaloisForLFunctions.RHTower.ChiRamanujanMixedLabelRows
import GaloisForLFunctions.RHTower.ChiRamanujanMaskedMellinSource
import GaloisForLFunctions.RHTower.ChiRamanujanMixedBaseLimit

/-!
# The complete original mixed-frequency growing source

The original completed labelled Euler cone at `1+u/log N` and
`1+v/log N+i*tau`, divided by `log N` squared, tends to
`exp(-2*gamma) * G(u)` for every nonzero u and real tau, and every complex v.
Both growing coprime cofactors, both label exclusions, the allowed first/second
coincidence, and every exact collision remain present.

The actual mixed Euler/cofactor limit and the complete masked-response limit
pay the full assembly. The leading profile is the same entire G whose signed
vertical integral is zero. This is a pointwise source law; uniform moving
physical-profile remainders and complete frequency tails remain open.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace RHTower.BAGTrace

/-- The original complete labelled source has its mixed-frequency growing
limit, retaining both original cofactors, both label exclusions and all collisions. -/
theorem criticalCompletedConeEuler_mixed_tendsto (u : ℂˣ) (v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ => criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
      (1+(u : ℂ)/(Real.log N : ℂ)) (1+(v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I))/
        (Real.log N : ℂ)^2) atTop
      (𝓝 ((Real.exp (-2*Real.eulerMascheroniConstant) : ℂ)*criticalMixedProfile u)) := by
  have hm := criticalMixedMaskedMellinResponse_tendsto u v tau
  simp only [add_assoc] at hm
  have h := ((criticalPrimeNormalization_logScale_tendsto.pow 3).mul hm).mul
    (criticalMixedCompletedTrace_tendsto u v tau)
  have hgamma : (Real.exp (-Real.eulerMascheroniConstant) : ℂ)^2=
      (Real.exp (-2*Real.eulerMascheroniConstant) : ℂ) := by
    rw [pow_two,← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  have hnorm : (Real.exp (-Real.eulerMascheroniConstant) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have he : (Real.exp (-Real.eulerMascheroniConstant) : ℂ)^3*(1-criticalExponentialMean u)^2*
      (criticalEulerCarrier u/((Real.exp (-Real.eulerMascheroniConstant) : ℂ)*(u : ℂ))) =
      (Real.exp (-2*Real.eulerMascheroniConstant) : ℂ)*criticalMixedProfile u := by
    rw [criticalMixedProfile_eq u,← hgamma]
    field_simp
  rw [he] at h
  apply h.congr'
  filter_upwards [criticalCompletedConeEuler_mixed_response u v tau,eventually_ge_atTop 2] with N hN hN2
  rw [hN]
  have hlog : (Real.log N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp

end RHTower.BAGTrace
