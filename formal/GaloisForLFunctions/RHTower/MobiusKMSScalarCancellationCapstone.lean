import GaloisForLFunctions.RHTower.MobiusIncidencePassiveCompletionNoGo
import GaloisForLFunctions.RHTower.PrimeArchPassiveResponseRH

/-!
# Scalar KMS cancellation capstone

Subtracting a universal KMS scalar response before adding an independently
passive KMS scalar response is not a new route around the source problem: if
both limits exist, their sum is a passive source realization and hence proves
RH.  A viable signed producer must therefore retain cancellation before scalar
response formation.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- A scalar difference of an independently passive finite KMS response and a
cofinally universal channel cannot evade the passive-source RH gate.  The base
channel is deliberately arbitrary: only its literal universal limit is used. -/
theorem riemannHypothesis_of_finiteKMSWightman_scalarCancellation_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (R : ℕ → ℂ → ℂ)
    (hbase : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
      Tendsto (fun N ↦ R N z) atTop
        (nhds (mobiusIncidenceUniversalGapResponse z)))
    (hcompletion : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
      Tendsto (fun N ↦
        HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z - R N z)
        atTop (nhds (mobiusIncidenceSourceCompletion z))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_finiteKMSWightmanResponse_tendsto d β energy amplitude
  intro z hzpos hzhalf hzeta
  have hsum := (hcompletion z hzpos hzhalf hzeta).add
    (hbase z hzpos hzhalf hzeta)
  convert hsum using 1
  · funext N
    abel
  · unfold mobiusIncidenceSourceCompletion
    abel

end

end RHTower
