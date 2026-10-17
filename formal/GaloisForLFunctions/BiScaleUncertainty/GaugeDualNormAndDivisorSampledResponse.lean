import GaloisForLFunctions.BiScaleUncertainty.ExponentialRectangleAndDivisorAverageLaw
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The gauge dual norm of the signed prime–polar measure and the divisor-sampled response

For every compactly supported `C¹` test `h`, the pairing with the signed prime–polar measure is the
inner product of the causal response with the gauge derivative,

`pairing N h = −∫ R_N(t) (h' − h/2)(t) dt`,

so by Cauchy–Schwarz

`(pairing N h)² ≤ laplaceEnergy N · ∫ (h' − h/2)²`:

the Laplace energy dominates the square of the dual norm of `ν_N` on the gauge Sobolev space with
norm `‖h' − h/2‖₂`.  Every smooth producer therefore gives a lower bound
`laplaceEnergy N ≥ (pairing N h)² / ‖h' − h/2‖₂²`, and a producer that pairs to `o(1)` certifies only
that `ν_N` has little energy in the direction `h' − h/2`.

Rectangle tests are not of this kind: `pairing N (e^{t/2} 1_{[0,a]}) = e^{a/2} R_N(a)` is a point
reading of the response, uncontrolled by its `L²` norm.  Sampling the response at the divisor points
`log(K/j)` with weights `√(K/j)` gives the exact Stirling-type law

`Σ_{j ≤ K} √(K/j) R_N(log(K/j)) = 2 log K! − K log K − K H_K + K`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The pairing as an inner product with the causal response -/

/-- **`pairing N h = −∫ R_N · (h' − h/2)`** for compactly supported `C¹` tests. -/
theorem pairing_eq_neg_integral_causalResponse_mul (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ))
    (N : ℕ) :
    pairing N f = -∫ t, causalResponse N t * gaugeDerivative f t := by
  have h := signedSource_eq_neg_integral_causalResponse f hf N 0
  have h0 : signedSource f N 0 = pairing N f := by
    show pairing N (fun s => f (0 + s)) = pairing N f
    congr 1
    funext s
    rw [zero_add]
  rw [h0] at h
  rw [h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show causalResponse N t * gaugeDerivative f (0 + t) = causalResponse N t * gaugeDerivative f t
  rw [zero_add]

/-- **Gauge dual-norm bound:** `(pairing N h)² ≤ laplaceEnergy N · ∫ (h' − h/2)²`. -/
theorem sq_pairing_le_laplaceEnergy_mul (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    pairing N f ^ 2 ≤ laplaceEnergy N * ∫ t, gaugeDerivative f t ^ 2 := by
  rw [pairing_eq_neg_integral_causalResponse_mul f hf N, neg_sq,
    ← integral_sq_causalResponse_eq_laplaceEnergy]
  have hg : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) :=
    hasCompactSupport_gaugeDerivative f.hasCompactSupport
  exact GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (measurable_causalResponse N).aestronglyMeasurable hg.aestronglyMeasurable
    (integrable_sq_causalResponse N) (integrable_sq hg hgs)

theorem abs_pairing_le_sqrt_laplaceEnergy_mul (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ))
    (N : ℕ) :
    |pairing N f| ≤ Real.sqrt (laplaceEnergy N) * Real.sqrt (∫ t, gaugeDerivative f t ^ 2) := by
  rw [← Real.sqrt_mul (laplaceEnergy_nonneg N)]
  exact Real.abs_le_sqrt (sq_pairing_le_laplaceEnergy_mul f hf N)

/-- **Every smooth producer is a lower bound for the Laplace energy.** -/
theorem sq_pairing_div_le_laplaceEnergy (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ)
    (hg : 0 < ∫ t, gaugeDerivative f t ^ 2) :
    pairing N f ^ 2 / (∫ t, gaugeDerivative f t ^ 2) ≤ laplaceEnergy N := by
  rw [div_le_iff₀ hg]
  exact sq_pairing_le_laplaceEnergy_mul f hf N

/-! ## Rectangle readings are point values of the response -/

/-- **`pairing N (e^{t/2} 1_{[0,a]}) = e^{a/2} R_N(a)`.** -/
theorem pairing_polarRectangle_eq_exp_mul_causalResponse (N : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (haL : a ≤ cutoff N) :
    pairing N (polarRectangle a) = Real.exp (a / 2) * causalResponse N a := by
  rw [pairing_polarRectangle N ha haL, causalResponse_eq_on_window N ha haL]
  unfold normalizedLogError
  have h : Real.exp (a / 2) * Real.exp (-a / 2) = 1 := by
    rw [← Real.exp_add, show a / 2 + -a / 2 = 0 by ring, Real.exp_zero]
  linear_combination (-(logError a + (1 - a))) * h

/-- **The divisor-sampled response law:**
`Σ_{j ≤ K} √(K/j) R_N(log(K/j)) = 2 log K! − K log K − K H_K + K`. -/
theorem sum_sqrt_mul_causalResponse_log_ratio_eq (N K : ℕ) (hK1 : 1 ≤ K)
    (hK : Real.log (K : ℝ) ≤ cutoff N) :
    (∑ j ∈ Finset.Icc 1 K, Real.sqrt ((K : ℝ) / j) * causalResponse N (Real.log ((K : ℝ) / j))) =
      2 * RHTower.floorSummatory RHTower.chebyshevPsi K - K * Real.log K - K * realHarmonic K + K := by
  rw [← pairing_factorialLift_eq N K hK1 hK, pairing_factorialLift N K hK]
  refine Finset.sum_congr rfl fun j hj => ?_
  have ha := log_ratio_nonneg hj
  have haL := (log_ratio_le_log hj).trans hK
  rw [← pairing_polarRectangle N ha haL, pairing_polarRectangle_eq_exp_mul_causalResponse N ha haL]
  congr 1
  obtain ⟨hj1, _⟩ := Finset.mem_Icc.mp hj
  have hr : (0 : ℝ) < (K : ℝ) / j := div_pos (by exact_mod_cast hK1) (by exact_mod_cast hj1)
  exact (exp_half_log_eq_sqrt hr).symm

/-- The chain input is the difference of two scaled rectangle readings of the response. -/
theorem chainInput_eq_causalResponse_sub (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {k : ℕ}
    (hk : (k + 1) * h ≤ cutoff N) :
    chainInput h k = causalResponse N ((k + 1) * h) - Real.exp (-h / 2) * causalResponse N (k * h) := by
  have := chainState_succ N hh hk
  unfold chainState at this
  rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by push_cast; ring] at this
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
