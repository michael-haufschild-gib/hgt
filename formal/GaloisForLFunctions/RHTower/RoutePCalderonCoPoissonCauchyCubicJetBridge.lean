import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaCoPoissonHodgeBoundaryComparison
import GaloisForLFunctions.RHTower.PrimeGammaCauchyCubicSignedEulerianCurvature

/-!
# Route-P cubic Cauchy jet of the actual Calderón/co-Poisson boundary

Route P's retained four-label incidence is the Cauchy-cubic kernel
`2 / (u + b)^(3 : ℕ)`; the actual oriented Calderón--Witt Gamma/co-Poisson
boundary has an unshifted Cauchy pairing.  This file proves their exact
relation, without replacing either source or target:

```text
d²/du² pairing(actualGammaCoPoissonTransport(u), commonTest(b))
  = actualUndeformedSourceCoefficient * 2/(u+b)^(3 : ℕ).
```

Thus P's cubic kernel is the second positive-action jet of the actual
Calderón/co-Poisson Hodge boundary.  The coefficient is precisely the
oriented source coefficient already carried by the nonlocal exterior.
No source aggregation, bounded/nuclear synthesis, scalar replacement, or
positivity claim is used.  In particular this bridge does not manufacture
the still-open coefficient orientation, graph-closed all-cell assembly, or
ordered signed-Eulerian descent action.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Cauchy response at real source action `u` against the real positive common test `b`. -/
def routePCoPoissonCauchyResponse (c : ℂ) (b u : ℝ) : ℂ :=
  c / ((u : ℂ) + (b : ℂ))

/-- Actual oriented Calderón--Witt Gamma/co-Poisson pairing at real positive action `u` against
the positive common test `b`. -/
def routePActualGammaCoPoissonCauchyResponse
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) (b u : ℝ) : ℂ :=
  eulerPrimitiveBoundaryPolarizedPairing
    (deningerCalderonWittGammaBoundaryVectorOrientation q
      (deningerCalderonWittGammaPolarizedVectorTransport u s p q e f))
    (eulerPrimitiveBoundaryPolarizedTest (b : ℂ))

/-- The actual pairing is the unshifted Cauchy response, carrying the original oriented source
coefficient unchanged. -/
theorem routePActualGammaCoPoissonCauchyResponse_eq
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) {b u : ℝ}
    (hu : 0 < u) (hb : 0 < b) :
    routePActualGammaCoPoissonCauchyResponse s p q e f b u =
      routePCoPoissonCauchyResponse
        (deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f) b u := by
  unfold routePActualGammaCoPoissonCauchyResponse routePCoPoissonCauchyResponse
  simpa only [RCLike.star_def, Complex.conj_ofReal] using
    (deningerCalderonWittGammaBoundaryVectorOrientation_transport_pairing_test
      (a := u) hu (b := (b : ℂ)) (by simpa using hb) s p q e f)

/-- First Cauchy-action derivative. -/
theorem hasDerivAt_routePCoPoissonCauchyResponse
    (c : ℂ) (b u : ℝ) (hden : (u : ℂ) + (b : ℂ) ≠ 0) :
    HasDerivAt (routePCoPoissonCauchyResponse c b)
      (-c / (((u : ℂ) + (b : ℂ)) ^ (2 : ℕ))) u := by
  let g : ℝ → ℂ := fun v => (v : ℂ) + (b : ℂ)
  have hg : HasDerivAt g 1 u := by
    simpa only [g, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Complex.ofRealCLM_apply, map_one, zero_add, add_comm] using!
      (Complex.ofRealCLM.hasDerivAt (x := u)).const_add (b : ℂ)
  have hinv : HasDerivAt (fun v => (g v)⁻¹)
      (-(1 : ℂ) / g u ^ (2 : ℕ)) u := hg.inv (by simpa [g] using hden)
  have hraw : HasDerivAt (fun v : ℝ => c * (g v)⁻¹)
      (c * (-(1 : ℂ) / g u ^ (2 : ℕ))) u := hinv.const_mul c
  convert hraw using 1
  · funext v
    simp [routePCoPoissonCauchyResponse, g, div_eq_mul_inv]
  · dsimp [g]
    ring

/-- The second positive-action derivative of a Cauchy response is its cubic Cauchy response. -/
theorem hasDerivAt_deriv_routePCoPoissonCauchyResponse
    (c : ℂ) (b u : ℝ) (hu : 0 < u) (hb : 0 < b) :
    HasDerivAt (fun v => deriv (routePCoPoissonCauchyResponse c b) v)
      (2 * c / (((u : ℂ) + (b : ℂ)) ^ (3 : ℕ))) u := by
  let g : ℝ → ℂ := fun v => (v : ℂ) + (b : ℂ)
  have hg : HasDerivAt g 1 u := by
    simpa only [g, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Complex.ofRealCLM_apply, map_one, zero_add, add_comm] using!
      (Complex.ofRealCLM.hasDerivAt (x := u)).const_add (b : ℂ)
  have hden : g u ≠ 0 := by
    dsimp [g]
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (add_pos hu hb))
  have hinv : HasDerivAt (fun v => (g v)⁻¹)
      (-(1 : ℂ) / g u ^ (2 : ℕ)) u := hg.inv hden
  have hraw : HasDerivAt (fun v : ℝ => (-c) * ((g v)⁻¹) ^ (2 : ℕ))
      ((-c) * ((2 : ℂ) * (g u)⁻¹ * (-(1 : ℂ) / g u ^ (2 : ℕ)))) u :=
    by simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hinv.pow 2).const_mul (-c)
  have heq : (fun v => deriv (routePCoPoissonCauchyResponse c b) v) =ᶠ[nhds u]
      (fun v : ℝ => (-c) * ((g v)⁻¹) ^ (2 : ℕ)) := by
    filter_upwards [eventually_gt_nhds hu] with v hv
    have hdenv : (v : ℂ) + (b : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
      exact ne_of_gt (add_pos hv hb)
    rw [(hasDerivAt_routePCoPoissonCauchyResponse c b v hdenv).deriv]
    simp [g, div_eq_mul_inv]
  have htrans := hraw.congr_of_eventuallyEq heq
  suffices hscalar : 2 * c / (((u : ℂ) + (b : ℂ)) ^ (3 : ℕ)) =
      (-c) * ((2 : ℂ) * (g u)⁻¹ * (-(1 : ℂ) / g u ^ (2 : ℕ))) by
    rw [hscalar]
    exact htrans
  let z : ℂ := (u : ℂ) + (b : ℂ)
  have hz : z ≠ 0 := by
    simpa only [z, g] using hden
  change 2 * c / z ^ (3 : ℕ) = (-c) * ((2 : ℂ) * z⁻¹ * (-(1 : ℂ) / z ^ (2 : ℕ)))
  rw [show z ^ (3 : ℕ) = z * z ^ (2 : ℕ) by ring]
  field_simp [hz]

/-- The first positive-action derivative of the actual oriented boundary pairing is the
coefficient-faithful Cauchy-square response. -/
theorem hasDerivAt_routePActualGammaCoPoissonCauchyResponse
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) {b u : ℝ}
    (hu : 0 < u) (hb : 0 < b) :
    HasDerivAt (routePActualGammaCoPoissonCauchyResponse s p q e f b)
      (-deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f /
        (((u : ℂ) + (b : ℂ)) ^ (2 : ℕ))) u := by
  have hden : (u : ℂ) + (b : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact ne_of_gt (add_pos hu hb)
  apply (hasDerivAt_routePCoPoissonCauchyResponse
    (deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f) b u hden).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact routePActualGammaCoPoissonCauchyResponse_eq s p q e f hv hb

/-- **P/Calderón bridge.**  The second action derivative of the actual oriented
Gamma/co-Poisson pairing is the coefficient-faithful cubic Cauchy response. -/
theorem hasDerivAt_deriv_routePActualGammaCoPoissonCauchyResponse
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) {b u : ℝ}
    (hu : 0 < u) (hb : 0 < b) :
    HasDerivAt (fun v =>
      deriv (routePActualGammaCoPoissonCauchyResponse s p q e f b) v)
      (2 * deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f /
        (((u : ℂ) + (b : ℂ)) ^ (3 : ℕ))) u := by
  apply (hasDerivAt_deriv_routePCoPoissonCauchyResponse
    (deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f) b u hu hb).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  have hdenv : (v : ℂ) + (b : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact ne_of_gt (add_pos hv hb)
  rw [(hasDerivAt_routePActualGammaCoPoissonCauchyResponse s p q e f hv hb).deriv,
    (hasDerivAt_routePCoPoissonCauchyResponse
      (deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f) b v hdenv).deriv]

/-- The cubic obtained from the actual Hodge boundary is exactly the Route-P Cauchy-cubic edge,
with no rescaling or fitted source coefficient. -/
theorem hasDerivAt_deriv_routePActualGammaCoPoissonCauchyResponse_eq_primeGammaCauchyCubic
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) {b u : ℝ}
    (hu : 0 < u) (hb : 0 < b) :
    HasDerivAt (fun v =>
      deriv (routePActualGammaCoPoissonCauchyResponse s p q e f b) v)
      (deningerCalderonWittGammaUndeformedScalarCoefficient s p q e f *
        (primeGammaCauchyCubicEdge u b : ℂ)) u := by
  have hedge : (primeGammaCauchyCubicEdge u b : ℂ) =
      2 / (((u : ℂ) + (b : ℂ)) ^ (3 : ℕ)) := by
    unfold primeGammaCauchyCubicEdge
    push_cast
    rw [← Complex.ofReal_add]
  rw [hedge]
  convert hasDerivAt_deriv_routePActualGammaCoPoissonCauchyResponse
    s p q e f hu hb using 1
  ring

end

end RHTower
