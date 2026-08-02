import GaloisForLFunctions.HTGeometry.EllipticGammaPointedIncidence
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.EllipticGammaFlatNonvanishing

/-!
# The translation cocycle is not a thin coboundary

The multiplicative translation cocycle `q ↦ σ_q(G)/G` becomes a coboundary in a sector exactly when
`G` differs from a member of that sector by a fixed element.  Over a non-discrete period group the
fixed elements are constants, so a coboundary presentation would put `G` itself in the sector.

For the elliptic gamma function the sector is the differentially algebraic one and `G` is
hypertranscendental, so the cocycle is a genuine anomaly: this is the nonvanishing of the
differentially algebraic edge of the pointed bi-anomaly.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **The translation cocycle of an element outside a constant-stable sector is not a coboundary in
that sector**, over a non-discrete period group. -/
theorem cocycle_not_coboundary_of_notMem {L : Submodule ℤ ℂ} (hL : ¬ DiscreteTopology L)
    {B : Set (meroField (Set.univ : Set ℂ))}
    (hBconst : ∀ (c : ℂ) (b : meroField (Set.univ : Set ℂ)), b ∈ B → meroConstant c * b ∈ B)
    {G b : meroField (Set.univ : Set ℂ)} (hGB : G ∉ B) (hbB : b ∈ B) (hb0 : b ≠ 0)
    (hcob : ∀ q ∈ L, addTranslationMeroEquiv q G * b = G * addTranslationMeroEquiv q b) :
    False := by
  have hfix : ∀ q ∈ L, addTranslationMeroEquiv q (G / b) = G / b := by
    intro q hq
    have hqb : addTranslationMeroEquiv q b ≠ 0 := by
      intro h0
      exact hb0 ((addTranslationMeroEquiv q).injective (by rw [h0, map_zero]))
    rw [map_div₀, div_eq_div_iff hqb hb0]
    exact hcob q hq
  obtain ⟨c, hc⟩ := exists_const_of_fixed_of_not_discrete hL hfix
  have hGval : G = meroConstant c * b := by
    rw [meroConstant, hc]
    field_simp
  exact hGB (hGval ▸ hBconst c b hbB)

/-- The differentially algebraic sector is stable under multiplication by constants. -/
theorem daSector_const_mul {c : ℂ} {b : meroField (Set.univ : Set ℂ)} (hb : b ∈ daSector) :
    meroConstant c * b ∈ daSector := by
  have hconst : DifferentialAlgebraicOver (RatFunc ℂ) (meroConstant c) := by
    have hval : meroConstant c
        = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (algebraMap ℂ (RatFunc ℂ) c) := by
      rw [ratfunc_algebraMap_complex]
      rfl
    rw [hval]
    exact differentialAlgebraicOver_algebraMap _
  exact differentialAlgebraicOver_mul hconst hb

/-- **The differentially algebraic edge of the elliptic gamma bi-anomaly is nonzero.**  No
differentially algebraic element presents the translation cocycle of the elliptic gamma as a
coboundary over the rank-three period group. -/
theorem ellipticGamma_cocycle_not_daCoboundary {sigma tau : ℂ}
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    {b : meroField (Set.univ : Set ℂ)} (hbB : b ∈ daSector) (hb0 : b ≠ 0)
    (hcob : ∀ q ∈ Submodule.span ℤ (Set.range (ellipticGammaSourcePeriods sigma tau)),
      addTranslationMeroEquiv q
          (multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
            (ellipticPeriodPair_im_pos hsigma htau)) * b
        = multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
            (ellipticPeriodPair_im_pos hsigma htau) * addTranslationMeroEquiv q b) :
    False := by
  have hHT : HypertranscendentalOver (RatFunc ℂ)
      (multipleEllipticGammaMero (ellipticPeriodPair sigma tau)
        (ellipticPeriodPair_im_pos hsigma htau)) :=
    (hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor
      (ellipticPeriodPair sigma tau) (ellipticPeriodPair_im_pos hsigma htau)).2
      (rankThreeMinor_ellipticPeriodPair hindep)
  refine cocycle_not_coboundary_of_notMem
    (not_discrete_intSpan_fin_three (ellipticGammaSourcePeriods sigma tau) hindep)
    (fun c b hb => daSector_const_mul hb) ?_ hbB hb0 hcob
  intro hmem
  exact hHT hmem

end

end GaloisForLFunctions.HTGeometry
