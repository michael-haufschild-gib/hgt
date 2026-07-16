import GaloisForLFunctions.RHTower.PrimeArchBernsteinAbelSharpSelectionMaster

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- A source-side single-valued meromorphic realization of the susceptibility throughout the
unconditional narrow collar.  Agreement is required only with the interior real Abel germ. -/
def PrimeArchEndpointBernsteinAbelMeromorphicCollar : Prop :=
  ∀ R : ℝ, 250000 / 251001 < R → R < 1 →
    ∃ f : ℂ → ℂ, MeromorphicAt f R ∧
      (fun t : ℝ => f t) =ᶠ[nhdsWithin R (Set.Ico 0 R)]
        (fun t : ℝ =>
          (primeArchEndpointBernsteinAbelSusceptibility t : ℂ))

/-- **Meromorphic-collar RH criterion.**  A single-valued source-side meromorphic realization on
the explicit narrow collar forces the unique Abel radius to reach one, hence RH.  Isolated poles
of arbitrary integer order are allowed; false RH is excluded by the selected half-order parity
obstruction. -/
theorem riemannHypothesis_of_primeArchEndpointBernsteinAbelMeromorphicCollar
    (hcollar : PrimeArchEndpointBernsteinAbelMeromorphicCollar) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hboundaryPos, hcritical, hboundary, hblowup⟩ :=
    exists_exactRadius_positiveHalfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh hRH
  obtain ⟨R, hR, hRunique⟩ := existsUnique_primeArchEndpointBernsteinAbelCriticalRadius
  have hReq : R = 1 / B ^ 2 :=
    primeArchEndpointBernsteinAbelCriticalRadius_unique hR.2.2.1 hcritical
  have hlower : (250000 / 251001 : ℝ) < 1 / B ^ 2 := by
    rw [← hReq]
    exact hR.1
  have hBsq : 1 < B ^ 2 := by nlinarith [sq_pos_of_pos (sub_pos.mpr hB)]
  have hupper : 1 / B ^ 2 < (1 : ℝ) := (div_lt_one (lt_trans zero_lt_one hBsq)).2 hBsq
  obtain ⟨f, hf, hagree⟩ := hcollar (1 / B ^ 2) hlower hupper
  exact
    GaloisForLFunctions.HTGeometry.false_of_meromorphicAt_of_positive_sqrt_scaled_boundary
      (lt_trans zero_lt_one hB) hboundaryPos hf hagree hboundary

end

end RHTower

