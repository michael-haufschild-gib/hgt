import GaloisForLFunctions.RHTower.MobiusCoupledFeatureIncidence
import GaloisForLFunctions.RHTower.SquarefreePartitionPole

/-!
# Paper certificate: the coupled Möbius source is an exact signed-channel projection

Formal certificate for
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`
`mobius-signed-channel-coisometry-incidence-law.md`, with `sigma = 1 + 2 omega`.

```text
(1)/(2)  P_omega is a probability measure on squarefree divisors with total
         Z_omega = zeta(sigma)/zeta(2 sigma) ;
(5)      R_omega((f_d)) = sum_d eps(d) sqrt(P_omega(d)) f_d ;
(6)      ||R_omega|| = 1  and  R_omega R_omega^* = I ;
(8)      (R_omega^* h)_d = eps(d) sqrt(P_omega(d)) h ;
(10)     Pi_omega = R_omega^* R_omega is an idempotent self-adjoint channel projection ;
(15)     ||B_{omega,d}||^2 = ||k_omega||^2 + c_omega^2 log d ;
(16)/(17) ||Y_omega||^2 = ||k_omega||^2 + c_omega^2 E_{P_omega}[log d],
          E_{P_omega}[log d] = -zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma) ;
(20)/(21) R_omega Y_omega = F_omega / Z_omega ;
(23)     ||F_omega|| = Z_omega ||Pi_omega Y_omega|| ;
(24)     Z_omega ~ 1/(2 omega zeta(2)) and E_{P_omega}[log d] ~ 1/(2 omega) ;
(25)-(27) every closed operator commutes with the signed synthesis on the graph-norm domain of
          its channelwise amplification.
```

All statements are unconditional and vector-generic in the causal input `k`.  The card's open
gates (the concrete archimedean graph-domain membership, the critical projected-component estimate,
the four-unit boundary norm, RH) are untouched.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

variable {sigma omega : ℝ}

/-- **Card `(1)`/`(2)`.** -/
theorem incidencePaper_probability (hsigma : 1 < sigma) :
    (∑' n : ℕ, squarefreeMobiusProbability sigma n) = 1 ∧
      ((squarefreeMobiusTotal sigma : ℝ) : ℂ) =
        riemannZeta (sigma : ℂ) / riemannZeta (2 * (sigma : ℂ)) :=
  ⟨tsum_squarefreeMobiusProbability hsigma, ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma⟩

/-- **Card `(5)`/`(8)`.**  The signed amplitude is a unit vector of the scalar channel. -/
theorem incidencePaper_unit_amplitude (hsigma : 1 < sigma) :
    ‖infiniteMobiusSignedWeightLp sigma hsigma‖ = 1 :=
  norm_infiniteMobiusSignedWeightLp hsigma

/-- **Card `(6)`.**  The signed synthesis is a contraction of the vector-valued channel. -/
theorem incidencePaper_synthesis_contraction (hsigma : 1 < sigma)
    (f : lp (fun _ : ℕ => Lp ℂ 2 (volume : Measure ℝ)) 2) :
    ‖vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma) f‖ ≤ ‖f‖ := by
  have h := norm_vectorSignedSynthesis_le (infiniteMobiusSignedWeightLp sigma hsigma) f
  rwa [incidencePaper_unit_amplitude hsigma, one_mul] at h

/-- **Card `(9)`.**  The signed synthesis is a coisometry: it is a left inverse of its adjoint. -/
theorem incidencePaper_coisometry (hsigma : 1 < sigma) (h : Lp ℂ 2 (volume : Measure ℝ)) :
    vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma)
        (vectorSignedAnalysis (infiniteMobiusSignedWeightLp sigma hsigma) h) = h :=
  vectorSignedSynthesis_analysis (incidencePaper_unit_amplitude hsigma) h

/-- **Card `(10)`.**  The channel projection is idempotent and self-adjoint. -/
theorem incidencePaper_projection (hsigma : 1 < sigma)
    (f g : lp (fun _ : ℕ => Lp ℂ 2 (volume : Measure ℝ)) 2) :
    vectorSignedProjection (infiniteMobiusSignedWeightLp sigma hsigma)
        (vectorSignedProjection (infiniteMobiusSignedWeightLp sigma hsigma) f)
        = vectorSignedProjection (infiniteMobiusSignedWeightLp sigma hsigma) f ∧
      inner ℂ (vectorSignedProjection (infiniteMobiusSignedWeightLp sigma hsigma) f) g =
        inner ℂ f (vectorSignedProjection (infiniteMobiusSignedWeightLp sigma hsigma) g) :=
  ⟨vectorSignedProjection_idempotent (incidencePaper_unit_amplitude hsigma) f,
    vectorSignedProjection_selfAdjoint _ f g⟩

/-- **Card `(15)`.** -/
theorem incidencePaper_channel_feature_norm
    (d : ℕ) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ‖coupledFeature omega k d‖ ^ 2 = ‖k‖ ^ 2 + (1 / (1 + omega)) ^ 2 * Real.log d :=
  norm_coupledFeature_sq d k hk

/-- **Card `(16)`.**  The logarithmic channel moment is the squarefree fixed current. -/
theorem incidencePaper_log_moment (hsigma : 1 < sigma) :
    ((squarefreeMobiusLogMoment 1 sigma : ℝ) : ℂ) =
      GaloisForLFunctions.squarefreeFixedCurrent (sigma : ℂ) :=
  ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hsigma

/-- **Card `(17)`.** -/
theorem incidencePaper_feature_norm (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ‖coupledFeatureVector sigma omega hsigma k hk‖ ^ 2 =
      ‖k‖ ^ 2 + (1 / (1 + omega)) ^ 2 * squarefreeMobiusLogMoment 1 sigma :=
  norm_coupledFeatureVector_sq hsigma k hk

/-- **Card `(21)`.** -/
theorem incidencePaper_source_projection (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ((squarefreeMobiusTotal sigma : ℝ) : ℂ) •
        vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma)
          (coupledFeatureVector sigma omega hsigma k hk)
      = ∑' d : ℕ,
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-sigma) : ℝ) : ℂ) •
            coupledFeature omega k d :=
  coupledError_eq_tsum hsigma k hk

/-- **Card `(23)`.**  The exact cancellation law. -/
theorem incidencePaper_cancellation (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ‖∑' d : ℕ,
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-sigma) : ℝ) : ℂ) •
          coupledFeature omega k d‖
      = squarefreeMobiusTotal sigma *
        ‖vectorSignedProjection (infiniteMobiusSignedWeightLp sigma hsigma)
          (coupledFeatureVector sigma omega hsigma k hk)‖ :=
  norm_coupledError_eq hsigma k hk

/-- **Card `(24)`.**  Both diagonal data blow up at the exact critical rate `1/(2 omega)`. -/
theorem incidencePaper_critical_rates :
    Tendsto (fun s : ℝ => (s - 1) * squarefreeMobiusTotal s)
        (nhdsWithin 1 (Ioi 1)) (nhds (6 / Real.pi ^ 2)) ∧
      Tendsto (fun s : ℝ => (s - 1) * squarefreeMobiusLogMoment 1 s)
        (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
  ⟨tendsto_sub_one_mul_squarefreeMobiusTotal, tendsto_squarefreeMobiusLogMoment_one_critical⟩

/-- **Card `(25)`--`(27)`.**  Closed-operator channel commutation. -/
theorem incidencePaper_closed_operator (hsigma : 1 < sigma)
    (G : Lp ℂ 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hG : IsClosed (G.graph : Set (Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ))))
    (f g : lp (fun _ : ℕ => Lp ℂ 2 (volume : Measure ℝ)) 2)
    (hdom : ∀ d : ℕ, (f : ℕ → Lp ℂ 2 (volume : Measure ℝ)) d ∈ G.domain)
    (hval : ∀ d : ℕ, G ⟨(f : ℕ → Lp ℂ 2 (volume : Measure ℝ)) d, hdom d⟩ =
      (g : ℕ → Lp ℂ 2 (volume : Measure ℝ)) d) :
    ∃ hmem : vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma) f ∈ G.domain,
      G ⟨vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma) f, hmem⟩ =
        vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma) g :=
  vectorSignedSynthesis_closedOperator _ G hG f g hdom hval

end RHTower
