import GaloisForLFunctions.RHTower.XiWardSchwarzCapSourcePairing

/-!
# Tau-parity no-go for the literal Ward Schwarz cap

The exact lower-cap source response is odd in the Cauchy height parameter
`tau`.  Hence every symmetric `±tau` regularization cancels the literal cap
response identically; it cannot furnish the orientation needed to exclude a
right-half Xi divisor.  This leaves a one-sided, source-selected tau law as
the only possible cap completion, rather than a symmetric smoothing argument.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Reversing the Cauchy height reverses the exact Schwarz cap kernel. -/
theorem xiWardSchwarzCapDifference_neg_tau (tau s x : ℝ) :
    xiWardSchwarzCapDifference (-tau) s x =
      -xiWardSchwarzCapDifference tau s x := by
  rw [xiWardSchwarzCapDifference_eq, xiWardSchwarzCapDifference_eq]
  have hnum :
      (-4 * I * ((-tau : ℝ) : ℂ)) = -(-4 * I * (tau : ℂ)) := by
    push_cast
    ring
  have hden :
      (((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((-tau + x : ℝ) : ℂ)) *
        ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((x - -tau : ℝ) : ℂ))) =
      (((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((tau + x : ℝ) : ℂ)) *
        ((((51 / 100 : ℝ) + xiWardTransverseLevel s : ℝ) : ℂ) +
          I * ((x - tau : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [hnum, hden]
  ring

/-- Every finite factorized cap is odd in its Cauchy height parameter. -/
theorem xiWardSchwarzCapFactorIntegral_neg_tau (tau s H : ℝ) :
    xiWardSchwarzCapFactorIntegral (-tau) s H =
      -xiWardSchwarzCapFactorIntegral tau s H := by
  unfold xiWardSchwarzCapFactorIntegral
  rw [show (fun x : ℝ =>
      xiWardSchwarzCapDifference (-tau) s x *
        continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)) =
      fun x : ℝ => -(xiWardSchwarzCapDifference tau s x *
        continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)) by
      funext x
      rw [xiWardSchwarzCapDifference_neg_tau]
      ring]
  exact intervalIntegral.integral_neg

/-- On the conull family where the factorization is source-faithful, the
literal completed-source cap itself is odd in `tau`. -/
theorem ae_forall_xiWardSchwarzCapSourceIntegral_neg_tau :
    ∀ᵐ s : ℝ ∂volume, ∀ tau H : ℝ,
      xiWardSchwarzCapSourceIntegral (-tau) s H =
        -xiWardSchwarzCapSourceIntegral tau s H := by
  filter_upwards [ae_forall_xiWardSchwarzCapSourceIntegral_eq] with s hs
  intro tau H
  rw [hs (-tau) H, hs tau H, xiWardSchwarzCapFactorIntegral_neg_tau]

end

end RHTower
