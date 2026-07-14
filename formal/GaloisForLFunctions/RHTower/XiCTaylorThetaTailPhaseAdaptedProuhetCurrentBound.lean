import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetPacket
import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicRelativeRemainder

/-!
# Relative bound for the phase-adapted untruncated Haar cross

The double-root Prouhet packet annihilates the complete one-sided translated value and derivative
vectors.  Its off-diagonal Hermitian cross with the fixed seam vector is therefore exactly zero,
not merely bounded.  The anisotropic local-order lower bound for the final Taylor section turns
that exact identity into the required strict `o(n)|P|^2` upper estimate even when the limiting Xi
value is zero.
-/

open Complex Real Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Any scheduled family of phase-adapted one-sided translation crosses is strictly smaller than
the anisotropic scaled squared final Taylor value.  All packet data may depend on the mesh index;
the result uses no boundedness or sign assumption because every cross packet is identically zero.
-/
theorem eventually_phaseAdaptedProuhetOneSidedTranslationHermitianCrossPacket_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ)
    (F F' E E' : ℕ → ℂ) (m : ℕ → ℕ)
    (q r tau a L : ℕ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      phaseAdaptedProuhetOneSidedTranslationHermitianCrossPacket
          (F n) (F' n) (E n) (E' n) (m n)
          (q n) (r n) (tau n) (a n) (L n)
          (xiCTaylorAnisotropicCenteredPoint sigma n) <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have hzero : Tendsto (fun n : ℕ =>
      (0 : ℝ) * (((n + 1 : ℕ) : ℝ) ^
        (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hbound := eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun _ : ℕ => (0 : ℝ)) hzero hepsilon
  filter_upwards [hbound] with n hn
  simpa only [phaseAdaptedProuhetOneSidedTranslationHermitianCrossPacket_eq_zero] using hn

end

end RHTower
