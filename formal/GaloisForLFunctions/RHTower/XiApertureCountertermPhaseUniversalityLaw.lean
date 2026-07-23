import GaloisForLFunctions.RHTower.XiAperturePoissonFullApertureHilbertTransport
import GaloisForLFunctions.RHTower.XiApertureResponseCorrelationDet2

/-!
# Universal counterterm phase of the fused Xi aperture response

The unit aperture has one non-trace-class prime-harmonic channel, whose unique subtraction
coefficient is `6`.  Every deeper positive integral aperture is already trace class, so any
nonzero prime-harmonic subtraction destroys summability.  This gives one exact all-depth
renormalization law with a boundary jump from `6` to `0`.
-/

namespace RHTower

noncomputable section

/-- Unique prime-harmonic counterterm coefficient at a positive integral aperture. -/
def xiAperturePrimeFusedResponseBoundaryCounterterm (a : ℕ) : ℝ :=
  if a = 1 then 6 else 0

/-- **Fused-response counterterm phase universality.** After subtracting the unit background
only at aperture one, the all-prime fused gain is summable after a scalar harmonic subtraction
exactly for the canonical coefficient: `6` at aperture one and `0` at every deeper positive
integral aperture. -/
theorem summable_xiAperturePrimeFusedResponseGainSq_sub_boundary_sub_c_mul_iff
    {a : ℕ} (ha : 0 < a) (c : ℝ) :
    Summable (fun p : Nat.Primes ↦
      xiAperturePrimeFusedResponseGainSq a p -
        (if a = 1 then 1 else 0) -
        c * xiTransversePrimeApertureDiskNode 1 p) ↔
      c = xiAperturePrimeFusedResponseBoundaryCounterterm a := by
  by_cases ha1 : a = 1
  · subst a
    simpa [xiAperturePrimeFusedResponseBoundaryCounterterm,
      xiAperturePrimeFusedResponseGainSq_one] using
      summable_xiApertureOnePrimeFusedResponseGainSq_sub_one_sub_c_mul_iff c
  · have ha2 : 2 ≤ a := by omega
    have hgain : Summable (xiAperturePrimeFusedResponseGainSq a) :=
      summable_xiAperturePrimeFusedResponseGainSq_of_two_le ha2
    simp only [ha1, if_false, sub_zero,
      xiAperturePrimeFusedResponseBoundaryCounterterm]
    constructor
    · intro hren
      have hscaled : Summable (fun p : Nat.Primes ↦
          c * xiTransversePrimeApertureDiskNode 1 p) := by
        have hdiff := hgain.sub hren
        convert hdiff using 1
        funext p
        ring
      by_contra hc
      have hnodes : Summable (fun p : Nat.Primes ↦
          xiTransversePrimeApertureDiskNode 1 p) :=
        (summable_mul_left_iff hc).mp hscaled
      apply Nat.Primes.not_summable_one_div
      simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, one_div] using hnodes
    · rintro rfl
      simpa using hgain

end

end RHTower
