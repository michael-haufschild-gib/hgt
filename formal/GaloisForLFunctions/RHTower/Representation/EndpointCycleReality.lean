import GaloisForLFunctions.RHTower.Representation.EndpointArithmeticMoments
import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicityFarRay

/-!
# Reality of the endpoint cycle values

Conjugation symmetry makes every resolvent moment real. Consequently the arithmetic cycle
values equal the full normalized complex endpoint power sums; taking real parts loses nothing.
-/

noncomputable section

namespace RHTower

/-- Arithmetic cycle values are the full complex divisor moments, not merely projections. -/
theorem xiEndpointArithmeticCycle_complex (n : ℕ) : (xiEndpointArithmeticCycle n : ℂ) =
    (∑' q, xiStripEdgeWeight q ^ (n + 1)) / (xiEndpointColorMass : ℂ) ^ (n + 1) := by
  rw [xiEndpointArithmeticCycle_eq_source, xiEndpointSourceCycle_eq_resolvent,
    Complex.ofReal_div, Complex.ofReal_pow]
  have hr : ((xiResolventMoment n (1 / 4)).re : ℂ) = xiResolventMoment n (1 / 4) := by
    apply Complex.ext
    · rfl
    · exact (xiResolventMoment_im_eq_zero (by positivity) n).symm
  rw [hr]
  simp only [xiResolventMoment, xiResolventPoint_endpoint]

end RHTower
