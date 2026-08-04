import GaloisForLFunctions.RHTower.PrimeDepthBVWoldSchattenAtlasLanding

/-!
# Singular inverse-Wold depth lowering

Depth raising multiplies the informative anomaly by `p⁻¹`, moving it across the Schatten wall.
The inverse move is therefore an unbounded prime multiplier.  Because the physical/unit-double
remainder is a fixed trace-class basepoint, the source-correct inverse is affine: subtract the
remainder, multiply by `p`, then restore it.  This is the exact adjacent-grade graph operation
whose trace-class domain selects the critical line.
-/

namespace RHTower

noncomputable section

/-- Affine inverse-Wold transport based at the physical trace-class seam. -/
def primeDepthBVWoldRenormalizedDepthLowering
    (f : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) * (f p - woldRemainder p) + woldRemainder p

/-- One Wold depth step is exactly multiplication by the inverse prime. -/
theorem prime_mul_woldCoeff_succ (p : Nat.Primes) (e : ℕ) :
    (p : ℝ) * woldCoeff (e + 1) p = woldCoeff e p := by
  rw [woldCoeff, woldCoeff, pow_succ]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hp0]
  ring

/-- The affine singular transport lowers the actual source-atlas coefficient by one depth. -/
theorem primeDepthBVWoldRenormalizedDepthLowering_relativeLogCoefficient
    (rho : XiDivisorSupport) (e : ℕ) (p : Nat.Primes) :
    primeDepthBVWoldRenormalizedDepthLowering
        (primeDepthBVWoldXiRelativeLogCoefficient rho (e + 1)) p =
      primeDepthBVWoldXiRelativeLogCoefficient rho e p := by
  rw [primeDepthBVWoldRenormalizedDepthLowering,
    primeDepthBVWoldXiRelativeLogCoefficient_eq,
    primeDepthBVWoldXiRelativeLogCoefficient_eq]
  have hsucc := prime_mul_woldCoeff_succ p e
  calc
    (p : ℝ) *
          (primeDepthBVWoldXiCenteredRate rho * woldCoeff (e + 1) p +
              woldRemainder p - woldRemainder p) +
        woldRemainder p =
        primeDepthBVWoldXiCenteredRate rho *
            ((p : ℝ) * woldCoeff (e + 1) p) + woldRemainder p := by ring
    _ = primeDepthBVWoldXiCenteredRate rho * woldCoeff e p +
        woldRemainder p := by rw [hsucc]

/-- Depth two is always in the ordinary trace-class coefficient space. -/
theorem summable_primeDepthBVWoldXiRelativeLogCoefficient_two
    (rho : XiDivisorSupport) :
    Summable (primeDepthBVWoldXiRelativeLogCoefficient rho 2) := by
  rw [summable_primeDepthBVWoldXiRelativeLogCoefficient_iff]
  exact Or.inr le_rfl

/-- The singular affine lowering of the unconditional depth-two family lands in trace class
exactly on the critical line. -/
theorem summable_renormalizedDepthLowering_relativeLogCoefficient_two_iff
    (rho : XiDivisorSupport) :
    Summable (primeDepthBVWoldRenormalizedDepthLowering
      (primeDepthBVWoldXiRelativeLogCoefficient rho 2)) ↔
      (rho : ℂ).re = 1 / 2 := by
  have hfun : primeDepthBVWoldRenormalizedDepthLowering
      (primeDepthBVWoldXiRelativeLogCoefficient rho 2) =
        primeDepthBVWoldXiRelativeLogCoefficient rho 1 := by
    funext p
    simpa using
      primeDepthBVWoldRenormalizedDepthLowering_relativeLogCoefficient rho 1 p
  rw [hfun, summable_primeDepthBVWoldXiRelativeLogCoefficient_one_iff]

/-- Graph domain of the singular affine inverse-Wold transport on the trace-class sequence space. -/
def PrimeDepthBVWoldRenormalizedDepthLoweringTraceDomain
    (f : Nat.Primes → ℝ) : Prop :=
  Summable f ∧ Summable (primeDepthBVWoldRenormalizedDepthLowering f)

/-- The actual depth-two relative coefficient lies in the singular graph domain exactly at
zero horizontal displacement. -/
theorem relativeLogCoefficient_two_mem_renormalizedDepthLoweringTraceDomain_iff
    (rho : XiDivisorSupport) :
    PrimeDepthBVWoldRenormalizedDepthLoweringTraceDomain
        (primeDepthBVWoldXiRelativeLogCoefficient rho 2) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [PrimeDepthBVWoldRenormalizedDepthLoweringTraceDomain,
    and_iff_right (summable_primeDepthBVWoldXiRelativeLogCoefficient_two rho),
    summable_renormalizedDepthLowering_relativeLogCoefficient_two_iff]

/-- Global source-side graph-domain admission proposition. -/
def PrimeDepthBVWoldXiSingularDepthLoweringLanding : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeDepthBVWoldRenormalizedDepthLoweringTraceDomain
      (primeDepthBVWoldXiRelativeLogCoefficient rho 2)

/-- Global singular adjacent-depth landing is exactly RH; this theorem isolates the producer. -/
theorem primeDepthBVWoldXiSingularDepthLoweringLanding_iff_riemannHypothesis :
    PrimeDepthBVWoldXiSingularDepthLoweringLanding ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (relativeLogCoefficient_two_mem_renormalizedDepthLoweringTraceDomain_iff rho).1
        (h rho)
    linarith [mem_rightHalf.mp hz]
  · intro hRH rho
    exact
      (relativeLogCoefficient_two_mem_renormalizedDepthLoweringTraceDomain_iff rho).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
