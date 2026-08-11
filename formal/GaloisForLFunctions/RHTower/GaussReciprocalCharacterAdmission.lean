import GaloisForLFunctions.HTGeometry.ReciprocalCharacterRealFormMechanics
import GaloisForLFunctions.RHTower.FisherDeconvolvedSameCarrierOrientationLaw
import GaloisForLFunctions.RHTower.GaussHodgeMassCurrent

/-!
# Gauss reciprocal-character admission

The literal Gauss residue/Fisher packet realizes reciprocal-character virial mechanics.  Its
Hodge mass is exactly the Euler-generated virial current and inherits its quadratic lower bound.
-/

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Source weight placing the Gauss Hodge shape in reciprocal-character normalization. -/
def gaussReciprocalCharacterWeight (m : ℕ) (p : Nat.Primes) : ℝ :=
  Real.log 2 / 2 * gaussChannelResidueCurrent m p *
    primeActivationOccupancyFisherDensity p / Real.log (p : ℝ)

theorem gaussReciprocalCharacterWeight_pos {m : ℕ} (hm : 1 ≤ m)
    (p : Nat.Primes) : 0 < gaussReciprocalCharacterWeight m p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hc := gaussChannelResidueCurrent_pos hm p
  have hf := primeActivationOccupancyFisherDensity_pos' p
  rw [gaussReciprocalCharacterWeight]
  positivity

/-- Fourth-organ generator identity: Gauss Hodge mass is the reciprocal virial current. -/
theorem gaussHodgeMassCurrent_eq_reciprocalCharacterVirial
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p =
      reciprocalCharacterVirialCurrent (gaussReciprocalCharacterWeight m p)
        (Real.log (p : ℝ)) (primeDepthBVWoldXiCenteredRate q.1) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [gaussHodgeMassCurrent_eq_boost_square, hodgeMassShape,
    reciprocalCharacterVirialCurrent, gaussReciprocalCharacterWeight,
    rpow_sub_rpow_neg_eq_two_sinh hp]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  field_simp

/-- Literal Gauss Hodge current inherits the universal virial quadratic lower bound. -/
theorem gaussHodgeMassCurrent_virial_lower {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    Real.log 2 * gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) *
          primeDepthBVWoldXiCenteredRate q.1 ^ 2 ≤
      gaussHodgeMassCurrent m q p := by
  rw [gaussHodgeMassCurrent_eq_reciprocalCharacterVirial]
  have h := reciprocalCharacterVirial_quadratic_lower
    (a := gaussReciprocalCharacterWeight m p)
    (lambda := Real.log (p : ℝ))
    (t := primeDepthBVWoldXiCenteredRate q.1)
    (gaussReciprocalCharacterWeight_pos hm p).le
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  refine le_trans (le_of_eq ?_) h
  rw [gaussReciprocalCharacterWeight]
  field_simp

end


end RHTower
