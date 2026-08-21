import GaloisForLFunctions.RHTower.PrimeBraid
import GaloisForLFunctions.RHTower.WindingDivisor
import GaloisForLFunctions.HTGeometry.KnotTheory.QuantumTrace

/-!
# A closed clock-normalized prime braid

The original prime strands use one common height coordinate and are not known here to possess a
common nonzero closing period.  Instead, this module keeps each literal prime strand but equips it
with its own angular clock: for `n = 2, 3`, time `-θ / log n` makes the strand close as `θ` runs from
`0` to `2π`.

The two re-clocked strands are distinct circles of radii `1/2` and `1/3`; their difference is the
radius-`1/6` circle and therefore has winding `+1`.  In the standard exponent coordinate
`B₂ ≃ ℤ`, pair framing `k` maps to the full-twist exponent `2k`.  The concrete `i • SWAP` phase
representation then sends this prime full twist to `-1`, exactly its double-braiding phase.

This is not a common-height periodicity claim for the original prime flow.  It is a closed,
clock-normalized two-prime braid object, with the reparameterization to the original paths proved
below.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry.KnotTheory

noncomputable section

/-- Two labelled noncolliding closed strands on the angular interval `[0, 2π]`. -/
structure ClosedPrimePairBraid where
  left : ℝ → ℂ
  right : ℝ → ℂ
  left_continuous : Continuous left
  right_continuous : Continuous right
  left_closed : left 0 = left (2 * Real.pi)
  right_closed : right 0 = right (2 * Real.pi)
  apart : ∀ θ, left θ ≠ right θ

/-- Prime `2` on its individual angular clock. -/
def twoClockNormalizedStrand (θ : ℝ) : ℂ :=
  (1 / (2 : ℂ)) * Complex.exp (Complex.I * (θ : ℂ))

/-- Prime `3` on its individual angular clock. -/
def threeClockNormalizedStrand (θ : ℝ) : ℂ :=
  (1 / (3 : ℂ)) * Complex.exp (Complex.I * (θ : ℂ))

/-- Relative strand of the closed `2,3` prime braid. -/
def twoThreeClockNormalizedDifference (θ : ℝ) : ℂ :=
  twoClockNormalizedStrand θ - threeClockNormalizedStrand θ

/-- The relative strand is precisely the positively oriented radius-`1/6` circle. -/
theorem twoThreeClockNormalizedDifference_eq_circle (θ : ℝ) :
    twoThreeClockNormalizedDifference θ =
      ((1 / 6 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
  simp [twoThreeClockNormalizedDifference, twoClockNormalizedStrand,
    threeClockNormalizedStrand]
  ring

/-- A concrete closed continuous braid built from the prime `2` and prime `3` strands. -/
def twoThreeClockNormalizedBraid : ClosedPrimePairBraid where
  left := twoClockNormalizedStrand
  right := threeClockNormalizedStrand
  left_continuous := by
    unfold twoClockNormalizedStrand
    fun_prop
  right_continuous := by
    unfold threeClockNormalizedStrand
    fun_prop
  left_closed := by
    simp only [twoClockNormalizedStrand, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      mul_one]
    rw [show Complex.I * (((2 : ℝ) * Real.pi : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
    simp
  right_closed := by
    simp only [threeClockNormalizedStrand, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      mul_one]
    rw [show Complex.I * (((2 : ℝ) * Real.pi : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
    simp
  apart := by
    intro θ h
    have hzero : twoThreeClockNormalizedDifference θ = 0 := sub_eq_zero.mpr h
    rw [twoThreeClockNormalizedDifference_eq_circle] at hzero
    exact (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)) hzero

/-- Integer pair framing of the closed `2,3` braid. -/
def twoThreePrimePairFraming : ℤ :=
  windingNumber twoThreeClockNormalizedDifference 0 (2 * Real.pi)

/-- The relative `2,3` framing is one positive turn. -/
theorem twoThreePrimePairFraming_eq_one : twoThreePrimePairFraming = 1 := by
  unfold twoThreePrimePairFraming
  have hcircle : twoThreeClockNormalizedDifference =
      fun θ : ℝ => ((1 / 6 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    ext θ
    exact twoThreeClockNormalizedDifference_eq_circle θ
  rw [hcircle]
  exact windingNumber_scaled_circle (r := (1 / 6 : ℝ)) (by norm_num)

/-- Individual height clock which closes the original prime-`2` strand. -/
def twoPrimeClock (θ : ℝ) : ℝ := -θ / Real.log 2

/-- Individual height clock which closes the original prime-`3` strand. -/
def threePrimeClock (θ : ℝ) : ℝ := -θ / Real.log 3

/-- The closed radius-`1/2` circle is the literal prime-`2` strand under its own clock. -/
theorem twoClockNormalizedStrand_eq_primeStrand (θ : ℝ) :
    twoClockNormalizedStrand θ = strand 2 1 (twoPrimeClock θ) := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := Nat.prime_two.log_ne_zero
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hlog
  have hpos : (0 : ℝ) < 2 := by positivity
  unfold twoClockNormalizedStrand twoPrimeClock strand
  calc
    1 / (2 : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp (-(Real.log 2 : ℂ)) * Complex.exp (Complex.I * (θ : ℂ)) := by
      congr 1
      rw [show -(Real.log 2 : ℂ) = ((-Real.log 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hpos]
      norm_num
    _ = Complex.exp (-(Real.log 2 : ℂ) + Complex.I * (θ : ℂ)) :=
      (Complex.exp_add _ _).symm
    _ = Complex.exp (-(((1 : ℂ) + ((-θ / Real.log 2 : ℝ) : ℂ) * Complex.I)) *
        (Real.log 2 : ℂ)) := by
      congr 1
      push_cast
      field_simp [hlogC]
      ring

/-- The closed radius-`1/3` circle is the literal prime-`3` strand under its own clock. -/
theorem threeClockNormalizedStrand_eq_primeStrand (θ : ℝ) :
    threeClockNormalizedStrand θ = strand 3 1 (threePrimeClock θ) := by
  have hlog : Real.log (3 : ℝ) ≠ 0 := Nat.prime_three.log_ne_zero
  have hlogC : (Real.log 3 : ℂ) ≠ 0 := by exact_mod_cast hlog
  have hpos : (0 : ℝ) < 3 := by positivity
  unfold threeClockNormalizedStrand threePrimeClock strand
  calc
    1 / (3 : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp (-(Real.log 3 : ℂ)) * Complex.exp (Complex.I * (θ : ℂ)) := by
      congr 1
      rw [show -(Real.log 3 : ℂ) = ((-Real.log 3 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hpos]
      norm_num
    _ = Complex.exp (-(Real.log 3 : ℂ) + Complex.I * (θ : ℂ)) :=
      (Complex.exp_add _ _).symm
    _ = Complex.exp (-(((1 : ℂ) + ((-θ / Real.log 3 : ℝ) : ℂ) * Complex.I)) *
        (Real.log 3 : ℂ)) := by
      congr 1
      push_cast
      field_simp [hlogC]
      ring

/-- Winding exponents, written multiplicatively to model the additive group `ℤ`. -/
abbrev WindingGroup := Multiplicative ℤ

/-- The standard exponent coordinate for the two-strand Artin braid group `B₂ ≃ ℤ`. -/
abbrev TwoStrandBraidGroup := Multiplicative ℤ

/-- Pair framing maps to the pure two-strand full twist, which has twice the exponent. -/
def fullTwistFromWinding : WindingGroup →* TwoStrandBraidGroup where
  toFun k := Multiplicative.ofAdd (2 * Multiplicative.toAdd k)
  map_one' := by rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change 2 * (Multiplicative.toAdd a + Multiplicative.toAdd b) =
      2 * Multiplicative.toAdd a + 2 * Multiplicative.toAdd b
    ring

/-- The phase representation of the two-strand braid exponent, sending its generator to `i`. -/
def twoStrandPhaseUnit (k : ℤ) : ℂˣ :=
  Units.mk0 (Complex.I ^ k) (zpow_ne_zero k Complex.I_ne_zero)

/-- A genuine group representation of the two-strand braid exponent coordinate. -/
def twoStrandPhaseRepresentation : TwoStrandBraidGroup →* ℂˣ where
  toFun k := twoStrandPhaseUnit (Multiplicative.toAdd k)
  map_one' := by
    apply Units.ext
    change Complex.I ^ (0 : ℤ) = 1
    simp
  map_mul' a b := by
    apply Units.ext
    change Complex.I ^ (Multiplicative.toAdd a + Multiplicative.toAdd b) =
      Complex.I ^ Multiplicative.toAdd a * Complex.I ^ Multiplicative.toAdd b
    rw [zpow_add₀ Complex.I_ne_zero]

/-- Braid class assigned to the closed `2,3` prime pair by its integer framing. -/
def twoThreePrimeBraidClass : TwoStrandBraidGroup :=
  fullTwistFromWinding (Multiplicative.ofAdd twoThreePrimePairFraming)

/-- The closed prime pair maps to the two-strand full twist. -/
theorem twoThreePrimeBraidClass_is_full_twist :
    Multiplicative.toAdd twoThreePrimeBraidClass = 2 := by
  unfold twoThreePrimeBraidClass fullTwistFromWinding
  rw [twoThreePrimePairFraming_eq_one]
  rfl

/-- The `i`-phase braid representation sends this prime full twist to `-1`. -/
theorem twoThreePrimeBraidPhase_eq_neg_one :
    ((twoStrandPhaseRepresentation twoThreePrimeBraidClass : ℂˣ) : ℂ) = -1 := by
  change Complex.I ^ Multiplicative.toAdd twoThreePrimeBraidClass = -1
  rw [twoThreePrimeBraidClass_is_full_twist]
  rw [zpow_two, Complex.I_mul_I]

/-- The two positive crossings representing the two-strand full twist in the local word layer. -/
def twoStrandFullTwistWord : BraidWord 1 :=
  [(0, CrossingSign.positive), (0, CrossingSign.positive)]

/-- The braid-word writhe agrees with the full-twist exponent. -/
theorem braidWrithe_twoStrandFullTwistWord : braidWrithe twoStrandFullTwistWord = 2 := by
  rfl

/-- The framed Markov phase of the word equals the representation phase of the closed prime braid. -/
theorem twoThreePrimeFramedTrace_eq_braidRepresentation :
    framedMarkovTrace twoStrandFullTwistWord =
      ((twoStrandPhaseRepresentation twoThreePrimeBraidClass : ℂˣ) : ℂ) := by
  change Complex.I ^ braidWrithe twoStrandFullTwistWord =
    Complex.I ^ Multiplicative.toAdd twoThreePrimeBraidClass
  rw [braidWrithe_twoStrandFullTwistWord, twoThreePrimeBraidClass_is_full_twist]

/-- The prime braid's full twist acts as the double `R`-matrix braid on every pair state. -/
theorem twoThreePrimeBraid_double_action (f : PairState) :
    rAction (rAction f) =
      ((twoStrandPhaseRepresentation twoThreePrimeBraidClass : ℂˣ) : ℂ) • f := by
  rw [twoThreePrimeBraidPhase_eq_neg_one]
  simpa using rAction_square f

/-- Markov normalization closes the scalar trace but erases the full-twist phase. -/
theorem twoThreePrimeBraid_closed_trace_eq_one :
    phaseQuantumTrace twoStrandFullTwistWord = 1 :=
  phaseQuantumTrace_eq_one twoStrandFullTwistWord

end

end RHTower
