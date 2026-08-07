import GaloisForLFunctions.RHTower.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination

/-!
# The kernel energy of the Riemann source is finite

The Hilbert--Schmidt energy of the source inverse in quantile coordinates is the theta-tail
integral

`M ∫_ℝ p(x)(1 - p(x)) / k(x) dx`.

Its convergence is a doubly exponential estimate: the theta source is squeezed between two
constant multiples of

`E(x) = e^{9x/2} e^{-π e^{2x}}`

on the positive half-line, and `E` decays so fast that its own tail integral past `x` is at most
`E(x)/(π e^{2x})`.  Dividing the two bounds gives `(1 - p(x))/k(x) = O(e^{-2x})`, and the
reflection law transports the estimate to the negative half-line.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt

/-! ### The doubly exponential envelope -/

/-- The doubly exponential envelope of the theta source. -/
def thetaEnvelope (x : ℝ) : ℝ := Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))

theorem thetaEnvelope_pos (x : ℝ) : 0 < thetaEnvelope x := by
  unfold thetaEnvelope
  positivity

theorem exp_sq (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem exp_four (x : ℝ) : Real.exp x ^ 4 = Real.exp (4 * x) := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem exp_half_add_four (x : ℝ) :
    Real.exp (x / 2) * Real.exp (4 * x) = Real.exp (9 * x / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The first theta atom in envelope coordinates. -/
theorem thetaCuspSourceTerm_one_eq (x : ℝ) :
    thetaCuspSourceTerm x 1
      = 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
  rw [thetaCuspSourceTerm, thetaCuspSeed]
  push_cast
  rw [one_mul, exp_sq, exp_four]
  ring

theorem thetaCuspSourceTerm_one_le (x : ℝ) :
    thetaCuspSourceTerm x 1 ≤ 4 * Real.pi ^ 2 * thetaEnvelope x := by
  have hpos : (0 : ℝ) ≤ Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)) := by positivity
  have hmul : 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
      ≤ 4 * Real.pi ^ 2 * Real.exp (4 * x) := by
    nlinarith [Real.pi_pos, Real.exp_pos (2 * x)]
  rw [thetaCuspSourceTerm_one_eq, thetaEnvelope]
  calc 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
      ≤ (4 * Real.pi ^ 2 * Real.exp (4 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) :=
        mul_le_mul_of_nonneg_right hmul hpos
    _ = 4 * Real.pi ^ 2 * (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
        rw [← exp_half_add_four]
        ring

theorem thetaCuspSourceTerm_one_ge {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.pi * (2 * Real.pi - 3) * thetaEnvelope x ≤ thetaCuspSourceTerm x 1 := by
  have hpos : (0 : ℝ) ≤ Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)) := by positivity
  have hexp : Real.exp (2 * x) ≤ Real.exp (4 * x) := Real.exp_le_exp.mpr (by linarith)
  have hmul : 2 * Real.pi * (2 * Real.pi - 3) * Real.exp (4 * x)
      ≤ 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x)) := by
    nlinarith [Real.pi_pos]
  rw [thetaCuspSourceTerm_one_eq, thetaEnvelope]
  calc 2 * Real.pi * (2 * Real.pi - 3)
        * (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
      = (2 * Real.pi * (2 * Real.pi - 3) * Real.exp (4 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
        rw [← exp_half_add_four]
        ring
    _ ≤ 2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x))
        * (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) :=
        mul_le_mul_of_nonneg_right hmul hpos

/-- The upper envelope constant. -/
def thetaEnvelopeUpper : ℝ := (1 + thetaCuspHigherAtomDominationWeight) * (4 * Real.pi ^ 2)

/-- The lower envelope constant. -/
def thetaEnvelopeLower : ℝ := 2 * Real.pi * (2 * Real.pi - 3)

theorem thetaEnvelopeLower_pos : 0 < thetaEnvelopeLower := by
  unfold thetaEnvelopeLower
  nlinarith [Real.pi_gt_three, Real.pi_pos]

theorem thetaEnvelopeUpper_pos : 0 < thetaEnvelopeUpper := by
  unfold thetaEnvelopeUpper
  have := thetaCuspHigherAtomDominationWeight_nonneg
  nlinarith [Real.pi_pos]

/-- **The theta source is dominated by the envelope** on the positive half-line. -/
theorem thetaCuspFullSource_le_envelope {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x ≤ thetaEnvelopeUpper * thetaEnvelope x := by
  have hW := thetaCuspHigherAtomDominationWeight_nonneg
  have h := thetaCuspFullSource_sub_first_le hx
  have h1 := thetaCuspSourceTerm_one_le x
  have h3 : thetaCuspFullSource x
      ≤ (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1 := by
    have e : (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1
        = thetaCuspSourceTerm x 1
          + thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 := by ring
    rw [e]
    linarith
  have h2 : (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1
      ≤ (1 + thetaCuspHigherAtomDominationWeight) * (4 * Real.pi ^ 2 * thetaEnvelope x) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  calc thetaCuspFullSource x
      ≤ (1 + thetaCuspHigherAtomDominationWeight) * thetaCuspSourceTerm x 1 := h3
    _ ≤ (1 + thetaCuspHigherAtomDominationWeight) * (4 * Real.pi ^ 2 * thetaEnvelope x) := h2
    _ = thetaEnvelopeUpper * thetaEnvelope x := by
        rw [thetaEnvelopeUpper]
        ring

/-- **The theta source dominates the envelope** on the open positive half-line. -/
theorem thetaCuspFullSource_ge_envelope {x : ℝ} (hx : 0 < x) :
    thetaEnvelopeLower * thetaEnvelope x ≤ thetaCuspFullSource x := by
  have hterm : thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x := by
    rw [thetaCuspFullSource]
    exact (summable_thetaCuspSourceTerm x).le_tsum 1
      (fun j _ => thetaCuspSourceTerm_nonneg_of_pos hx j)
  have := thetaCuspSourceTerm_one_ge hx.le
  rw [thetaEnvelopeLower]
  linarith

/-! ### The tail of the envelope -/

theorem thetaEnvelope_le_shift {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    thetaEnvelope y ≤ thetaEnvelope x * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by
  have hd : (0 : ℝ) ≤ y - x := by linarith
  have hbig : Real.exp (2 * x) * (1 + 2 * (y - x)) ≤ Real.exp (2 * y) := by
    have h := Real.add_one_le_exp (2 * (y - x))
    have hpos : (0 : ℝ) < Real.exp (2 * x) := Real.exp_pos _
    have hmul : Real.exp (2 * x) * (2 * (y - x) + 1)
        ≤ Real.exp (2 * x) * Real.exp (2 * (y - x)) := mul_le_mul_of_nonneg_left h hpos.le
    rwa [← Real.exp_add, show 2 * x + 2 * (y - x) = 2 * y by ring,
      show 2 * (y - x) + 1 = 1 + 2 * (y - x) by ring] at hmul
  have hpi : 9 / 2 ≤ Real.pi * Real.exp (2 * x) := by
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have h2 : Real.exp 2 ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.pi_gt_three]
  have hE : Real.exp (9 * y / 2) = Real.exp (9 * x / 2) * Real.exp (9 * (y - x) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hD : Real.exp (-Real.pi * Real.exp (2 * y))
      ≤ Real.exp (-Real.pi * Real.exp (2 * x))
        * Real.exp (-(2 * Real.pi * Real.exp (2 * x)) * (y - x)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [Real.pi_pos, hbig]
  rw [thetaEnvelope, thetaEnvelope]
  calc Real.exp (9 * y / 2) * Real.exp (-Real.pi * Real.exp (2 * y))
      ≤ (Real.exp (9 * x / 2) * Real.exp (9 * (y - x) / 2))
        * (Real.exp (-Real.pi * Real.exp (2 * x))
          * Real.exp (-(2 * Real.pi * Real.exp (2 * x)) * (y - x))) := by
        rw [hE]
        exact mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
        * (Real.exp (9 * (y - x) / 2)
          * Real.exp (-(2 * Real.pi * Real.exp (2 * x)) * (y - x))) := by ring
    _ ≤ (Real.exp (9 * x / 2) * Real.exp (-Real.pi * Real.exp (2 * x)))
        * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hpi, hd]

/-- **The theta source decays exponentially past any point of the positive half-line**, with a
rate that grows doubly exponentially. -/
theorem thetaCuspFullSource_le_shift {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    thetaCuspFullSource y
      ≤ (thetaEnvelopeUpper * thetaEnvelope x)
        * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by
  have h1 := thetaCuspFullSource_le_envelope (le_trans (by linarith) hxy)
  have h2 := thetaEnvelope_le_shift hx hxy
  have hU := thetaEnvelopeUpper_pos
  calc thetaCuspFullSource y ≤ thetaEnvelopeUpper * thetaEnvelope y := h1
    _ ≤ thetaEnvelopeUpper
        * (thetaEnvelope x * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x))) :=
        mul_le_mul_of_nonneg_left h2 hU.le
    _ = (thetaEnvelopeUpper * thetaEnvelope x)
        * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by ring

end HedenmalmThetaSource

end

end RHTower
