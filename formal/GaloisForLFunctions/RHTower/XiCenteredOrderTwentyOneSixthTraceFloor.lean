import GaloisForLFunctions.RHTower.XiCenteredOrderNineteenSourceBudgetClosure
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation

/-!
# Sixth-trace floor on the centered order-twenty-one residual annulus

For horizontal and vertical squares `u` and `v`, and `w = u + v`, the real
part of the centered reciprocal-square cube factors as

`((v-u)/w) * ((v²-14uv+u²)/w²) * (1/w³)`.

The full residual rectangle gives the three exact lower factors
`589/591`, `575/591`, and `(4/723)³`.  Thus every residual atom exceeds
`1/6100000`.  FE--Schwarz symmetry turns this into a four-copy source charge
strictly above `2/3050000`.  No zero table or height computation enters.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact factorization of the real sixth reciprocal-trace atom. -/
theorem xiZeroCopyReciprocalSquare_cube_re_formula (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re =
      let u := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
      let v := (q.1 : ℂ).im ^ (2 : ℕ)
      let w := u + v
      ((v - u) / w) * ((v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ)) * (1 / w ^ (3 : ℕ)) := by
  dsimp only
  rw [show xiZeroCopyReciprocalSquare q ^ (3 : ℕ) =
      xiZeroCopyReciprocalSquare q ^ (2 : ℕ) * xiZeroCopyReciprocalSquare q by ring,
    Complex.mul_re, pow_two, Complex.mul_re, Complex.mul_im,
    xiZeroCopyReciprocalSquare_re_formula,
    xiZeroCopyReciprocalSquare_im_formula]
  have hden : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  field_simp [hden]
  ring

/-- Uniform sixth-trace floor on the full order-twenty-one residual height rectangle. -/
theorem one_div_sixMillionOneHundredThousand_lt_xiSixthReciprocalTraceAtom
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < 361 / 2) :
    (1 / 6100000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let w : ℝ := u + v
  have hu0 : 0 < u := by simpa only [u] using huLower
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < 361 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hvw : v < w := by dsimp only [w]; linarith
  have hwU : w < 723 / 4 := by dsimp only [w]; linarith
  have hur : 591 * u < w := by dsimp only [w]; linarith
  have huv : 591 * (u * v) < w ^ (2 : ℕ) := by
    have hleft : 591 * u * v < w * v :=
      mul_lt_mul_of_pos_right hur hv0
    have hright : w * v < w * w :=
      mul_lt_mul_of_pos_left hvw hw0
    nlinarith
  have hfirst : (589 / 591 : ℝ) < (v - u) / w := by
    rw [lt_div_iff₀ hw0]
    dsimp only [w]
    nlinarith
  have hsecond : (575 / 591 : ℝ) <
      (v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ) := by
    rw [lt_div_iff₀ (sq_pos_of_pos hw0)]
    have hid : v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ) = w ^ (2 : ℕ) - 16 * u * v := by
      dsimp only [w]
      ring
    rw [hid]
    nlinarith
  have hthird : (4 / 723 : ℝ) ^ (3 : ℕ) < 1 / w ^ (3 : ℕ) := by
    have hw3 : w ^ (3 : ℕ) < (723 / 4 : ℝ) ^ (3 : ℕ) :=
      pow_lt_pow_left₀ hwU hw0.le (by norm_num)
    rw [one_div]
    rw [show (4 / 723 : ℝ) ^ (3 : ℕ) = ((723 / 4 : ℝ) ^ (3 : ℕ))⁻¹ by norm_num]
    simpa only [one_div] using one_div_lt_one_div_of_lt (pow_pos hw0 3) hw3
  have hfirst0 : 0 < (v - u) / w :=
    (by norm_num : (0 : ℝ) < 589 / 591).trans hfirst
  have hsecond0 : 0 < (v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ) :=
    (by norm_num : (0 : ℝ) < 575 / 591).trans hsecond
  have hrat : (1 / 6100000 : ℝ) <
      (589 / 591 : ℝ) * (575 / 591 : ℝ) * (4 / 723 : ℝ) ^ (3 : ℕ) := by
    norm_num
  rw [xiZeroCopyReciprocalSquare_cube_re_formula]
  dsimp only [u, v, w] at *
  calc
    (1 / 6100000 : ℝ) <
        (589 / 591 : ℝ) * (575 / 591 : ℝ) * (4 / 723 : ℝ) ^ (3 : ℕ) := hrat
    _ < ((v - u) / w) * (575 / 591 : ℝ) * (4 / 723 : ℝ) ^ (3 : ℕ) := by
      gcongr
    _ < ((v - u) / w) *
        ((v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ)) * (4 / 723 : ℝ) ^ (3 : ℕ) := by
      gcongr
    _ < ((v - u) / w) *
        ((v ^ (2 : ℕ) - 14 * u * v + u ^ (2 : ℕ)) / w ^ (2 : ℕ)) * (1 / w ^ (3 : ℕ)) := by
      gcongr

lemma xiSixthReciprocalTraceAtom_lineConj (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) ^ (3 : ℕ)).re =
      (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re := by
  have hz :
      xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) =
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
    rw [xiZeroCopyReciprocalSquare, xiZeroCopyReciprocalSquare,
      xiSpectralPoint_lineConj, map_pow, map_inv₀]
  rw [hz, ← map_pow, Complex.conj_re]

lemma xiSixthReciprocalTraceAtom_conj (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) ^ (3 : ℕ)).re =
      (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re := by
  have hz :
      xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) =
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
    rw [xiZeroCopyReciprocalSquare, xiZeroCopyReciprocalSquare,
      xiSpectralPoint_copyConj, map_pow, map_inv₀, inv_neg]
    ring
  rw [hz, ← map_pow, Complex.conj_re]

/-- The complete sixth reciprocal trace is the second normalized source moment. -/
theorem tsum_xiSixthReciprocalTraceAtom_eq_source :
    (∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re) =
      normalizedPrimeArchMoment 2 := by
  have hsum := summable_xiZeroCopyReciprocalSquare_pow 2
  calc
    (∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re) =
        (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re := by
      rw [Complex.re_tsum hsum]
    _ = (xiCentralReciprocalMoment 2).re := by
      rw [tsum_xiZeroCopyReciprocalSquare_pow 2]
    _ = normalizedPrimeArchMoment 2 := by
      have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 2
      simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
        congrArg Complex.re hsource.symm

/-- Four distinct FE--Schwarz copies of an off-line sixth-trace atom are bounded by the source. -/
theorem four_mul_xiSixthReciprocalTraceAtom_le_source_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 * (xiZeroCopyReciprocalSquare q ^ (3 : ℕ)).re ≤
      normalizedPrimeArchMoment 2 := by
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ (3 : ℕ)).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 2).mapL Complex.reCLM
  have hle := four_mul_le_tsum_of_quartet_invariant
    re_xiCentral_cube_nonneg hsum
    xiSixthReciprocalTraceAtom_lineConj xiSixthReciprocalTraceAtom_conj q hoff
  rw [tsum_xiSixthReciprocalTraceAtom_eq_source] at hle
  exact hle

/-- Every zero in the order-twenty-one residual annulus forces a source charge above the exact
quartet threshold `2/3050000`. -/
theorem two_over_threeMillionFiftyThousand_lt_source_of_centeredOrderTwentyOneResidualAnnulus
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyOneResidualAnnulus q) :
    (2 / 3050000 : ℝ) < normalizedPrimeArchMoment 2 := by
  have hle := four_mul_xiSixthReciprocalTraceAtom_le_source_of_offLine q hq.1
  have hatom := one_div_sixMillionOneHundredThousand_lt_xiSixthReciprocalTraceAtom
    q (by linarith [hq.2.1]) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  nlinarith

end

end RHTower
