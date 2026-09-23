import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentFloor

/-!
# Sixteenth-mesh floor for the dominant theta fourth moment

The earlier eighth-mesh certificate leaves too much source slack to decide the first residual
centered order-twenty annulus.  Halving the mesh replaces the quarter-exponential chord by an
eighth-exponential chord.  The resulting exact rational certificate proves

`139 / 50000 < thetaCuspAtomRawEvenMoment 2 1`.

No zero table or numerical integration enters: convexity, Taylor inequalities, and exact
polynomial interval integrals supply the complete certificate.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- Rational majorant for one eighth of the exponential clock. -/
def thetaCuspEighthExpMajorant : ℝ := 567 / 500

/-- Convex rational chord on the `j`-th interval of length `1/16`. -/
def thetaCuspEighthExpChord (j : ℕ) (x : ℝ) : ℝ :=
  let t : ℝ := 16 * x - j
  (1 - t) * thetaCuspEighthExpMajorant ^ j +
    t * thetaCuspEighthExpMajorant ^ (j + 1)

/-- Rational rate majorant on a sixteenth interval. -/
def thetaCuspFirstLiouvilleRateMajorantSixteenth (j : ℕ) (x : ℝ) : ℝ :=
  (3927 / 1250 : ℝ) * (thetaCuspEighthExpChord j x - 1) - 5 * x / 2

/-- Slope of the sixteenth-mesh affine rate majorant. -/
def thetaCuspFirstLiouvilleRateSlopeSixteenth (j : ℕ) : ℝ :=
  (3927 / 1250 : ℝ) * 16 *
      (thetaCuspEighthExpMajorant ^ (j + 1) -
        thetaCuspEighthExpMajorant ^ j) -
    5 / 2

/-- Alternating endpoint certificate for the sixteenth mesh. -/
def thetaCuspFirstLiouvilleEndpointCertificateSixteenth (j : ℕ) : ℝ :=
  (expNegTruncPoly 64).eval
    (thetaCuspFirstLiouvilleRateMajorantSixteenth j
      (((j + 1 : ℕ) : ℝ) / 16))

/-- Rational lower density on the `j`-th sixteenth interval. -/
def thetaCuspFirstAtomFourthIntervalCertificateSixteenth (j : ℕ) (x : ℝ) : ℝ :=
  (6283 / 500 : ℝ) * (3 / 70) *
    thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
    x ^ (4 : ℕ) *
    ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
    thetaCuspExpTaylorFive
      (thetaCuspFirstLiouvilleRateSlopeSixteenth j *
        (((j + 1 : ℕ) : ℝ) / 16 - x))

/-- Exact algebraic mass of one sixteenth-mesh certificate. -/
def thetaCuspFirstAtomFourthIntervalMassSixteenth (j : ℕ) : ℝ :=
  (6283 / 500 : ℝ) * (3 / 70) *
    thetaCuspFirstAtomFourthTaylorMass
      ((j : ℝ) / 16) (((j + 1 : ℕ) : ℝ) / 16)
      (thetaCuspFirstLiouvilleRateSlopeSixteenth j)

theorem exp_one_eighth_lt_thetaCuspEighthExpMajorant :
    Real.exp (1 / 8 : ℝ) < thetaCuspEighthExpMajorant := by
  rw [thetaCuspEighthExpMajorant]
  by_contra h
  have hle : (567 / 500 : ℝ) ≤ Real.exp (1 / 8 : ℝ) := le_of_not_gt h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 567 / 500) hle 8
  have heq : Real.exp (1 / 8 : ℝ) ^ (8 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq] at hp
  have hu : Real.exp 1 < (567 / 500 : ℝ) ^ (8 : ℕ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  linarith

theorem exp_nat_eighth_le_thetaCuspEighthExpMajorant_pow (j : ℕ) :
    Real.exp ((j : ℝ) / 8) ≤ thetaCuspEighthExpMajorant ^ j := by
  rw [show (j : ℝ) / 8 = (j : ℕ) * (1 / 8 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le
    exp_one_eighth_lt_thetaCuspEighthExpMajorant.le j

/-- Convexity controls `exp (2x)` on each sixteenth interval. -/
theorem exp_two_mul_le_thetaCuspEighthExpChord
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 16 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 16)) :
    Real.exp (2 * x) ≤ thetaCuspEighthExpChord j x := by
  let t : ℝ := 16 * x - j
  have ht0 : 0 ≤ t := by dsimp only [t]; push_cast at hx ⊢; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; push_cast at hx ⊢; linarith
  have hconv := convexOn_exp.2
    (Set.mem_univ ((j : ℝ) / 8))
    (Set.mem_univ (((j + 1 : ℕ) : ℝ) / 8))
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  have harg :
      (1 - t) * ((j : ℝ) / 8) +
          t * (((j + 1 : ℕ) : ℝ) / 8) = 2 * x := by
    dsimp only [t]
    push_cast
    ring
  simp only [smul_eq_mul] at hconv
  rw [harg] at hconv
  have hj := exp_nat_eighth_le_thetaCuspEighthExpMajorant_pow j
  have hj1 := exp_nat_eighth_le_thetaCuspEighthExpMajorant_pow (j + 1)
  calc
    Real.exp (2 * x) ≤
        (1 - t) * Real.exp ((j : ℝ) / 8) +
          t * Real.exp (((j + 1 : ℕ) : ℝ) / 8) := hconv
    _ ≤ (1 - t) * thetaCuspEighthExpMajorant ^ j +
          t * thetaCuspEighthExpMajorant ^ (j + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hj1 ht0)
    _ = thetaCuspEighthExpChord j x := by
      simp only [thetaCuspEighthExpChord, t]

theorem thetaCuspFirstLiouvilleRate_le_majorantSixteenth
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 16 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 16)) :
    thetaCuspFirstLiouvilleRate x ≤
      thetaCuspFirstLiouvilleRateMajorantSixteenth j x := by
  have hx0 : 0 ≤ x := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / 16 := by positivity
    linarith [hx.1]
  have hchord := exp_two_mul_le_thetaCuspEighthExpChord hx
  have hone : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
  have hchord0 : 0 ≤ thetaCuspEighthExpChord j x - 1 := by linarith
  have hpi : Real.pi < (3927 / 1250 : ℝ) := by
    nlinarith [Real.pi_lt_d4]
  rw [thetaCuspFirstLiouvilleRate,
    thetaCuspFirstLiouvilleRateMajorantSixteenth]
  calc
    Real.pi * (Real.exp (2 * x) - 1) - 5 * x / 2 ≤
        Real.pi * (thetaCuspEighthExpChord j x - 1) - 5 * x / 2 := by
      gcongr
    _ ≤ (3927 / 1250 : ℝ) * (thetaCuspEighthExpChord j x - 1) -
          5 * x / 2 := by
      gcongr

theorem thetaCuspFirstLiouvilleRateMajorantSixteenth_affine
    (j : ℕ) (x : ℝ) :
    thetaCuspFirstLiouvilleRateMajorantSixteenth j x =
      thetaCuspFirstLiouvilleRateMajorantSixteenth j
          (((j + 1 : ℕ) : ℝ) / 16) -
        thetaCuspFirstLiouvilleRateSlopeSixteenth j *
          (((j + 1 : ℕ) : ℝ) / 16 - x) := by
  simp only [thetaCuspFirstLiouvilleRateMajorantSixteenth,
    thetaCuspFirstLiouvilleRateSlopeSixteenth, thetaCuspEighthExpChord,
    thetaCuspEighthExpMajorant]
  push_cast
  ring

theorem thetaCuspFirstLiouvilleRateSlopeSixteenth_pos
    {j : ℕ} (hj : j < 14) :
    0 < thetaCuspFirstLiouvilleRateSlopeSixteenth j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstLiouvilleRateSlopeSixteenth,
      thetaCuspEighthExpMajorant]

theorem thetaCuspFirstLiouvilleRateMajorantSixteenth_endpoint_pos
    {j : ℕ} (hj : j < 14) :
    0 < thetaCuspFirstLiouvilleRateMajorantSixteenth j
      (((j + 1 : ℕ) : ℝ) / 16) := by
  interval_cases j <;>
    norm_num [thetaCuspFirstLiouvilleRateMajorantSixteenth,
      thetaCuspEighthExpChord, thetaCuspEighthExpMajorant]

theorem thetaCuspFirstLiouvilleEndpointCertificateSixteenth_pos
    {j : ℕ} (hj : j < 14) :
    0 < thetaCuspFirstLiouvilleEndpointCertificateSixteenth j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstLiouvilleEndpointCertificateSixteenth,
      thetaCuspFirstLiouvilleRateMajorantSixteenth,
      thetaCuspEighthExpChord, thetaCuspEighthExpMajorant,
      eval_expNegTruncPoly, Finset.sum_range_succ]

theorem thetaCuspFirstLiouvilleEndpointCertificateSixteenth_lt_exp
    {j : ℕ} (hj : j < 14) :
    thetaCuspFirstLiouvilleEndpointCertificateSixteenth j <
      Real.exp
        (-thetaCuspFirstLiouvilleRateMajorantSixteenth j
          (((j + 1 : ℕ) : ℝ) / 16)) := by
  have hz := thetaCuspFirstLiouvilleRateMajorantSixteenth_endpoint_pos hj
  have h := expNegTruncPoly_sub_exp_oriented_pos
    (m := 64) (by norm_num) hz
  norm_num at h
  rw [thetaCuspFirstLiouvilleEndpointCertificateSixteenth]
  convert h using 1 <;> push_cast <;> ring

theorem thetaCuspFirstLiouvilleIntervalCertificateSixteenth_le_gibbs
    {j : ℕ} (hj : j < 14) {x : ℝ}
    (hx : (j : ℝ) / 16 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 16)) :
    (3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
        thetaCuspExpTaylorFive
          (thetaCuspFirstLiouvilleRateSlopeSixteenth j *
            (((j + 1 : ℕ) : ℝ) / 16 - x)) ≤
      thetaCuspLiouvilleGibbsAtom 1 x := by
  let b : ℝ := ((j + 1 : ℕ) : ℝ) / 16
  let z : ℝ := thetaCuspFirstLiouvilleRateMajorantSixteenth j b
  let k : ℝ := thetaCuspFirstLiouvilleRateSlopeSixteenth j
  let u : ℝ := k * (b - x)
  have hk : 0 < k := by
    simpa only [k] using thetaCuspFirstLiouvilleRateSlopeSixteenth_pos hj
  have hxb : 0 ≤ b - x := by dsimp only [b]; push_cast at hx ⊢; linarith
  have hu : 0 ≤ u := mul_nonneg hk.le hxb
  have hrate := thetaCuspFirstLiouvilleRate_le_majorantSixteenth hx
  have haffine := thetaCuspFirstLiouvilleRateMajorantSixteenth_affine j x
  have hrate' : thetaCuspFirstLiouvilleRate x ≤ z - u := by
    dsimp only [z, u, k, b]
    rw [← haffine]
    exact hrate
  have hexpRate : Real.exp (-z) * Real.exp u ≤
      Real.exp (-thetaCuspFirstLiouvilleRate x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hP := thetaCuspFirstLiouvilleEndpointCertificateSixteenth_lt_exp hj
  have hP0 := thetaCuspFirstLiouvilleEndpointCertificateSixteenth_pos hj
  have hT := thetaCuspExpTaylorFive_le_exp hu
  have hT0 := thetaCuspExpTaylorFive_nonneg hu
  have hPT : thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
      thetaCuspExpTaylorFive u ≤ Real.exp (-z) * Real.exp u := by
    exact mul_le_mul hP.le hT hT0 (Real.exp_pos _).le
  rw [thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    (3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
          thetaCuspExpTaylorFive
            (thetaCuspFirstLiouvilleRateSlopeSixteenth j *
              (((j + 1 : ℕ) : ℝ) / 16 - x)) =
        (3 / 70 : ℝ) *
          (thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
            thetaCuspExpTaylorFive u) := by
      dsimp only [u, k, b]
      ring
    _ ≤ Real.exp (-Real.pi) *
          (thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
            thetaCuspExpTaylorFive u) := by
      exact mul_le_mul_of_nonneg_right three_div_seventy_lt_exp_neg_pi.le
        (mul_nonneg hP0.le hT0)
    _ ≤ Real.exp (-Real.pi) * (Real.exp (-z) * Real.exp u) := by
      exact mul_le_mul_of_nonneg_left hPT (Real.exp_pos _).le
    _ ≤ Real.exp (-Real.pi) * Real.exp (-thetaCuspFirstLiouvilleRate x) := by
      exact mul_le_mul_of_nonneg_left hexpRate (Real.exp_pos _).le

theorem thetaCuspFirstAtomFourthIntervalCertificateSixteenth_le_density
    {j : ℕ} (hj : j < 14) {x : ℝ}
    (hx : (j : ℝ) / 16 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 16)) :
    thetaCuspFirstAtomFourthIntervalCertificateSixteenth j x ≤
      2 * (x ^ (4 : ℕ) * thetaCuspSourceTerm x 1) := by
  have hx0 : 0 ≤ x := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [hx.1]
  have hTsource := thetaCuspExpTaylorFive_le_exp
    (u := 2 * x) (by positivity)
  have hinner :
      (6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3 ≤
        2 * Real.pi * Real.exp (2 * x) - 3 := by
    have hpi : (6283 / 1000 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_d4]
    calc
      (6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3 ≤
          (6283 / 1000 : ℝ) * Real.exp (2 * x) - 3 := by
        gcongr
      _ ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by
        gcongr
  have hinner0 :
      0 ≤ (6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3 := by
    rw [thetaCuspExpTaylorFive]
    nlinarith [sq_nonneg x, pow_nonneg hx0 3, pow_nonneg hx0 4,
      pow_nonneg hx0 5]
  have houter : (6283 / 500 : ℝ) ≤ 4 * Real.pi := by
    nlinarith [Real.pi_gt_d4]
  have hb := thetaCuspFirstLiouvilleIntervalCertificateSixteenth_le_gibbs hj hx
  have hb0 : 0 ≤
      (3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
        thetaCuspExpTaylorFive
          (thetaCuspFirstLiouvilleRateSlopeSixteenth j *
            (((j + 1 : ℕ) : ℝ) / 16 - x)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (thetaCuspFirstLiouvilleEndpointCertificateSixteenth_pos hj).le)
      (thetaCuspExpTaylorFive_nonneg (mul_nonneg
        (thetaCuspFirstLiouvilleRateSlopeSixteenth_pos hj).le (by
          push_cast at hx ⊢
          linarith [hx.2])))
  have hgibbs0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hactualInner0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 :=
    hinner0.trans hinner
  rw [thetaCuspFirstAtomFourthIntervalCertificateSixteenth,
    thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    (6283 / 500 : ℝ) * (3 / 70) *
          thetaCuspFirstLiouvilleEndpointCertificateSixteenth j * x ^ (4 : ℕ) *
          ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
          thetaCuspExpTaylorFive
            (thetaCuspFirstLiouvilleRateSlopeSixteenth j *
              (((j + 1 : ℕ) : ℝ) / 16 - x)) =
        (6283 / 500 : ℝ) * x ^ (4 : ℕ) *
          ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
          ((3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
            thetaCuspExpTaylorFive
              (thetaCuspFirstLiouvilleRateSlopeSixteenth j *
                (((j + 1 : ℕ) : ℝ) / 16 - x))) := by
      ring
    _ ≤ (6283 / 500 : ℝ) * x ^ (4 : ℕ) *
          ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_left hb
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 4)) hinner0)
    _ ≤ (6283 / 500 : ℝ) * x ^ (4 : ℕ) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (by norm_num) (pow_nonneg hx0 4))) hgibbs0
    _ ≤ (4 * Real.pi) * x ^ (4 : ℕ) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 4)) hactualInner0)
        hgibbs0
    _ = 2 * (x ^ (4 : ℕ) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) := by ring

theorem intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificateSixteenth_eq_mass
    (j : ℕ) :
    (∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16),
      thetaCuspFirstAtomFourthIntervalCertificateSixteenth j x) =
      thetaCuspFirstLiouvilleEndpointCertificateSixteenth j *
        thetaCuspFirstAtomFourthIntervalMassSixteenth j := by
  rw [show
      (fun x : ℝ => thetaCuspFirstAtomFourthIntervalCertificateSixteenth j x) =
        fun x : ℝ =>
          ((6283 / 500 : ℝ) * (3 / 70) *
              thetaCuspFirstLiouvilleEndpointCertificateSixteenth j) *
            (x ^ (4 : ℕ) *
              ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
              thetaCuspExpTaylorFive
                (thetaCuspFirstLiouvilleRateSlopeSixteenth j *
                  ((((j + 1 : ℕ) : ℝ) / 16) - x))) by
    funext x
    rw [thetaCuspFirstAtomFourthIntervalCertificateSixteenth]
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_thetaCuspFirstAtomFourthTaylorShape_eq_mass]
  rw [thetaCuspFirstAtomFourthIntervalMassSixteenth]
  ring

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
/-- Fourteen exact rational interval certificates clear `139/50000`. -/
theorem oneHundredThirtyNine_div_fiftyThousand_lt_sum_thetaCuspFirstAtomFourthIntervalCertificateSixteenth :
    (139 / 50000 : ℝ) <
      ∑ j ∈ Finset.range 14,
        ∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16),
          thetaCuspFirstAtomFourthIntervalCertificateSixteenth j x := by
  simp_rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificateSixteenth_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMassSixteenth,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlopeSixteenth,
    thetaCuspFirstLiouvilleEndpointCertificateSixteenth,
    thetaCuspFirstLiouvilleRateMajorantSixteenth, thetaCuspEighthExpChord,
    thetaCuspEighthExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

/-- **Unconditional sharpened dominant-atom fourth-moment floor.** -/
theorem oneHundredThirtyNine_div_fiftyThousand_lt_thetaCuspAtomRawEvenMoment_two_one :
    (139 / 50000 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (4 : ℕ) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm 2 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by norm_num) <|
      mul_nonneg (pow_nonneg hx.le _) (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hsegment (j : ℕ) (hj : j < 14) :
      (∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16),
          thetaCuspFirstAtomFourthIntervalCertificateSixteenth j x) ≤
        ∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16), f x := by
    apply intervalIntegral.integral_mono_on
    · push_cast
      linarith
    · have hcertcont : Continuous
          (thetaCuspFirstAtomFourthIntervalCertificateSixteenth j) := by
        unfold thetaCuspFirstAtomFourthIntervalCertificateSixteenth
          thetaCuspExpTaylorFive
        fun_prop
      exact hcertcont.intervalIntegrable _ _
    · exact hfcont.intervalIntegrable _ _
    · intro x hx
      exact thetaCuspFirstAtomFourthIntervalCertificateSixteenth_le_density hj hx
  have hsum :
      (∑ j ∈ Finset.range 14,
          ∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16),
            thetaCuspFirstAtomFourthIntervalCertificateSixteenth j x) ≤
        ∑ j ∈ Finset.range 14,
          ∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16), f x := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 14,
          ∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16), f x) =
        ∫ x in (0 : ℝ)..7 / 8, f x := by
    convert
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := f) (a := fun k : ℕ => (k : ℝ) / 16) (n := 14) (μ := volume)
        (fun k _ => hfcont.intervalIntegrable _ _)) using 1 <;> norm_num
  have hwindow : (∫ x in (0 : ℝ)..7 / 8, f x) ≤ ∫ x in Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set hfint hfnonneg
      (Filter.Eventually.of_forall fun x hx => hx.1)
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment 2 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  have hcert :=
    oneHundredThirtyNine_div_fiftyThousand_lt_sum_thetaCuspFirstAtomFourthIntervalCertificateSixteenth
  calc
    (139 / 50000 : ℝ) <
        ∑ j ∈ Finset.range 14,
          ∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16),
            thetaCuspFirstAtomFourthIntervalCertificateSixteenth j x := hcert
    _ ≤ ∑ j ∈ Finset.range 14,
          ∫ x in (j : ℝ) / 16..(((j + 1 : ℕ) : ℝ) / 16), f x := hsum
    _ = ∫ x in (0 : ℝ)..7 / 8, f x := hjoin
    _ ≤ ∫ x in Ioi 0, f x := hwindow
    _ = thetaCuspAtomRawEvenMoment 2 1 := hraw

end

end RHTower
