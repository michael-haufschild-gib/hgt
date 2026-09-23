import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodLiftReduction
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthAtomPairTrace
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthFockSector
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalTailCooling
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleSixBound

/-!
# Fourth/fifth logarithmic likelihood cooling on the C5 structural tail

This module closes the scalar cooling gate

`-J₅(x) < 6 A(x) J₄(x)` for `x ≥ 0` and `A(x) ≥ 6`.

The proof isolates the exact `n = 2` atom--ray reserve, absorbs every stable `n ≥ 3`
carrier by the eighth-monomial tower, and retains a quantitative reserve of
`16128 A⁴ exp(-3A)` after normalization.  Bell corrections are genuinely colder:
the support-edge law gives `p < 35 exp(-3A)`, hence the complete fourth Bell loss costs
less than `2000000 exp(-3A)`.  At scale six the reserve dominates.

RH proof chain: this cooling gate pairs with third/second likelihood cooling to orient the first
nonzero C5 likelihood seam coefficient; that supplies the convex likelihood lift used by the
far-tail C5 orientation, then the CLG/TTF or Weil-positivity endpoint.
-/

namespace RHTower

noncomputable section

open MeasureTheory Set

def thetaCuspLikelihoodFourthFifthDominantReservePolynomial (A : ℝ) : ℝ :=
  27648 * A ^ (9 : ℕ) - 266976 * A ^ (8 : ℕ) + 1120128 * A ^ (7 : ℕ) -
    2666128 * A ^ (6 : ℕ) + 3891600 * A ^ (5 : ℕ) - 3546654 * A ^ (4 : ℕ) +
    1938420 * A ^ (3 : ℕ) - 573156 * A ^ (2 : ℕ) + 68850 * A - 1215

theorem thetaCuspLikelihoodFourthFifthDominantReservePolynomial_pos
    {A : ℝ} (hA : 6 ≤ A) :
    0 < thetaCuspLikelihoodFourthFifthDominantReservePolynomial A := by
  let y := A - 6
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hAeq : A = y + 6 := by dsimp only [y]; ring
  rw [hAeq]
  unfold thetaCuspLikelihoodFourthFifthDominantReservePolynomial
  ring_nf
  positivity

def thetaCuspLikelihoodDominantOrdinaryCoolingReserve (A : ℝ) : ℝ :=
  let B := A - 3 / 2
  let M := fun q : ℕ =>
    (∫ t : ℝ, t ^ q * Real.exp (-(B * t))
      ∂thetaCuspAtomLikelihoodSpectralMeasure 2)
  (-A ^ (5 : ℕ) * M 5 + (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) * M 4 -
    (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) * M 3 +
    (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) * M 2 -
    (3 * A ^ (2 : ℕ) + A) * M 1)

theorem thetaCuspLikelihoodDominantOrdinaryCoolingReserve_eq
    {A : ℝ} (hA : 6 ≤ A) :
    thetaCuspLikelihoodDominantOrdinaryCoolingReserve A =
      Real.exp (-3 * A) *
        (12 * A * thetaCuspLikelihoodFourthFifthDominantReservePolynomial A /
          (2 * A - 3) ^ (6 : ℕ)) := by
  have hB : 0 < A - 3 / 2 := by linarith
  have hBne : A - 3 / 2 ≠ 0 := ne_of_gt hB
  have hden : 2 * A - 3 ≠ 0 := by linarith
  have hdenpow : (2 * A - 3) ^ (6 : ℕ) ≠ 0 := pow_ne_zero 6 hden
  rw [show Real.exp (-3 * A) *
      (12 * A * thetaCuspLikelihoodFourthFifthDominantReservePolynomial A /
        (2 * A - 3) ^ (6 : ℕ)) =
      (Real.exp (-3 * A) *
        (12 * A * thetaCuspLikelihoodFourthFifthDominantReservePolynomial A)) /
          (2 * A - 3) ^ (6 : ℕ) by ring]
  apply (eq_div_iff hdenpow).2
  unfold thetaCuspLikelihoodDominantOrdinaryCoolingReserve
  dsimp only
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 5 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 4 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 3 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 2 hB,
    integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
      (n := 2) (by norm_num) 1 hB]
  have hgap : thetaCuspLikelihoodGap 2 = 3 := by
    norm_num [thetaCuspLikelihoodGap]
  rw [hgap]
  generalize hBeq : A - 3 / 2 = B at *
  rw [show Real.exp (-(3 / 2 : ℝ) * 3) *
      Real.exp (-(B * 3)) = Real.exp (-3 * A) by
    rw [← Real.exp_add]
    congr 1
    nlinarith]
  simp only [Finset.sum_range_succ, Nat.factorial, Nat.choose,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul, Nat.cast_add]
  have hAB : A = B + 3 / 2 := by linarith
  rw [hAB]
  field_simp [hBne]
  unfold thetaCuspLikelihoodFourthFifthDominantReservePolynomial
  ring

theorem thetaCuspLikelihoodDominantOrdinaryCoolingReserve_pos
    {A : ℝ} (hA : 6 ≤ A) :
    0 < thetaCuspLikelihoodDominantOrdinaryCoolingReserve A := by
  rw [thetaCuspLikelihoodDominantOrdinaryCoolingReserve_eq hA]
  have hpoly := thetaCuspLikelihoodFourthFifthDominantReservePolynomial_pos hA
  have hA0 : 0 < A := by linarith
  have hden : 0 < (2 * A - 3) ^ (6 : ℕ) := pow_pos (by linarith) 6
  positivity

theorem threeThousandTwentyFour_mul_pow_four_lt_dominantCoolingCore
    {A : ℝ} (hA : 6 ≤ A) :
    3024 * A ^ (4 : ℕ) <
      12 * A * thetaCuspLikelihoodFourthFifthDominantReservePolynomial A /
        (2 * A - 3) ^ (6 : ℕ) := by
  have hden : 0 < (2 * A - 3) ^ (6 : ℕ) := pow_pos (by linarith) 6
  apply (lt_div_iff₀ hden).2
  let y := A - 6
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  rw [show A = y + 6 by dsimp only [y]; ring]
  unfold thetaCuspLikelihoodFourthFifthDominantReservePolynomial
  apply sub_pos.mp
  ring_nf
  positivity

theorem fourThousandThirtyTwo_mul_pow_four_lt_dominantCoolingCore
    {A : ℝ} (hA : 6 ≤ A) :
    4032 * A ^ (4 : ℕ) <
      12 * A * thetaCuspLikelihoodFourthFifthDominantReservePolynomial A /
        (2 * A - 3) ^ (6 : ℕ) := by
  have hden : 0 < (2 * A - 3) ^ (6 : ℕ) := pow_pos (by linarith) 6
  apply (lt_div_iff₀ hden).2
  let y := A - 6
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  rw [show A = y + 6 by dsimp only [y]; ring]
  unfold thetaCuspLikelihoodFourthFifthDominantReservePolynomial
  apply sub_pos.mp
  ring_nf
  positivity

theorem pow_four_mul_thetaCuspLikelihoodStableShiftedEighthTail_lt
    {A : ℝ} (hA : 6 ≤ A) :
    A ^ (4 : ℕ) * thetaCuspLikelihoodStableShiftedEighthTail A < 756 := by
  have hApi : Real.pi ≤ A := by nlinarith [Real.pi_lt_four]
  have hdelta : 0 ≤ A - Real.pi := sub_nonneg.mpr hApi
  have hexpTen : Real.exp (-10) < (1 / 1000 : ℝ) := by
    have he1 : (2 : ℝ) < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
    have hten : (1000 : ℝ) < Real.exp 10 := by
      have hp : (2 : ℝ) ^ (10 : ℕ) < Real.exp 1 ^ (10 : ℕ) :=
        pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
      rw [← Real.exp_nat_mul] at hp
      norm_num at hp
      linarith
    have hprod : Real.exp (-10) * Real.exp 10 = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (-10), Real.exp_pos 10]
  have hedge : Real.exp (-5 * (6 - Real.pi)) < (1 / 1000 : ℝ) := by
    have harg : -5 * (6 - Real.pi) < -10 := by nlinarith [Real.pi_lt_four]
    exact (Real.exp_lt_exp.mpr harg).trans hexpTen
  let s := A - 6
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  have hone : 1 + s / 6 ≤ Real.exp (s / 6) := by
    simpa only [add_comm] using Real.add_one_le_exp (s / 6)
  have hone0 : 0 ≤ 1 + s / 6 := by positivity
  have hpow := pow_le_pow_left₀ hone0 hone 4
  have hexppow : Real.exp (s / 6) ^ (4 : ℕ) = Real.exp (2 * s / 3) := by
    rw [show Real.exp (s / 6) ^ (4 : ℕ) =
        Real.exp (s / 6) * Real.exp (s / 6) *
          Real.exp (s / 6) * Real.exp (s / 6) by ring,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexppow] at hpow
  have hscale : A ^ (4 : ℕ) * Real.exp (-5 * (A - 6)) ≤ 6 ^ (4 : ℕ) := by
    have hAeq : A = 6 * (1 + s / 6) := by dsimp only [s]; ring
    have hcombine : Real.exp (2 * s / 3) * Real.exp (-5 * s) =
        Real.exp (-13 * s / 3) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsmall : Real.exp (-13 * s / 3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    rw [hAeq, mul_pow,
      show -5 * (6 * (1 + s / 6) - 6) = -5 * s by ring]
    calc
      (6 : ℝ) ^ (4 : ℕ) * (1 + s / 6) ^ (4 : ℕ) * Real.exp (-5 * s) ≤
          6 ^ (4 : ℕ) * Real.exp (2 * s / 3) * Real.exp (-5 * s) := by gcongr
      _ = 6 ^ (4 : ℕ) * (Real.exp (2 * s / 3) * Real.exp (-5 * s)) := by ring
      _ = 6 ^ (4 : ℕ) * Real.exp (-13 * s / 3) := by rw [hcombine]
      _ ≤ 6 ^ (4 : ℕ) := by nlinarith [show (0 : ℝ) ≤ 6 ^ (4 : ℕ) by positivity]
  have hfactor :
      A ^ (4 : ℕ) * Real.exp (-5 * (A - Real.pi)) < (1296 / 1000 : ℝ) := by
    have hsplit : Real.exp (-5 * (A - Real.pi)) =
        Real.exp (-5 * (A - 6)) * Real.exp (-5 * (6 - Real.pi)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    have hpositive : 0 < A ^ (4 : ℕ) * Real.exp (-5 * (A - 6)) := by positivity
    have hmul := mul_lt_mul_of_pos_left hedge hpositive
    nlinarith
  have hterm : ∀ k : ℕ,
      ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
          Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3))) ≤
        Real.exp (-5 * (A - Real.pi)) *
          (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
            Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) := by
    intro k
    let g := thetaCuspLikelihoodGap (k + 3) - 3
    have hg : 5 ≤ g := by
      dsimp only [g, thetaCuspLikelihoodGap]
      have hk : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
      nlinarith
    have harg : -(A - Real.pi) * g ≤ -5 * (A - Real.pi) := by
      nlinarith
    have hexp := Real.exp_le_exp.mpr harg
    have hsplit : Real.exp (-(A * g)) =
        Real.exp (-Real.pi * g) * Real.exp (-(A - Real.pi) * g) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [g] at hsplit ⊢
    rw [hsplit]
    calc
      _ = (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
          Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) *
            Real.exp (-(A - Real.pi) * (thetaCuspLikelihoodGap (k + 3) - 3)) := by ring
      _ ≤ (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
          Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) *
            Real.exp (-5 * (A - Real.pi)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hsA := summable_thetaCuspLikelihoodStableShiftedEighthTail hApi
  have hsPi := summable_thetaCuspLikelihoodStableShiftedEighthTail (le_refl Real.pi)
  have hsMajor := hsPi.mul_left (Real.exp (-5 * (A - Real.pi)))
  have hsMajor' : Summable (fun k : ℕ => Real.exp (-5 * (A - Real.pi)) *
      (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)))) := by
    simpa only [neg_mul] using hsMajor
  have htail : thetaCuspLikelihoodStableShiftedEighthTail A ≤
      Real.exp (-5 * (A - Real.pi)) *
        thetaCuspLikelihoodStableShiftedEighthTail Real.pi := by
    unfold thetaCuspLikelihoodStableShiftedEighthTail
    calc
      _ ≤ ∑' k : ℕ, Real.exp (-5 * (A - Real.pi)) *
          (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
            Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) :=
        Summable.tsum_le_tsum hterm hsA hsMajor'
      _ = _ := by
        rw [tsum_mul_left]
        congr 1
        apply tsum_congr
        intro k
        congr 1
        ring
  have htailPi := thetaCuspLikelihoodStableShiftedEighthTail_le (le_refl Real.pi)
  have hbound : A ^ (4 : ℕ) * thetaCuspLikelihoodStableShiftedEighthTail A ≤
      (A ^ (4 : ℕ) * Real.exp (-5 * (A - Real.pi))) * 583 := by
    have hfirst := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ A ^ (4 : ℕ))
    have hsecond := mul_le_mul_of_nonneg_left htailPi
      (by positivity : 0 ≤ A ^ (4 : ℕ) * Real.exp (-5 * (A - Real.pi)))
    calc
      _ ≤ A ^ (4 : ℕ) * (Real.exp (-5 * (A - Real.pi)) *
          thetaCuspLikelihoodStableShiftedEighthTail Real.pi) := hfirst
      _ = (A ^ (4 : ℕ) * Real.exp (-5 * (A - Real.pi))) *
          thetaCuspLikelihoodStableShiftedEighthTail Real.pi := by ring
      _ ≤ (A ^ (4 : ℕ) * Real.exp (-5 * (A - Real.pi))) * 583 := hsecond
  have hfinal := mul_lt_mul_of_pos_right hfactor (by norm_num : (0 : ℝ) < 583)
  nlinarith

/-- One-particle score for the derivative of `exp (3A) F₄`. -/
def thetaCuspLikelihoodFourthFifthCoolingScore (A t : ℝ) : ℝ :=
  -A ^ (5 : ℕ) * t ^ (5 : ℕ) + (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) * t ^ (4 : ℕ) -
    (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) * t ^ (3 : ℕ) +
    (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) * t ^ (2 : ℕ) - (3 * A ^ (2 : ℕ) + A) * t

private theorem cooling_negative_envelope {z : ℝ} (hz : 48 ≤ z) :
    z ^ (5 : ℕ) + (18 * z + 25) * z ^ (3 : ℕ) + (3 * z + 1) * z ≤ z ^ (8 : ℕ) := by
  let y := z - 48
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  apply sub_nonneg.mp
  rw [show z = y + 48 by dsimp only [y]; ring]
  ring
  positivity

theorem neg_pow_eight_le_thetaCuspLikelihoodFourthFifthCoolingScore
    {A t : ℝ} (hA : 6 ≤ A) (ht : 8 ≤ t) :
    -(A * t) ^ (8 : ℕ) ≤ thetaCuspLikelihoodFourthFifthCoolingScore A t := by
  let z := A * t
  have hA0 : 0 ≤ A := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hz : 48 ≤ z := by dsimp only [z]; nlinarith
  have hz0 : 0 ≤ z := by linarith
  have hAz : A ≤ z := by
    dsimp only [z]
    nlinarith [mul_le_mul_of_nonneg_left ht1 hA0]
  have h3 : (18 * A + 25) * z ^ (3 : ℕ) ≤ (18 * z + 25) * z ^ (3 : ℕ) := by gcongr
  have h1 : (3 * A + 1) * z ≤ (3 * z + 1) * z := by gcongr
  have henv := cooling_negative_envelope hz
  have hdrop :
      -z ^ (5 : ℕ) - (18 * A + 25) * z ^ (3 : ℕ) - (3 * A + 1) * z ≤
        thetaCuspLikelihoodFourthFifthCoolingScore A t := by
    dsimp only [thetaCuspLikelihoodFourthFifthCoolingScore, z]
    have hp4 : 0 ≤ (3 * A + 10) * (A * t) ^ (4 : ℕ) := by positivity
    have hp2 : 0 ≤ (21 * A + 15) * (A * t) ^ (2 : ℕ) := by positivity
    nlinarith [show
      -A ^ (5 : ℕ) * t ^ (5 : ℕ) + (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) * t ^ (4 : ℕ) -
          (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) * t ^ (3 : ℕ) +
          (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) * t ^ (2 : ℕ) - (3 * A ^ (2 : ℕ) + A) * t =
        -(A * t) ^ (5 : ℕ) + (3 * A + 10) * (A * t) ^ (4 : ℕ) -
          (18 * A + 25) * (A * t) ^ (3 : ℕ) +
          (21 * A + 15) * (A * t) ^ (2 : ℕ) - (3 * A + 1) * (A * t) by ring]
  have hneg : -z ^ (8 : ℕ) ≤ -z ^ (5 : ℕ) - (18 * A + 25) * z ^ (3 : ℕ) - (3 * A + 1) * z := by
    nlinarith
  simpa only [z] using hneg.trans hdrop

private theorem ae_gap_le_thetaCuspAtomLikelihoodSpectralMeasure
    {n : ℕ} (_hn : 2 ≤ n) :
    ∀ᵐ t ∂thetaCuspAtomLikelihoodSpectralMeasure n,
      thetaCuspLikelihoodGap n ≤ t := by
  rw [thetaCuspAtomLikelihoodSpectralMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff measurableSet_Ici]
  · apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ht.le

private theorem integrable_thetaCuspLikelihoodFourthFifthCoolingScore_mul_exp
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ =>
      thetaCuspLikelihoodFourthFifthCoolingScore A t * Real.exp (-(B * t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  have h5 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 5 hB).const_mul (-A ^ (5 : ℕ))
  have h4 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul
    (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ))
  have h3 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
    (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ))
  have h2 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
    (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ))
  have h1 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul
    (3 * A ^ (2 : ℕ) + A)
  convert (((h5.add h4).sub h3).add h2).sub h1 using 1
  funext t
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold thetaCuspLikelihoodFourthFifthCoolingScore
  rw [show B * t = t * B by ring]
  ring_nf

def thetaCuspLikelihoodAtomFourthFifthCoolingMass (n : ℕ) (A B : ℝ) : ℝ :=
  ∫ t : ℝ, thetaCuspLikelihoodFourthFifthCoolingScore A t * Real.exp (-(B * t))
    ∂thetaCuspAtomLikelihoodSpectralMeasure n

private theorem integrable_atom_fourthFifthCooling
    {n : ℕ} (hn : 2 ≤ n) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ =>
      thetaCuspLikelihoodFourthFifthCoolingScore A t * Real.exp (-(B * t)))
      (thetaCuspAtomLikelihoodSpectralMeasure n) := by
  have h := integrable_thetaCuspLikelihoodFourthFifthCoolingScore_mul_exp A hB
  have hnEq : n - 2 + 2 = n := by omega
  rw [← hnEq]
  exact h.mono_measure (Measure.le_sum _ (n - 2))

theorem neg_atomEighthMonomialMass_le_atomFourthFifthCoolingMass
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : 6 ≤ A) (hB : 0 < B) :
    -thetaCuspLikelihoodAtomEighthMonomialMass n A B ≤
      thetaCuspLikelihoodAtomFourthFifthCoolingMass n A B := by
  have hd : 8 ≤ thetaCuspLikelihoodGap n := by
    unfold thetaCuspLikelihoodGap
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hae := ae_gap_le_thetaCuspAtomLikelihoodSpectralMeasure (show 2 ≤ n by omega)
  have hcool := integrable_atom_fourthFifthCooling (show 2 ≤ n by omega) A hB
  have heighth : Integrable (fun t : ℝ =>
      (A * t) ^ (8 : ℕ) * Real.exp (-(B * t)))
      (thetaCuspAtomLikelihoodSpectralMeasure n) := by
    have hfull := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 8 hB).const_mul (A ^ (8 : ℕ))
    have hnEq : n - 2 + 2 = n := by omega
    rw [← hnEq]
    convert hfull.mono_measure (Measure.le_sum _ (n - 2)) using 1
    funext t
    ring
  rw [thetaCuspLikelihoodAtomEighthMonomialMass,
    thetaCuspLikelihoodAtomFourthFifthCoolingMass, ← integral_neg]
  apply integral_mono_ae heighth.neg hcool
  filter_upwards [hae] with t ht
  have hscore := neg_pow_eight_le_thetaCuspLikelihoodFourthFifthCoolingScore hA (hd.trans ht)
  simp only [Pi.neg_apply]
  calc
    -((A * t) ^ (8 : ℕ) * Real.exp (-(B * t))) =
        (-(A * t) ^ (8 : ℕ)) * Real.exp (-(B * t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscore (Real.exp_pos (-(B * t))).le

theorem thetaCuspLikelihoodAtomFourthFifthCoolingMass_two_eq_dominantReserve
    {A : ℝ} (hA : 6 ≤ A) :
    thetaCuspLikelihoodAtomFourthFifthCoolingMass 2 A (A - 3 / 2) =
      thetaCuspLikelihoodDominantOrdinaryCoolingReserve A := by
  have hB : 0 < A - 3 / 2 := by linarith
  have hq (q : ℕ) : Integrable (fun t : ℝ =>
      t ^ q * Real.exp (-((A - 3 / 2) * t)))
      (thetaCuspAtomLikelihoodSpectralMeasure 2) := by
    simpa only [Nat.zero_add, neg_mul] using
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure q hB).mono_measure
        (Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0)
  let f5 : ℝ → ℝ := fun t => (-A ^ (5 : ℕ)) *
    (t ^ (5 : ℕ) * Real.exp (-((A - 3 / 2) * t)))
  let f4 : ℝ → ℝ := fun t => (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) *
    (t ^ (4 : ℕ) * Real.exp (-((A - 3 / 2) * t)))
  let f3 : ℝ → ℝ := fun t => (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) *
    (t ^ (3 : ℕ) * Real.exp (-((A - 3 / 2) * t)))
  let f2 : ℝ → ℝ := fun t => (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) *
    (t ^ (2 : ℕ) * Real.exp (-((A - 3 / 2) * t)))
  let f1 : ℝ → ℝ := fun t => (3 * A ^ (2 : ℕ) + A) *
    (t ^ (1 : ℕ) * Real.exp (-((A - 3 / 2) * t)))
  have h5 : Integrable f5 (thetaCuspAtomLikelihoodSpectralMeasure 2) :=
    (hq 5).const_mul (-A ^ (5 : ℕ))
  have h4 : Integrable f4 (thetaCuspAtomLikelihoodSpectralMeasure 2) :=
    (hq 4).const_mul (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ))
  have h3 : Integrable f3 (thetaCuspAtomLikelihoodSpectralMeasure 2) :=
    (hq 3).const_mul (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ))
  have h2 : Integrable f2 (thetaCuspAtomLikelihoodSpectralMeasure 2) :=
    (hq 2).const_mul (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ))
  have h1 : Integrable f1 (thetaCuspAtomLikelihoodSpectralMeasure 2) :=
    (hq 1).const_mul (3 * A ^ (2 : ℕ) + A)
  unfold thetaCuspLikelihoodAtomFourthFifthCoolingMass
    thetaCuspLikelihoodDominantOrdinaryCoolingReserve
  dsimp only
  rw [show (fun t : ℝ => thetaCuspLikelihoodFourthFifthCoolingScore A t *
      Real.exp (-((A - 3 / 2) * t))) = (((f5 + f4) - f3) + f2) - f1 by
    funext t
    simp only [Pi.add_apply, Pi.sub_apply]
    dsimp only [f5, f4, f3, f2, f1]
    unfold thetaCuspLikelihoodFourthFifthCoolingScore
    ring]
  rw [integral_sub' (((h5.add h4).sub h3).add h2) h1,
    integral_add' ((h5.add h4).sub h3) h2,
    integral_sub' (h5.add h4) h3, integral_add' h5 h4]
  simp only [f5, f4, f3, f2, f1, integral_const_mul, pow_one]

theorem thetaCuspLikelihoodStableEighthMonomialMassTail_lt_coolingFloor
    {A B : ℝ} (hA : 6 ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodStableEighthMonomialMassTail A B <
      3024 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) := by
  have hApi : Real.pi ≤ A := by nlinarith [Real.pi_lt_four]
  have hB : 0 < B := by rw [hBA]; linarith
  have hsAll := summable_thetaCuspLikelihoodAtomEighthMonomialMass A hB
  have hs : Summable (fun k : ℕ =>
      thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 1).2 hsAll
  have hshift := summable_thetaCuspLikelihoodStableShiftedEighthTail hApi
  have hmajor := hshift.mul_left (4 * A ^ (8 : ℕ) * Real.exp (-(3 * A)))
  have hpoint : ∀ k : ℕ,
      thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B ≤
        4 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
          (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
            Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) := by
    intro k
    have hm := thetaCuspLikelihoodStableAtomEighthMonomialMass_le
      (n := k + 3) (by omega) hApi hBA
    have hexp : Real.exp (-(A * thetaCuspLikelihoodGap (k + 3))) =
        Real.exp (-(3 * A)) *
          Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hm
    nlinarith
  have hsum : thetaCuspLikelihoodStableEighthMonomialMassTail A B ≤
      (4 * A ^ (8 : ℕ) * Real.exp (-(3 * A))) *
        thetaCuspLikelihoodStableShiftedEighthTail A := by
    unfold thetaCuspLikelihoodStableEighthMonomialMassTail
    calc
      _ ≤ ∑' k : ℕ, 4 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
          (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
            Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) :=
        Summable.tsum_le_tsum hpoint hs hmajor
      _ = _ := by
        unfold thetaCuspLikelihoodStableShiftedEighthTail
        rw [tsum_mul_left]
  have hrefined := pow_four_mul_thetaCuspLikelihoodStableShiftedEighthTail_lt hA
  have hpos : 0 < 4 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hrefined hpos
  nlinarith [show
    (4 * A ^ (8 : ℕ) * Real.exp (-(3 * A))) *
        thetaCuspLikelihoodStableShiftedEighthTail A =
      (4 * A ^ (4 : ℕ) * Real.exp (-(3 * A))) *
        (A ^ (4 : ℕ) * thetaCuspLikelihoodStableShiftedEighthTail A) by ring]

theorem summable_thetaCuspLikelihoodAtomFourthFifthCoolingMass
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Summable (fun k : ℕ =>
      thetaCuspLikelihoodAtomFourthFifthCoolingMass (k + 2) A B) := by
  let f : ℝ → ℝ := fun t =>
    thetaCuspLikelihoodFourthFifthCoolingScore A t * Real.exp (-(B * t))
  have hInt := integrable_thetaCuspLikelihoodFourthFifthCoolingScore_mul_exp A hB
  rw [thetaCuspHigherLikelihoodSpectralMeasure] at hInt
  have hnorm := hInt.summable_integral
  apply Summable.of_norm_bounded hnorm
  intro k
  exact norm_integral_le_integral_norm _

theorem integral_thetaCuspLikelihoodFourthFifthCoolingScore_eq_tsum
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaCuspLikelihoodFourthFifthCoolingScore A t *
      Real.exp (-(B * t)) ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      ∑' k : ℕ, thetaCuspLikelihoodAtomFourthFifthCoolingMass (k + 2) A B := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure,
    integral_sum_measure
      (integrable_thetaCuspLikelihoodFourthFifthCoolingScore_mul_exp A hB)]
  rfl

theorem oneThousandEight_mul_pow_four_mul_exp_lt_integral_coolingScore
    {A B : ℝ} (hA : 6 ≤ A) (hBA : B = A - 3 / 2) :
    1008 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) <
      ∫ t : ℝ, thetaCuspLikelihoodFourthFifthCoolingScore A t *
      Real.exp (-(B * t)) ∂thetaCuspHigherLikelihoodSpectralMeasure := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hs := summable_thetaCuspLikelihoodAtomFourthFifthCoolingMass A hB
  have hsStable : Summable (fun k : ℕ =>
      thetaCuspLikelihoodAtomFourthFifthCoolingMass (k + 3) A B) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 1).2 hs
  have hsEightAll := summable_thetaCuspLikelihoodAtomEighthMonomialMass A hB
  have hsEight : Summable (fun k : ℕ =>
      thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 1).2 hsEightAll
  have hpoint : ∀ k : ℕ,
      -thetaCuspLikelihoodAtomEighthMonomialMass (k + 3) A B ≤
        thetaCuspLikelihoodAtomFourthFifthCoolingMass (k + 3) A B := by
    intro k
    exact neg_atomEighthMonomialMass_le_atomFourthFifthCoolingMass
      (n := k + 3) (by omega) hA hB
  have hstable := Summable.tsum_le_tsum hpoint hsEight.neg hsStable
  rw [tsum_neg] at hstable
  have heighth := thetaCuspLikelihoodStableEighthMonomialMassTail_lt_coolingFloor hA hBA
  have hcore := fourThousandThirtyTwo_mul_pow_four_lt_dominantCoolingCore hA
  have hcoreScaled := mul_lt_mul_of_pos_left hcore (Real.exp_pos (-3 * A))
  have hdom : 4032 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) <
      thetaCuspLikelihoodAtomFourthFifthCoolingMass 2 A B := by
    rw [hBA,
      thetaCuspLikelihoodAtomFourthFifthCoolingMass_two_eq_dominantReserve hA,
      thetaCuspLikelihoodDominantOrdinaryCoolingReserve_eq hA]
    calc
      4032 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) =
          Real.exp (-3 * A) * (4032 * A ^ (4 : ℕ)) := by ring
      _ < Real.exp (-3 * A) *
          (12 * A * thetaCuspLikelihoodFourthFifthDominantReservePolynomial A /
            (2 * A - 3) ^ (6 : ℕ)) := hcoreScaled
  rw [integral_thetaCuspLikelihoodFourthFifthCoolingScore_eq_tsum A hB,
    hs.tsum_eq_zero_add]
  change 1008 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) <
    thetaCuspLikelihoodAtomFourthFifthCoolingMass 2 A B +
    ∑' k : ℕ, thetaCuspLikelihoodAtomFourthFifthCoolingMass (k + 3) A B
  change -thetaCuspLikelihoodStableEighthMonomialMassTail A B ≤
    ∑' k : ℕ, thetaCuspLikelihoodAtomFourthFifthCoolingMass (k + 3) A B at hstable
  nlinarith

theorem integral_thetaCuspLikelihoodFourthFifthCoolingScore_pos
    {A B : ℝ} (hA : 6 ≤ A) (hBA : B = A - 3 / 2) :
    0 < ∫ t : ℝ, thetaCuspLikelihoodFourthFifthCoolingScore A t *
      Real.exp (-(B * t)) ∂thetaCuspHigherLikelihoodSpectralMeasure := by
  have h := oneThousandEight_mul_pow_four_mul_exp_lt_integral_coolingScore hA hBA
  have hfloor : 0 < 1008 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) := by
    have hA0 : 0 < A := by linarith
    positivity
  linarith

private theorem integral_thetaCuspLikelihoodFourthFifthCoolingScore_eq_moments
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, thetaCuspLikelihoodFourthFifthCoolingScore A t * Real.exp (-(B * t))
      ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      -A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 +
        (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
        (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
        (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
        (3 * A ^ (2 : ℕ) + A) * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  let f5 : ℝ → ℝ := fun t => (-A ^ (5 : ℕ)) * (t ^ (5 : ℕ) * Real.exp (-(B * t)))
  let f4 : ℝ → ℝ := fun t => (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) *
    (t ^ (4 : ℕ) * Real.exp (-(B * t)))
  let f3 : ℝ → ℝ := fun t => (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) *
    (t ^ (3 : ℕ) * Real.exp (-(B * t)))
  let f2 : ℝ → ℝ := fun t => (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) *
    (t ^ (2 : ℕ) * Real.exp (-(B * t)))
  let f1 : ℝ → ℝ := fun t => (3 * A ^ (2 : ℕ) + A) *
    (t ^ (1 : ℕ) * Real.exp (-(B * t)))
  have h5 : Integrable f5 thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [f5, neg_mul] using
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 5 hB).const_mul
        (-A ^ (5 : ℕ))
  have h4 : Integrable f4 thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [f4, neg_mul] using
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul
        (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ))
  have h3 : Integrable f3 thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [f3, neg_mul] using
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
        (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ))
  have h2 : Integrable f2 thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [f2, neg_mul] using
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
        (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ))
  have h1 : Integrable f1 thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [f1, neg_mul] using
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul
        (3 * A ^ (2 : ℕ) + A)
  rw [show (fun t : ℝ => thetaCuspLikelihoodFourthFifthCoolingScore A t *
      Real.exp (-(B * t))) = (((f5 + f4) - f3) + f2) - f1 by
    funext t
    simp only [Pi.add_apply, Pi.sub_apply]
    dsimp only [f5, f4, f3, f2, f1]
    unfold thetaCuspLikelihoodFourthFifthCoolingScore
    ring]
  rw [integral_sub' (((h5.add h4).sub h3).add h2) h1,
    integral_add' ((h5.add h4).sub h3) h2,
    integral_sub' (h5.add h4) h3, integral_add' h5 h4]
  simp only [f5, f4, f3, f2, f1, integral_const_mul, pow_one]
  simp only [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  simp only [neg_mul, pow_one]

private theorem fourthFifthCooling_normalization
    (A P M1 M2 M3 M4 M5 : ℝ) :
    (32 / P) *
        (-A ^ (5 : ℕ) * M5 +
          (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) * M4 -
          (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) * M3 +
          (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) * M2 -
          (3 * A ^ (2 : ℕ) + A) * M1) =
      -32 * (A ^ (5 : ℕ) * (M5 / P) -
        10 * A ^ (4 : ℕ) * (M4 / P) +
        25 * A ^ (3 : ℕ) * (M3 / P) -
        15 * A ^ (2 : ℕ) * (M2 / P) +
        A * (M1 / P)) +
      6 * A * (16 * (A ^ (4 : ℕ) * (M4 / P) -
        6 * A ^ (3 : ℕ) * (M3 / P) +
        7 * A ^ (2 : ℕ) * (M2 / P) -
        A * (M1 / P))) := by
  ring

/-- Complete one-particle ordinary sector satisfies fourth/fifth cooling above scale six. -/
theorem thetaCuspLikelihoodEighthBellJetFive_lt_six_mul_scale_mul_ordinaryJetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLikelihoodEighthBellJetFive x <
      6 * thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspLikelihoodSourceOrdinaryJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hint := integral_thetaCuspLikelihoodFourthFifthCoolingScore_pos hA hBA
  have heq := integral_thetaCuspLikelihoodFourthFifthCoolingScore_eq_moments A hB
  rw [heq] at hint
  unfold thetaCuspLikelihoodEighthBellJetFive
    thetaCuspLikelihoodSourceOrdinaryJetFour
  dsimp only [A, B]
  unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
  have hscaled := mul_pos (div_pos (by norm_num : (0 : ℝ) < 32) hP) hint
  change
    32 * (A ^ (5 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) -
        10 * A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) +
        25 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) -
        15 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) +
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P)) <
      6 * A * (16 * (A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) -
        6 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) +
        7 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) -
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P)))
  have hid :
    (32 / P) *
        (-A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 +
          (3 * A ^ (5 : ℕ) + 10 * A ^ (4 : ℕ)) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          (18 * A ^ (4 : ℕ) + 25 * A ^ (3 : ℕ)) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          (21 * A ^ (3 : ℕ) + 15 * A ^ (2 : ℕ)) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
          (3 * A ^ (2 : ℕ) + A) * thetaCuspHigherLikelihoodSpectralMoment B 1) =
      -32 * (A ^ (5 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 5 / P) -
        10 * A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) +
        25 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) -
        15 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) +
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P)) +
      6 * A * (16 * (A ^ (4 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 4 / P) -
        6 * A ^ (3 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 3 / P) +
        7 * A ^ (2 : ℕ) * (thetaCuspHigherLikelihoodSpectralMoment B 2 / P) -
        A * (thetaCuspHigherLikelihoodSpectralMoment B 1 / P))) :=
    fourthFifthCooling_normalization A P
      (thetaCuspHigherLikelihoodSpectralMoment B 1)
      (thetaCuspHigherLikelihoodSpectralMoment B 2)
      (thetaCuspHigherLikelihoodSpectralMoment B 3)
      (thetaCuspHigherLikelihoodSpectralMoment B 4)
      (thetaCuspHigherLikelihoodSpectralMoment B 5)
  rw [hid] at hscaled
  nlinarith

/-- Quantitative ordinary fourth/fifth reserve left after complete stable-tower absorption. -/
theorem sixteenThousandOneHundredTwentyEight_mul_scale_pow_four_mul_exp_lt_ordinaryReserve
    {x : ℝ} (hx : 0 ≤ x)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    16128 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      6 * thetaCuspSingleAtomReflectionScale 1 x *
          thetaCuspLikelihoodSourceOrdinaryJetFour x -
        thetaCuspLikelihoodEighthBellJetFive x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hrSmall : 399 * thetaCuspHigherLikelihoodSpectralResponse B < 1 := by
    simpa only [B] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  have hPtwo : P < 2 := by
    dsimp only [P]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
      thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    linarith
  have hcoeff : 16 < 32 / P := by
    apply (lt_div_iff₀ hP).2
    nlinarith
  have hint :=
    oneThousandEight_mul_pow_four_mul_exp_lt_integral_coolingScore hA hBA
  have heq := integral_thetaCuspLikelihoodFourthFifthCoolingScore_eq_moments A hB
  rw [heq] at hint
  dsimp only [A] at hint
  have hscaled := mul_lt_mul_of_pos_left hint
    (show (0 : ℝ) < 32 / P by positivity)
  have hfloorPos : 0 < 1008 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) := by
    have hA0 : 0 < A := by dsimp only [A] at hA ⊢; linarith
    positivity
  have hleft := mul_lt_mul_of_pos_right hcoeff hfloorPos
  rw [fourthFifthCooling_normalization A P
      (thetaCuspHigherLikelihoodSpectralMoment B 1)
      (thetaCuspHigherLikelihoodSpectralMoment B 2)
      (thetaCuspHigherLikelihoodSpectralMoment B 3)
      (thetaCuspHigherLikelihoodSpectralMoment B 4)
      (thetaCuspHigherLikelihoodSpectralMoment B 5)] at hscaled
  unfold thetaCuspLikelihoodSourceOrdinaryJetFour
    thetaCuspLikelihoodEighthBellJetFive
  dsimp only [A, B]
  unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
  dsimp only [P] at hscaled hleft
  nlinarith

/-- Scale-six tail probability has its sharp support-edge exponential rate. -/
theorem thetaCuspLikelihoodTailProbability_lt_thirtyFive_mul_exp_neg_three_scale
    {x : ℝ} (hx : 0 ≤ x)
    (hA6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLikelihoodTailProbability (thetaCuspLikelihoodCoordinate x) <
      35 * Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let B₀ := thetaCuspLikelihoodCoordinate 0
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let r₀ := thetaCuspHigherLikelihoodSpectralResponse B₀
  let p := thetaCuspLikelihoodTailProbability B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hB₀ : 0 < B₀ := by
    simpa only [B₀] using thetaCuspLikelihoodCoordinate_pos (x := 0) (by norm_num)
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hB₀eq : B₀ = Real.pi - 3 / 2 := by
    dsimp only [B₀, thetaCuspLikelihoodCoordinate]
    norm_num
  have hB₀B : B₀ ≤ B := by
    rw [hBA, hB₀eq]
    dsimp only [A] at hA6 ⊢
    nlinarith [Real.pi_lt_four]
  have hcompare :=
    thetaCuspHigherLikelihoodSpectralMoment_zero_le_exp_support_comparison
      hB₀ hB hB₀B
  rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB,
    thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀] at hcompare
  have hr₀0 : 0 ≤ r₀ := by
    dsimp only [r₀]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB₀]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hcal : 399 * r₀ < 1 := by
    simpa only [r₀, B₀] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one
        (x := 0) (by norm_num)
  have hr₀small : r₀ < (1 / 399 : ℝ) := by nlinarith
  have hexpPi : Real.exp (3 * Real.pi) < 13824 := by
    have hneg := one_div_twentyFour_lt_exp_neg_pi
    have hprod : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hpi : Real.exp Real.pi < 24 := by
      nlinarith [Real.exp_pos (-Real.pi), Real.exp_pos Real.pi]
    have hpow := pow_lt_pow_left₀ hpi (Real.exp_pos Real.pi).le (by norm_num : (3 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    simpa only [mul_comm] using hpow
  have hexpSplit : Real.exp (-3 * (B - B₀)) =
      Real.exp (-(3 * A)) * Real.exp (3 * Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA, hB₀eq]
    ring
  have htransport : r < 35 * Real.exp (-(3 * A)) := by
    have hfirst : r ≤ Real.exp (-3 * (B - B₀)) * r₀ := by
      simpa only [r, r₀] using hcompare
    have hsecond := mul_lt_mul_of_pos_left hr₀small
      (Real.exp_pos (-3 * (B - B₀)))
    rw [hexpSplit] at hsecond
    have hthird := mul_lt_mul_of_pos_left hexpPi
      (Real.exp_pos (-(3 * A)))
    nlinarith [Real.exp_pos (-(3 * A))]
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hpEq : p = r / (1 + r) := by
    dsimp only [p, r]
    unfold thetaCuspLikelihoodTailProbability thetaCuspLikelihoodNormalizedMoment
      thetaCuspLikelihoodPartition
    rw [thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hden : 0 < 1 + r := by linarith
  have hpr : p ≤ r := by
    rw [hpEq]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg r]
  simpa only [p, B, A] using hpr.trans_lt htransport

/-- Above scale six, fourth ordinary mass costs fewer than `3000/A²` units. -/
theorem scale_sq_mul_thetaCuspLikelihoodSourceOrdinaryJetFour_lt_threeThousand
    {x : ℝ} (hx : 0 ≤ x)
    (hA6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
        thetaCuspLikelihoodSourceOrdinaryJetFour x < 3000 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e6 := thetaCuspLikelihoodNormalizedMoment B 6
  let b4 := thetaCuspLikelihoodSourceOrdinaryJetFour x
  let b6 := thetaCuspLikelihoodSourceOrdinaryJetSix x
  have hA0 : 0 < A := by dsimp only [A] at hA6 ⊢; linarith
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    dsimp only [P]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    exact le_add_of_nonneg_right (thetaCuspHigherLikelihoodSpectralMoment_nonneg 0)
  have hscore := integral_thetaLikelihoodSixthScore_lt_fiftyFive_of_six_le_scale hx hA6
  have hb6pos : 0 < b6 := by
    simpa only [b6] using thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
  have hb6Upper : b6 < 3520 := by
    dsimp only [b6] at hb6pos ⊢
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx] at hb6pos ⊢
    have hcoeff : 0 < 64 / P := div_pos (by norm_num) hP
    have hcoeffUpper : 64 / P ≤ 64 := by
      apply (div_le_iff₀ hP).2
      nlinarith
    have hmass0 : 0 < (∫ t : ℝ,
        thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
      change 0 < (64 / P) * (∫ t : ℝ,
        thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) at hb6pos
      rcases (mul_pos_iff.mp hb6pos) with hpos | hneg
      · exact hpos.2
      · exfalso
        linarith
    have hscaled := mul_lt_mul_of_pos_left hscore hcoeff
    have hcoeffScaled := mul_le_mul_of_nonneg_right hcoeffUpper hmass0.le
    dsimp only [A, B, P] at hscaled hcoeffScaled ⊢
    nlinarith
  have he4 : 0 < e4 := by
    have he2 := thetaCuspLikelihoodNormalizedMoment_two_pos hB
    have he23 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
    have he34 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
    dsimp only [e4]
    nlinarith
  have he46 : 9 * e4 ≤ e6 := by
    have h45 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
    have h56 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
    simpa only [e4, e6] using (show
      9 * thetaCuspLikelihoodNormalizedMoment B 4 ≤
        thetaCuspLikelihoodNormalizedMoment B 6 by nlinarith)
  have hb4Upper : b4 ≤ 16 * A ^ (4 : ℕ) * e4 := by
    have he2pos := thetaCuspLikelihoodNormalizedMoment_two_pos hB
    have he23 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
    have hseven :
        7 * thetaCuspLikelihoodNormalizedMoment B 2 ≤
          6 * A * thetaCuspLikelihoodNormalizedMoment B 3 := by
      have hA3 : 3 ≤ A := by linarith
      nlinarith
    have hsevenScaled := mul_le_mul_of_nonneg_left hseven (sq_nonneg A)
    dsimp only [b4, A, B, e4, thetaCuspLikelihoodSourceOrdinaryJetFour]
    have hm := thetaCuspLikelihoodMean_pos hB
    nlinarith
  have hb6Lower : (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6 ≤ b6 := by
    have h := one_thirtieth_mul_likelihoodSourceLinearSix_le hx
    dsimp only [A, B, e6, b6, thetaCuspLikelihoodSourceOrdinaryJetSix] at h ⊢
    nlinarith
  have h4scaled := mul_le_mul_of_nonneg_left hb4Upper (sq_nonneg A)
  have h46scaled := mul_le_mul_of_nonneg_left he46
    (by positivity : 0 ≤ (32 / 3 : ℝ) * A ^ (6 : ℕ))
  have h6scaled := mul_le_mul_of_nonneg_left hb6Lower (by norm_num : (0 : ℝ) ≤ 5)
  dsimp only [A, b4, b6] at hb6Upper ⊢
  nlinarith [show
    A ^ (2 : ℕ) * (16 * A ^ (4 : ℕ) * e4) = 16 * A ^ (6 : ℕ) * e4 by ring,
    show (32 / 3 : ℝ) * A ^ (6 : ℕ) * (9 * e4) = 96 * A ^ (6 : ℕ) * e4 by ring,
    show (32 / 3 : ℝ) * A ^ (6 : ℕ) * e6 =
      5 * ((64 / 30 : ℝ) * A ^ (6 : ℕ) * e6) by ring]

/-- All fourth-jet Bell loss is quadratically colder than the ordinary cooling reserve. -/
theorem six_mul_scale_mul_fourthBellLoss_lt_twoMillion_mul_exp_neg_three_scale
    {x : ℝ} (hx : 0 ≤ x)
    (hA6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    6 * thetaCuspSingleAtomReflectionScale 1 x *
        (thetaCuspLikelihoodSourceOrdinaryJetFour x -
          thetaCuspLikelihoodSourceLogPartitionJetFour x) <
      2000000 * Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ (2 : ℕ) * e2 - A * e1)
  let b3 := 8 * (A ^ (3 : ℕ) * e3 - 3 * A ^ (2 : ℕ) * e2 + A * e1)
  let b4 := thetaCuspLikelihoodSourceOrdinaryJetFour x
  let loss := b4 - thetaCuspLikelihoodSourceLogPartitionJetFour x
  have hA0 : 0 < A := by dsimp only [A] at hA6 ⊢; linarith
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have he1 : 0 < e1 := by simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    simpa only [e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have hpSmall : 1995 * p < 1 := by
    have hscale : (59 / 16 : ℝ) ≤ A := by linarith
    simpa only [A, B, p] using
      oneThousandNineHundredNinetyFive_mul_thetaCuspLikelihoodTailProbability_lt_one_of_59Over16_le
        hx hscale
  have hp : 0 < p := by
    have h22 := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    have h22' : e2 ^ (2 : ℕ) ≤ p * e4 := by
      simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h22
    nlinarith [sq_pos_of_pos he2]
  have h11 : e1 ^ (2 : ℕ) ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h13 : e1 * e3 ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 3
    simpa only [B, p, e1, e3, e4, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 3 = 4 by norm_num] using h
  have h22 : e2 ^ (2 : ℕ) ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hb1 : 0 < b1 := by dsimp only [b1]; positivity
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right (show (3 : ℝ) < A by linarith) he2
    nlinarith
  have hb2 : 0 < b2 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b2]
    nlinarith
  have hb2Upper : b2 ≤ 4 * A ^ (2 : ℕ) * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right (show (3 : ℝ) < A by linarith) he3
    nlinarith
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have hb3Upper : b3 ≤ 8 * A ^ (3 : ℕ) * e3 := by
    dsimp only [b3]
    have hcross : A * e1 ≤ 3 * A ^ (2 : ℕ) * e2 := by
      have hleft : A * e1 ≤ A * (e2 / 3) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hA0.le
      have hright : A * (e2 / 3) ≤ 3 * A ^ (2 : ℕ) * e2 := by
        nlinarith [mul_pos hA0 he2]
      exact hleft.trans hright
    nlinarith
  have hb4Lower : (32 / 5 : ℝ) * A ^ (4 : ℕ) * e4 ≤ b4 := by
    simpa only [A, B, e4, b4] using two_fifths_le_thetaCuspLikelihoodSourceOrdinaryJetFour hx
  have hb4 : 0 < b4 := lt_of_lt_of_le (by positivity) hb4Lower
  have hb1b3Core : b1 * b3 ≤ 16 * A ^ (4 : ℕ) * (e1 * e3) := by
    calc
      b1 * b3 ≤ (2 * A * e1) * (8 * A ^ (3 : ℕ) * e3) := by
        dsimp only [b1]
        gcongr
      _ = 16 * A ^ (4 : ℕ) * (e1 * e3) := by ring
  have hb1b3Moment : 16 * A ^ (4 : ℕ) * (e1 * e3) ≤ 16 * A ^ (4 : ℕ) * (p * e4) := by
    gcongr
  have hb1b3 : 4 * b1 * b3 ≤ 10 * p * b4 := by
    have hcore := hb1b3Core.trans hb1b3Moment
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower
      (by positivity : 0 ≤ 10 * p)
    nlinarith
  have hb2sqCore : b2 ^ (2 : ℕ) ≤ 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by
    have hpow := pow_le_pow_left₀ hb2.le hb2Upper 2
    calc
      b2 ^ (2 : ℕ) ≤ (4 * A ^ (2 : ℕ) * e2) ^ (2 : ℕ) := hpow
      _ = 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by ring
  have hb2sqMoment : 16 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) ≤ 16 * A ^ (4 : ℕ) * (p * e4) := by
    gcongr
  have hb2sq : 3 * b2 ^ (2 : ℕ) ≤ (15 / 2 : ℝ) * p * b4 := by
    have hcore := hb2sqCore.trans hb2sqMoment
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower
      (by positivity : 0 ≤ (15 / 2 : ℝ) * p)
    nlinarith
  have he1four : e1 ^ (4 : ℕ) ≤ p ^ (3 : ℕ) * e4 := by
    have h11sq := pow_le_pow_left₀ (sq_nonneg e1) h11 2
    have hstep : (p * e2) ^ (2 : ℕ) ≤ p ^ (2 : ℕ) * (p * e4) := by
      rw [mul_pow]
      gcongr
    calc
      e1 ^ (4 : ℕ) = (e1 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ (p * e2) ^ (2 : ℕ) := h11sq
      _ ≤ p ^ (2 : ℕ) * (p * e4) := hstep
      _ = p ^ (3 : ℕ) * e4 := by ring
  have hb1four : 6 * b1 ^ (4 : ℕ) ≤ 15 * p ^ (3 : ℕ) * b4 := by
    have hcore : 6 * b1 ^ (4 : ℕ) ≤ 96 * A ^ (4 : ℕ) * (p ^ (3 : ℕ) * e4) := by
      dsimp only [b1]
      have hscaled := mul_le_mul_of_nonneg_left he1four
        (by positivity : 0 ≤ 96 * A ^ (4 : ℕ))
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hb4Lower
      (by positivity : 0 ≤ 15 * p ^ (3 : ℕ))
    nlinarith
  have hcoeff : (35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ) < 18 * p := by
    have hpUpper : p < (1 / 1995 : ℝ) := by linarith
    have hpSq : p ^ (2 : ℕ) < (1 / 1995 : ℝ) ^ (2 : ℕ) :=
      pow_lt_pow_left₀ hpUpper hp.le (by norm_num)
    have hpSqScaled : 15 * p ^ (2 : ℕ) < (1 / 2 : ℝ) :=
      (mul_lt_mul_of_pos_left hpSq (by norm_num)).trans (by norm_num)
    have hbracket : 0 < (1 / 2 : ℝ) - 15 * p ^ (2 : ℕ) := by
      linarith only [hpSqScaled]
    apply sub_pos.mp
    rw [show 18 * p - ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ)) =
      p * ((1 / 2 : ℝ) - 15 * p ^ (2 : ℕ)) by ring]
    exact mul_pos hp hbracket
  have hdecomp : loss =
      4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) - 12 * b1 ^ (2 : ℕ) * b2 + 6 * b1 ^ (4 : ℕ) := by
    dsimp only [loss, b1, b2, b3, b4, A, B, e1, e2, e3, e4]
    unfold thetaCuspLikelihoodSourceOrdinaryJetFour
      thetaCuspLikelihoodSourceLogPartitionJetFour thetaCuspLikelihoodFourthCumulant
      thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
    ring
  have hloss : loss < 18 * p * b4 := by
    rw [hdecomp]
    have hnegative : 0 < 12 * b1 ^ (2 : ℕ) * b2 := by positivity
    have hsum := add_le_add (add_le_add hb1b3 hb2sq) hb1four
    have hcoeffScaled := mul_lt_mul_of_pos_right hcoeff hb4
    calc
      4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) - 12 * b1 ^ (2 : ℕ) * b2 + 6 * b1 ^ (4 : ℕ) =
          (4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ)) - 12 * b1 ^ (2 : ℕ) * b2 := by ring
      _ < 4 * b1 * b3 + 3 * b2 ^ (2 : ℕ) + 6 * b1 ^ (4 : ℕ) := sub_lt_self _ hnegative
      _ ≤ 10 * p * b4 + (15 / 2 : ℝ) * p * b4 + 15 * p ^ (3 : ℕ) * b4 := by
        simpa only [add_assoc] using hsum
      _ = ((35 / 2 : ℝ) * p + 15 * p ^ (3 : ℕ)) * b4 := by ring
      _ < 18 * p * b4 := hcoeffScaled
  have hpExp : p < 35 * Real.exp (-(3 * A)) := by
    simpa only [A, B, p] using
      thetaCuspLikelihoodTailProbability_lt_thirtyFive_mul_exp_neg_three_scale hx hA6
  have hb4Scaled : A ^ (2 : ℕ) * b4 < 3000 := by
    simpa only [A, b4] using
      scale_sq_mul_thetaCuspLikelihoodSourceOrdinaryJetFour_lt_threeThousand hx hA6
  have hExp : 0 < Real.exp (-(3 * A)) := Real.exp_pos _
  by_cases hloss0 : 0 ≤ loss
  · have hlossScaled := mul_lt_mul_of_pos_left hloss (sq_pos_of_pos hA0)
    have hproduct : A ^ (2 : ℕ) * (18 * p * b4) <
        1890000 * Real.exp (-(3 * A)) := by
      calc
        A ^ (2 : ℕ) * (18 * p * b4) = 18 * p * (A ^ (2 : ℕ) * b4) := by ring
        _ < 18 * p * 3000 := mul_lt_mul_of_pos_left hb4Scaled (by positivity)
        _ < 18 * (35 * Real.exp (-(3 * A))) * 3000 := by gcongr
        _ = 1890000 * Real.exp (-(3 * A)) := by ring
    have hscale : 6 * A ≤ A ^ (2 : ℕ) := by
      calc
        6 * A ≤ A * A := mul_le_mul_of_nonneg_right hA6 hA0.le
        _ = A ^ (2 : ℕ) := by ring
    have hscaleLoss := mul_le_mul_of_nonneg_right hscale hloss0
    have hlossFinal := hlossScaled.trans hproduct
    have hconstant : 1890000 * Real.exp (-(3 * A)) <
        2000000 * Real.exp (-(3 * A)) :=
      mul_lt_mul_of_pos_right (by norm_num) hExp
    change 6 * A * loss < 2000000 * Real.exp (-(3 * A))
    exact hscaleLoss.trans_lt (hlossFinal.trans hconstant)
  · have hlossNeg : loss < 0 := lt_of_not_ge hloss0
    have hleftRaw := mul_lt_mul_of_pos_left hlossNeg
      (show 0 < 6 * A by positivity)
    have hleft : 6 * A * loss < 0 := by simpa only [mul_zero] using hleftRaw
    have hright : 0 < 2000000 * Real.exp (-(3 * A)) := by positivity
    change 6 * A * loss < 2000000 * Real.exp (-(3 * A))
    exact hleft.trans hright

/-- Logarithmic Bell correction strictly lowers magnitude of adverse fifth source jet. -/
theorem neg_thetaCuspLikelihoodSourceLogPartitionJetFive_lt_bellJetFive
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -thetaCuspLikelihoodSourceLogPartitionJetFive x <
      thetaCuspLikelihoodEighthBellJetFive x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  have hA : 6 ≤ A := by simpa only [A] using hscale
  have hA0 : 0 < A := by linarith
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 60 * m < 1 := by
    simpa only [B, m] using sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have hmOne : m < 1 := by nlinarith
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * m ≤ e2 := by
    simpa only [m, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have hcoef1 : 20 * A * m + 40 < 15 * A := by
    have hAm := mul_lt_mul_of_pos_left hmSmall hA0
    nlinarith
  have hcore1 : 0 < 5 * A * e4 - 20 * A * m * e3 - 40 * e3 := by
    have hc := mul_lt_mul_of_pos_right hcoef1 he3
    have hg := mul_le_mul_of_nonneg_left he34 (by positivity : 0 ≤ 5 * A)
    nlinarith
  have hgroup1 : 0 <
      5 * A ^ (5 : ℕ) * m * e4 - 20 * A ^ (5 : ℕ) * m ^ (2 : ℕ) * e3 -
        40 * A ^ (4 : ℕ) * m * e3 := by
    have hp := mul_pos (mul_pos (pow_pos hA0 4) hm) hcore1
    nlinarith [show
      A ^ (4 : ℕ) * m * (5 * A * e4 - 20 * A * m * e3 - 40 * e3) =
        5 * A ^ (5 : ℕ) * m * e4 - 20 * A ^ (5 : ℕ) * m ^ (2 : ℕ) * e3 -
          40 * A ^ (4 : ℕ) * m * e3 by ring]
  have hcoef2 : 3 * A * m + 3 < 3 * A := by
    have hgap : 0 < A * (1 - m) - 1 := by
      have hprod : 5 < A * (1 - m) := by
        have hmfrac : (59 / 60 : ℝ) < 1 - m := by nlinarith
        have hmul := mul_lt_mul_of_pos_left hmfrac hA0
        nlinarith
      linarith
    nlinarith
  have hcore2 : 0 < A * e3 - 3 * A * m * e2 - 3 * e2 := by
    have hc := mul_lt_mul_of_pos_right hcoef2 he2
    have hg := mul_le_mul_of_nonneg_left he23 hA0.le
    nlinarith
  have hgroup2 : 0 <
      10 * A ^ (5 : ℕ) * e2 * e3 - 30 * A ^ (5 : ℕ) * m * e2 ^ (2 : ℕ) -
        30 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) := by
    have hp := mul_pos (mul_pos (by positivity : 0 < 10 * A ^ (4 : ℕ)) he2) hcore2
    nlinarith [show
      10 * A ^ (4 : ℕ) * e2 * (A * e3 - 3 * A * m * e2 - 3 * e2) =
        10 * A ^ (5 : ℕ) * e2 * e3 - 30 * A ^ (5 : ℕ) * m * e2 ^ (2 : ℕ) -
          30 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ) by ring]
  have hcore31 : 0 < 5 * e2 - 2 * m ^ (2 : ℕ) := by
    have hmSq : m ^ (2 : ℕ) < m := by nlinarith [mul_pos hm (sub_pos.mpr hmOne)]
    nlinarith
  have hgroup31 : 0 < 60 * A ^ (5 : ℕ) * m ^ (3 : ℕ) * e2 - 24 * A ^ (5 : ℕ) * m ^ (5 : ℕ) := by
    have hp := mul_pos (by positivity : 0 < 12 * A ^ (5 : ℕ) * m ^ (3 : ℕ)) hcore31
    nlinarith [show
      12 * A ^ (5 : ℕ) * m ^ (3 : ℕ) * (5 * e2 - 2 * m ^ (2 : ℕ)) =
        60 * A ^ (5 : ℕ) * m ^ (3 : ℕ) * e2 - 24 * A ^ (5 : ℕ) * m ^ (5 : ℕ) by ring]
  have hcore32 : 0 < 2 * e2 - m ^ (2 : ℕ) := by
    have hmSq : m ^ (2 : ℕ) < m := by nlinarith [mul_pos hm (sub_pos.mpr hmOne)]
    nlinarith
  have hgroup32 : 0 < 120 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * e2 - 60 * A ^ (4 : ℕ) * m ^ (4 : ℕ) := by
    have hp := mul_pos (by positivity : 0 < 60 * A ^ (4 : ℕ) * m ^ (2 : ℕ)) hcore32
    nlinarith [show
      60 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * (2 * e2 - m ^ (2 : ℕ)) =
        120 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * e2 - 60 * A ^ (4 : ℕ) * m ^ (4 : ℕ) by ring]
  have hcore33 : 0 < 15 * A * e2 - 10 * A * m ^ (2 : ℕ) - 3 * m := by
    have hmSq : m ^ (2 : ℕ) < m := by nlinarith [mul_pos hm (sub_pos.mpr hmOne)]
    nlinarith
  have hgroup33 : 0 <
      75 * A ^ (3 : ℕ) * m * e2 - 50 * A ^ (3 : ℕ) * m ^ (3 : ℕ) - 15 * A ^ (2 : ℕ) * m ^ (2 : ℕ) := by
    have hp := mul_pos (by positivity : 0 < 5 * A ^ (2 : ℕ) * m) hcore33
    nlinarith [show
      5 * A ^ (2 : ℕ) * m * (15 * A * e2 - 10 * A * m ^ (2 : ℕ) - 3 * m) =
        75 * A ^ (3 : ℕ) * m * e2 - 50 * A ^ (3 : ℕ) * m ^ (3 : ℕ) -
          15 * A ^ (2 : ℕ) * m ^ (2 : ℕ) by ring]
  have hsum : 0 <
      (5 * A ^ (5 : ℕ) * m * e4 - 20 * A ^ (5 : ℕ) * m ^ (2 : ℕ) * e3 -
          40 * A ^ (4 : ℕ) * m * e3) +
        (10 * A ^ (5 : ℕ) * e2 * e3 - 30 * A ^ (5 : ℕ) * m * e2 ^ (2 : ℕ) -
          30 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ)) +
        (60 * A ^ (5 : ℕ) * m ^ (3 : ℕ) * e2 - 24 * A ^ (5 : ℕ) * m ^ (5 : ℕ)) +
        (120 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * e2 - 60 * A ^ (4 : ℕ) * m ^ (4 : ℕ)) +
        (75 * A ^ (3 : ℕ) * m * e2 - 50 * A ^ (3 : ℕ) * m ^ (3 : ℕ) -
          15 * A ^ (2 : ℕ) * m ^ (2 : ℕ)) :=
    add_pos (add_pos (add_pos (add_pos hgroup1 hgroup2) hgroup31) hgroup32) hgroup33
  have hid :
      thetaCuspLikelihoodEighthBellJetFive x +
          thetaCuspLikelihoodSourceLogPartitionJetFive x =
        32 * ((5 * A ^ (5 : ℕ) * m * e4 - 20 * A ^ (5 : ℕ) * m ^ (2 : ℕ) * e3 -
            40 * A ^ (4 : ℕ) * m * e3) +
          (10 * A ^ (5 : ℕ) * e2 * e3 - 30 * A ^ (5 : ℕ) * m * e2 ^ (2 : ℕ) -
            30 * A ^ (4 : ℕ) * e2 ^ (2 : ℕ)) +
          (60 * A ^ (5 : ℕ) * m ^ (3 : ℕ) * e2 - 24 * A ^ (5 : ℕ) * m ^ (5 : ℕ)) +
          (120 * A ^ (4 : ℕ) * m ^ (2 : ℕ) * e2 - 60 * A ^ (4 : ℕ) * m ^ (4 : ℕ)) +
          (75 * A ^ (3 : ℕ) * m * e2 - 50 * A ^ (3 : ℕ) * m ^ (3 : ℕ) -
            15 * A ^ (2 : ℕ) * m ^ (2 : ℕ))) := by
    unfold thetaCuspLikelihoodSourceLogPartitionJetFive
      thetaCuspLikelihoodEighthBellJetFive thetaCuspLikelihoodFifthCumulant
      thetaCuspLikelihoodFourthCumulant thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    dsimp only [A, B, m, e2, e3, e4, e5]
    unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
    ring
  have hpos : 0 < thetaCuspLikelihoodEighthBellJetFive x +
      thetaCuspLikelihoodSourceLogPartitionJetFive x := by
    rw [hid]
    positivity
  linarith

/-- Complete logarithmic fourth/fifth cooling gate on structural tail. -/
theorem neg_thetaCuspLikelihoodSourceLogPartitionJetFive_lt_six_mul_scale_mul_jetFour
    {x : ℝ} (hx : 0 ≤ x)
    (hA6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -thetaCuspLikelihoodSourceLogPartitionJetFive x <
      6 * thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let b4 := thetaCuspLikelihoodSourceOrdinaryJetFour x
  let j4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let b5 := thetaCuspLikelihoodEighthBellJetFive x
  let j5 := thetaCuspLikelihoodSourceLogPartitionJetFive x
  let loss := b4 - j4
  have hA : 6 ≤ A := by simpa only [A] using hA6
  have hExp : 0 < Real.exp (-(3 * A)) := Real.exp_pos _
  have hBell : -j5 < b5 := by
    simpa only [j5, b5] using
      neg_thetaCuspLikelihoodSourceLogPartitionJetFive_lt_bellJetFive hx hA6
  have hReserve :
      16128 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) < 6 * A * b4 - b5 := by
    simpa only [A, b4, b5] using
      sixteenThousandOneHundredTwentyEight_mul_scale_pow_four_mul_exp_lt_ordinaryReserve
        hx hA6
  have hLoss : 6 * A * loss < 2000000 * Real.exp (-(3 * A)) := by
    simpa only [A, b4, j4, loss] using
      six_mul_scale_mul_fourthBellLoss_lt_twoMillion_mul_exp_neg_three_scale hx hA6
  have hA4 : (6 : ℝ) ^ (4 : ℕ) ≤ A ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hA 4
  have hconstant : 2000000 * Real.exp (-(3 * A)) <
      16128 * A ^ (4 : ℕ) * Real.exp (-(3 * A)) := by
    apply mul_lt_mul_of_pos_right _ hExp
    nlinarith
  have hLossReserve : 6 * A * loss < 6 * A * b4 - b5 :=
    hLoss.trans (hconstant.trans hReserve)
  have hb5 : b5 < 6 * A * (b4 - loss) := by
    calc
      b5 < 6 * A * b4 - 6 * A * loss := by linarith only [hLossReserve]
      _ = 6 * A * (b4 - loss) := by ring
  have hb5j4 : b5 < 6 * A * j4 := by
    calc
      b5 < 6 * A * (b4 - loss) := hb5
      _ = 6 * A * j4 := by dsimp only [loss]; ring
  simpa only [A, j4, j5] using hBell.trans hb5j4

end

end RHTower
