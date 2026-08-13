import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussBulkLowEdgeFloor
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussRiccatiSource
import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierChristoffelSourceWall
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Adaptive arithmetic bulk pays admission effectivity with strict low-edge reserve

The remaining escape after degree-uniform source noncollapse is multiplicative admission
amplitude.  This module makes that effectivity cost intrinsic.  Logarithmic current-norm rate is a
forced Jacobi trace.  Sharp weighted Cauchy shows its square is paid by same adaptive Gaussian-
visible completed source, while twice first Christoffel edge remains as strict reserve.

At square mass source account is literal adaptive mixed rational--Gamma/von-Mangoldt `P^sharp`
aggregate minus exact newborn norm lost by current Gaussian observation.  Admission, amplitude,
and completion are formed before any reflection aggregation.
-/

open Matrix Polynomial MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp Cauchy weight for multiplicative admission-effectivity rate. -/
def xiShiftedAdmissionEffectivityCauchyWeight (n : ℕ) : ℝ :=
  4 * (n : ℝ) + (n + 1 : ℝ) ^ 2 / (3 * (n : ℝ) / 4 + 1)

theorem xiShiftedAdmissionEffectivityCauchyWeight_pos
    {n : ℕ} (hn : 0 < n) :
    0 < xiShiftedAdmissionEffectivityCauchyWeight n := by
  unfold xiShiftedAdmissionEffectivityCauchyWeight
  positivity

/-- Generic source/effectivity inequality.  Newborn Gaussian edge has been removed from adaptive
source.  Remaining bulk pays squared multiplicative norm rate and retains strict low-edge reserve. -/
theorem jacobiEffectivityRate_sq_add_lowEdge_lt_weight_mul_visibleEnergy
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n + 2 ≤ N) :
    let rate := 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      (2 * n + 1 : ℝ) * HTGeometry.monicOrthoAlpha s n
    let bulk := HTGeometry.adaptiveOrthoJacobiEnergy s n -
      (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1)
    rate ^ 2 +
        2 * xiShiftedAdmissionEffectivityCauchyWeight n *
          HTGeometry.monicOrthoBeta s 1 <
      xiShiftedAdmissionEffectivityCauchyWeight n * bulk := by
  dsimp only
  let a := HTGeometry.monicOrthoAlpha s n
  let S := ∑ j ∈ Finset.range n,
    (HTGeometry.monicOrthoAlpha s j + a / 2)
  let Q := ∑ j ∈ Finset.range n,
    (HTGeometry.monicOrthoAlpha s j + a / 2) ^ 2
  let q : ℝ := 3 * (n : ℝ) / 4 + 1
  let c : ℝ := n + 1
  let K := xiShiftedAdmissionEffectivityCauchyWeight n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range n)
    (f := fun j => HTGeometry.monicOrthoAlpha s j + a / 2)
  simp only [Finset.card_range] at hcs
  change S ^ 2 ≤ (n : ℝ) * Q at hcs
  have hK : K = 4 * (n : ℝ) + c ^ 2 / q := by
    simp only [K, xiShiftedAdmissionEffectivityCauchyWeight, c, q]
  have hid :
      (n : ℝ) * q *
          (K * (Q + q * a ^ 2) - (2 * S + c * a) ^ 2) =
        (4 * (n : ℝ) * q + c ^ 2) * ((n : ℝ) * Q - S ^ 2) +
          (c * S - 2 * (n : ℝ) * q * a) ^ 2 := by
    rw [hK]
    field_simp [ne_of_gt hq]
    ring
  have hfactor : 0 ≤ 4 * (n : ℝ) * q + c ^ 2 := by positivity
  have hrhs : 0 ≤
      (4 * (n : ℝ) * q + c ^ 2) * ((n : ℝ) * Q - S ^ 2) +
        (c * S - 2 * (n : ℝ) * q * a) ^ 2 :=
    add_nonneg (mul_nonneg hfactor (sub_nonneg.mpr hcs)) (sq_nonneg _)
  have hweighted : 0 ≤ K * (Q + q * a ^ 2) - (2 * S + c * a) ^ 2 := by
    have hprod : 0 ≤ (n : ℝ) * q *
        (K * (Q + q * a ^ 2) - (2 * S + c * a) ^ 2) := by
      rw [hid]
      exact hrhs
    exact (mul_nonneg_iff_of_pos_left (mul_pos hnR hq)).mp hprod
  have hrate :
      2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
          (2 * n + 1 : ℝ) * HTGeometry.monicOrthoAlpha s n =
        2 * S + c * a := by
    simp only [S, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, a, c]
    ring
  have halpha :
      Q + q * a ^ 2 =
        (∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j +
            HTGeometry.monicOrthoAlpha s n / 2) ^ 2) +
        (3 * (n : ℝ) / 4 + 1) * HTGeometry.monicOrthoAlpha s n ^ 2 := rfl
  have hbeta_nonneg : ∀ j ∈ Finset.range n,
      0 ≤ HTGeometry.monicOrthoBeta s j := by
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hone : 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hlow : HTGeometry.monicOrthoBeta s 1 ≤
      ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    calc
      HTGeometry.monicOrthoBeta s 1 =
          ∑ j ∈ ({1} : Finset ℕ), HTGeometry.monicOrthoBeta s j := by simp
      _ ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.singleton_subset_iff.mpr hone)
          (fun j hj _ => hbeta_nonneg j hj)
  have hcurrent : 0 < (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n := by
    exact mul_pos (by positivity)
      (HTGeometry.monicOrthoBeta_pos_below h (by omega) (by omega))
  have hKpos : 0 < K := xiShiftedAdmissionEffectivityCauchyWeight_pos (by omega)
  rw [hrate]
  have hbulk :
      Q + q * a ^ 2 + 2 * HTGeometry.monicOrthoBeta s 1 <
        HTGeometry.adaptiveOrthoJacobiEnergy s n -
          (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) := by
    unfold HTGeometry.adaptiveOrthoJacobiEnergy
    rw [← halpha]
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hbulk hKpos
  nlinarith

/-- Multiplicative rate whose negative is current admitted-norm logarithmic velocity. -/
def xiShiftedCanonicalAdmissionEffectivityRate (y : ℝ) (n : ℕ) : ℝ :=
  -2 * xiShiftedCanonicalAdmissionFirstCoeff y n +
    (2 * n + 1 : ℝ) * xiShiftedCanonicalAdmissionAlpha y n

/-- Exact division-free effectivity flow: norm derivative is rate times current norm, with minus
sign. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionNorm v n)
      (-xiShiftedCanonicalAdmissionEffectivityRate y n *
        xiShiftedCanonicalAdmissionNorm y n) y := by
  have hflow := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow hy hn hH
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
  unfold xiShiftedCanonicalAdmissionEffectivityRate
  rw [xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff hn hH,
    xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hH]
  exact hflow.congr_deriv (by push_cast; ring)

/-- Actual effectivity rate is current Jacobi trace with endpoint multiplicity `2n+1`. -/
theorem xiShiftedCanonicalAdmissionEffectivityRate_eq_jacobi
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionEffectivityRate y n =
      2 * (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) j) +
      (2 * n + 1 : ℝ) * HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedCanonicalAdmissionEffectivityRate,
    xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff hn hH,
    xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hH,
    HTGeometry.monicOrthoFirstCoeff_eq_neg_sum_below hbelow (by omega)]
  ring

/-- Effectivity-aware source law in actual mass coordinates. -/
theorem effectivityRate_sq_add_lowEdge_lt_weight_mul_relativeGaussBulk
    {y : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2 +
        2 * xiShiftedAdmissionEffectivityCauchyWeight n *
          HTGeometry.monicOrthoBeta
            (fun k => (xiShiftedReciprocalMoment y k).re) 1 <
      xiShiftedAdmissionEffectivityCauchyWeight n *
        xiShiftedCanonicalAdmissionRelativeGaussBulk y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hbase := jacobiEffectivityRate_sq_add_lowEdge_lt_weight_mul_visibleEnergy
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn le_rfl
  rw [xiShiftedCanonicalAdmissionEffectivityRate_eq_jacobi (by omega) hH,
    xiShiftedCanonicalAdmissionRelativeGaussBulk_eq_visibleEnergy (by omega) hH]
  exact hbase

/-- Literal adaptive mixed completed source, after exact newborn-norm removal and current-norm
normalization, is current Gaussian-visible bulk. -/
theorem xiShiftedCanonicalAdmissionRelativeGaussBulk_sq_eq_literal
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionRelativeGaussBulk (w ^ 2) n =
      (xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) -
        2 * (n + 1 : ℝ) *
          xiShiftedCanonicalAdmissionNorm (w ^ 2) (n + 1)) /
      (2 * xiShiftedCanonicalAdmissionNorm (w ^ 2) n) := by
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : xiShiftedCanonicalAdmissionNorm (w ^ 2) n =
      HTGeometry.monicOrthoNormSq s n := by
    exact xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH
  have hnextH : (HTGeometry.momentHankelMatrix s (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hnext : xiShiftedCanonicalAdmissionNorm (w ^ 2) (n + 1) =
      HTGeometry.monicOrthoNormSq s (n + 1) := by
    exact xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hnextH
  have hsource :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw hn hH
  have hedge : HTGeometry.monicOrthoNormSq s n *
      HTGeometry.monicOrthoBeta s (n + 1) =
      HTGeometry.monicOrthoNormSq s (n + 1) :=
    HTGeometry.monicOrthoNormSq_mul_nextBeta hbelow (by omega)
  have hnormPos : 0 < HTGeometry.monicOrthoNormSq s n :=
    HTGeometry.monicOrtho_inner_self_pos_below hbelow (by omega)
  rw [xiShiftedCanonicalAdmissionRelativeGaussBulk_eq_visibleEnergy hn hH,
    hsource, hnorm, hnext, ← hedge]
  change HTGeometry.adaptiveOrthoJacobiEnergy s n -
      (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) =
    (2 * HTGeometry.monicOrthoNormSq s n *
          HTGeometry.adaptiveOrthoJacobiEnergy s n -
        2 * (n + 1 : ℝ) *
          (HTGeometry.monicOrthoNormSq s n *
            HTGeometry.monicOrthoBeta s (n + 1))) /
      (2 * HTGeometry.monicOrthoNormSq s n)
  field_simp [ne_of_gt hnormPos]

/-- **Literal source/effectivity coercivity.**  Adaptive mixed completed `P^sharp` source minus
its exact newborn observation loss pays squared admission-amplitude rate and strict low-edge
reserve before reflection aggregation. -/
theorem literalArithmeticGaussBulk_pays_effectivityRate_and_lowEdge
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) n ^ 2 +
        2 * xiShiftedAdmissionEffectivityCauchyWeight n *
          HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) 1 <
      xiShiftedAdmissionEffectivityCauchyWeight n *
        ((xiShiftedAdaptiveMixedCompletedArithmeticSource w
              (HTGeometry.monicMomentAdmissionPolynomial
                (xiShiftedRealMomentSequence w) n) -
            2 * (n + 1 : ℝ) *
              xiShiftedCanonicalAdmissionNorm (w ^ 2) (n + 1)) /
          (2 * xiShiftedCanonicalAdmissionNorm (w ^ 2) n)) := by
  rw [← xiShiftedCanonicalAdmissionRelativeGaussBulk_sq_eq_literal hw (by omega) hH]
  exact effectivityRate_sq_add_lowEdge_lt_weight_mul_relativeGaussBulk hn hH

/-! ## Integrated admission-effectivity action -/

/-- Literal adaptive completed arithmetic bulk at physical mass `y`.  Square root converts mass
back to source coordinate before current admission selects the polynomial. -/
def xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass (y : ℝ) (n : ℕ) : ℝ :=
  (xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt y)
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence (Real.sqrt y)) n) -
      2 * (n + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm y (n + 1)) /
    (2 * xiShiftedCanonicalAdmissionNorm y n)

/-- Literal prime--Gamma source bulk is the division-free current adaptive shear quotient before
observation.  No positivity premise is needed. -/
theorem xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass_eq_shear
    {y : ℝ} (hy : 1 / 4 < y) (n : ℕ) :
    xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n =
      (2 * xiShiftedCanonicalAdmissionAdaptiveShear y n -
          2 * (n + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm y (n + 1)) /
        (2 * xiShiftedCanonicalAdmissionNorm y n) := by
  have hy0 : 0 ≤ y := (by linarith : 0 ≤ y)
  have hsqrt : 1 / 2 < Real.sqrt y := by
    have hsqrt0 := Real.sqrt_nonneg y
    have hsq' := Real.sq_sqrt hy0
    by_contra hnot
    have hsqrtle : Real.sqrt y ≤ 1 / 2 := le_of_not_gt hnot
    nlinarith
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  let P := HTGeometry.monicMomentAdmissionPolynomial
    (xiShiftedRealMomentSequence (Real.sqrt y)) n
  have hsource := two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hsqrt P
  rw [hsq] at hsource
  have hP : P = HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n := by
    dsimp only [P]
    unfold xiShiftedRealMomentSequence
    rw [hsq]
  unfold xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass
  change
    (xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt y) P -
        2 * (n + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm y (n + 1)) /
      (2 * xiShiftedCanonicalAdmissionNorm y n) = _
  rw [← hsource, hP]
  rfl

/-- Literal adaptive arithmetic bulk is continuous at every physical mass where current and next
admission blocks are nonsingular. -/
theorem continuousAt_xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass
    {y : ℝ} (hy : 1 / 4 < y) (n : ℕ)
    (hH : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef) :
    ContinuousAt (fun v => xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass v n) y := by
  have hy0 : 0 < y := by linarith
  have hhead : (xiShiftedMomentHankelMatrix y n).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hnextHead : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hdet : (xiShiftedMomentHankelMatrix y n).det ≠ 0 := ne_of_gt hhead.det_pos
  have hdetNext : (xiShiftedMomentHankelMatrix y (n + 1)).det ≠ 0 :=
    ne_of_gt hnextHead.det_pos
  have hshear : ContinuousAt
      (fun v => xiShiftedCanonicalAdmissionAdaptiveShear v n) y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment hy0 n hdet
    simpa only [xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hnorm := continuousAt_xiShiftedCanonicalAdmissionNorm_of_det hy0 n hdet
  have hnext := continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
    hy0 (n + 1) hdetNext
  have hnormNe : 2 * xiShiftedCanonicalAdmissionNorm y n ≠ 0 := by
    have hnormPos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
      rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hhead]
      exact HTGeometry.monicOrthoNorm_pos_below
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
    positivity
  have hquot : ContinuousAt
      (fun v =>
        (2 * xiShiftedCanonicalAdmissionAdaptiveShear v n -
            2 * (n + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm v (n + 1)) /
          (2 * xiShiftedCanonicalAdmissionNorm v n)) y := by
    exact ((continuousAt_const.mul hshear).sub
      ((continuousAt_const.mul continuousAt_const).mul hnext)).div
        (continuousAt_const.mul hnorm) hnormNe
  apply hquot.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hy] with v hv
  exact xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass_eq_shear hv n

/-- On the physical mass ray, literal rational--Gamma/von-Mangoldt source bulk is exactly the
mass-coordinate Gaussian-visible bulk. -/
theorem xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass_eq_relative
    {y : ℝ} (hy : 1 / 4 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n =
      xiShiftedCanonicalAdmissionRelativeGaussBulk y n := by
  have hy0 : 0 ≤ y := (by linarith : 0 ≤ y)
  have hsqrt : 1 / 2 < Real.sqrt y := by
    have hsqrt0 := Real.sqrt_nonneg y
    have hsq' := Real.sq_sqrt hy0
    by_contra hnot
    have hsqrtle : Real.sqrt y ≤ 1 / 2 := le_of_not_gt hnot
    nlinarith
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
      (n + 2)).PosDef
    rw [hsq]
    exact hH
  have hliteral := xiShiftedCanonicalAdmissionRelativeGaussBulk_sq_eq_literal
    hsqrt hn hHsqrt
  rw [hsq] at hliteral
  exact hliteral.symm

/-- Exact logarithmic admission transport.  Integral of effectivity rate is log loss of current
admitted norm across any positive chamber. -/
theorem integral_xiShiftedCanonicalAdmissionEffectivityRate_eq_log_norm_ratio
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hR : IntervalIntegrable
      (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n) volume a b) :
    (∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n) =
      Real.log (xiShiftedCanonicalAdmissionNorm a n) -
        Real.log (xiShiftedCanonicalAdmissionNorm b n) := by
  have hd : ∀ y ∈ Icc a b,
      HasDerivAt (fun v => Real.log (xiShiftedCanonicalAdmissionNorm v n))
        (-xiShiftedCanonicalAdmissionEffectivityRate y n) y := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le ha hy.1
    have hN := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul
      hypos hn (hH y hy)
    have hNpos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
      rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm (hH y hy)]
      exact HTGeometry.monicOrthoNorm_pos_below
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef (hH y hy)) (by omega)
    have hlog := hN.log hNpos.ne'
    have hderiv :
        (-xiShiftedCanonicalAdmissionEffectivityRate y n *
            xiShiftedCanonicalAdmissionNorm y n) /
          xiShiftedCanonicalAdmissionNorm y n =
            -xiShiftedCanonicalAdmissionEffectivityRate y n := by
      field_simp [hNpos.ne']
    exact hlog.congr_deriv hderiv
  have hneg : IntervalIntegrable
      (fun y => -xiShiftedCanonicalAdmissionEffectivityRate y n) volume a b := hR.neg
  have hd' : ∀ y ∈ uIcc a b,
      HasDerivAt (fun v => Real.log (xiShiftedCanonicalAdmissionNorm v n))
        (-xiShiftedCanonicalAdmissionEffectivityRate y n) y := by
    intro y hy
    exact hd y (by simpa [uIcc_of_le hab] using hy)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd' hneg
  rw [intervalIntegral.integral_neg] at hftc
  linarith

private theorem sq_intervalIntegral_le_length_mul_integral_sq
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b)
    (hfsq : IntervalIntegrable (fun y => f y ^ 2) volume a b) :
    (∫ y in a..b, f y) ^ 2 ≤
      (b - a) * ∫ y in a..b, f y ^ 2 := by
  let mu : Measure ℝ := volume.restrict (Ioc a b)
  have hfmu : Integrable f mu := hf.1
  have hsqmu : Integrable (fun y => f y ^ 2) mu := hfsq.1
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc a b) volume
    exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have honeSq : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) mu := by
    simpa only [one_pow] using hone
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := mu)
    hone.aestronglyMeasurable hfmu.aestronglyMeasurable honeSq hsqmu
  have hmu : mu.real univ = b - a := by
    simp [mu, Measure.real, Real.volume_Ioc, hab]
  have hfIntegral : ∫ y, f y ∂mu = ∫ y in a..b, f y := by
    rw [intervalIntegral.integral_of_le hab]
  have hfsqIntegral : ∫ y, f y ^ 2 ∂mu = ∫ y in a..b, f y ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
  simp only [one_mul, one_pow] at hcs
  rw [MeasureTheory.integral_const] at hcs
  simp only [smul_eq_mul, mul_one] at hcs
  simpa only [hmu, hfIntegral, hfsqIntegral] using hcs

/-- **Arithmetic source action/Lipschitz law.**  Across any actual positive chamber, literal
adaptive completed `P^sharp` bulk pays squared logarithmic motion of current admission amplitude.
Source is formed before reflection; no fixed reporter occurs. -/
theorem log_norm_sub_log_norm_sq_le_literalArithmeticGaussBulk_action
    {a b : ℝ} (hab : a ≤ b) (ha : 1 / 4 < a) {n : ℕ} (hn : 2 ≤ n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hR : IntervalIntegrable
      (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n) volume a b)
    (hR2 : IntervalIntegrable
      (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2) volume a b)
    (hsource : IntervalIntegrable
      (fun y => xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) volume a b) :
    (Real.log (xiShiftedCanonicalAdmissionNorm b n) -
        Real.log (xiShiftedCanonicalAdmissionNorm a n)) ^ 2 ≤
      (b - a) * xiShiftedAdmissionEffectivityCauchyWeight n *
        ∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n := by
  have hftc := integral_xiShiftedCanonicalAdmissionEffectivityRate_eq_log_norm_ratio
    hab (by linarith : 0 < a) (by omega : 0 < n) hH hR
  have hcs := sq_intervalIntegral_le_length_mul_integral_sq hab
    (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n) hR hR2
  have hpoint : ∀ y ∈ Icc a b,
      xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2 ≤
        xiShiftedAdmissionEffectivityCauchyWeight n *
          xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n := by
    intro y hy
    have hyquarter : 1 / 4 < y := lt_of_lt_of_le ha hy.1
    have hcoercive := effectivityRate_sq_add_lowEdge_lt_weight_mul_relativeGaussBulk
      hn (hH y hy)
    rw [← xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass_eq_relative
      hyquarter (by omega) (hH y hy)] at hcoercive
    have hbeta : 0 ≤ HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) 1 := by
      exact (HTGeometry.monicOrthoBeta_pos_below
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef (hH y hy))
        (by omega) (by omega)).le
    have hweight : 0 < xiShiftedAdmissionEffectivityCauchyWeight n :=
      xiShiftedAdmissionEffectivityCauchyWeight_pos (by omega)
    nlinarith
  have hmono :
      (∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2) ≤
        ∫ y in a..b, xiShiftedAdmissionEffectivityCauchyWeight n *
          xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n :=
    intervalIntegral.integral_mono_on hab hR2
      (hsource.const_mul (xiShiftedAdmissionEffectivityCauchyWeight n)) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  calc
    (Real.log (xiShiftedCanonicalAdmissionNorm b n) -
        Real.log (xiShiftedCanonicalAdmissionNorm a n)) ^ 2 =
        (∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n) ^ 2 := by
          rw [hftc]
          ring
    _ ≤ (b - a) *
        ∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2 := hcs
    _ ≤ (b - a) *
        (xiShiftedAdmissionEffectivityCauchyWeight n *
          ∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) :=
      mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hab)
    _ = (b - a) * xiShiftedAdmissionEffectivityCauchyWeight n *
        ∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n := by ring

/-- Chamber-native form of arithmetic source action law.  Positivity of actual moving Hankel
block automatically supplies all continuity and integrability obligations. -/
theorem log_norm_sub_log_norm_sq_le_literalArithmeticGaussBulk_action_of_posDef
    {a b : ℝ} (hab : a ≤ b) (ha : 1 / 4 < a) {n : ℕ} (hn : 2 ≤ n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (Real.log (xiShiftedCanonicalAdmissionNorm b n) -
        Real.log (xiShiftedCanonicalAdmissionNorm a n)) ^ 2 ≤
      (b - a) * xiShiftedAdmissionEffectivityCauchyWeight n *
        ∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n := by
  have hRcont : ContinuousOn
      (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n) (Icc a b) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hhead : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) (hH y hy)
    have hfirst := (hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff
      hy0 (by omega : 0 < n) (ne_of_gt hhead.det_pos)).continuousAt
    have halpha := (hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_sourceConnection
      hy0 (by omega : 0 < n) (hH y hy)).continuousAt
    exact ((continuousAt_const.mul hfirst).add
      (continuousAt_const.mul halpha)).continuousWithinAt
  have hsourceCont : ContinuousOn
      (fun y => xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) (Icc a b) := by
    intro y hy
    have hyquarter : 1 / 4 < y := lt_of_lt_of_le ha hy.1
    have hHy : (xiShiftedMomentHankelMatrix y (n + 2)).PosDef := hH y hy
    exact (continuousAt_xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass
      hyquarter n hHy).continuousWithinAt
  have hRcont' : ContinuousOn
      (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n) (uIcc a b) := by
    simpa [uIcc_of_le hab] using hRcont
  have hsourceCont' : ContinuousOn
      (fun y => xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) (uIcc a b) := by
    simpa [uIcc_of_le hab] using hsourceCont
  exact log_norm_sub_log_norm_sq_le_literalArithmeticGaussBulk_action
    hab ha hn hH hRcont'.intervalIntegrable
      (hRcont'.pow 2).intervalIntegrable hsourceCont'.intervalIntegrable

end
end RHTower
