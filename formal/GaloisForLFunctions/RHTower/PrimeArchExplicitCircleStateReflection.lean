import GaloisForLFunctions.RHTower.PrimeArchShiftedCircleDensity
import GaloisForLFunctions.HTGeometry.PolynomialHankelTailCone
import GaloisForLFunctions.HTGeometry.AbsConvergentPowerSeries
import GaloisForLFunctions.RHTower.CompleteHankelSignCone
import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail

/-!
# Explicit central prime--archimedean circle state

This module specializes the shifted circle carrier at the central moment and proves the sharper
source constants available only at shift zero.  It also extracts the exact all-degree coefficient
cone and the complementary tail-dominant integer-polynomial RH criterion.

All carrier, reflection, and coercivity declarations are unconditional.  Reflected positivity on
the complementary tail-dominant family remains exactly equivalent to RH.
-/

open scoped BigOperators
open Polynomial
open MeasureTheory

namespace RHTower

noncomputable section

private theorem zero_le_twelve : 0 ≤ 12 := by omega

/-- The central prime--archimedean symmetric circle density. -/
def primeArchCircleDensity : Circle → ℝ :=
  primeArchShiftCircleDensity 0

/-- The central prime--archimedean probability carrier. -/
abbrev primeArchCircleProbabilityMeasure : MeasureTheory.Measure Circle :=
  primeArchShiftCircleProbabilityMeasure 0

/-- The central circle density defines a probability measure. -/
theorem isProbabilityMeasure_primeArchCircleProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure primeArchCircleProbabilityMeasure := by
  simpa [primeArchCircleProbabilityMeasure] using
    isProbabilityMeasure_primeArchShiftCircleProbabilityMeasure_of_le_twelve 0 zero_le_twelve

/-- Exact central Fourier-moment recovery. -/
theorem integral_coe_pow_primeArchCircleProbabilityMeasure (k : ℕ) :
    (∫ z : Circle, (z : ℂ) ^ k ∂primeArchCircleProbabilityMeasure) =
      (normalizedPrimeArchMoment k : ℂ) /
        (normalizedPrimeArchMoment 0 : ℂ) := by
  simpa [primeArchCircleProbabilityMeasure] using
    integral_coe_pow_primeArchShiftCircleProbabilityMeasure 0 zero_le_twelve k

/-- The `1/84` atomwise sector gives the exact mass ratio used by the central card. -/
theorem eightyFour_div_eightyFive_mul_xiShiftAbsoluteMass_zero_le_head :
    (84 / 85 : ℝ) * xiShiftAbsoluteMass 0 ≤
      normalizedPrimeArchMoment 0 := by
  have h := sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment 0
  have hJ := xiShiftAbsoluteMass_nonneg 0
  norm_num at h ⊢
  nlinarith

/-- Exact relative absolute Fourier-tail bound at the central state. -/
theorem four_over_thirtyNine_xiShiftAbsoluteMass_zero_le_eightyFive_over_eightNineteen_head :
    (4 / 39 : ℝ) * xiShiftAbsoluteMass 0 ≤
      (85 / 819 : ℝ) * normalizedPrimeArchMoment 0 := by
  have hmass := eightyFour_div_eightyFive_mul_xiShiftAbsoluteMass_zero_le_head
  have hhead := normalizedPrimeArchMoment_zero_pos
  norm_num at hmass ⊢
  nlinarith

/-- Exact lower source-density bound `(734/819) M ≤ w`. -/
theorem primeArchCircleDensity_lower (z : Circle) :
    (734 / 819 : ℝ) * normalizedPrimeArchMoment 0 ≤
      primeArchCircleDensity z := by
  have hbase :=
    normalizedPrimeArchMoment_sub_four_over_thirtyNine_xiShiftAbsoluteMass_le_density 0 z
  have htail :=
    four_over_thirtyNine_xiShiftAbsoluteMass_zero_le_eightyFive_over_eightNineteen_head
  norm_num [primeArchCircleDensity] at hbase htail ⊢
  nlinarith

/-- Exact upper source-density bound `w ≤ (904/819) M`. -/
theorem primeArchCircleDensity_upper (z : Circle) :
    primeArchCircleDensity z ≤
      (904 / 819 : ℝ) * normalizedPrimeArchMoment 0 := by
  have hbase :=
    density_le_normalizedPrimeArchMoment_add_four_over_thirtyNine_xiShiftAbsoluteMass 0 z
  have htail :=
    four_over_thirtyNine_xiShiftAbsoluteMass_zero_le_eightyFive_over_eightNineteen_head
  norm_num [primeArchCircleDensity] at hbase htail ⊢
  nlinarith

/-- The central probability carrier is measure-equivalent to normalized circle Haar measure. -/
theorem primeArchCircleProbabilityMeasure_mutuallyAbsolutelyContinuous_circleLebesgue :
    primeArchCircleProbabilityMeasure ≪
        GaloisForLFunctions.HTGeometry.circleLebesgue ∧
      GaloisForLFunctions.HTGeometry.circleLebesgue ≪
        primeArchCircleProbabilityMeasure := by
  simpa [primeArchCircleProbabilityMeasure] using
    primeArchShiftCircleProbabilityMeasure_mutuallyAbsolutelyContinuous_circleLebesgue
      0 zero_le_twelve

/-- Holomorphic Laurent extension of the central real-analytic circle density. -/
abbrev primeArchCircleLaurentExtension : ℂ → ℂ :=
  primeArchShiftCircleLaurentExtension 0

/-- The central density extends holomorphically near every point of the unit circle. -/
theorem analyticAt_primeArchCircleLaurentExtension_on_unitCircle (z : Circle) :
    AnalyticAt ℂ primeArchCircleLaurentExtension (z : ℂ) := by
  simpa [primeArchCircleLaurentExtension] using
    analyticAt_primeArchShiftCircleLaurentExtension_on_unitCircle 0 z

/-- The central Laurent extension restricts exactly to the explicit circle density. -/
theorem primeArchCircleLaurentExtension_coe (z : Circle) :
    primeArchCircleLaurentExtension (z : ℂ) =
      (primeArchCircleDensity z : ℂ) := by
  simpa [primeArchCircleLaurentExtension, primeArchCircleDensity] using
    primeArchShiftCircleLaurentExtension_coe 0 z

/-- The unnormalized nonconstant central moment tail is at most `(85/1638) M`. -/
theorem tsum_abs_normalizedPrimeArchMoment_tail_le_eightyFive_over_sixteenThirtyEight_head :
    (∑' n : ℕ, |normalizedPrimeArchMoment (n + 1)|) ≤
      (85 / 1638 : ℝ) * normalizedPrimeArchMoment 0 := by
  have hbase := tsum_abs_primeArchShiftMoment_tail_le 0
  have htail :=
    four_over_thirtyNine_xiShiftAbsoluteMass_zero_le_eightyFive_over_eightNineteen_head
  simpa only [primeArchShiftMoment, Nat.zero_add] using (show
    (∑' n : ℕ, |primeArchShiftMoment 0 (n + 1)|) ≤
      (85 / 1638 : ℝ) * normalizedPrimeArchMoment 0 by
        norm_num at hbase htail ⊢
        nlinarith)

/-- Central reflected carrier. -/
abbrev primeArchCircleReflectionLI :
    MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure →ₗᵢ[ℂ]
      MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure :=
  primeArchShiftCircleReflectionLI 0

/-- The central analytic monomial orbit. -/
abbrev primeArchCircleMonomialLp (n : ℕ) :
    MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure :=
  primeArchShiftCircleMonomialLp 0 zero_le_twelve n

/-- Multiplication by the circle coordinate on the central carrier, packaged as a unitary linear
isometric equivalence. -/
def primeArchCircleShiftLIE :
    MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure ≃ₗᵢ[ℂ]
      MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure := by
  letI : IsProbabilityMeasure primeArchCircleProbabilityMeasure :=
    isProbabilityMeasure_primeArchCircleProbabilityMeasure
  exact GaloisForLFunctions.HTGeometry.circleZMulLIE primeArchCircleProbabilityMeasure

/-- Central circle reflection is an involution. -/
theorem primeArchCircleReflectionLI_apply_self
    (f : MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure) :
    primeArchCircleReflectionLI (primeArchCircleReflectionLI f) = f := by
  exact GaloisForLFunctions.HTGeometry.circleInvReflectionLI_apply_self
    _ (measurePreserving_inv_primeArchShiftCircleProbabilityMeasure 0) f

/-- Exact central carrier relation `Theta U Theta = U⁻¹`. -/
theorem primeArchCircleReflectionLI_circleZMulLp_conj
    (f : MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure) :
    letI : IsProbabilityMeasure primeArchCircleProbabilityMeasure :=
      isProbabilityMeasure_primeArchCircleProbabilityMeasure
    primeArchCircleReflectionLI
        (GaloisForLFunctions.HTGeometry.circleZMulLp _
          (primeArchCircleReflectionLI f)) =
      primeArchCircleShiftLIE.symm f := by
  simpa [primeArchCircleProbabilityMeasure, primeArchCircleShiftLIE] using
    primeArchShiftCircleReflectionLI_circleZMulLp_conj 0 zero_le_twelve f

/-- A finite real analytic polynomial in the central carrier. -/
abbrev primeArchFiniteRealCirclePolynomialLp {n : ℕ} (v : Fin n → ℝ) :
    MeasureTheory.Lp ℂ 2 primeArchCircleProbabilityMeasure :=
  primeArchShiftFiniteRealCirclePolynomialLp 0 zero_le_twelve v

/-- The central reflected monomial Gram kernel is the normalized prime--Gamma Hankel kernel. -/
theorem inner_primeArchCircleReflectionLI_monomial (i j : ℕ) :
    inner ℂ (primeArchCircleReflectionLI (primeArchCircleMonomialLp i))
        (primeArchCircleMonomialLp j) =
      (normalizedPrimeArchMoment (i + j) : ℂ) /
        (normalizedPrimeArchMoment 0 : ℂ) := by
  simpa only [Nat.zero_add] using
    inner_primeArchShiftCircleReflectionLI_monomial 0 zero_le_twelve i j

/-- Reflected Gram value of a finite real central polynomial as the normalized moment
functional. -/
theorem inner_primeArchCircleReflectionLI_finitePolynomial_eq_momentFunctional
    {n : ℕ} (v : Fin n → ℝ) :
    inner ℂ (primeArchCircleReflectionLI
        (primeArchFiniteRealCirclePolynomialLp v))
        (primeArchFiniteRealCirclePolynomialLp v) =
      (HTGeometry.momentFunctional normalizedPrimeArchMoment
          ((∑ i : Fin n, v i • Polynomial.X ^ (i : ℕ)) ^ 2) /
        normalizedPrimeArchMoment 0 : ℂ) := by
  have h := inner_primeArchShiftCircleReflectionLI_finitePolynomial_eq_momentFunctional
    0 zero_le_twelve v
  have hm : primeArchShiftMoment 0 = normalizedPrimeArchMoment := by
    funext k
    simp [primeArchShiftMoment]
  rw [hm] at h
  exact h

/-- Exact central cosine--sine polarization identity. -/
theorem primeArchCircle_cosine_sine_polarization {n : ℕ} (v : Fin n → ℝ) :
    let R := primeArchCircleReflectionLI
    let P := primeArchFiniteRealCirclePolynomialLp v
    ‖GaloisForLFunctions.HTGeometry.circleReflectionCosineChannel R P‖ ^ 2 -
        ‖GaloisForLFunctions.HTGeometry.circleReflectionSineChannel R P‖ ^ 2 =
      HTGeometry.momentFunctional normalizedPrimeArchMoment
          ((∑ i : Fin n, v i • Polynomial.X ^ (i : ℕ)) ^ 2) /
        normalizedPrimeArchMoment 0 := by
  have h := primeArchShiftCircle_cosine_sine_polarization 0 zero_le_twelve v
  have hm : primeArchShiftMoment 0 = normalizedPrimeArchMoment := by
    funext k
    simp [primeArchShiftMoment]
  rw [hm] at h
  exact h

/-- Reflection positivity of every finite real polynomial section of the explicit central
carrier. -/
def PrimeArchCircleReflectionPositive : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ),
    0 ≤ (inner ℂ
      (primeArchCircleReflectionLI (primeArchFiniteRealCirclePolynomialLp v))
      (primeArchFiniteRealCirclePolynomialLp v)).re

/-- Explicit carrier reflection positivity is exactly the complete real Hankel cone. -/
theorem primeArchCircleReflectionPositive_iff_completeHankelCone :
    PrimeArchCircleReflectionPositive ↔
      CompleteHankelCone normalizedPrimeArchMoment := by
  constructor
  · intro h n v
    have hv := h n v
    rw [inner_primeArchCircleReflectionLI_finitePolynomial_eq_momentFunctional] at hv
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.normSq_ofReal] at hv
    have hhead := normalizedPrimeArchMoment_zero_pos
    rw [← HTGeometry.momentFunctional_sq_eq_hankelForm]
    field_simp [hhead.ne'] at hv
    nlinarith
  · intro h n v
    rw [inner_primeArchCircleReflectionLI_finitePolynomial_eq_momentFunctional]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.normSq_ofReal]
    have hhead := normalizedPrimeArchMoment_zero_pos
    rw [HTGeometry.momentFunctional_sq_eq_hankelForm]
    have hv := h n v
    positivity

/-- Complete real prime--Gamma Hankel positivity is exactly RH. -/
theorem completeHankelCone_normalizedPrimeArchMoment_iff_riemannHypothesis :
    CompleteHankelCone normalizedPrimeArchMoment ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    intro p
    rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
    exact (completeHankelCone_iff_momentFunctional_square_nonnegative
      normalizedPrimeArchMoment).mp h (p.map (Int.castRingHom ℝ))
  · intro hRH
    apply (completeHankelCone_iff_momentFunctional_square_nonnegative
      normalizedPrimeArchMoment).mpr
    obtain ⟨mu, hmom, hint⟩ :=
      primeArchMomentRepresentation_of_riemannHypothesis hRH
    intro p
    exact HTGeometry.momentFunctional_pow_two_nonneg
      normalizedPrimeArchMoment hmom hint p

/-- Reflection positivity of the explicit central circle carrier is exactly RH. -/
theorem primeArchCircleReflectionPositive_iff_riemannHypothesis :
    PrimeArchCircleReflectionPositive ↔ RiemannHypothesis :=
  primeArchCircleReflectionPositive_iff_completeHankelCone.trans
    completeHankelCone_normalizedPrimeArchMoment_iff_riemannHypothesis

/-- Reflection positivity restricted to integer polynomials, represented by their complete finite
coefficient vectors in the explicit central carrier. -/
def PrimeArchCircleIntegerPolynomialReflectionPositive : Prop :=
  ∀ p : Polynomial ℤ,
    let P := p.map (Int.castRingHom ℝ)
    let v : Fin (P.natDegree + 1) → ℝ := fun i => P.coeff (i : ℕ)
    0 ≤ (inner ℂ
      (primeArchCircleReflectionLI (primeArchFiniteRealCirclePolynomialLp v))
      (primeArchFiniteRealCirclePolynomialLp v)).re

/-- Explicit integer-polynomial reflection positivity is the established countable source Hankel
criterion. -/
theorem primeArchCircleIntegerPolynomialReflectionPositive_iff_sourceHankel :
    PrimeArchCircleIntegerPolynomialReflectionPositive ↔
      PrimeArchSourceTraceHankelIntNonnegative := by
  constructor
  · intro h p
    let P := p.map (Int.castRingHom ℝ)
    let v : Fin (P.natDegree + 1) → ℝ := fun i => P.coeff (i : ℕ)
    have hp := h p
    dsimp only at hp
    rw [inner_primeArchCircleReflectionLI_finitePolynomial_eq_momentFunctional] at hp
    have hpoly : (∑ i : Fin (P.natDegree + 1),
        v i • Polynomial.X ^ (i : ℕ)) = P := by
      exact finCoefficientPolynomial_coeff_natDegree_eq P
    rw [hpoly] at hp
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.normSq_ofReal] at hp
    rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
    have hhead := normalizedPrimeArchMoment_zero_pos
    field_simp [hhead.ne'] at hp
    nlinarith
  · intro h p
    let P := p.map (Int.castRingHom ℝ)
    let v : Fin (P.natDegree + 1) → ℝ := fun i => P.coeff (i : ℕ)
    dsimp only
    rw [inner_primeArchCircleReflectionLI_finitePolynomial_eq_momentFunctional]
    have hpoly : (∑ i : Fin (P.natDegree + 1),
        v i • Polynomial.X ^ (i : ℕ)) = P := by
      exact finCoefficientPolynomial_coeff_natDegree_eq P
    rw [hpoly]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.normSq_ofReal]
    have hp := h p
    rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq] at hp
    have hhead := normalizedPrimeArchMoment_zero_pos
    positivity

/-- Integer-polynomial reflection positivity of the explicit central carrier is exactly RH. -/
theorem primeArchCircleIntegerPolynomialReflectionPositive_iff_riemannHypothesis :
    PrimeArchCircleIntegerPolynomialReflectionPositive ↔ RiemannHypothesis :=
  primeArchCircleIntegerPolynomialReflectionPositive_iff_sourceHankel.trans
    primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis

/-- Exact central all-degree lower coefficient bound. -/
theorem primeArchSourceMomentFunctional_sq_centralCoeff_lower
    (p : Polynomial ℝ) :
    (734 / 819 : ℝ) * normalizedPrimeArchMoment 0 * (p.coeff 0) ^ 2 -
        (85 / 819 : ℝ) * normalizedPrimeArchMoment 0 *
          HTGeometry.polynomialNonconstantCoeffSqEnergy p ≤
      HTGeometry.momentFunctional normalizedPrimeArchMoment (p ^ 2) := by
  have habs := HTGeometry.abs_momentFunctional_sq_sub_vacuum_le
    normalizedPrimeArchMoment p
      (B := (85 / 1638 : ℝ) * normalizedPrimeArchMoment 0)
    (by simpa [primeArchShiftMoment] using summable_abs_primeArchShiftMoment_tail 0)
    tsum_abs_normalizedPrimeArchMoment_tail_le_eightyFive_over_sixteenThirtyEight_head
  have hlower := (abs_le.mp habs).1
  have hhead := normalizedPrimeArchMoment_zero_pos
  have henergy := HTGeometry.polynomialCoeffSqEnergy_nonneg p
  rw [HTGeometry.polynomialCoeffSqEnergy] at habs hlower henergy
  norm_num at habs hlower ⊢
  nlinarith

/-- Every polynomial in the exact central coefficient cone has nonnegative source Hankel value. -/
theorem re_primeArchSourceTraceHankel_nonneg_of_centralCoeffCone
    (p : Polynomial ℝ)
    (hcone : 85 * HTGeometry.polynomialNonconstantCoeffSqEnergy p ≤
      734 * (p.coeff 0) ^ 2) :
    0 ≤ (primeArchSourceTraceHankel p).re := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  have hbound := primeArchSourceMomentFunctional_sq_centralCoeff_lower p
  have hhead := normalizedPrimeArchMoment_zero_pos
  norm_num at hbound ⊢
  nlinarith

/-- Source Hankel positivity on the exact complementary integer-polynomial tail-dominant cone. -/
def PrimeArchSourceTraceHankelIntTailDominantNonnegative : Prop :=
  ∀ p : Polynomial ℤ,
    734 * ((p.map (Int.castRingHom ℝ)).coeff 0) ^ 2 <
        85 * HTGeometry.polynomialNonconstantCoeffSqEnergy
          (p.map (Int.castRingHom ℝ)) →
      0 ≤ (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re

/-- Positivity only on the complementary tail-dominant cone is exactly RH. -/
theorem primeArchSourceTraceHankelIntTailDominantNonnegative_iff_riemannHypothesis :
    PrimeArchSourceTraceHankelIntTailDominantNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro htail
    apply riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    intro p
    by_cases hcone :
        85 * HTGeometry.polynomialNonconstantCoeffSqEnergy
            (p.map (Int.castRingHom ℝ)) ≤
          734 * ((p.map (Int.castRingHom ℝ)).coeff 0) ^ 2
    · exact re_primeArchSourceTraceHankel_nonneg_of_centralCoeffCone _ hcone
    · exact htail p (lt_of_not_ge hcone)
  · intro hRH p _
    exact (primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis.mpr hRH) p

/-! ## Explicit strict Schur source -/

/-- Ordinary central moment resolvent `G(z) = Σ mₙ zⁿ`. -/
def primeArchCircleMomentResolvent (z : ℂ) : ℂ :=
  ∑' n : ℕ, (normalizedPrimeArchMoment n : ℂ) * z ^ n

/-- Atomwise reciprocal-square resolvent, in the ordinary moment coordinate. -/
def primeArchCircleAtomicResolvent (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy,
    xiZeroCopyReciprocalSquare q /
      (1 - xiZeroCopyReciprocalSquare q * z)

/-- On the closed unit disk, the source moment resolvent is exactly the absolutely convergent
reciprocal-square atom resolvent. -/
theorem primeArchCircleMomentResolvent_eq_atomicResolvent
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    primeArchCircleMomentResolvent z = primeArchCircleAtomicResolvent z := by
  let lam : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare
  have hlam : Summable (fun q => ‖lam q‖) := by
    simpa only [lam] using summable_xiZeroCopyReciprocalSquare.norm
  let ratio : ℝ := ‖z‖ * (2 / 41)
  have hratio0 : 0 ≤ ratio := mul_nonneg (norm_nonneg z) (by norm_num)
  have hratio1 : ratio < 1 := by
    dsimp only [ratio]
    nlinarith [norm_nonneg z]
  have hgeom : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hboundTerm : ∀ (n : ℕ) (q : XiZeroCopy),
      ‖z ^ n * lam q ^ (n + 1)‖ ≤ ratio ^ n * ‖lam q‖ := by
    intro n q
    rw [norm_mul, norm_pow, norm_pow, pow_succ]
    have hlamPow : ‖lam q‖ ^ n ≤ (2 / 41 : ℝ) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _)
        (by simpa only [lam] using
          (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le) n
    calc
      ‖z‖ ^ n * (‖lam q‖ ^ n * ‖lam q‖) ≤
          ‖z‖ ^ n * ((2 / 41 : ℝ) ^ n * ‖lam q‖) := by
        gcongr
      _ = ratio ^ n * ‖lam q‖ := by
        rw [mul_pow]
        ring
  have hnorm : Summable (fun p : ℕ × XiZeroCopy =>
      ratio ^ p.1 * ‖lam p.2‖) := by
    rw [summable_prod_of_nonneg
      (fun p => mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))]
    constructor
    · intro n
      exact hlam.mul_left (ratio ^ n)
    · apply Summable.of_nonneg_of_le
        (fun n => tsum_nonneg fun _ =>
          mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))
        (fun n => le_rfl)
      exact (hgeom.mul_right (∑' q : XiZeroCopy, ‖lam q‖)).congr
        (fun n => by rw [← tsum_mul_left])
  have huncurry : Summable (Function.uncurry
      (fun (n : ℕ) (q : XiZeroCopy) => z ^ n * lam q ^ (n + 1))) := by
    apply Summable.of_norm_bounded hnorm
    intro p
    exact hboundTerm p.1 p.2
  rw [primeArchCircleMomentResolvent]
  have hstep : ∀ n : ℕ,
      (normalizedPrimeArchMoment n : ℂ) * z ^ n =
        ∑' q : XiZeroCopy, z ^ n * lam q ^ (n + 1) := by
    intro n
    have hm : (normalizedPrimeArchMoment n : ℂ) =
        xiCentralReciprocalMoment n := by
      rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment]
      apply Complex.ext
      · simp
      · simp [xiCentralReciprocalMoment_im_eq_zero]
    rw [hm, ← tsum_xiZeroCopyReciprocalSquare_pow n, ← tsum_mul_right]
    apply tsum_congr
    intro q
    dsimp [lam]
    ring
  rw [tsum_congr hstep, ← Summable.tsum_comm huncurry]
  apply tsum_congr
  intro q
  have hzlam : ‖z * lam q‖ < 1 := by
    rw [norm_mul]
    have hq := norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q
    dsimp only [lam]
    nlinarith [norm_nonneg z]
  change (∑' n : ℕ, z ^ n * lam q ^ (n + 1)) =
    lam q / (1 - lam q * z)
  calc
    (∑' n : ℕ, z ^ n * lam q ^ (n + 1)) =
        lam q * ∑' n : ℕ, (z * lam q) ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_pow, pow_succ]
      ring
    _ = lam q / (1 - lam q * z) := by
      rw [tsum_geometric_of_norm_lt_one hzlam, div_eq_mul_inv]
      congr 2
      ring

/-- The moment-resolvent coefficients converge absolutely through the explicit radius `41/4`. -/
theorem summable_norm_normalizedPrimeArchMoment_mul_radius :
    Summable (fun n : ℕ =>
      ‖(normalizedPrimeArchMoment n : ℂ)‖ * (41 / 4 : ℝ) ^ n) := by
  have hgeo : Summable (fun n : ℕ =>
      (1 / 2 : ℝ) ^ n * xiShiftAbsoluteMass 0) := by
    exact (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right _
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  have h := abs_normalizedPrimeArchMoment_add_le_xiShiftAbsoluteMass 0 n
  simp only [Nat.zero_add, Complex.norm_real, Real.norm_eq_abs] at h ⊢
  calc
    |normalizedPrimeArchMoment n| * (41 / 4 : ℝ) ^ n ≤
        ((2 / 41 : ℝ) ^ n * xiShiftAbsoluteMass 0) * (41 / 4 : ℝ) ^ n := by
      gcongr
    _ = (1 / 2 : ℝ) ^ n * xiShiftAbsoluteMass 0 := by
      calc
        ((2 / 41 : ℝ) ^ n * xiShiftAbsoluteMass 0) * (41 / 4 : ℝ) ^ n =
            ((2 / 41 : ℝ) ^ n * (41 / 4 : ℝ) ^ n) * xiShiftAbsoluteMass 0 := by ring
        _ = (1 / 2 : ℝ) ^ n * xiShiftAbsoluteMass 0 := by
          rw [← mul_pow]
          norm_num

/-- The ordinary moment resolvent is analytic on a disk strictly larger than the closed unit
disk. -/
theorem analyticOnNhd_primeArchCircleMomentResolvent :
    AnalyticOnNhd ℂ primeArchCircleMomentResolvent (Metric.ball 0 (41 / 4 : ℝ)) := by
  exact GaloisForLFunctions.HTGeometry.analyticOnNhd_powerSum
    (ρ := (41 / 4 : NNReal)) (by norm_num)
    summable_norm_normalizedPrimeArchMoment_mul_radius

/-- Absolute convergence of the nonconstant resolvent tail on the closed unit disk. -/
theorem summable_primeArchCircleMomentResolvent_tail {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ =>
      (normalizedPrimeArchMoment (n + 1) : ℂ) * z ^ (n + 1)) := by
  apply Summable.of_norm_bounded
    (by simpa [primeArchShiftMoment] using summable_abs_primeArchShiftMoment_tail 0)
  intro n
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

/-- The resolvent minus its head is exactly the nonconstant moment tail. -/
theorem primeArchCircleMomentResolvent_sub_head {z : ℂ} (hz : ‖z‖ ≤ 1) :
    primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ) =
      ∑' n : ℕ, (normalizedPrimeArchMoment (n + 1) : ℂ) * z ^ (n + 1) := by
  have hsfull : Summable (fun n : ℕ =>
      (normalizedPrimeArchMoment n : ℂ) * z ^ n) := by
    apply Summable.of_norm_bounded summable_norm_normalizedPrimeArchMoment_mul_radius
    intro n
    rw [norm_mul, norm_pow]
    have hzpow : ‖z‖ ^ n ≤ (41 / 4 : ℝ) ^ n := by
      apply pow_le_pow_left₀ (norm_nonneg z) _ n
      nlinarith
    exact mul_le_mul_of_nonneg_left hzpow (norm_nonneg _)
  rw [primeArchCircleMomentResolvent, hsfull.tsum_eq_zero_add]
  simp

/-- Exact closed-disk resolvent displacement bound. -/
theorem norm_primeArchCircleMomentResolvent_sub_head_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ)‖ ≤
      (85 / 1638 : ℝ) * normalizedPrimeArchMoment 0 := by
  rw [primeArchCircleMomentResolvent_sub_head hz]
  have hs := summable_primeArchCircleMomentResolvent_tail hz
  calc
    ‖∑' n : ℕ, (normalizedPrimeArchMoment (n + 1) : ℂ) * z ^ (n + 1)‖ ≤
        ∑' n : ℕ, ‖(normalizedPrimeArchMoment (n + 1) : ℂ) * z ^ (n + 1)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, |normalizedPrimeArchMoment (n + 1)| := by
      exact hs.norm.tsum_le_tsum
        (fun n => by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg _)
            (pow_le_one₀ (norm_nonneg _) hz))
        (by simpa [primeArchShiftMoment] using summable_abs_primeArchShiftMoment_tail 0)
    _ ≤ _ :=
      tsum_abs_normalizedPrimeArchMoment_tail_le_eightyFive_over_sixteenThirtyEight_head

/-- The moment resolvent has no zero on the closed unit disk. -/
theorem primeArchCircleMomentResolvent_ne_zero {z : ℂ} (hz : ‖z‖ ≤ 1) :
    primeArchCircleMomentResolvent z ≠ 0 := by
  have hbound := norm_primeArchCircleMomentResolvent_sub_head_le hz
  have hhead := normalizedPrimeArchMoment_zero_pos
  have htriangle : normalizedPrimeArchMoment 0 ≤
      ‖primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ)‖ +
        ‖primeArchCircleMomentResolvent z‖ := by
    have h := norm_sub_le (primeArchCircleMomentResolvent z)
      (primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ))
    simpa [abs_of_pos hhead, add_comm] using h
  rw [← norm_pos_iff]
  norm_num at hbound
  nlinarith

/-- Exact source Schur value `φ(z) = 1 - M/G(z)`. -/
def primeArchCircleSchurFunction (z : ℂ) : ℂ :=
  1 - (normalizedPrimeArchMoment 0 : ℂ) / primeArchCircleMomentResolvent z

/-- The source Schur function has the strict closed-disk bound `85/1553`. -/
theorem norm_primeArchCircleSchurFunction_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖primeArchCircleSchurFunction z‖ ≤ (85 / 1553 : ℝ) := by
  have hbound := norm_primeArchCircleMomentResolvent_sub_head_le hz
  have hhead := normalizedPrimeArchMoment_zero_pos
  have htriangle : normalizedPrimeArchMoment 0 ≤
      ‖primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ)‖ +
        ‖primeArchCircleMomentResolvent z‖ := by
    have h := norm_sub_le (primeArchCircleMomentResolvent z)
      (primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ))
    simpa [abs_of_pos hhead, add_comm] using h
  have hresolvent : (1553 / 1638 : ℝ) * normalizedPrimeArchMoment 0 ≤
      ‖primeArchCircleMomentResolvent z‖ := by
    norm_num at hbound ⊢
    nlinarith
  have hpos : 0 < ‖primeArchCircleMomentResolvent z‖ :=
    norm_pos_iff.mpr (primeArchCircleMomentResolvent_ne_zero hz)
  have hquotient : primeArchCircleSchurFunction z =
      (primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ)) /
        primeArchCircleMomentResolvent z := by
    rw [primeArchCircleSchurFunction]
    field_simp [primeArchCircleMomentResolvent_ne_zero hz]
  rw [hquotient, norm_div]
  apply (div_le_iff₀ hpos).2
  norm_num at hbound hresolvent ⊢
  nlinarith

/-- Exact central Carathéodory source `F(z) = 2G(z)/M - 1`. -/
def primeArchCircleCaratheodoryFunction (z : ℂ) : ℂ :=
  2 * primeArchCircleMomentResolvent z /
      (normalizedPrimeArchMoment 0 : ℂ) - 1

/-- The exact source Carathéodory function has strictly positive real part throughout the closed
unit disk. -/
theorem primeArchCircleCaratheodoryFunction_re_pos {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 < (primeArchCircleCaratheodoryFunction z).re := by
  have hbound := norm_primeArchCircleMomentResolvent_sub_head_le hz
  have hhead := normalizedPrimeArchMoment_zero_pos
  have hre : normalizedPrimeArchMoment 0 -
      ‖primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ)‖ ≤
        (primeArchCircleMomentResolvent z).re := by
    have h := Complex.abs_re_le_norm
      (primeArchCircleMomentResolvent z - (normalizedPrimeArchMoment 0 : ℂ))
    have hlower := (abs_le.mp h).1
    norm_num at hlower ⊢
    linarith
  have hresolventRe : (1553 / 1638 : ℝ) * normalizedPrimeArchMoment 0 ≤
      (primeArchCircleMomentResolvent z).re := by
    norm_num at hbound hre ⊢
    linarith
  change 0 < (2 * primeArchCircleMomentResolvent z /
    (normalizedPrimeArchMoment 0 : ℂ) - 1).re
  rw [Complex.sub_re, Complex.div_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    Complex.normSq_ofReal, Complex.one_re]
  norm_num [hhead.ne'] at ⊢
  field_simp [hhead.ne']
  norm_num at hresolventRe ⊢
  nlinarith

/-- Exact Cayley identity between the source Carathéodory and Schur functions. -/
theorem primeArchCircleSchurFunction_eq_cayley {z : ℂ} (hz : ‖z‖ ≤ 1) :
    primeArchCircleSchurFunction z =
      (primeArchCircleCaratheodoryFunction z - 1) /
        (primeArchCircleCaratheodoryFunction z + 1) := by
  have hhead := normalizedPrimeArchMoment_zero_pos
  rw [primeArchCircleSchurFunction, primeArchCircleCaratheodoryFunction]
  field_simp [hhead.ne', primeArchCircleMomentResolvent_ne_zero hz]
  ring

end

end RHTower
