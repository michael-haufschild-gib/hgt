import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionArithmeticTransgression
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession

/-!
# Covariant defect energy for frozen/current shifted-Xi admission

The mixed mass--admission source debt has an exact connection-free primitive.  If `P_y` is current
canonical monic admission, `A` is a fixed monic amplitude of the same degree, and `D_y=A-P_y`,
then the completed source transgression is

`T_y(P_y,A) = -d/dy L_y(X D_y^2) - 2 h_y' [X^(n-1)]D_y`.

The inverse-Hankel coefficient velocity cancels identically.  Thus mixed source curvature is
carried only by odd defect-energy drift and canonical norm flux, not by raw admission speed.
-/

open Complex Matrix MeasureTheory Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Difference between a fixed amplitude and current canonical admission. -/
def xiShiftedCanonicalAdmissionDefect
    (y : ℝ) (n : ℕ) (A : Polynomial ℝ) : Polynomial ℝ :=
  A - HTGeometry.monicMomentAdmissionPolynomial
    (fun k => (xiShiftedReciprocalMoment y k).re) n

/-- Odd defect energy selected before source aggregation. -/
def xiShiftedCanonicalAdmissionDefectOddEnergy
    (y : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  let D := xiShiftedCanonicalAdmissionDefect y n A
  HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment y k).re) D (X * D)

/-- Subleading coefficient displacement from current admission to a fixed monic amplitude. -/
def xiShiftedCanonicalAdmissionDefectFirstCoeff
    (y : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  A.coeff (n - 1) - xiShiftedCanonicalAdmissionFirstCoeff y n

/-- Source-mass form of literal adaptive admission transgression. -/
def xiShiftedAdaptiveShearAdmissionTransgression
    (y : ℝ) (P A : Polynomial ℝ) : ℝ :=
  2 * (HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A) -
    HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (X * P) (X * xiShiftedBoundaryShiftedEuler 1 P))

/-- Total covariant source density driving frozen/current odd defect energy. -/
def xiShiftedCanonicalAdmissionDefectSourceDensity
    (y : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  xiShiftedAdaptiveShearAdmissionTransgression y
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment y k).re) n) A +
    2 * xiShiftedCanonicalAdmissionNormFlux y n *
      xiShiftedCanonicalAdmissionDefectFirstCoeff y n A

/-- Every fixed finite adaptive shear packet is continuous in positive source mass. -/
theorem continuousAt_xiShiftedFixedAdaptiveShearMoment
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ) :
    ContinuousAt (fun v => HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment v k).re)
      (xiShiftedBoundaryAdaptiveShearPolynomial A)) y := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  apply continuousAt_finsetSum
  intro k _
  exact continuousAt_const.mul
    (hasDerivAt_re_xiShiftedReciprocalMoment hy k).continuousAt

/-- At a nonsingular shifted-Xi Hankel block, the adaptive shear selected by canonical admission
is continuous in source mass. -/
theorem continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    ContinuousAt (fun v =>
      let P := HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (xiShiftedBoundaryAdaptiveShearPolynomial P)) y := by
  let P : ℝ → Polynomial ℝ := fun v => HTGeometry.monicMomentAdmissionPolynomial
    (fun k => (xiShiftedReciprocalMoment v k).re) n
  let Q : ℝ → Polynomial ℝ := fun v => xiShiftedBoundaryAdaptiveShearPolynomial (P v)
  let N := 2 * n + 2
  have hs : ∀ k, Tendsto
      (fun v => (xiShiftedReciprocalMoment v k).re) (nhds y)
      (nhds (xiShiftedReciprocalMoment y k).re) := fun k =>
    (hasDerivAt_re_xiShiftedReciprocalMoment hy k).continuousAt
  have hPcoeff : ∀ k, Tendsto (fun v => (P v).coeff k) (nhds y)
      (nhds ((P y).coeff k)) := fun k =>
    HTGeometry.tendsto_monicMomentAdmissionPolynomial_coeff hs hdet k
  have hQcoeff : ∀ k, Tendsto (fun v => (Q v).coeff k) (nhds y)
      (nhds ((Q y).coeff k)) :=
    XiShiftedCanonicalAdmission.tendsto_adaptiveShear_coeff hPcoeff
  have hsum := tendsto_finsetSum (Finset.range (N + 1)) fun k _ =>
    (hQcoeff k).mul (hs k)
  have hdeg : ∀ v, (Q v).natDegree ≤ N := by
    intro v
    exact natDegree_xiShiftedBoundaryAdaptiveShearPolynomial_le
      (HTGeometry.monicMomentAdmissionPolynomial_monic _ _)
      (HTGeometry.monicMomentAdmissionPolynomial_natDegree _ _)
  change Tendsto (fun v => HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment v k).re) (Q v)) (nhds y)
    (nhds (HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) (Q y)))
  simpa only [XiShiftedCanonicalAdmission.momentFunctional_eq_sum_range_of_natDegree_le
    (hdeg y)] using hsum.congr' (Eventually.of_forall fun v => by
      rw [XiShiftedCanonicalAdmission.momentFunctional_eq_sum_range_of_natDegree_le
        (hdeg v)])

/-- Same-degree monic polynomials differ in strictly lower degree. -/
theorem natDegree_sub_lt_of_monic_same_degree
    {A P : Polynomial ℝ} {n : ℕ} (hn : 0 < n)
    (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hP : P.Monic) (hPdeg : P.natDegree = n) :
    (A - P).natDegree < n := by
  by_cases hzero : A - P = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hn
  · apply (Polynomial.natDegree_lt_iff_degree_lt hzero).2
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    have hnk : n ≤ k := by exact_mod_cast hk
    by_cases hkn : k = n
    · subst k
      have hAc : A.coeff n = 1 := by
        simpa only [hAdeg] using hA.coeff_natDegree
      have hPc : P.coeff n = 1 := by
        simpa only [hPdeg] using hP.coeff_natDegree
      simp [hAc, hPc]
    · have hnk' : n < k := lt_of_le_of_ne hnk (Ne.symm hkn)
      have hAz : A.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hAdeg.symm ▸ hnk')
      have hPz : P.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hPdeg.symm ▸ hnk')
      simp [hAz, hPz]

/-- **Odd-current defect decomposition.**  Frozen/current odd-current mismatch is one canonical
connection displacement plus the odd energy of the full admission defect. -/
theorem xiShiftedCanonicalAdmission_oddCurrentGap_eq_normCoeff_add_defectEnergy
    {y : ℝ} {n : ℕ} (hn : 0 < n) (A : Polynomial ℝ)
    (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re) A (X * A) -
        xiShiftedCanonicalAdmissionOddCurrent y n =
      2 * xiShiftedCanonicalAdmissionNorm y n *
          xiShiftedCanonicalAdmissionDefectFirstCoeff y n A +
        xiShiftedCanonicalAdmissionDefectOddEnergy y n A := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s n
  let D := A - P
  have hPmono : P.Monic := HTGeometry.monicMomentAdmissionPolynomial_monic s n
  have hPdeg : P.natDegree = n :=
    HTGeometry.monicMomentAdmissionPolynomial_natDegree s n
  have hDdeg : D.natDegree < n :=
    natDegree_sub_lt_of_monic_same_degree hn hA hAdeg hPmono hPdeg
  have hPeq : P = HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hcross : HTGeometry.momentInner s P (X * D) =
      HTGeometry.monicOrthoNormSq s n * D.coeff (n - 1) := by
    rw [hPeq]
    calc
      HTGeometry.momentInner s (HTGeometry.monicOrtho s n) (X * D) =
          HTGeometry.momentInner s (X * D) (HTGeometry.monicOrtho s n) :=
        HTGeometry.momentInner_comm _ _ _
      _ = HTGeometry.momentInner s D (X * HTGeometry.monicOrtho s n) :=
        HTGeometry.momentInner_X_mul _ _ _
      _ = HTGeometry.monicOrthoNormSq s n * D.coeff (n - 1) :=
        momentInner_velocity_X_monicOrtho_eq_norm_mul_coeff_below
          (N := n + 2) (n := n) hbelow hn (by omega) hDdeg
  have hAeq : A = P + D := by
    dsimp only [D]
    ring
  have hcomm : HTGeometry.momentInner s D (X * P) =
      HTGeometry.momentInner s P (X * D) := by
    simp only [HTGeometry.momentInner_def]
    congr 1
    ring
  have hnorm : HTGeometry.momentInner s P P =
      HTGeometry.monicOrthoNormSq s n := by
    rw [hPeq]
    rfl
  have hcoeff : D.coeff (n - 1) =
      A.coeff (n - 1) - P.coeff (n - 1) := by
    rfl
  change HTGeometry.momentInner s A (X * A) -
      HTGeometry.momentInner s P (X * P) =
    2 * HTGeometry.momentInner s P P *
        (A.coeff (n - 1) - P.coeff (n - 1)) +
      HTGeometry.momentInner s D (X * D)
  rw [← hcoeff, hnorm, hAeq, HTGeometry.momentInner_add_left,
    mul_add, HTGeometry.momentInner_add_right,
    HTGeometry.momentInner_add_right, hcomm, hcross]
  ring

/-- Source-mass shear transgression is the literal arithmetic transgression at square mass. -/
theorem xiShiftedAdaptiveShearAdmissionTransgression_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (P A : Polynomial ℝ) :
    xiShiftedAdaptiveShearAdmissionTransgression (w ^ 2) P A =
      xiShiftedAdaptiveArithmeticAdmissionTransgression w P A := by
  rw [xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw,
    ← two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw A,
    ← two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw P]
  unfold xiShiftedAdaptiveShearAdmissionTransgression
  ring

/-- Current canonical odd current differentiates into fixed-amplitude shear plus exactly one
subleading admission-velocity coefficient. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_shear_add_connection
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionOddCurrent v n)
      (-2 * xiShiftedCanonicalAdmissionAdaptiveShear y n +
        2 * xiShiftedCanonicalAdmissionNorm y n *
          (finitePolynomialVelocity
            (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s n
  let V := finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have hcurve := hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet
  have hraw := hasDerivAt_xiShiftedMomentInner_movingOddCurrent hy
    (xiShiftedCanonicalAdmissionCurve n)
    (xiShiftedCanonicalAdmissionVelocity y n) hcurve
  have hPeq : P = HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hVdeg : V.natDegree < n :=
    natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt hn y
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hconnection : HTGeometry.momentInner s V (X * P) =
      HTGeometry.monicOrthoNormSq s n * V.coeff (n - 1) := by
    rw [hPeq]
    exact momentInner_velocity_X_monicOrtho_eq_norm_mul_coeff_below
      hbelow hn (by omega) hVdeg
  have hnorm : xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNormSq s n :=
    xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH
  rw [finitePolynomialCurve_xiShiftedCanonicalAdmission] at hraw
  change HasDerivAt (fun v => xiShiftedCanonicalAdmissionOddCurrent v n)
      (-2 * xiShiftedCanonicalAdmissionAdaptiveShear y n +
        2 * HTGeometry.momentInner s V (X * P)) y at hraw
  rw [hconnection, ← hnorm] at hraw
  exact hraw.congr_deriv (by ring)

/-- **Covariant defect-energy source law.**  Raw inverse-Hankel admission velocity cancels from
mixed source curvature.  Only odd defect-energy drift and canonical norm flux remain. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionDefectOddEnergy
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n) (A : Polynomial ℝ)
    (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionDefectOddEnergy v n A)
      (-xiShiftedAdaptiveShearAdmissionTransgression y
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment y k).re) n) A -
        2 * xiShiftedCanonicalAdmissionNormFlux y n *
          xiShiftedCanonicalAdmissionDefectFirstCoeff y n A) y := by
  let fixedOdd : ℝ → ℝ := fun v => HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment v k).re) A (X * A)
  let currentOdd : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionOddCurrent v n
  let norm : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v n
  let gap : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionDefectFirstCoeff v n A
  let defect : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionDefectOddEnergy v n A
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have hfixed : HasDerivAt fixedOdd
      (-2 * HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)) y := by
    simpa only [fixedOdd] using
      hasDerivAt_xiShiftedMomentInner_oddCrossing_eq_adaptiveShear hy A
  have hcurrent :=
    hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_shear_add_connection
      hy hn hH
  have hnorm :=
    hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det hy hn hdet
  have hfirst :=
    hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy hn hdet
  have hgap : HasDerivAt gap
      (-(finitePolynomialVelocity
        (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)) y := by
    simpa only [gap, xiShiftedCanonicalAdmissionDefectFirstCoeff] using
      hfirst.const_sub (A.coeff (n - 1))
  have hrhs := (hfixed.sub hcurrent).sub ((hnorm.mul hgap).const_mul 2)
  have hposAdd := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hH
  have hshift : Tendsto (fun v : ℝ => v - y) (nhds y) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr tendsto_id
  have hpos : ∀ᶠ v in nhds y,
      (xiShiftedMomentHankelMatrix v (n + 2)).PosDef := by
    filter_upwards [hshift.eventually hposAdd] with v hv
    convert hv using 1 <;> ring
  have heq : defect =ᶠ[nhds y]
      (fun v => fixedOdd v - currentOdd v - 2 * norm v * gap v) := by
    filter_upwards [hpos] with v hv
    have hdecomp :=
      xiShiftedCanonicalAdmission_oddCurrentGap_eq_normCoeff_add_defectEnergy
        hn A hA hAdeg hv
    dsimp only [defect, fixedOdd, currentOdd, norm, gap]
    linarith
  have hderiv :
      (-2 * HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * A) (X * xiShiftedBoundaryShiftedEuler 1 A)) -
        (-2 * xiShiftedCanonicalAdmissionAdaptiveShear y n +
          2 * xiShiftedCanonicalAdmissionNorm y n *
            (finitePolynomialVelocity
              (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1)) -
        2 * (xiShiftedCanonicalAdmissionNormFlux y n *
            xiShiftedCanonicalAdmissionDefectFirstCoeff y n A +
          xiShiftedCanonicalAdmissionNorm y n *
            (-(finitePolynomialVelocity
              (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1))) =
      -xiShiftedAdaptiveShearAdmissionTransgression y
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment y k).re) n) A -
        2 * xiShiftedCanonicalAdmissionNormFlux y n *
          xiShiftedCanonicalAdmissionDefectFirstCoeff y n A := by
    simp only [xiShiftedCanonicalAdmissionAdaptiveShear,
      xiShiftedAdaptiveShearAdmissionTransgression]
    ring
  apply (hrhs.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards [heq] with v hv
  simpa [Pi.sub_apply, Pi.mul_apply, defect, fixedOdd, currentOdd, norm, gap,
    mul_assoc] using hv

end

end RHTower
