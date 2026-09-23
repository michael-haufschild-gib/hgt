import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionArithmeticTransgression
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession

/-!
# Covariant defect energy for frozen/current shifted-Xi admission

The mixed mass--admission source debt has an exact connection-free primitive.  If `P_y` is current
canonical monic admission, `A` is a fixed monic amplitude of the same degree, and `D_y=A-P_y`,
then the completed source transgression is

`T_y(P_y,A) = -d/dy L_y(X D_y^(2 : ℕ)) - 2 h_y' [X^(n-1)]D_y`.

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

/-- Literal rational--Gamma/von Mangoldt form of covariant defect-source density at square mass. -/
def xiShiftedCanonicalAdmissionArithmeticDefectSourceDensity
    (w : ℝ) (n : ℕ) (A : Polynomial ℝ) : ℝ :=
  xiShiftedAdaptiveArithmeticAdmissionTransgression w
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n) A +
    2 * xiShiftedCanonicalAdmissionNormFlux (w ^ (2 : ℕ)) n *
      xiShiftedCanonicalAdmissionDefectFirstCoeff (w ^ (2 : ℕ)) n A

/-- Every fixed finite adaptive shear packet is continuous in positive source mass. -/
theorem continuousAt_xiShiftedFixedAdaptiveShearMoment
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ) :
    ContinuousAt (fun v => HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment v k).re)
      (xiShiftedBoundaryAdaptiveShearPolynomial A)) y := by
  let Q := xiShiftedBoundaryAdaptiveShearPolynomial A
  have hsum : Tendsto
      (fun v => ∑ k ∈ Q.support, Q.coeff k *
        (xiShiftedReciprocalMoment v k).re) (nhds y)
      (nhds (∑ k ∈ Q.support, Q.coeff k *
        (xiShiftedReciprocalMoment y k).re)) := by
    apply tendsto_finsetSum
    intro k _
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => Q.coeff k)
      (nhds y) (nhds (Q.coeff k))).mul
        (hasDerivAt_re_xiShiftedReciprocalMoment hy k).continuousAt
  change Tendsto
    (fun v => HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment v k).re) Q) (nhds y)
    (nhds (HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) Q))
  simpa only [HTGeometry.momentFunctional_eq_support_sum, Q] using hsum

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
  convert hsum using 1
  · funext v
    exact XiShiftedCanonicalAdmission.momentFunctional_eq_sum_range_of_natDegree_le
      (s := fun k => (xiShiftedReciprocalMoment v k).re)
      (P := Q v) (N := N) (hdeg v)
  · exact congrArg nhds
      (XiShiftedCanonicalAdmission.momentFunctional_eq_sum_range_of_natDegree_le
        (s := fun k => (xiShiftedReciprocalMoment y k).re)
        (P := Q y) (N := N) (hdeg y))

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
    xiShiftedAdaptiveShearAdmissionTransgression (w ^ (2 : ℕ)) P A =
      xiShiftedAdaptiveArithmeticAdmissionTransgression w P A := by
  rw [xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw,
    ← two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw A,
    ← two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw P]
  unfold xiShiftedAdaptiveShearAdmissionTransgression
  ring

/-- Covariant density really is the literal completed arithmetic source formation at square mass,
plus its canonical norm connection. -/
theorem xiShiftedCanonicalAdmissionDefectSourceDensity_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (A : Polynomial ℝ) :
    xiShiftedCanonicalAdmissionDefectSourceDensity (w ^ (2 : ℕ)) n A =
      xiShiftedCanonicalAdmissionArithmeticDefectSourceDensity w n A := by
  rw [xiShiftedCanonicalAdmissionDefectSourceDensity,
    xiShiftedCanonicalAdmissionArithmeticDefectSourceDensity,
    xiShiftedAdaptiveShearAdmissionTransgression_sq_eq_arithmetic hw]

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
    have heq : y + (v - y) = v := by ring
    rw [heq] at hv
    exact hv
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

/-- Compact form of the covariant law: defect energy derivative is minus total source density. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionDefectOddEnergy_eq_neg_sourceDensity
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n) (A : Polynomial ℝ)
    (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionDefectOddEnergy v n A)
      (-xiShiftedCanonicalAdmissionDefectSourceDensity y n A) y := by
  have h := hasDerivAt_xiShiftedCanonicalAdmissionDefectOddEnergy
    hy hn A hA hAdeg hH
  apply h.congr_deriv
  simp only [xiShiftedCanonicalAdmissionDefectSourceDensity]
  ring

/-- **Literal arithmetic producer law.**  At square mass, odd defect-energy derivative is minus
the rational--Gamma/von Mangoldt admission transgression with its forced canonical connection. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionDefectOddEnergy_eq_neg_arithmeticSourceDensity_sq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n) (A : Polynomial ℝ)
    (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef) :
    HasDerivAt (fun y => xiShiftedCanonicalAdmissionDefectOddEnergy y n A)
      (-xiShiftedCanonicalAdmissionArithmeticDefectSourceDensity w n A) (w ^ (2 : ℕ)) := by
  have hwpos : 0 < w := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hw
  have h := hasDerivAt_xiShiftedCanonicalAdmissionDefectOddEnergy_eq_neg_sourceDensity
    (sq_pos_of_pos hwpos) hn A hA hAdeg hH
  apply h.congr_deriv
  rw [xiShiftedCanonicalAdmissionDefectSourceDensity_sq_eq_arithmetic hw]

/-- Literal frozen/current adaptive-shear transgression is continuous wherever current admission
is nonsingular. -/
theorem continuousAt_xiShiftedAdaptiveShearAdmissionTransgression
    {y : ℝ} (hy : 0 < y) (n : ℕ) (A : Polynomial ℝ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    ContinuousAt (fun v => xiShiftedAdaptiveShearAdmissionTransgression v
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n) A) y := by
  have hfixed := continuousAt_xiShiftedFixedAdaptiveShearMoment hy A
  have hcurrent :=
    continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment hy n hdet
  have h := (hfixed.sub hcurrent).const_mul 2
  simpa only [xiShiftedAdaptiveShearAdmissionTransgression,
    HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial,
    Pi.sub_apply] using h

/-- Canonical norm flux is continuous on every positive nonsingular admission chamber. -/
theorem continuousAt_xiShiftedCanonicalAdmissionNormFlux
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    ContinuousAt (fun v => xiShiftedCanonicalAdmissionNormFlux v n) y := by
  have hfirst :=
    (hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy hn hdet).continuousAt
  have hnorm :=
    (hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
      hy hn hdet).continuousAt
  have hcurrent :=
    (hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_shear_add_connection
      hy hn hH).continuousAt
  have h := ((hfirst.mul hnorm).const_mul 2).sub
    (hcurrent.const_mul (((2 * n + 1 : ℕ) : ℝ)))
  unfold xiShiftedCanonicalAdmissionNormFlux
  convert h using 1
  funext v
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

/-- Total covariant source density is continuous on every positive finite Hankel chamber. -/
theorem continuousAt_xiShiftedCanonicalAdmissionDefectSourceDensity
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n) (A : Polynomial ℝ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    ContinuousAt (fun v =>
      xiShiftedCanonicalAdmissionDefectSourceDensity v n A) y := by
  have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH
  have htrans := continuousAt_xiShiftedAdaptiveShearAdmissionTransgression
    hy n A hdet
  have hflux := continuousAt_xiShiftedCanonicalAdmissionNormFlux
    hy hn hdet hH
  have hfirst :=
    (hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy hn hdet).continuousAt
  have hgap : ContinuousAt (fun v =>
      xiShiftedCanonicalAdmissionDefectFirstCoeff v n A) y := by
    change Tendsto
      (fun v => A.coeff (n - 1) - xiShiftedCanonicalAdmissionFirstCoeff v n)
      (nhds y)
      (nhds (A.coeff (n - 1) - xiShiftedCanonicalAdmissionFirstCoeff y n))
    exact hfirst.const_sub (A.coeff (n - 1))
  have h := htrans.add ((hflux.mul hgap).const_mul 2)
  unfold xiShiftedCanonicalAdmissionDefectSourceDensity
  convert h using 1
  funext v
  simp only [Pi.mul_apply, Pi.add_apply]
  ring

/-- On a positive compact admission chamber, total covariant source density is continuous. -/
theorem continuousOn_xiShiftedCanonicalAdmissionDefectSourceDensity_Icc
    {a b : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n)
    (A : Polynomial ℝ)
    (hH : ∀ y ∈ Set.Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    ContinuousOn (fun y =>
      xiShiftedCanonicalAdmissionDefectSourceDensity y n A) (Set.Icc a b) := by
  intro y hy
  exact (continuousAt_xiShiftedCanonicalAdmissionDefectSourceDensity
    (lt_of_lt_of_le ha hy.1) hn A (hH y hy)).continuousWithinAt

/-- **Exact covariant debt budget.**  Integrated adaptive source debt equals loss of odd defect
energy.  No admission velocity, reporter, or reflection aggregate survives. -/
theorem intervalIntegral_xiShiftedCanonicalAdmissionDefectSourceDensity_eq_energy_sub
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {n : ℕ} (hn : 0 < n)
    (A : Polynomial ℝ) (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hH : ∀ y ∈ Set.Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (∫ y in a..b, xiShiftedCanonicalAdmissionDefectSourceDensity y n A) =
      xiShiftedCanonicalAdmissionDefectOddEnergy a n A -
        xiShiftedCanonicalAdmissionDefectOddEnergy b n A := by
  let E : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionDefectOddEnergy y n A
  let S : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionDefectSourceDensity y n A
  have hpoint : ∀ y ∈ Set.uIcc a b, HasDerivAt E (-S y) y := by
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    exact hasDerivAt_xiShiftedCanonicalAdmissionDefectOddEnergy_eq_neg_sourceDensity
      (lt_of_lt_of_le ha hy.1) hn A hA hAdeg (hH y hy)
  have hdiff : ∀ y ∈ Set.uIcc a b, DifferentiableAt ℝ E y :=
    fun y hy => (hpoint y hy).differentiableAt
  have hderiv : Set.EqOn (deriv E) (fun y => -S y) (Set.uIcc a b) :=
    fun y hy => (hpoint y hy).deriv
  have hcontS : ContinuousOn S (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_xiShiftedCanonicalAdmissionDefectSourceDensity_Icc
      ha hn A hH
  have hcontDeriv : ContinuousOn (deriv E) (Set.uIcc a b) :=
    hcontS.neg.congr fun y hy => hderiv hy
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff
    hcontDeriv.intervalIntegrable
  have hint : (∫ y in a..b, -S y) = E b - E a := by
    calc
      (∫ y in a..b, -S y) = ∫ y in a..b, deriv E y :=
        intervalIntegral.integral_congr fun y hy => (hderiv hy).symm
      _ = E b - E a := hfund
  calc
    (∫ y in a..b, xiShiftedCanonicalAdmissionDefectSourceDensity y n A) =
        -(∫ y in a..b, -S y) := by
      rw [intervalIntegral.integral_neg]
      simp only [S]
      ring
    _ = _ := by rw [hint]; simp only [E]; ring

/-- **Actual integral Lipschitz theorem.**  Defect-energy displacement is bounded by the `L¹`
mass of the admission-sensitive arithmetic source density. -/
theorem abs_xiShiftedCanonicalAdmissionDefectOddEnergy_sub_le_integral_abs_sourceDensity
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {n : ℕ} (hn : 0 < n)
    (A : Polynomial ℝ) (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hH : ∀ y ∈ Set.Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    |xiShiftedCanonicalAdmissionDefectOddEnergy b n A -
        xiShiftedCanonicalAdmissionDefectOddEnergy a n A| ≤
      ∫ y in a..b, |xiShiftedCanonicalAdmissionDefectSourceDensity y n A| := by
  have hexact :=
    intervalIntegral_xiShiftedCanonicalAdmissionDefectSourceDensity_eq_energy_sub
      ha hab hn A hA hAdeg hH
  calc
    |xiShiftedCanonicalAdmissionDefectOddEnergy b n A -
        xiShiftedCanonicalAdmissionDefectOddEnergy a n A| =
        |∫ y in a..b, xiShiftedCanonicalAdmissionDefectSourceDensity y n A| := by
      rw [hexact]
      exact abs_sub_comm _ _
    _ ≤ ∫ y in a..b, |xiShiftedCanonicalAdmissionDefectSourceDensity y n A| :=
      intervalIntegral.abs_integral_le_integral_abs hab

/-- Uniform source control gives a literal Lipschitz constant for odd defect energy. -/
theorem abs_xiShiftedCanonicalAdmissionDefectOddEnergy_sub_le_mul
    {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b) {n : ℕ} (hn : 0 < n)
    (A : Polynomial ℝ) (hA : A.Monic) (hAdeg : A.natDegree = n)
    (hH : ∀ y ∈ Set.Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hC : ∀ y ∈ Set.Icc a b,
      |xiShiftedCanonicalAdmissionDefectSourceDensity y n A| ≤ C) :
    |xiShiftedCanonicalAdmissionDefectOddEnergy b n A -
        xiShiftedCanonicalAdmissionDefectOddEnergy a n A| ≤ C * (b - a) := by
  have hexact :=
    intervalIntegral_xiShiftedCanonicalAdmissionDefectSourceDensity_eq_energy_sub
      ha hab hn A hA hAdeg hH
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b)
    (f := fun y => xiShiftedCanonicalAdmissionDefectSourceDensity y n A) (C := C)
    (fun y hy => by
      simpa only [Real.norm_eq_abs] using hC y (by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hy))
  calc
    |xiShiftedCanonicalAdmissionDefectOddEnergy b n A -
        xiShiftedCanonicalAdmissionDefectOddEnergy a n A| =
        ‖∫ y in a..b, xiShiftedCanonicalAdmissionDefectSourceDensity y n A‖ := by
      rw [hexact, Real.norm_eq_abs]
      exact abs_sub_comm _ _
    _ ≤ C * |b - a| := hbound
    _ = C * (b - a) := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]

/-- **Frozen-admission debt identity.**  Freezing the comparator at the left endpoint annihilates
initial defect energy, so integrated source debt is exactly negative terminal odd defect energy. -/
theorem intervalIntegral_xiShiftedCanonicalFrozenAdmissionDefectSourceDensity_eq_neg_energy
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Set.Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    let A := HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment a k).re) n
    (∫ y in a..b, xiShiftedCanonicalAdmissionDefectSourceDensity y n A) =
      -xiShiftedCanonicalAdmissionDefectOddEnergy b n A := by
  let A := HTGeometry.monicMomentAdmissionPolynomial
    (fun k => (xiShiftedReciprocalMoment a k).re) n
  have hA : A.Monic := HTGeometry.monicMomentAdmissionPolynomial_monic _ _
  have hAdeg : A.natDegree = n :=
    HTGeometry.monicMomentAdmissionPolynomial_natDegree _ _
  have hexact :=
    intervalIntegral_xiShiftedCanonicalAdmissionDefectSourceDensity_eq_energy_sub
      ha hab hn A hA hAdeg hH
  have hzero : xiShiftedCanonicalAdmissionDefectOddEnergy a n A = 0 := by
    simp only [xiShiftedCanonicalAdmissionDefectOddEnergy,
      xiShiftedCanonicalAdmissionDefect, A, sub_self,
      HTGeometry.momentInner_zero_left]
  simpa only [hzero, zero_sub] using hexact

end

end RHTower
