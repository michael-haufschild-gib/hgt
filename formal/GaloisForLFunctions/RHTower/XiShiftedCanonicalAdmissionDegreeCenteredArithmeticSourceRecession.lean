import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalCurvatureRecession

/-!
# Recession of the degree-centered arithmetic source

The degree-centered producer has exact positive shifted-arcsine margins: `1/16` in degree one and
`monicScale(n)^2 * 5n/16` above degree one.  Its reciprocal-mass dilation has the same homogeneous
weight as the adaptive source, and coefficientwise canonical admission recession transports these
margins to the literal rational--Gamma-minus-von-Mangoldt source.

Consequently every fixed positive-degree canonical admission eventually has strictly positive
degree-centered arithmetic source.  This is source-native positivity: admission and Euler
centering occur before arithmetic formation, with no orientation map or fixed linear reporter.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Exact prefix sum of shifted-arcsine lower Jacobi edges. -/
theorem sum_monicOrthoBeta_normalizedCentralBinom_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoBeta
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom j) = (n : ℝ) / 16 := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [monicOrthoBeta_normalizedCentralBinom_one]
      norm_num [HTGeometry.monicOrthoBeta]
  | succ n hn ih =>
      rw [Finset.sum_range_succ, ih,
        monicOrthoBeta_normalizedCentralBinom_of_two_le hn]
      push_cast
      ring

/-- Degree-one shifted-arcsine causal history. -/
theorem degreeCenteredOrthoJacobiHistory_normalizedCentralBinom_one :
    HTGeometry.degreeCenteredOrthoJacobiHistory
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom 1 = 1 / 2 := by
  simp [HTGeometry.degreeCenteredOrthoJacobiHistory,
    monicOrthoAlpha_normalizedCentralBinom, HTGeometry.monicOrthoBeta]
  norm_num

/-- Exact shifted-arcsine causal history above the endpoint exception. -/
theorem degreeCenteredOrthoJacobiHistory_normalizedCentralBinom_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    HTGeometry.degreeCenteredOrthoJacobiHistory
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom n = 5 * (n : ℝ) / 8 := by
  rw [HTGeometry.degreeCenteredOrthoJacobiHistory,
    sum_monicOrthoBeta_normalizedCentralBinom_of_two_le hn]
  simp_rw [monicOrthoAlpha_normalizedCentralBinom]
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Exact monic shifted-arcsine norm in orthogonal-polynomial coordinates. -/
theorem monicOrthoNormSq_normalizedCentralBinom
    {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.monicOrthoNormSq
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom n =
        Arc.monicScale n ^ 2 / 2 := by
  rw [HTGeometry.monicOrthoNormSq, HTGeometry.momentInner_self,
    monicOrtho_normalizedCentralBinom_eq_arc_amplitude,
    XiShiftedArcsineAdmission.momentFunctional_amplitude_sq hn]

/-- Degree-one centered-source shifted-arcsine margin. -/
theorem momentFunctional_degreeCenteredShear_arc_amplitude_one :
    HTGeometry.momentFunctional
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom
      (xiShiftedBoundaryDegreeCenteredShearPolynomial 1 (Arc.amplitude 1)) =
        1 / 16 := by
  rw [← monicOrtho_normalizedCentralBinom_eq_arc_amplitude,
    xiShiftedBoundaryDegreeCenteredShearPolynomial_monicOrtho,
    HTGeometry.momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm (by omega),
    degreeCenteredOrthoJacobiHistory_normalizedCentralBinom_one,
    monicOrthoNormSq_normalizedCentralBinom (by omega)]
  norm_num [Arc.monicScale, XiShiftedArcsineAdmission.monicScale]

/-- Positive-degree centered-source shifted-arcsine margin above degree one. -/
theorem momentFunctional_degreeCenteredShear_arc_amplitude_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    HTGeometry.momentFunctional
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom
      (xiShiftedBoundaryDegreeCenteredShearPolynomial n (Arc.amplitude n)) =
        Arc.monicScale n ^ 2 * (5 * (n : ℝ)) / 16 := by
  rw [← monicOrtho_normalizedCentralBinom_eq_arc_amplitude,
    xiShiftedBoundaryDegreeCenteredShearPolynomial_monicOrtho,
    HTGeometry.momentFunctional_degreeCenteredOrthoSourcePolynomial_eq_jacobiHistory
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm (by omega),
    degreeCenteredOrthoJacobiHistory_normalizedCentralBinom_of_two_le hn,
    monicOrthoNormSq_normalizedCentralBinom (by omega)]
  ring

/-- Centered-source shifted-arcsine margin is positive in every positive degree. -/
theorem momentFunctional_degreeCenteredShear_arc_amplitude_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < HTGeometry.momentFunctional
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom
      (xiShiftedBoundaryDegreeCenteredShearPolynomial n (Arc.amplitude n)) := by
  rcases n with _ | _ | n
  · exact (hn rfl).elim
  · rw [momentFunctional_degreeCenteredShear_arc_amplitude_one]
    norm_num
  · rw [momentFunctional_degreeCenteredShear_arc_amplitude_of_two_le (by omega)]
    have hs : 0 < Arc.monicScale (n + 2) := by
      unfold Arc.monicScale XiShiftedArcsineAdmission.monicScale
      positivity
    positivity

/-- Degree-centered shear is quadratic in amplitude. -/
theorem degreeCenteredShear_smul (c : ℝ) (n : ℕ) (Q : Polynomial ℝ) :
    xiShiftedBoundaryDegreeCenteredShearPolynomial n (c • Q) =
      c ^ 2 • xiShiftedBoundaryDegreeCenteredShearPolynomial n Q := by
  simp only [xiShiftedBoundaryDegreeCenteredShearPolynomial,
    xiShiftedBoundaryDegreeCenteredEuler, Polynomial.smul_eq_C_mul,
    Polynomial.derivative_C_mul]
  rw [Polynomial.C_pow]
  ring

/-- Coordinate dilation covariance of degree-centered shear. -/
theorem degreeCenteredShear_comp_C_mul_X
    {d : ℝ} (n : ℕ) (Q : Polynomial ℝ) :
    d ^ 2 • xiShiftedBoundaryDegreeCenteredShearPolynomial n
        (Q.comp (Polynomial.C d * X)) =
      (xiShiftedBoundaryDegreeCenteredShearPolynomial n Q).comp
        (Polynomial.C d * X) := by
  simp only [xiShiftedBoundaryDegreeCenteredShearPolynomial,
    xiShiftedBoundaryDegreeCenteredEuler, Polynomial.derivative_comp,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, Polynomial.mul_comp,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    Polynomial.smul_eq_C_mul]
  rw [Polynomial.C_pow]
  ring

/-- Exact reciprocal-mass homogeneous weight of degree-centered shear. -/
theorem degreeCenteredShear_sourceCoordinateDilation
    {w : ℝ} (hw : w ≠ 0) (n : ℕ) (Q : Polynomial ℝ) :
    xiShiftedBoundaryDegreeCenteredShearPolynomial n
        ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X)) =
      (w ^ (4 * n + 4))⁻¹ •
        (xiShiftedBoundaryDegreeCenteredShearPolynomial n Q).comp
          (Polynomial.C (w ^ 2) * X) := by
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero _ hw
  rw [degreeCenteredShear_smul]
  have hcomp := degreeCenteredShear_comp_C_mul_X (d := w ^ 2) n Q
  have hscalar : (w ^ (2 * n))⁻¹ ^ 2 =
      (w ^ (4 * n + 4))⁻¹ * (w ^ 2) ^ 2 := by
    field_simp [hw]
    ring
  rw [hscalar, mul_smul, hcomp]

/-- Exact source-first mass-dilation law for literal degree-centered arithmetic formation. -/
theorem scaled_degreeCenteredArithmeticSource_sourceCoordinateDilation
    {w : ℝ} (hw : 1 < w) (n : ℕ) (Q : Polynomial ℝ) :
    w ^ (4 * n + 5) / Real.log w *
        xiShiftedDegreeCenteredCompletedArithmeticSource w n
          ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X)) =
      HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
        (xiShiftedBoundaryDegreeCenteredShearPolynomial n Q) := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  have hsource := xiShiftedDegreeCenteredCompletedArithmeticSource_eq_momentFunctional
    (by linarith : 1 / 2 < w) n
      ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X))
  rw [degreeCenteredShear_sourceCoordinateDilation hw0 n Q,
    HTGeometry.momentFunctional_smul] at hsource
  unfold xiShiftedRealMomentSequence at hsource
  have hnorm := momentFunctional_normalized_eq_massDilation hw
    (xiShiftedBoundaryDegreeCenteredShearPolynomial n Q)
  rw [hsource, hnorm]
  field_simp [hw0, hlog]
  ring

/-- Coordinate multiplication and squaring preserve coefficientwise convergence. -/
theorem tendsto_X_mul_sq_coeff
    {α : Type*} {l : Filter α} {F : α → Polynomial ℝ} {P : Polynomial ℝ}
    (hcoeff : ∀ k, Tendsto (fun x => (F x).coeff k) l (nhds (P.coeff k)))
    (k : ℕ) :
    Tendsto (fun x => (((X * F x) ^ 2).coeff k)) l
      (nhds (((X * P) ^ 2).coeff k)) := by
  apply tendsto_sq_coeff (P := X * P)
  intro r
  cases r with
  | zero =>
      simpa using (tendsto_const_nhds :
        Tendsto (fun _ : α => (0 : ℝ)) l (nhds 0))
  | succ r =>
      simpa [Nat.succ_eq_add_one] using hcoeff r

/-- Coefficients of degree-centered shear vary continuously with admitted amplitude. -/
theorem tendsto_degreeCenteredShear_coeff
    {α : Type*} {l : Filter α} {F : α → Polynomial ℝ} {P : Polynomial ℝ}
    (hcoeff : ∀ k, Tendsto (fun x => (F x).coeff k) l (nhds (P.coeff k)))
    (n k : ℕ) :
    Tendsto
      (fun x => (xiShiftedBoundaryDegreeCenteredShearPolynomial n (F x)).coeff k) l
      (nhds ((xiShiftedBoundaryDegreeCenteredShearPolynomial n P).coeff k)) := by
  have ha := tendsto_adaptiveShear_coeff hcoeff k
  have hx := tendsto_X_mul_sq_coeff hcoeff k
  rw [show (fun x =>
      (xiShiftedBoundaryDegreeCenteredShearPolynomial n (F x)).coeff k) =
      (fun x =>
        (xiShiftedBoundaryAdaptiveShearPolynomial (F x)).coeff k -
          (n + 1 : ℝ) * (((X * F x) ^ 2).coeff k)) by
      funext x
      rw [xiShiftedBoundaryDegreeCenteredShearPolynomial_eq_adaptive_sub_square,
        Polynomial.coeff_sub, Polynomial.coeff_smul]
      simp only [smul_eq_mul]]
  rw [show (xiShiftedBoundaryDegreeCenteredShearPolynomial n P).coeff k =
      (xiShiftedBoundaryAdaptiveShearPolynomial P).coeff k -
        (n + 1 : ℝ) * (((X * P) ^ 2).coeff k) by
      rw [xiShiftedBoundaryDegreeCenteredShearPolynomial_eq_adaptive_sub_square,
        Polynomial.coeff_sub, Polynomial.coeff_smul]
      simp only [smul_eq_mul]]
  exact ha.sub (hx.const_mul (n + 1 : ℝ))

/-- Normalized canonical centered source converges to its exact arcsine source. -/
theorem tendsto_dimensionlessAdmission_degreeCenteredShearMoment
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ =>
        HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
          (xiShiftedBoundaryDegreeCenteredShearPolynomial n
            (dimensionlessAdmission w n)))
      atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryDegreeCenteredShearPolynomial n (Arc.amplitude n)))) := by
  let N := 2 * n + 1
  have hterms : ∀ k ∈ Finset.range (N + 1),
      Tendsto
        (fun w : ℝ =>
          (xiShiftedBoundaryDegreeCenteredShearPolynomial n
            (dimensionlessAdmission w n)).coeff k *
              xiShiftedFarRightNormalizedMoment w k)
        atTop
        (nhds ((xiShiftedBoundaryDegreeCenteredShearPolynomial n
            (Arc.amplitude n)).coeff k *
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom k)) := by
    intro k _
    exact (tendsto_degreeCenteredShear_coeff
      (fun j => tendsto_dimensionlessAdmission_coeff hn j) n k).mul
        (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam k)
  have hsum := tendsto_finsetSum (Finset.range (N + 1)) hterms
  have hdegXi : ∀ w : ℝ,
      (xiShiftedBoundaryDegreeCenteredShearPolynomial n
        (dimensionlessAdmission w n)).natDegree ≤ N := by
    intro w
    exact natDegree_xiShiftedBoundaryDegreeCenteredShearPolynomial_le
      (Nat.pos_of_ne_zero hn) (dimensionlessAdmission_natDegree w n)
  have hdegArc :
      (xiShiftedBoundaryDegreeCenteredShearPolynomial n
        (Arc.amplitude n)).natDegree ≤ N :=
    natDegree_xiShiftedBoundaryDegreeCenteredShearPolynomial_le
      (Nat.pos_of_ne_zero hn) (amplitude_natDegree hn)
  simpa only [momentFunctional_eq_sum_range_of_natDegree_le
      (s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom) hdegArc] using
    hsum.congr' (Filter.Eventually.of_forall fun w => by
      rw [momentFunctional_eq_sum_range_of_natDegree_le
        (s := xiShiftedFarRightNormalizedMoment w) (hdegXi w)])

/-- Fixed-degree literal centered arithmetic source has exact positive arcsine recession. -/
theorem tendsto_scaled_canonicalDegreeCenteredArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ => w ^ (4 * n + 5) / Real.log w *
        xiShiftedDegreeCenteredCompletedArithmeticSource w n
          (sourceCoordinateAdmission w n))
      atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryDegreeCenteredShearPolynomial n (Arc.amplitude n)))) := by
  apply tendsto_dimensionlessAdmission_degreeCenteredShearMoment hn |>.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  exact (scaled_degreeCenteredArithmeticSource_sourceCoordinateDilation hw n
    (dimensionlessAdmission w n)).symm

theorem tendsto_scaled_canonicalDegreeCenteredArithmeticSource_one :
    Tendsto
      (fun w : ℝ => w ^ 9 / Real.log w *
        xiShiftedDegreeCenteredCompletedArithmeticSource w 1
          (sourceCoordinateAdmission w 1))
      atTop (nhds (1 / 16 : ℝ)) := by
  have h := tendsto_scaled_canonicalDegreeCenteredArithmeticSource
    (n := 1) (by omega)
  rw [momentFunctional_degreeCenteredShear_arc_amplitude_one] at h
  simpa using h

theorem tendsto_scaled_canonicalDegreeCenteredArithmeticSource_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    Tendsto
      (fun w : ℝ => w ^ (4 * n + 5) / Real.log w *
        xiShiftedDegreeCenteredCompletedArithmeticSource w n
          (sourceCoordinateAdmission w n))
      atTop (nhds (Arc.monicScale n ^ 2 * (5 * (n : ℝ)) / 16)) := by
  have h := tendsto_scaled_canonicalDegreeCenteredArithmeticSource
    (n := n) (by omega)
  rw [momentFunctional_degreeCenteredShear_arc_amplitude_of_two_le hn] at h
  exact h

/-- **Fixed-degree producer theorem.**  Every fixed positive-degree canonical shifted-Xi
admission eventually lands in strictly positive literal degree-centered arithmetic source. -/
theorem canonicalDegreeCenteredArithmeticSource_eventually_pos
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedDegreeCenteredCompletedArithmeticSource w n
        (sourceCoordinateAdmission w n) := by
  have hmargin := momentFunctional_degreeCenteredShear_arc_amplitude_pos hn
  have hscaled := (tendsto_scaled_canonicalDegreeCenteredArithmeticSource hn).eventually
    (Ioi_mem_nhds hmargin)
  filter_upwards [hscaled, eventually_gt_atTop (1 : ℝ)] with w hs hw
  have hfactor : 0 < w ^ (4 * n + 5) / Real.log w :=
    div_pos (pow_pos (lt_trans zero_lt_one hw) _) (Real.log_pos hw)
  rcases mul_pos_iff.mp hs with h | h
  · exact h.2
  · exact (not_lt_of_ge hfactor.le h.1).elim

/-! ## Trace-coupled producer recession -/

/-- Exact negative next coefficient of every positive-degree monic shifted-arcsine admission. -/
theorem arc_amplitude_nextCoeff
    {n : ℕ} (hn : n ≠ 0) :
    (Arc.amplitude n).nextCoeff = -(n : ℝ) / 2 := by
  rw [← monicOrtho_normalizedCentralBinom_eq_arc_amplitude]
  have hnext : (HTGeometry.monicOrtho
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom n).nextCoeff =
      HTGeometry.monicOrthoFirstCoeff
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Polynomial.nextCoeff_of_natDegree_pos]
    · simp [HTGeometry.natDegree_monicOrtho, HTGeometry.monicOrthoFirstCoeff]
    · rw [HTGeometry.natDegree_monicOrtho]
      omega
  rw [hnext, HTGeometry.monicOrthoFirstCoeff_eq_neg_sum
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm]
  simp_rw [monicOrthoAlpha_normalizedCentralBinom]
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Canonical dimensionless admission next coefficient converges to its exact arcsine trace. -/
theorem tendsto_dimensionlessAdmission_nextCoeff
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => (dimensionlessAdmission w n).nextCoeff)
      atTop (nhds ((Arc.amplitude n).nextCoeff)) := by
  have hcoeff := tendsto_dimensionlessAdmission_coeff hn (n - 1)
  have hfun : (fun w : ℝ => (dimensionlessAdmission w n).nextCoeff) =
      (fun w : ℝ => (dimensionlessAdmission w n).coeff (n - 1)) := by
    funext w
    rw [Polynomial.nextCoeff_of_natDegree_pos]
    · rw [dimensionlessAdmission_natDegree]
    · rw [dimensionlessAdmission_natDegree]
      exact Nat.pos_of_ne_zero hn
  have harc : (Arc.amplitude n).nextCoeff = (Arc.amplitude n).coeff (n - 1) := by
    rw [Polynomial.nextCoeff_of_natDegree_pos]
    · rw [amplitude_natDegree hn]
    · rw [amplitude_natDegree hn]
      exact Nat.pos_of_ne_zero hn
  rw [hfun, harc]
  exact hcoeff

/-- Exact reciprocal-mass weight of the actual admission trace. -/
theorem sourceCoordinateAdmission_nextCoeff
    {w : ℝ} (hw : w ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (sourceCoordinateAdmission w n).nextCoeff =
      (w ^ 2)⁻¹ * (dimensionlessAdmission w n).nextCoeff := by
  have hnpos := Nat.pos_of_ne_zero hn
  have hsourceDeg : (sourceCoordinateAdmission w n).natDegree = n :=
    sourceCoordinateAdmission_natDegree hw hn
  have hdimDeg : (dimensionlessAdmission w n).natDegree = n :=
    dimensionlessAdmission_natDegree w n
  have hsourcePos : 0 < (sourceCoordinateAdmission w n).natDegree := by
    rw [hsourceDeg]
    exact hnpos
  have hdimPos : 0 < (dimensionlessAdmission w n).natDegree := by
    rw [hdimDeg]
    exact hnpos
  rw [Polynomial.nextCoeff_of_natDegree_pos hsourcePos, hsourceDeg,
    sourceCoordinateAdmission_coeff_prev hw hnpos,
    Polynomial.nextCoeff_of_natDegree_pos hdimPos, hdimDeg]

/-- Exact mass completion of the source-first trace-coupled producer. -/
theorem scaled_traceCoupledDegreeCenteredArithmeticSource_sourceCoordinateAdmission
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : n ≠ 0) :
    w ^ (4 * n + 7) / Real.log w *
        xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w n
          (sourceCoordinateAdmission w n) =
      -(dimensionlessAdmission w n).nextCoeff *
        (w ^ (4 * n + 5) / Real.log w *
          xiShiftedDegreeCenteredCompletedArithmeticSource w n
            (sourceCoordinateAdmission w n)) := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  rw [xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource_eq_mul
      (by linarith : 1 / 2 < w),
    sourceCoordinateAdmission_nextCoeff hw0 hn]
  field_simp [hw0, hlog]
  ring

/-- Trace-coupled literal source retains the positive arcsine trace times centered margin. -/
theorem tendsto_scaled_canonicalTraceCoupledDegreeCenteredArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ => w ^ (4 * n + 7) / Real.log w *
        xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w n
          (sourceCoordinateAdmission w n))
      atTop
      (nhds ((n : ℝ) / 2 *
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          (xiShiftedBoundaryDegreeCenteredShearPolynomial n (Arc.amplitude n)))) := by
  have hnext := (tendsto_dimensionlessAdmission_nextCoeff hn).neg
  rw [arc_amplitude_nextCoeff hn] at hnext
  have h := hnext.mul (tendsto_scaled_canonicalDegreeCenteredArithmeticSource hn)
  have hlimit : -(-(n : ℝ) / 2) *
      HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryDegreeCenteredShearPolynomial n (Arc.amplitude n)) =
      (n : ℝ) / 2 *
      HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryDegreeCenteredShearPolynomial n (Arc.amplitude n)) := by ring
  rw [hlimit] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  exact (scaled_traceCoupledDegreeCenteredArithmeticSource_sourceCoordinateAdmission
    hw hn).symm

theorem tendsto_scaled_canonicalTraceCoupledDegreeCenteredArithmeticSource_one :
    Tendsto
      (fun w : ℝ => w ^ 11 / Real.log w *
        xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w 1
          (sourceCoordinateAdmission w 1))
      atTop (nhds (1 / 32 : ℝ)) := by
  have h := tendsto_scaled_canonicalTraceCoupledDegreeCenteredArithmeticSource
    (n := 1) (by omega)
  rw [momentFunctional_degreeCenteredShear_arc_amplitude_one] at h
  norm_num at h ⊢
  exact h

theorem tendsto_scaled_canonicalTraceCoupledDegreeCenteredArithmeticSource_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    Tendsto
      (fun w : ℝ => w ^ (4 * n + 7) / Real.log w *
        xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w n
          (sourceCoordinateAdmission w n))
      atTop (nhds (Arc.monicScale n ^ 2 * (5 * (n : ℝ) ^ 2) / 32)) := by
  have h := tendsto_scaled_canonicalTraceCoupledDegreeCenteredArithmeticSource
    (n := n) (by omega)
  rw [momentFunctional_degreeCenteredShear_arc_amplitude_of_two_le hn] at h
  convert h using 1
  ring_nf

/-- Actual fixed-degree admission trace is eventually strictly positive after negation. -/
theorem sourceCoordinateAdmission_nextCoeff_eventually_neg
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop, (sourceCoordinateAdmission w n).nextCoeff < 0 := by
  have hnext := tendsto_dimensionlessAdmission_nextCoeff hn
  rw [arc_amplitude_nextCoeff hn] at hnext
  have hneg : -(n : ℝ) / 2 < 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    linarith
  have hdim := hnext.eventually (Iio_mem_nhds hneg)
  filter_upwards [hdim, eventually_gt_atTop (1 : ℝ)] with w hcoeff hw
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  rw [sourceCoordinateAdmission_nextCoeff hw0 hn]
  exact mul_neg_of_pos_of_neg
    (inv_pos.mpr (sq_pos_of_pos (lt_trans zero_lt_one hw))) hcoeff

/-- **Trace-coupled fixed-degree producer theorem.**  Every fixed canonical admission eventually
lands in strictly positive literal trace-coupled source, while every first crossing makes the same
producer nonpositive. -/
theorem canonicalTraceCoupledDegreeCenteredArithmeticSource_eventually_pos
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource w n
        (sourceCoordinateAdmission w n) := by
  filter_upwards [sourceCoordinateAdmission_nextCoeff_eventually_neg hn,
    canonicalDegreeCenteredArithmeticSource_eventually_pos hn,
    eventually_gt_atTop (1 : ℝ)] with w hnext hcenter hw
  rw [xiShiftedTraceCoupledDegreeCenteredCompletedArithmeticSource_eq_mul
    (by linarith : 1 / 2 < w)]
  exact mul_pos (neg_pos.mpr hnext) hcenter

end
end XiShiftedCanonicalAdmission
end RHTower
