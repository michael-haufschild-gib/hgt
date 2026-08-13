import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRecession

/-!
# Canonical shifted-Xi admission lands in a positive arithmetic source

The dimensionless inverse-Hankel admission is pulled back to the reciprocal-mass coordinate before
the adaptive bilinear landing.  The landing obeys an exact mass-dilation identity: after scaling by
`w^(4n+5)/log w`, the literal rational-Gamma-minus-von-Mangoldt source is exactly the normalized
Xi moment functional of the dimensionless adaptive shear.

Coefficientwise admission convergence then gives a fixed-degree source recession to the exact
positive arcsine margin.  No reflection reporter or orientation map intervenes.  The only
remaining obstruction is degree escape, because the already-proved margins collapse as
`(2n+3/4)16^(-n)`.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower

namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Pull the dimensionless monic admission back through the reciprocal-mass dilation. -/
def sourceCoordinateAdmission (w : ℝ) (n : ℕ) : Polynomial ℝ :=
  (w ^ (2 * n))⁻¹ •
    (dimensionlessAdmission w n).comp (Polynomial.C (w ^ 2) * X)

theorem adaptiveShear_smul (c : ℝ) (Q : Polynomial ℝ) :
    xiShiftedBoundaryAdaptiveShearPolynomial (c • Q) =
      c ^ 2 • xiShiftedBoundaryAdaptiveShearPolynomial Q := by
  simp only [xiShiftedBoundaryAdaptiveShearPolynomial,
    xiShiftedBoundaryShiftedEuler, Polynomial.smul_eq_C_mul,
    Polynomial.derivative_C_mul]
  have hC : Polynomial.C (c ^ 2) = Polynomial.C c ^ 2 := by
    rw [Polynomial.C_pow]
  rw [hC]
  ring

theorem adaptiveShear_comp_C_mul_X
    {d : ℝ} (Q : Polynomial ℝ) :
    d ^ 2 • xiShiftedBoundaryAdaptiveShearPolynomial
        (Q.comp (Polynomial.C d * X)) =
      (xiShiftedBoundaryAdaptiveShearPolynomial Q).comp
        (Polynomial.C d * X) := by
  simp only [xiShiftedBoundaryAdaptiveShearPolynomial,
    xiShiftedBoundaryShiftedEuler, Polynomial.derivative_comp,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, Polynomial.mul_comp,
    Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
    Polynomial.smul_eq_C_mul]
  have hCd : Polynomial.C (d ^ 2) = Polynomial.C d ^ 2 := by
    rw [Polynomial.C_pow]
  rw [hCd]
  ring

/-- Adaptive shear commutes with reciprocal-mass dilation with its exact homogeneous weight. -/
theorem adaptiveShear_sourceCoordinateDilation
    {w : ℝ} (hw : w ≠ 0) (n : ℕ) (Q : Polynomial ℝ) :
    xiShiftedBoundaryAdaptiveShearPolynomial
        ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X)) =
      (w ^ (4 * n + 4))⁻¹ •
        (xiShiftedBoundaryAdaptiveShearPolynomial Q).comp
          (Polynomial.C (w ^ 2) * X) := by
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero _ hw
  rw [adaptiveShear_smul]
  have hcomp := adaptiveShear_comp_C_mul_X Q
  have hscalar : (w ^ (2 * n))⁻¹ ^ 2 =
      (w ^ (4 * n + 4))⁻¹ * (w ^ 2) ^ 2 := by
    field_simp [hw]
    ring
  rw [hscalar, mul_smul, hcomp]

/-- A moment functional is a fixed finite coefficient sum once a degree bound is known. -/
theorem momentFunctional_eq_sum_range_of_natDegree_le
    (s : ℕ → ℝ) {P : Polynomial ℝ} {N : ℕ} (hdegree : P.natDegree ≤ N) :
    HTGeometry.momentFunctional s P =
      ∑ k ∈ Finset.range (N + 1), P.coeff k * s k := by
  conv_lhs => rw [P.as_sum_range' (N + 1) (by omega)]
  rw [HTGeometry.momentFunctional_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [HTGeometry.momentFunctional_monomial]

/-- Exact relation between the normalized moment functional and mass dilation of a polynomial. -/
theorem momentFunctional_normalized_eq_massDilation
    {w : ℝ} (hw : 1 < w) (Q : Polynomial ℝ) :
    HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w) Q =
      (2 * w / Real.log w) *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
          (Q.comp (Polynomial.C (w ^ 2) * X)) := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  have hdil : (Polynomial.C (w ^ 2) * X : Polynomial ℝ).natDegree = 1 := by
    exact Polynomial.natDegree_C_mul_X (w ^ 2) (pow_ne_zero _ hw0)
  have hcomp :
      (Q.comp (Polynomial.C (w ^ 2) * X)).natDegree ≤ Q.natDegree := by
    calc
      _ ≤ Q.natDegree * (Polynomial.C (w ^ 2) * X : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_comp_le
      _ = Q.natDegree := by rw [hdil, Nat.mul_one]
  rw [momentFunctional_eq_sum_range_of_natDegree_le
      (s := xiShiftedFarRightNormalizedMoment w) (P := Q) le_rfl,
    momentFunctional_eq_sum_range_of_natDegree_le
      (s := fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) hcomp,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.comp_C_mul_X_coeff]
  simp only [xiShiftedFarRightNormalizedMoment]
  have hsq : (w ^ 2) ^ k = w ^ (2 * k) := by rw [← pow_mul]
  rw [hsq]
  field_simp [hw0, hlog]
  ring

/-- Exact source-first identity for a mass-dilated degree-`n` amplitude. -/
theorem scaled_arithmeticSource_sourceCoordinateDilation
    {w : ℝ} (hw : 1 < w) (n : ℕ) (Q : Polynomial ℝ) :
    w ^ (4 * n + 5) / Real.log w *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X)) =
      HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
        (xiShiftedBoundaryAdaptiveShearPolynomial Q) := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  have hsource := two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource
    (by linarith : 1 / 2 < w)
    ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X))
  rw [HTGeometry.momentInner_def] at hsource
  have hshear :
      (X * ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X))) *
          (X * xiShiftedBoundaryShiftedEuler 1
            ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X))) =
        xiShiftedBoundaryAdaptiveShearPolynomial
          ((w ^ (2 * n))⁻¹ • Q.comp (Polynomial.C (w ^ 2) * X)) := rfl
  rw [hshear,
    adaptiveShear_sourceCoordinateDilation hw0 n Q,
    HTGeometry.momentFunctional_smul] at hsource
  have hnorm := momentFunctional_normalized_eq_massDilation hw
    (xiShiftedBoundaryAdaptiveShearPolynomial Q)
  rw [← hsource, hnorm]
  field_simp [hw0, hlog]
  ring

theorem dimensionlessAdmission_monic (w : ℝ) (n : ℕ) :
    (dimensionlessAdmission w n).Monic :=
  HTGeometry.monicMomentAdmissionPolynomial_monic _ _

theorem dimensionlessAdmission_natDegree (w : ℝ) (n : ℕ) :
    (dimensionlessAdmission w n).natDegree = n :=
  HTGeometry.monicMomentAdmissionPolynomial_natDegree _ _

/-- Coefficients of the adaptive shear vary continuously under coefficientwise amplitude
convergence. -/
theorem tendsto_adaptiveShear_coeff
    {α : Type*} {l : Filter α} {F : α → Polynomial ℝ} {P : Polynomial ℝ}
    (hcoeff : ∀ k, Tendsto (fun x => (F x).coeff k) l (nhds (P.coeff k)))
    (k : ℕ) :
    Tendsto
      (fun x => (xiShiftedBoundaryAdaptiveShearPolynomial (F x)).coeff k) l
      (nhds ((xiShiftedBoundaryAdaptiveShearPolynomial P).coeff k)) := by
  have hXA : ∀ r, Tendsto (fun x => (X * F x).coeff r) l
      (nhds ((X * P).coeff r)) := by
    intro r
    cases r with
    | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (nhds 0))
    | succ r => simpa [Nat.succ_eq_add_one] using hcoeff r
  have hXE : ∀ r, Tendsto
      (fun x => (X * xiShiftedBoundaryShiftedEuler 1 (F x)).coeff r) l
      (nhds ((X * xiShiftedBoundaryShiftedEuler 1 P).coeff r)) := by
    intro r
    cases r with
    | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (nhds 0))
    | succ r =>
        simpa [Nat.succ_eq_add_one, xiShiftedBoundaryShiftedEuler_coeff] using
          (hcoeff r).const_mul ((r + 1 : ℕ) : ℝ)
  change Tendsto
    (fun x => ((X * F x) *
      (X * xiShiftedBoundaryShiftedEuler 1 (F x))).coeff k) l
    (nhds (((X * P) *
      (X * xiShiftedBoundaryShiftedEuler 1 P)).coeff k))
  rw [Polynomial.coeff_mul]
  have hfun :
      (fun x => ((X * F x) *
        (X * xiShiftedBoundaryShiftedEuler 1 (F x))).coeff k) =
      (fun x => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
        (X * F x).coeff ij.1 *
          (X * xiShiftedBoundaryShiftedEuler 1 (F x)).coeff ij.2) := by
    funext x
    rw [Polynomial.coeff_mul]
  rw [hfun]
  apply tendsto_finsetSum
  intro ij _
  exact (hXA ij.1).mul (hXE ij.2)

/-- The normalized adaptive source selected by the actual Xi admission converges to its exact
arcsine counterpart. -/
theorem tendsto_dimensionlessAdmission_adaptiveShearMoment
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ =>
        HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
          (xiShiftedBoundaryAdaptiveShearPolynomial (dimensionlessAdmission w n)))
      atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryAdaptiveShearPolynomial (Arc.amplitude n)))) := by
  let N := 2 * n + 2
  have hterms : ∀ k ∈ Finset.range (N + 1),
      Tendsto
        (fun w : ℝ =>
          (xiShiftedBoundaryAdaptiveShearPolynomial
            (dimensionlessAdmission w n)).coeff k *
              xiShiftedFarRightNormalizedMoment w k)
        atTop
        (nhds ((xiShiftedBoundaryAdaptiveShearPolynomial (Arc.amplitude n)).coeff k *
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom k)) := by
    intro k _
    exact (tendsto_adaptiveShear_coeff
      (fun j => tendsto_dimensionlessAdmission_coeff hn j) k).mul
        (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam k)
  have hsum := tendsto_finsetSum (Finset.range (N + 1)) hterms
  have hdegXi : ∀ w : ℝ,
      (xiShiftedBoundaryAdaptiveShearPolynomial
        (dimensionlessAdmission w n)).natDegree ≤ N := by
    intro w
    exact natDegree_xiShiftedBoundaryAdaptiveShearPolynomial_le
      (dimensionlessAdmission_monic w n) (dimensionlessAdmission_natDegree w n)
  have hdegArc :
      (xiShiftedBoundaryAdaptiveShearPolynomial (Arc.amplitude n)).natDegree ≤ N :=
    natDegree_xiShiftedBoundaryAdaptiveShearPolynomial_le
      (Arc.amplitude_monic hn) (amplitude_natDegree hn)
  simpa only [momentFunctional_eq_sum_range_of_natDegree_le
      (s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom) hdegArc] using
    hsum.congr' (Filter.Eventually.of_forall fun w => by
      rw [momentFunctional_eq_sum_range_of_natDegree_le
        (s := xiShiftedFarRightNormalizedMoment w) (hdegXi w)])

/-- **Canonical fixed-degree arithmetic-source recession.**  The literal source selected by the
actual Xi monic admission converges, after exact mass scaling, to the positive arcsine margin. -/
theorem tendsto_scaled_canonicalArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ => w ^ (4 * n + 5) / Real.log w *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (sourceCoordinateAdmission w n))
      atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryAdaptiveShearPolynomial (Arc.amplitude n)))) := by
  apply tendsto_dimensionlessAdmission_adaptiveShearMoment hn |>.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  exact (scaled_arithmeticSource_sourceCoordinateDilation hw n
    (dimensionlessAdmission w n)).symm

theorem tendsto_scaled_canonicalArithmeticSource_one :
    Tendsto
      (fun w : ℝ => w ^ 9 / Real.log w *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (sourceCoordinateAdmission w 1))
      atTop (nhds (11 / 64 : ℝ)) := by
  have h := tendsto_scaled_canonicalArithmeticSource (n := 1) (by omega)
  rw [XiShiftedArcsineAdmission.momentFunctional_adaptiveShear_amplitude_one] at h
  simpa using h

theorem tendsto_scaled_canonicalArithmeticSource_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    Tendsto
      (fun w : ℝ => w ^ (4 * n + 5) / Real.log w *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (sourceCoordinateAdmission w n))
      atTop (nhds (Arc.monicScale n ^ 2 * (8 * n + 3) / 16)) := by
  have h := tendsto_scaled_canonicalArithmeticSource (n := n) (by omega)
  rw [XiShiftedArcsineAdmission.momentFunctional_adaptiveShear_amplitude_of_two_le hn] at h
  exact h

/-- Every fixed nonzero canonical Xi admission lands in a strictly positive literal arithmetic
source sufficiently far right. -/
theorem canonicalArithmeticSource_eventually_pos
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (sourceCoordinateAdmission w n) := by
  have hmargin := XiShiftedArcsineAdmission.momentFunctional_adaptiveShear_amplitude_pos hn
  have hscaled := (tendsto_scaled_canonicalArithmeticSource hn).eventually
    (Ioi_mem_nhds hmargin)
  filter_upwards [hscaled, eventually_gt_atTop (1 : ℝ)] with w hs hw
  have hfactor : 0 < w ^ (4 * n + 5) / Real.log w :=
    div_pos (pow_pos (lt_trans zero_lt_one hw) _) (Real.log_pos hw)
  rcases mul_pos_iff.mp hs with h | h
  · exact h.2
  · exact (not_lt_of_ge hfactor.le h.1).elim

/-- **Admission-sensitive source producer.**  In every fixed positive degree, the unique monic
shifted-Xi admission is selected before landing, and its mass-dilated adaptive arithmetic source
is eventually strictly positive. -/
theorem canonicalUniqueAdmissionArithmeticSource_eventually_pos
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop,
      (∀ p : Polynomial ℝ,
        p.Monic → p.natDegree = n →
        (∀ i : Fin n, HTGeometry.momentFunctional
          (xiShiftedFarRightNormalizedMoment w) (X ^ (i : ℕ) * p) = 0) →
        p = dimensionlessAdmission w n) ∧
      0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (sourceCoordinateAdmission w n) := by
  filter_upwards [dimensionlessAdmission_eventually_unique n,
    canonicalArithmeticSource_eventually_pos hn] with w hadmission hsource
  exact ⟨hadmission, hsource⟩

end

end XiShiftedCanonicalAdmission

end RHTower
