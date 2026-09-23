import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession
import GaloisForLFunctions.RHTower.XiShiftedAdaptiveOrthogonalSourceJacobiEnergy

/-!
# Relative coercivity of canonical shifted-Xi source admission

The absolute arcsine source margin of the monic degree-`n` admission decays exponentially because
the monic Chebyshev norm does.  Dividing by that intrinsic admitted norm removes the coordinate
collapse: the source-to-norm ratio is exactly `n + 3/8` in every positive degree.

For the actual shifted-Xi inverse-Hankel admission, the mass-scaled literal rational--Gamma minus
von Mangoldt source divided by the normalized admitted norm converges to the same linearly growing
ratio.  This identifies the precise remaining obstruction: fixed-degree source recession is
relatively coercive, so only absence of a degree-uniform diagonal convergence rate can permit
cofinal face escape.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower

noncomputable section

namespace XiShiftedArcsineAdmission

/-- Exact squared norm of the monic shifted-Chebyshev admission on the arcsine face. -/
theorem momentFunctional_amplitude_sq
    {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        ((amplitude n) ^ (2 : ℕ)) =
      monicScale n ^ (2 : ℕ) / 2 := by
  have hsq :
      (amplitude n) ^ (2 : ℕ) =
        monicScale n ^ (2 : ℕ) •
          ((Polynomial.Chebyshev.T ℝ n) ^ (2 : ℕ)).comp affine := by
    simp only [amplitude, Polynomial.smul_eq_C_mul, Polynomial.pow_comp]
    rw [Polynomial.C_pow]
    ring
  rw [hsq, HTGeometry.momentFunctional_smul]
  change monicScale n ^ (2 : ℕ) * L ((Polynomial.Chebyshev.T ℝ n) ^ (2 : ℕ)) = _
  rw [show (Polynomial.Chebyshev.T ℝ n) ^ (2 : ℕ) =
      Polynomial.Chebyshev.T ℝ n * Polynomial.Chebyshev.T ℝ n by ring,
    L_T_mul_self_of_ne_zero hn]
  ring

/-- **Scale-free arcsine source law.**  Exponential decay of the absolute monic source margin is
exactly the decay of the admitted orthogonal norm; their ratio grows linearly with degree. -/
theorem momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear
    {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n)) =
      ((n : ℝ) + 3 / 8) *
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((amplitude n) ^ (2 : ℕ)) := by
  by_cases hn1 : n = 1
  · subst n
    rw [momentFunctional_adaptiveShear_amplitude_one,
      momentFunctional_amplitude_sq (by omega)]
    norm_num [monicScale]
  · have hn2 : 2 ≤ n := by omega
    rw [momentFunctional_adaptiveShear_amplitude_of_two_le hn2,
      momentFunctional_amplitude_sq hn]
    ring

/-- The admitted arcsine norm is strictly positive in every positive degree. -/
theorem momentFunctional_amplitude_sq_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        ((amplitude n) ^ (2 : ℕ)) := by
  rw [momentFunctional_amplitude_sq hn]
  have hs : 0 < monicScale n := by
    unfold monicScale
    exact inv_pos.mpr (pow_pos (by norm_num) _)
  positivity

/-- The scale-free source margin strictly dominates degree times admitted norm. -/
theorem degree_mul_momentFunctional_amplitude_sq_lt_adaptiveShear
    {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) *
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((amplitude n) ^ (2 : ℕ)) <
      HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n)) := by
  rw [momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear hn]
  have hnorm := momentFunctional_amplitude_sq_pos hn
  nlinarith

end XiShiftedArcsineAdmission

namespace XiShiftedCanonicalAdmission

/-- Normalized squared norm of the actual dimensionless inverse-Hankel admission. -/
def normalizedAdmissionNorm (w : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
    ((dimensionlessAdmission w n) ^ (2 : ℕ))

/-- Normalized adaptive source of the same admission, formed before any reporting map. -/
def normalizedAdmissionSource (w : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
    (xiShiftedBoundaryAdaptiveShearPolynomial (dimensionlessAdmission w n))

/-- Coefficientwise convergence of a finite polynomial curve passes to its square. -/
theorem tendsto_sq_coeff
    {α : Type*} {l : Filter α} {F : α → Polynomial ℝ} {P : Polynomial ℝ}
    (hcoeff : ∀ k, Tendsto (fun x => (F x).coeff k) l (nhds (P.coeff k)))
    (k : ℕ) :
    Tendsto (fun x => ((F x) ^ (2 : ℕ)).coeff k) l (nhds ((P ^ (2 : ℕ)).coeff k)) := by
  simp only [pow_two, Polynomial.coeff_mul]
  apply tendsto_finsetSum
  intro ij _
  exact (hcoeff ij.1).mul (hcoeff ij.2)

/-- The normalized admitted norm converges to the exact arcsine admitted norm. -/
theorem tendsto_normalizedAdmissionNorm
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => normalizedAdmissionNorm w n) atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        ((Arc.amplitude n) ^ (2 : ℕ)))) := by
  let N := 2 * n
  have hterms : ∀ k ∈ Finset.range (N + 1),
      Tendsto
        (fun w : ℝ => ((dimensionlessAdmission w n) ^ (2 : ℕ)).coeff k *
          xiShiftedFarRightNormalizedMoment w k)
        atTop
        (nhds (((Arc.amplitude n) ^ (2 : ℕ)).coeff k *
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom k)) := by
    intro k _
    exact (tendsto_sq_coeff
      (fun j => tendsto_dimensionlessAdmission_coeff hn j) k).mul
        (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam k)
  have hsum := tendsto_finsetSum (Finset.range (N + 1)) hterms
  have hdegXi : ∀ w : ℝ, ((dimensionlessAdmission w n) ^ (2 : ℕ)).natDegree ≤ N := by
    intro w
    rw [Polynomial.natDegree_pow, dimensionlessAdmission_natDegree]
  have hdegArc : ((Arc.amplitude n) ^ (2 : ℕ)).natDegree ≤ N := by
    rw [Polynomial.natDegree_pow, amplitude_natDegree hn]
  simpa only [normalizedAdmissionNorm,
      momentFunctional_eq_sum_range_of_natDegree_le
        (s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom) hdegArc] using
    hsum.congr' (Filter.Eventually.of_forall fun w => by
      rw [momentFunctional_eq_sum_range_of_natDegree_le
        (s := xiShiftedFarRightNormalizedMoment w) (hdegXi w)])

/-- The normalized adaptive source-to-admitted-norm ratio converges to `n + 3/8`. -/
theorem tendsto_normalizedAdmissionSource_div_norm
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ => normalizedAdmissionSource w n / normalizedAdmissionNorm w n)
      atTop (nhds ((n : ℝ) + 3 / 8)) := by
  have hsource := tendsto_dimensionlessAdmission_adaptiveShearMoment hn
  have hnorm := tendsto_normalizedAdmissionNorm hn
  have hnormPos := XiShiftedArcsineAdmission.momentFunctional_amplitude_sq_pos hn
  have hdiv := hsource.div hnorm (ne_of_gt hnormPos)
  have hlimit :
      HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          (xiShiftedBoundaryAdaptiveShearPolynomial (Arc.amplitude n)) /
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((Arc.amplitude n) ^ (2 : ℕ)) =
        (n : ℝ) + 3 / 8 := by
    rw [XiShiftedArcsineAdmission.momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear hn]
    field_simp [ne_of_gt hnormPos]
  rw [hlimit] at hdiv
  apply hdiv.congr'
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Literal mass-scaled rational--Gamma minus von Mangoldt source, divided by intrinsic normalized
admitted norm. -/
def relativeArithmeticSource (w : ℝ) (n : ℕ) : ℝ :=
  (w ^ (4 * n + 5) / Real.log w *
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (sourceCoordinateAdmission w n)) /
    normalizedAdmissionNorm w n

/-- Before taking any limit, the relative arithmetic source is exactly the normalized adaptive
source quotient. -/
theorem relativeArithmeticSource_eq_normalizedAdmissionSource_div_norm
    {w : ℝ} (hw : 1 < w) (n : ℕ) :
    relativeArithmeticSource w n =
      normalizedAdmissionSource w n / normalizedAdmissionNorm w n := by
  rw [relativeArithmeticSource, normalizedAdmissionSource,
    sourceCoordinateAdmission,
    scaled_arithmeticSource_sourceCoordinateDilation hw n (dimensionlessAdmission w n)]

/-- Inside one normalized positive Hankel chamber, inverse-Hankel admission is literally the
monic orthogonal polynomial.  This is the admission-sensitive identification needed before
forming the Jacobi source energy. -/
theorem dimensionlessAdmission_eq_monicOrtho_of_hankelPosDef
    {w : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    dimensionlessAdmission w n =
      HTGeometry.monicOrtho (xiShiftedFarRightNormalizedMoment w) n := by
  let s := xiShiftedFarRightNormalizedMoment w
  let e : Fin n → Fin (n + 2) := fun i => ⟨i, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg Fin.val hij
  have hhead : (HTGeometry.momentHankelMatrix s n).PosDef := by
    have hsub := hH.submatrix he
    have heq :
        (HTGeometry.momentHankelMatrix
          (xiShiftedFarRightNormalizedMoment w) (n + 2)).submatrix e e =
          HTGeometry.momentHankelMatrix s n := by
      ext i j
      rfl
    rwa [heq] at hsub
  symm
  apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    (ne_of_gt hhead.det_pos)
    (HTGeometry.monicOrtho_monic s n)
    (HTGeometry.natDegree_monicOrtho_eq s n)
  intro i
  change HTGeometry.momentInner s (X ^ (i : ℕ))
      (HTGeometry.monicOrtho s n) = 0
  rw [HTGeometry.momentInner_comm]
  exact HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
      (by rw [Polynomial.degree_X_pow]; exact_mod_cast i.isLt)

/-- **Exact Jacobi localization of the arithmetic source.**  Before any limit, the literal
mass-scaled rational--Gamma minus von Mangoldt source quotient is the adaptive Jacobi energy of
the currently admitted normalized flag. -/
theorem relativeArithmeticSource_eq_adaptiveOrthoJacobiEnergy
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    relativeArithmeticSource w n =
      HTGeometry.adaptiveOrthoJacobiEnergy
        (xiShiftedFarRightNormalizedMoment w) n := by
  let s := xiShiftedFarRightNormalizedMoment w
  let P := HTGeometry.monicOrtho s n
  have hP : dimensionlessAdmission w n = P :=
    dimensionlessAdmission_eq_monicOrtho_of_hankelPosDef hH
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : 0 < HTGeometry.monicOrthoNormSq s n :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hshear : xiShiftedBoundaryAdaptiveShearPolynomial P =
      HTGeometry.adaptiveOrthoSourcePolynomial s n := by
    simp only [P, xiShiftedBoundaryAdaptiveShearPolynomial,
      xiShiftedBoundaryShiftedEuler, HTGeometry.adaptiveOrthoSourcePolynomial,
      C_1, one_mul]
  rw [relativeArithmeticSource_eq_normalizedAdmissionSource_div_norm hw n,
    normalizedAdmissionSource, normalizedAdmissionNorm, hP, hshear]
  rw [show HTGeometry.momentFunctional
      (xiShiftedFarRightNormalizedMoment w) (P ^ (2 : ℕ)) =
      HTGeometry.momentInner (xiShiftedFarRightNormalizedMoment w) P P by
    rw [HTGeometry.momentInner_def, pow_two]]
  change HTGeometry.momentFunctional s
      (HTGeometry.adaptiveOrthoSourcePolynomial s n) /
      HTGeometry.momentInner s P P = _
  rw [HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
    hbelow hn le_rfl]
  change (HTGeometry.monicOrthoNormSq s n *
      HTGeometry.adaptiveOrthoJacobiEnergy s n) /
      HTGeometry.monicOrthoNormSq s n = _
  field_simp [ne_of_gt hnorm]
  rfl

/-- The degree-uniform relative-source target is exactly a Jacobi-energy target in every current
positive admission chamber. -/
theorem relativeArithmeticSource_gt_degree_iff_jacobiEnergy_gt_degree
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    (n : ℝ) < relativeArithmeticSource w n ↔
      (n : ℝ) < HTGeometry.adaptiveOrthoJacobiEnergy
        (xiShiftedFarRightNormalizedMoment w) n := by
  rw [relativeArithmeticSource_eq_adaptiveOrthoJacobiEnergy hw hn hH]

/-- **Relative canonical arithmetic-source recession.**  The literal completed source has a
linearly growing, not exponentially collapsing, source-to-admitted-norm limit. -/
theorem tendsto_relativeArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => relativeArithmeticSource w n) atTop
      (nhds ((n : ℝ) + 3 / 8)) := by
  apply (tendsto_normalizedAdmissionSource_div_norm hn).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  exact (relativeArithmeticSource_eq_normalizedAdmissionSource_div_norm hw n).symm

/-- Every fixed positive degree eventually has relative arithmetic-source margin strictly larger
than the degree itself. -/
theorem relativeArithmeticSource_eventually_gt_degree
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop, (n : ℝ) < relativeArithmeticSource w n := by
  have htarget : (n : ℝ) < (n : ℝ) + 3 / 8 := by norm_num
  exact (tendsto_relativeArithmeticSource hn).eventually (Ioi_mem_nhds htarget)

end XiShiftedCanonicalAdmission

namespace XiShiftedArcsineAdmission

/-- Coordinate dilation of the arcsine moment sequence. -/
def coordinateDilatedMoment (r : ℝ) (k : ℕ) : ℝ :=
  r ^ k * GaloisForLFunctions.HTGeometry.normalizedCentralBinom k

/-- Monic arcsine admission transported through the coordinate dilation `X ↦ rX`. -/
def coordinateDilatedAmplitude (r : ℝ) (n : ℕ) : Polynomial ℝ :=
  r ^ n • (amplitude n).comp (Polynomial.C r⁻¹ * X)

/-- Evaluation of the dilated moment functional is exactly polynomial pullback by `X ↦ rX`. -/
theorem momentFunctional_coordinateDilatedMoment
    {r : ℝ} (hr : r ≠ 0) (Q : Polynomial ℝ) :
    HTGeometry.momentFunctional (coordinateDilatedMoment r) Q =
      HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (Q.comp (Polynomial.C r * X)) := by
  have hlin : (Polynomial.C r * X : Polynomial ℝ).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X r hr
  have hdegree : (Q.comp (Polynomial.C r * X)).natDegree ≤ Q.natDegree := by
    calc
      _ ≤ Q.natDegree * (Polynomial.C r * X : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_comp_le
      _ = Q.natDegree := by rw [hlin, Nat.mul_one]
  rw [XiShiftedCanonicalAdmission.momentFunctional_eq_sum_range_of_natDegree_le
      (s := coordinateDilatedMoment r) (P := Q) le_rfl,
    XiShiftedCanonicalAdmission.momentFunctional_eq_sum_range_of_natDegree_le
      (s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom) hdegree]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.comp_C_mul_X_coeff]
  simp only [coordinateDilatedMoment]
  ring

/-- Pulling the transported admission back by `X ↦ rX` recovers the original arcsine flag. -/
theorem coordinateDilatedAmplitude_comp
    {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    (coordinateDilatedAmplitude r n).comp (Polynomial.C r * X) =
      r ^ n • amplitude n := by
  simp only [coordinateDilatedAmplitude,
    Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp, Polynomial.smul_eq_C_mul]
  have hscalar : Polynomial.C r⁻¹ * (Polynomial.C r * X) = X := by
    rw [← mul_assoc, ← Polynomial.C_mul]
    field_simp [hr]
    simp
  rw [hscalar, Polynomial.comp_X]

/-- Coordinate-dilated arcsine admission remains monic. -/
theorem coordinateDilatedAmplitude_monic
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (coordinateDilatedAmplitude r n).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · rw [coordinateDilatedAmplitude, Polynomial.natDegree_smul _ (pow_ne_zero _ hr),
      Polynomial.natDegree_comp,
      Polynomial.natDegree_C_mul_X r⁻¹ (inv_ne_zero hr),
      XiShiftedCanonicalAdmission.amplitude_natDegree hn, Nat.mul_one]
  · simp only [coordinateDilatedAmplitude, Polynomial.coeff_smul,
      Polynomial.comp_C_mul_X_coeff]
    have hamp : (amplitude n).coeff n = 1 := by
      have hcoeff := (amplitude_monic hn).coeff_natDegree
      rw [XiShiftedCanonicalAdmission.amplitude_natDegree hn] at hcoeff
      exact hcoeff
    rw [hamp]
    change r ^ n * (1 * r⁻¹ ^ n) = 1
    rw [one_mul, ← mul_pow]
    field_simp [hr]
    simp

/-- Coordinate-dilated arcsine admission retains degree. -/
theorem coordinateDilatedAmplitude_natDegree
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (coordinateDilatedAmplitude r n).natDegree = n := by
  rw [coordinateDilatedAmplitude, Polynomial.natDegree_smul _ (pow_ne_zero _ hr),
    Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X r⁻¹ (inv_ne_zero hr),
    XiShiftedCanonicalAdmission.amplitude_natDegree hn, Nat.mul_one]

/-- The dilated arcsine sequence is still a positive moment form. -/
theorem coordinateDilatedMoment_positiveMomentForm
    {r : ℝ} (hr : r ≠ 0) :
    HTGeometry.PositiveMomentForm (coordinateDilatedMoment r) := by
  refine ⟨fun Q hQ => ?_⟩
  rw [HTGeometry.momentInner_self,
    momentFunctional_coordinateDilatedMoment hr]
  have hcomp : Q.comp (Polynomial.C r * X) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun P : Polynomial ℝ => P.coeff Q.natDegree) hzero
    rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_zero] at hcoeff
    exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ)
      (pow_ne_zero _ hr)) hcoeff
  rw [Polynomial.pow_comp, ← HTGeometry.momentInner_self]
  exact
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm.pos_of_ne_zero
      _ hcomp

/-- The transported flag is the actual canonical admission of the dilated positive moment form. -/
theorem coordinateDilatedAmplitude_eq_monicMomentAdmissionPolynomial
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    coordinateDilatedAmplitude r n =
      HTGeometry.monicMomentAdmissionPolynomial (coordinateDilatedMoment r) n := by
  have hpos := coordinateDilatedMoment_positiveMomentForm hr
  apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    (ne_of_gt ((HTGeometry.positiveMomentForm_iff_momentHankelMatrix_posDef.mp hpos n).det_pos))
    (coordinateDilatedAmplitude_monic hr hn)
    (coordinateDilatedAmplitude_natDegree hr hn)
  intro i
  rw [momentFunctional_coordinateDilatedMoment hr]
  have hpoly :
      (X ^ (i : ℕ) * coordinateDilatedAmplitude r n).comp
          (Polynomial.C r * X) =
        r ^ ((i : ℕ) + n) • (X ^ (i : ℕ) * amplitude n) := by
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      coordinateDilatedAmplitude_comp hr n]
    simp only [Polynomial.smul_eq_C_mul]
    rw [mul_pow, Polynomial.C_pow, pow_add, Polynomial.C_mul]
    simp only [Polynomial.C_pow]
    ring
  rw [hpoly, HTGeometry.momentFunctional_smul]
  have hzero := XiShiftedCanonicalAdmission.momentFunctional_X_pow_mul_arcsine_amplitude_eq_zero
    hn i
  rw [hzero, mul_zero]

/-- Adaptive source shear has coordinate weight two relative to admitted norm. -/
theorem adaptiveShear_coordinateDilatedAmplitude_comp
    {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    (xiShiftedBoundaryAdaptiveShearPolynomial
        (coordinateDilatedAmplitude r n)).comp (Polynomial.C r * X) =
      r ^ (2 * n + 2) •
        xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n) := by
  have h := XiShiftedCanonicalAdmission.adaptiveShear_comp_C_mul_X (d := r)
    (coordinateDilatedAmplitude r n)
  rw [coordinateDilatedAmplitude_comp hr n,
    XiShiftedCanonicalAdmission.adaptiveShear_smul] at h
  rw [← h, smul_smul]
  congr 1
  rw [pow_add, pow_mul]
  ring

/-- Exact norm scaling of the transported canonical admission. -/
theorem momentFunctional_coordinateDilatedAmplitude_sq
    {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    HTGeometry.momentFunctional (coordinateDilatedMoment r)
        ((coordinateDilatedAmplitude r n) ^ (2 : ℕ)) =
      r ^ (2 * n) *
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((amplitude n) ^ (2 : ℕ)) := by
  rw [momentFunctional_coordinateDilatedMoment hr]
  have hpoly :
      ((coordinateDilatedAmplitude r n) ^ (2 : ℕ)).comp (Polynomial.C r * X) =
        r ^ (2 * n) • ((amplitude n) ^ (2 : ℕ)) := by
    rw [Polynomial.pow_comp, coordinateDilatedAmplitude_comp hr n]
    simp only [Polynomial.smul_eq_C_mul]
    rw [pow_mul, Polynomial.C_pow]
    simp only [Polynomial.C_pow]
    ring
  rw [hpoly, HTGeometry.momentFunctional_smul]

/-- Exact adaptive-source scaling of the transported canonical admission. -/
theorem momentFunctional_coordinateDilatedAmplitude_adaptiveShear
    {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    HTGeometry.momentFunctional (coordinateDilatedMoment r)
        (xiShiftedBoundaryAdaptiveShearPolynomial
          (coordinateDilatedAmplitude r n)) =
      r ^ (2 * n + 2) *
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          (xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n)) := by
  rw [momentFunctional_coordinateDilatedMoment hr,
    adaptiveShear_coordinateDilatedAmplitude_comp hr n,
    HTGeometry.momentFunctional_smul]

/-- **Exact thermodynamic sensitivity law.**  On a positive canonical admission family obtained
by coordinate dilation, source divided by admitted norm scales by `r²`. -/
theorem coordinateDilated_adaptiveShear_div_norm
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.momentFunctional (coordinateDilatedMoment r)
        (xiShiftedBoundaryAdaptiveShearPolynomial
          (coordinateDilatedAmplitude r n)) /
      HTGeometry.momentFunctional (coordinateDilatedMoment r)
        ((coordinateDilatedAmplitude r n) ^ (2 : ℕ)) =
      r ^ (2 : ℕ) * ((n : ℝ) + 3 / 8) := by
  rw [momentFunctional_coordinateDilatedAmplitude_adaptiveShear hr n,
    momentFunctional_coordinateDilatedAmplitude_sq hr n,
    momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear hn]
  have hnorm := momentFunctional_amplitude_sq_pos hn
  field_simp [hr, ne_of_gt hnorm]
  ring

/-- Sharp admission window in the dilation model: relative source beats degree exactly when the
coordinate contraction is within an inverse-degree edge window. -/
theorem coordinateDilated_adaptiveShear_div_norm_gt_degree_iff
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) <
        HTGeometry.momentFunctional (coordinateDilatedMoment r)
            (xiShiftedBoundaryAdaptiveShearPolynomial
              (coordinateDilatedAmplitude r n)) /
          HTGeometry.momentFunctional (coordinateDilatedMoment r)
            ((coordinateDilatedAmplitude r n) ^ (2 : ℕ)) ↔
      8 * (n : ℝ) * (1 - r ^ (2 : ℕ)) < 3 * r ^ (2 : ℕ) := by
  rw [coordinateDilated_adaptiveShear_div_norm hr hn]
  constructor <;> intro h <;> nlinarith

/-- A large enough degree defeats the `> degree` target after any fixed strict coordinate
contraction, even though every dilated moment form remains positive and every flag is canonical. -/
theorem coordinateDilated_adaptiveShear_div_norm_lt_degree
    {r : ℝ} (hr : 0 < r) (_hrone : r < 1) {n : ℕ} (hn : n ≠ 0)
    (hlarge : 3 * r ^ (2 : ℕ) < 8 * (n : ℝ) * (1 - r ^ (2 : ℕ))) :
    HTGeometry.momentFunctional (coordinateDilatedMoment r)
        (xiShiftedBoundaryAdaptiveShearPolynomial
          (coordinateDilatedAmplitude r n)) /
      HTGeometry.momentFunctional (coordinateDilatedMoment r)
        ((coordinateDilatedAmplitude r n) ^ (2 : ℕ)) < (n : ℝ) := by
  rw [coordinateDilated_adaptiveShear_div_norm (ne_of_gt hr) hn]
  nlinarith

/-- Fixed positive contractions violate relative degree coercivity at all sufficiently large
degrees.  Therefore no degree-independent open neighborhood of the arcsine face can prove the
cofinal source inequality. -/
theorem coordinateDilated_adaptiveShear_div_norm_eventually_lt_degree
    {r : ℝ} (hr : 0 < r) (hrone : r < 1) :
    ∀ᶠ n : ℕ in atTop,
      HTGeometry.momentFunctional (coordinateDilatedMoment r)
          (xiShiftedBoundaryAdaptiveShearPolynomial
            (coordinateDilatedAmplitude r n)) /
        HTGeometry.momentFunctional (coordinateDilatedMoment r)
          ((coordinateDilatedAmplitude r n) ^ (2 : ℕ)) < (n : ℝ) := by
  have hrSq : r ^ (2 : ℕ) < 1 := by
    have hprod : 0 < (1 - r) * (1 + r) :=
      mul_pos (sub_pos.mpr hrone) (add_pos zero_lt_one hr)
    nlinarith
  have hden : 0 < 8 * (1 - r ^ (2 : ℕ)) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * r ^ (2 : ℕ) / (8 * (1 - r ^ (2 : ℕ))))
  filter_upwards [eventually_ge_atTop (max N 1)] with n hnmax
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hnmax
  have hn0 : n ≠ 0 := by omega
  have hratio : 3 * r ^ (2 : ℕ) / (8 * (1 - r ^ (2 : ℕ))) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hnN)
  have hlarge : 3 * r ^ (2 : ℕ) < 8 * (n : ℝ) * (1 - r ^ (2 : ℕ)) := by
    have := (div_lt_iff₀ hden).mp hratio
    nlinarith
  exact coordinateDilated_adaptiveShear_div_norm_lt_degree hr hrone hn0 hlarge

end XiShiftedArcsineAdmission

end

end RHTower
