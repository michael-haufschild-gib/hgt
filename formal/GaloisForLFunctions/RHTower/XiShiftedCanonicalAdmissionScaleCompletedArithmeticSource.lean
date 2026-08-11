import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRelativeSourceCoercivity

/-!
# Christoffel-scale completion of the canonical shifted-Xi arithmetic source

Dividing the completed arithmetic source by admitted norm removes amplitude gauge but not
coordinate gauge.  A coordinate dilation by `r` multiplies that quotient by `r²`, and therefore
destroys `source > degree` cofinally for every fixed contraction `r < 1`.

The next canonical norm ratio has the same coordinate weight.  This file forms it from the current
admission, before any reflection aggregation, and proves that the twice-normalized literal
rational--Gamma minus von Mangoldt source is invariant on the entire positive dilated-arcsine
family.  Inside a finite positive shifted-Xi chamber it is exactly Jacobi energy divided by the
next Christoffel scale.
-/

open Filter Matrix Polynomial Topology

namespace RHTower

noncomputable section

namespace XiShiftedCanonicalAdmission

/-- Coordinate scale selected by two consecutive admitted squared norms. -/
def admissionChristoffelScaleSq (w : ℝ) (n : ℕ) : ℝ :=
  16 * normalizedAdmissionNorm w (n + 1) / normalizedAdmissionNorm w n

/-- Literal relative arithmetic source completed by current admission's coordinate scale. -/
def scaleCompletedRelativeArithmeticSource (w : ℝ) (n : ℕ) : ℝ :=
  relativeArithmeticSource w n / admissionChristoffelScaleSq w n

/-- Jacobi source energy strictly dominates its forced next-edge Christoffel contribution. -/
theorem adaptiveOrthoJacobiEnergy_gt_succ_mul_nextBeta
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) <
      HTGeometry.adaptiveOrthoJacobiEnergy s n := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha s j + HTGeometry.monicOrthoAlpha s n / 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1) * HTGeometry.monicOrthoAlpha s n ^ 2 := by
    positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hboundary :
      (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) <
        (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
    have hbeta := HTGeometry.monicOrthoBeta_pos_below h hn (by omega)
    nlinarith
  unfold HTGeometry.adaptiveOrthoJacobiEnergy
  linarith

/-- A positive `(n+2)` normalized block already identifies the degree-`n+1` inverse-Hankel
admission with its monic orthogonal polynomial. -/
theorem dimensionlessAdmission_succ_eq_monicOrtho_of_hankelPosDef
    {w : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    dimensionlessAdmission w (n + 1) =
      HTGeometry.monicOrtho (xiShiftedFarRightNormalizedMoment w) (n + 1) := by
  let s := xiShiftedFarRightNormalizedMoment w
  let e : Fin (n + 1) → Fin (n + 2) := fun i => ⟨i, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg Fin.val hij
  have hhead : (HTGeometry.momentHankelMatrix s (n + 1)).PosDef := by
    have hsub := hH.submatrix he
    have heq :
        (HTGeometry.momentHankelMatrix
          (xiShiftedFarRightNormalizedMoment w) (n + 2)).submatrix e e =
          HTGeometry.momentHankelMatrix s (n + 1) := by
      ext i j
      rfl
    rwa [heq] at hsub
  symm
  apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    (ne_of_gt hhead.det_pos)
    (HTGeometry.monicOrtho_monic s (n + 1))
    (HTGeometry.natDegree_monicOrtho_eq s (n + 1))
  intro i
  change HTGeometry.momentInner s (X ^ (i : ℕ))
      (HTGeometry.monicOrtho s (n + 1)) = 0
  rw [HTGeometry.momentInner_comm]
  exact HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
      (by rw [Polynomial.degree_X_pow]; exact_mod_cast i.isLt)

/-- In a finite positive chamber, admission scale is exactly sixteen times the next monic Jacobi
coefficient. -/
theorem admissionChristoffelScaleSq_eq_sixteen_mul_monicOrthoBeta
    {w : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    admissionChristoffelScaleSq w n =
      16 * HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment w) (n + 1) := by
  let s := xiShiftedFarRightNormalizedMoment w
  have hPn : dimensionlessAdmission w n = HTGeometry.monicOrtho s n :=
    dimensionlessAdmission_eq_monicOrtho_of_hankelPosDef hH
  have hPnext : dimensionlessAdmission w (n + 1) =
      HTGeometry.monicOrtho s (n + 1) := by
    exact dimensionlessAdmission_succ_eq_monicOrtho_of_hankelPosDef hH
  rw [admissionChristoffelScaleSq, normalizedAdmissionNorm, normalizedAdmissionNorm,
    hPn, hPnext, HTGeometry.monicOrthoBeta]
  simp only [HTGeometry.monicOrthoNormSq, HTGeometry.momentInner_self, pow_two, s]
  ring

/-- Current Christoffel coordinate scale is strictly positive in a finite positive chamber. -/
theorem admissionChristoffelScaleSq_pos
    {w : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    0 < admissionChristoffelScaleSq w n := by
  rw [admissionChristoffelScaleSq_eq_sixteen_mul_monicOrthoBeta hH]
  exact mul_pos (by norm_num)
    (HTGeometry.monicOrthoBeta_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega) (by omega))

/-- **Scale-completed arithmetic source law.**  The literal source is Jacobi energy divided by
the positive next Christoffel scale, with admission performed first. -/
theorem scaleCompletedRelativeArithmeticSource_eq_jacobiEnergy_div_christoffel
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    scaleCompletedRelativeArithmeticSource w n =
      HTGeometry.adaptiveOrthoJacobiEnergy
          (xiShiftedFarRightNormalizedMoment w) n /
        (16 * HTGeometry.monicOrthoBeta
          (xiShiftedFarRightNormalizedMoment w) (n + 1)) := by
  rw [scaleCompletedRelativeArithmeticSource,
    relativeArithmeticSource_eq_adaptiveOrthoJacobiEnergy hw hn hH,
    admissionChristoffelScaleSq_eq_sixteen_mul_monicOrthoBeta hH]

/-- **Coordinate-covariant arithmetic coercivity.**  In every finite positive current chamber,
literal relative arithmetic source strictly dominates degree times the next Christoffel edge. -/
theorem succ_mul_nextBeta_lt_relativeArithmeticSource
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    (n + 1 : ℝ) * HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment w) (n + 1) <
      relativeArithmeticSource w n := by
  rw [relativeArithmeticSource_eq_adaptiveOrthoJacobiEnergy hw hn hH]
  exact adaptiveOrthoJacobiEnergy_gt_succ_mul_nextBeta
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn le_rfl

/-- Calibrated scale completion has an unconditional linear lower bound in every positive chamber. -/
theorem succ_div_sixteen_lt_scaleCompletedRelativeArithmeticSource
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    (n + 1 : ℝ) / 16 < scaleCompletedRelativeArithmeticSource w n := by
  rw [scaleCompletedRelativeArithmeticSource_eq_jacobiEnergy_div_christoffel hw hn hH]
  have hbeta : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedFarRightNormalizedMoment w) (n + 1) :=
    HTGeometry.monicOrthoBeta_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega) (by omega)
  apply (lt_div_iff₀ (mul_pos (by norm_num) hbeta)).2
  have henergy := adaptiveOrthoJacobiEnergy_gt_succ_mul_nextBeta
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn le_rfl
  nlinarith

/-- Scale-completed source remains strictly positive in every positive current admission chamber. -/
theorem scaleCompletedRelativeArithmeticSource_pos
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    0 < scaleCompletedRelativeArithmeticSource w n := by
  rw [scaleCompletedRelativeArithmeticSource_eq_jacobiEnergy_div_christoffel hw hn hH]
  exact div_pos
    (HTGeometry.adaptiveOrthoJacobiEnergy_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn le_rfl)
    (mul_pos (by norm_num)
      (HTGeometry.monicOrthoBeta_pos_below
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega) (by omega)))

/-- Fixed-degree canonical Christoffel scale recedes to the arcsine coordinate scale `1`. -/
theorem tendsto_admissionChristoffelScaleSq
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => admissionChristoffelScaleSq w n) atTop (nhds 1) := by
  have hnext := tendsto_normalizedAdmissionNorm (n := n + 1) (by omega)
  have hcurrent := tendsto_normalizedAdmissionNorm (n := n) hn
  have hcurrentPos := XiShiftedArcsineAdmission.momentFunctional_amplitude_sq_pos hn
  have hratio := hnext.div hcurrent (ne_of_gt hcurrentPos)
  have hscaled := (tendsto_const_nhds.mul hratio :
    Tendsto
      (fun w : ℝ => 16 *
        (normalizedAdmissionNorm w (n + 1) / normalizedAdmissionNorm w n))
      atTop
      (nhds (16 *
        (HTGeometry.momentFunctional
            GaloisForLFunctions.HTGeometry.normalizedCentralBinom
            ((Arc.amplitude (n + 1)) ^ 2) /
          HTGeometry.momentFunctional
            GaloisForLFunctions.HTGeometry.normalizedCentralBinom
            ((Arc.amplitude n) ^ 2)))))
  have hlimit :
      16 *
          (HTGeometry.momentFunctional
              GaloisForLFunctions.HTGeometry.normalizedCentralBinom
              ((Arc.amplitude (n + 1)) ^ 2) /
            HTGeometry.momentFunctional
              GaloisForLFunctions.HTGeometry.normalizedCentralBinom
              ((Arc.amplitude n) ^ 2)) = 1 := by
    rw [XiShiftedArcsineAdmission.momentFunctional_amplitude_sq (by omega),
      XiShiftedArcsineAdmission.momentFunctional_amplitude_sq hn]
    simp only [XiShiftedArcsineAdmission.monicScale]
    field_simp
    have hrExp : 2 * (n + 1) = 2 * n + 2 := by omega
    have htwoExp : 2 * n + 2 - 1 = (2 * n - 1) + 2 := by omega
    rw [hrExp, htwoExp, pow_add]
    norm_num
    ring
  rw [hlimit] at hscaled
  apply hscaled.congr'
  exact Filter.Eventually.of_forall fun w => by
    unfold admissionChristoffelScaleSq
    ring

/-- Fixed-degree scale-completed literal arithmetic source retains exact arcsine recession. -/
theorem tendsto_scaleCompletedRelativeArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => scaleCompletedRelativeArithmeticSource w n) atTop
      (nhds ((n : ℝ) + 3 / 8)) := by
  have hdiv := (tendsto_relativeArithmeticSource hn).div
    (tendsto_admissionChristoffelScaleSq hn) one_ne_zero
  unfold scaleCompletedRelativeArithmeticSource
  change Tendsto
    ((fun w : ℝ => relativeArithmeticSource w n) /
      (fun w : ℝ => admissionChristoffelScaleSq w n)) atTop
      (nhds ((n : ℝ) + 3 / 8))
  simpa only [div_one] using hdiv

/-- Every fixed positive degree eventually beats degree after both amplitude and coordinate gauge
are removed. -/
theorem scaleCompletedRelativeArithmeticSource_eventually_gt_degree
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop, (n : ℝ) < scaleCompletedRelativeArithmeticSource w n := by
  have htarget : (n : ℝ) < (n : ℝ) + 3 / 8 := by norm_num
  exact (tendsto_scaleCompletedRelativeArithmeticSource hn).eventually
    (Ioi_mem_nhds htarget)

end XiShiftedCanonicalAdmission

namespace XiShiftedArcsineAdmission

/-- Christoffel coordinate scale of consecutive coordinate-dilated canonical admissions. -/
def coordinateDilatedAdmissionChristoffelScaleSq (r : ℝ) (n : ℕ) : ℝ :=
  16 *
      HTGeometry.momentFunctional (coordinateDilatedMoment r)
        ((coordinateDilatedAmplitude r (n + 1)) ^ 2) /
    HTGeometry.momentFunctional (coordinateDilatedMoment r)
      ((coordinateDilatedAmplitude r n) ^ 2)

/-- The current Christoffel scale recovers exactly the missing coordinate weight `r²`. -/
theorem coordinateDilatedAdmissionChristoffelScaleSq_eq
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    coordinateDilatedAdmissionChristoffelScaleSq r n = r ^ 2 := by
  rw [coordinateDilatedAdmissionChristoffelScaleSq,
    momentFunctional_coordinateDilatedAmplitude_sq hr (n + 1),
    momentFunctional_coordinateDilatedAmplitude_sq hr n,
    momentFunctional_amplitude_sq (by omega),
    momentFunctional_amplitude_sq hn]
  simp only [monicScale]
  field_simp [hr]
  have hrExp : 2 * (n + 1) = 2 * n + 2 := by omega
  have htwoExp : 2 * n + 2 - 1 = (2 * n - 1) + 2 := by omega
  rw [hrExp, htwoExp, pow_add, pow_add]
  norm_num
  ring

/-- **Exact coordinate-gauge cancellation.**  Completing source/norm by the current next
Christoffel ratio restores `n + 3/8` on every nonzero coordinate dilation, uniformly in degree. -/
theorem coordinateDilated_scaleCompletedSource_eq
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (HTGeometry.momentFunctional (coordinateDilatedMoment r)
          (xiShiftedBoundaryAdaptiveShearPolynomial
            (coordinateDilatedAmplitude r n)) /
        HTGeometry.momentFunctional (coordinateDilatedMoment r)
          ((coordinateDilatedAmplitude r n) ^ 2)) /
      coordinateDilatedAdmissionChristoffelScaleSq r n =
        (n : ℝ) + 3 / 8 := by
  rw [coordinateDilated_adaptiveShear_div_norm hr hn,
    coordinateDilatedAdmissionChristoffelScaleSq_eq hr hn]
  field_simp [hr]

end XiShiftedArcsineAdmission

end

end RHTower
