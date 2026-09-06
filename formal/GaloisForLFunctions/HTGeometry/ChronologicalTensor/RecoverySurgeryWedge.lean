import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryMoments

/-!
# The actual limiting wedge and its explicit positive representing measure

The limiting wedge's actual quotient infima equal the sharp Chebyshev costs.
The product of two uniform interval variables, divided by four, gives an
explicit positive measure representing their squared normalized values.
Thus the Hausdorff limit has a moment representation while every member of
the dyadic surgery family fails one at its exact prescribed degree.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set MeasureTheory
open _root_.HTGeometry

def recoveryWedgeCapacity (k : ℕ) (P : cubicHomogeneousSpace k) : ℝ :=
  sSup ((fun p => |recoveryPlaneEval P.val p|) '' recoveryWedge)

theorem recoveryWedge_nonempty : recoveryWedge.Nonempty :=
  ⟨(0,0),by simp [recoveryWedge]⟩

theorem recoveryWedgeCapacity_bound (k : ℕ) (P : cubicHomogeneousSpace k)
    (p : ℝ × ℝ) (hp : p ∈ recoveryWedge) : |recoveryPlaneEval P.val p| ≤ recoveryWedgeCapacity k P :=
  le_csSup ((recoveryWedge_compact.image (recoveryPlaneEval_continuous P.val).abs).bddAbove)
    ⟨p,hp,rfl⟩

theorem recoveryWedgeCapacity_le (k : ℕ) (P : cubicHomogeneousSpace k) (b : ℝ)
    (hb : ∀ p ∈ recoveryWedge, |recoveryPlaneEval P.val p| ≤ b) : recoveryWedgeCapacity k P ≤ b := by
  apply csSup_le (recoveryWedge_nonempty.image _)
  rintro y ⟨p,hp,rfl⟩
  exact hb p hp

theorem recoverySurgeryCapacity_le_wedge (n k : ℕ) (P : cubicHomogeneousSpace k) :
    recoverySurgeryCapacity n k P ≤ recoveryWedgeCapacity k P := by
  apply recoverySurgeryCapacity_le
  intro p hp
  exact recoveryWedgeCapacity_bound k P p hp.1

theorem recoveryWedgeResidual_lower (k : ℕ) (P : cubicHomogeneousSpace (k+1))
    (hP : P ∈ cubicNormalizedResiduals k) : recoveryWedgeGap k ≤ recoveryWedgeCapacity (k+1) P :=
  (recoverySurgeryResidual_prefix_bound k ⟨k,by omega⟩ P hP).trans
    (recoverySurgeryCapacity_le_wedge k (k+1) P)

theorem recoveryWedgeResidual_attainment (k : ℕ) :
    recoveryWedgeCapacity (k+1) ((-recoveryWedgeGap k) • recoveryWedgeExtremal k)=recoveryWedgeGap k := by
  apply le_antisymm _ (recoveryWedgeResidual_lower k _ (recoveryWedgeExtremal_normalized k))
  apply recoveryWedgeCapacity_le
  intro p hp
  change |recoveryPlaneEval ((-recoveryWedgeGap k) • (recoveryWedgeExtremal k).val) p| ≤ _
  rw [recoveryPlaneEval_smul,abs_mul,abs_neg,abs_of_pos (recoveryWedgeGap_positive k)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (recoveryWedgeExtremal_bound k p hp)
    (le_of_lt (recoveryWedgeGap_positive k))

def recoveryWedgeErrors (k : ℕ) : Set ℝ :=
  recoveryWedgeCapacity (k+1) ''
    {P : cubicHomogeneousSpace (k+1) | (cubicHomogeneousMissing k-P).val ∈ cubicCuspAlgebra}

def recoveryWedgeActualGap (k : ℕ) : ℝ := sInf (recoveryWedgeErrors k)

theorem recoveryWedgeErrors_isLeast (k : ℕ) : IsLeast (recoveryWedgeErrors k) (recoveryWedgeGap k) := by
  constructor
  · exact ⟨(-recoveryWedgeGap k) • recoveryWedgeExtremal k,
      (cubicNormalizedResiduals_mem k _).mp (recoveryWedgeExtremal_normalized k),
      recoveryWedgeResidual_attainment k⟩
  · rintro y ⟨P,hP,rfl⟩
    exact recoveryWedgeResidual_lower k P ((cubicNormalizedResiduals_mem k P).mpr hP)

theorem recoveryWedgeActualGap_eq (k : ℕ) : recoveryWedgeActualGap k=recoveryWedgeGap k :=
  (recoveryWedgeErrors_isLeast k).csInf_eq

def recoveryWedgeMeasure : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1*p.2/4)
    ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1)))

theorem recoveryWedgeMeasure_monomial_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x^k) recoveryWedgeMeasure := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1*p.2/4) := by fun_prop
  apply (integrable_map_measure (g := fun x : ℝ => x^k) (continuous_id.pow k).aestronglyMeasurable hc.measurable.aemeasurable).mpr
  have hi : Integrable (fun x : ℝ => x^k) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuous_id.pow k).intervalIntegrable 0 1).1
  have h := (hi.mul_prod hi).div_const ((4 : ℝ)^k)
  simpa only [Function.comp_def, div_pow,mul_pow] using h

theorem recoveryWedgeMeasure_moment (k : ℕ) :
    ∫ x, x^k ∂recoveryWedgeMeasure = recoveryWedgeMoment k := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1*p.2/4) := by fun_prop
  rw [recoveryWedgeMeasure,integral_map (f := fun x : ℝ => x^k) hc.measurable.aemeasurable (continuous_id.pow k).aestronglyMeasurable]
  simp_rw [div_pow,mul_pow]
  have hi : (∫ x, x^k ∂volume.restrict (Ioc (0 : ℝ) 1))=1/(k+1 : ℝ) := by
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ)≤1 by linarith), integral_pow]
    simp only [one_pow,zero_pow (Nat.succ_ne_zero k),sub_zero]
  rw [integral_div,integral_prod_mul (fun x : ℝ => x^k) (fun x : ℝ => x^k)]
  simp only [hi]
  unfold recoveryWedgeMoment
  field_simp

theorem recoveryWedgeActualGap_measure :
    (∀ k : ℕ, Integrable (fun x : ℝ => x^k) recoveryWedgeMeasure) ∧
      ∀ k : ℕ, (recoveryWedgeActualGap k/recoveryWedgeActualGap 0)^2 =
        ∫ x, x^k ∂recoveryWedgeMeasure := by
  refine ⟨recoveryWedgeMeasure_monomial_integrable,?_⟩
  intro k
  rw [recoveryWedgeActualGap_eq,recoveryWedgeActualGap_eq,recoveryWedgeMoment_normalized,
    recoveryWedgeMeasure_moment]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
