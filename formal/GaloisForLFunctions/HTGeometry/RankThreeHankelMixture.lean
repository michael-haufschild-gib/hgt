import GaloisForLFunctions.HilbertMetric.FourthCurvatureMixture
import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet

/-!
# Strict rank-three Hankel mixing

A division-free completion of squares and an integrated cofactor vector
transport strict leading-minor positivity without a uniform pointwise gap.
-/

open MeasureTheory
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A division-free completion of squares for a symmetric rank-three Hankel form. -/
theorem threeByThreeQuadratic_pos_of_minors
    {p0 p2 p4 p6 p8 x y z : ℝ}
    (hp0 : 0 < p0) (hhead : 0 < p0*p4-p2^(2 : ℕ))
    (hdet : 0 < _root_.HilbertMetric.signedEvenHankelThreeDet p0 p2 p4 p6 p8)
    (hz : z ≠ 0) :
    0 < p0*x^(2 : ℕ) + 2*p2*x*y + p4*(y^(2 : ℕ)+2*x*z) + 2*p6*y*z + p8*z^(2 : ℕ) := by
  let d := p0*p4-p2^(2 : ℕ)
  have hd : 0 < d := hhead
  have hid : (p0*d) *
      (p0*x^(2 : ℕ) + 2*p2*x*y + p4*(y^(2 : ℕ)+2*x*z) + 2*p6*y*z + p8*z^(2 : ℕ)) =
      d*(p0*x+p2*y+p4*z)^(2 : ℕ) + (d*y+(p0*p6-p2*p4)*z)^(2 : ℕ) +
        p0*_root_.HilbertMetric.signedEvenHankelThreeDet p0 p2 p4 p6 p8*z^(2 : ℕ) := by
    dsimp only [d, _root_.HilbertMetric.signedEvenHankelThreeDet]
    ring
  have hproduct : 0 < (p0*d) *
      (p0*x^(2 : ℕ) + 2*p2*x*y + p4*(y^(2 : ℕ)+2*x*z) + 2*p6*y*z + p8*z^(2 : ℕ)) := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg hd.le (sq_nonneg _)) (sq_nonneg _))
      (mul_pos (mul_pos hp0 hdet) (sq_pos_of_ne_zero hz))
  exact (mul_pos_iff_of_pos_left (mul_pos hp0 hd)).mp hproduct

/-- Strict rank-three Hankel positivity survives integration without a uniform spectral gap. -/
theorem integral_threeByThree_det_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p0 p2 p4 p6 p8 : α → ℝ)
    (hp0Int : Integrable p0 μ) (hp2Int : Integrable p2 μ)
    (hp4Int : Integrable p4 μ) (hp6Int : Integrable p6 μ) (hp8Int : Integrable p8 μ)
    (hmass : 0 < ∫ x, p0 x ∂μ)
    (hpoint : ∀ᵐ x ∂μ, 0 < p0 x ∧ 0 < p0 x*p4 x-p2 x^(2 : ℕ) ∧
      0 < _root_.HilbertMetric.signedEvenHankelThreeDet (p0 x) (p2 x) (p4 x) (p6 x) (p8 x)) :
    0 < _root_.HilbertMetric.signedEvenHankelThreeDet
      (∫ x, p0 x ∂μ) (∫ x, p2 x ∂μ) (∫ x, p4 x ∂μ)
      (∫ x, p6 x ∂μ) (∫ x, p8 x ∂μ) := by
  let A := ∫ x, p0 x ∂μ
  let B := ∫ x, p2 x ∂μ
  let C := ∫ x, p4 x ∂μ
  let D := ∫ x, p6 x ∂μ
  let E := ∫ x, p8 x ∂μ
  let X := B*D-C^(2 : ℕ)
  let Y := B*C-A*D
  let Z := A*C-B^(2 : ℕ)
  have hZ : 0 < Z := GaloisForLFunctions.HilbertMetric.integral_twoByTwo_det_pos p0 p2 p4 hp0Int hp2Int hp4Int hmass
    (hpoint.mono fun _ hx => ⟨hx.1,hx.2.1⟩)
  let Q : α → ℝ := fun r => X^(2 : ℕ)*p0 r + (2*X*Y)*p2 r +
    (Y^(2 : ℕ)+2*X*Z)*p4 r + (2*Y*Z)*p6 r + Z^(2 : ℕ)*p8 r
  have hQint : Integrable Q μ :=
    ((((hp0Int.const_mul (X^(2 : ℕ))).add (hp2Int.const_mul (2*X*Y))).add
      (hp4Int.const_mul (Y^(2 : ℕ)+2*X*Z))).add (hp6Int.const_mul (2*Y*Z))).add
      (hp8Int.const_mul (Z^(2 : ℕ)))
  have hQpos : ∀ᵐ r ∂μ, 0 < Q r := by
    filter_upwards [hpoint] with r hr
    have h := threeByThreeQuadratic_pos_of_minors
      (x:=X) (y:=Y) hr.1 hr.2.1 hr.2.2 hZ.ne'
    dsimp only [Q]
    convert h using 1; ring
  have hμ : μ ≠ 0 := by
    intro hzero
    apply hmass.ne'
    simp [hzero]
  have hsupport : μ Set.univ ≤ μ (Function.support Q) := by
    apply measure_mono_ae
    filter_upwards [hQpos] with r hr
    intro _
    exact hr.ne'
  have hQpositive : 0 < ∫ r, Q r ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (hQpos.mono fun _ h => h.le) hQint]
    exact (MeasureTheory.Measure.measure_univ_pos.mpr hμ).trans_le hsupport
  have hvalue : (∫ r, Q r ∂μ) =
      Z * _root_.HilbertMetric.signedEvenHankelThreeDet A B C D E := by
    dsimp only [Q]
    rw [integral_add, integral_add, integral_add, integral_add] <;> try fun_prop
    simp only [integral_const_mul]
    dsimp only [A,B,C,D,E,X,Y,Z, _root_.HilbertMetric.signedEvenHankelThreeDet]
    ring
  rw [hvalue] at hQpositive
  exact (mul_pos_iff_of_pos_left hZ).mp hQpositive

end
end GaloisForLFunctions.HTGeometry
