import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitMassBoundaryOfPositiveAnnihilators
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.ThePoissonJensenIdentity
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel
import GaloisForLFunctions.RHTower.Reflection

/-!
# A positive annihilator's zero divisor consumes its mass

Poisson–Jensen bounds the complete right-half-plane zero divisor by the drop
of the real logarithmic mass. Conjugate zeros contribute equally, imposing
an exponential mass cost on multiplicity at fixed height and displacement.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Filter Topology MeasureTheory
open scoped NNReal ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator


private theorem monomialLog_nonneg (d : Fin 2 →₀ ℕ) : 0 ≤ monomialLog d := by
  change 0 ≤ (d 0 : ℝ) * Real.log 2 + (d 1 : ℝ) * Real.log 3
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  positivity

private theorem tailMass_antitone (P : MvPolynomial (Fin 2) ℝ≥0) :
    Antitone (dirichletTailMass P) := by
  intro σ τ hστ
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (P.coeff d).coe_nonneg
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hστ (neg_nonpos.mpr (monomialLog_nonneg d))

private theorem norm_eval_le_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) :
    ‖dirichletEval s P‖ ≤ 1 + dirichletTailMass P σ := by
  rw [dirichletEval_eq_one_add_tail hP]
  calc
    _ ≤ 1 + ‖∑ d ∈ P.support.erase 0,
        (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s)‖ := by
      simpa only [norm_one] using norm_add_le (1 : ℂ) _
    _ ≤ 1 + ∑ d ∈ P.support.erase 0,
        ‖(((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s)‖ :=
      add_le_add_left (norm_sum_le _ _) 1
    _ = 1 + dirichletTailMass P s.re := by
      congr 1
      unfold dirichletTailMass
      apply Finset.sum_congr rfl
      intro d _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (P.coeff d).coe_nonneg, Complex.norm_exp, Complex.mul_re,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        neg_zero, zero_mul, sub_zero]
    _ ≤ _ := add_le_add_left (tailMass_antitone P hs) 1

private theorem norm_eval_real {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (x : ℝ) :
    ‖dirichletEval (x : ℂ) P‖ = 1 + dirichletTailMass P x := by
  rw [dirichletEval_ofReal_eq_one_add_tail hP, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith only [dirichletTailMass_nonneg P x] : 0 < 1 + dirichletTailMass P x)]

private theorem eval_real_ne_zero {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (x : ℝ) : dirichletEval (x : ℂ) P ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_eval_real hP]
  linarith only [dirichletTailMass_nonneg P x]

private def halfPlaneAnnihilator (P : MvPolynomial (Fin 2) ℝ≥0) (σ : ℝ) (s : ℂ) : ℂ :=
  dirichletEval (s + ((σ - 1 / 2 : ℝ) : ℂ)) P

private theorem halfPlaneAnnihilator_datum {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (σ : ℝ) :
    ArithmeticInnerFunctionTheory.IsHalfPlaneDatum (halfPlaneAnnihilator P σ) := by
  constructor
  · exact (differentiable_dirichletEval P).comp
      (differentiable_id.add_const ((σ - 1 / 2 : ℝ) : ℂ))
  · refine ⟨1 + dirichletTailMass P σ,
      by linarith only [dirichletTailMass_nonneg P σ], ?_⟩
    intro s hs
    have hb : ‖halfPlaneAnnihilator P σ s‖ ≤ 1 + dirichletTailMass P σ := by
      apply norm_eval_le_mass hP
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith only [hs]
    have hsq : (1 : ℝ) ≤ (‖s‖ + 2) ^ 2 := by nlinarith only [norm_nonneg s, sq_nonneg ‖s‖]
    exact hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq
      (by linarith only [dirichletTailMass_nonneg P σ] : 0 ≤ 1 + dirichletTailMass P σ))

private theorem halfPlaneAnnihilator_real (P : MvPolynomial (Fin 2) ℝ≥0) (σ x : ℝ) :
    halfPlaneAnnihilator P σ ((x - σ + 1 / 2 : ℝ) : ℂ) = dirichletEval (x : ℂ) P := by
  unfold halfPlaneAnnihilator
  congr 1
  push_cast
  ring

private theorem halfPlaneAnnihilator_centre {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {σ x : ℝ} (hx : σ < x) :
    ArithmeticInnerFunctionTheory.IsCentre (halfPlaneAnnihilator P σ)
      ((x - σ + 1 / 2 : ℝ) : ℂ) := by
  constructor
  · simp only [Complex.ofReal_re]
    linarith only [hx]
  · rw [halfPlaneAnnihilator_real]
    exact eval_real_ne_zero hP x
  · refine ⟨1, 0, one_pos, fun t _ => ?_⟩
    simp only [Complex.ofReal_im, Complex.ofReal_zero, zero_mul, add_zero]
    change 1 ≤ ‖dirichletEval ((t : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ)) P‖
    rw [← Complex.ofReal_add, norm_eval_real hP]
    linarith only [dirichletTailMass_nonneg P (t + (σ - 1 / 2))]

/-- Zeros strictly to the right of the line where mass is measured. -/
abbrev AnnihilatorZeroAbove (P : MvPolynomial (Fin 2) ℝ≥0) (σ : ℝ) :=
  {ρ : ℂ // dirichletEval ρ P = 0 ∧ σ < ρ.re}

/-- Half-plane Green cost as seen from a real point `x`. -/
def annihilatorGreenCost (σ x : ℝ) (ρ : ℂ) : ℝ :=
  Real.log (‖ρ + ((x - 2 * σ : ℝ) : ℂ)‖ / ‖ρ - (x : ℂ)‖)

private def shiftedZeroEquiv (P : MvPolynomial (Fin 2) ℝ≥0) (σ : ℝ) :
    AnnihilatorZeroAbove P σ ≃ ArithmeticInnerFunctionTheory.RightZeros (halfPlaneAnnihilator P σ) where
  toFun ρ := ⟨(ρ : ℂ) - ((σ - 1 / 2 : ℝ) : ℂ), by
    constructor
    · simpa only [halfPlaneAnnihilator, sub_add_cancel] using ρ.2.1
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith only [ρ.2.2]⟩
  invFun z := ⟨(z : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ), by
    constructor
    · exact z.2.1
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith only [z.2.2]⟩
  left_inv ρ := Subtype.ext (sub_add_cancel _ _)
  right_inv z := Subtype.ext (add_sub_cancel_right _ _)

private theorem shifted_order (P : MvPolynomial (Fin 2) ℝ≥0) (σ : ℝ) (ρ : ℂ) :
    analyticOrderNatAt (halfPlaneAnnihilator P σ) (ρ - ((σ - 1 / 2 : ℝ) : ℂ)) =
      analyticOrderNatAt (fun s => dirichletEval s P) ρ := by
  unfold analyticOrderNatAt
  congr 1
  have hd := (hasDerivAt_id (ρ - ((σ - 1 / 2 : ℝ) : ℂ))).add_const ((σ - 1 / 2 : ℝ) : ℂ)
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := fun s => dirichletEval s P)
    (z₀ := ρ - ((σ - 1 / 2 : ℝ) : ℂ))
    (g := fun s : ℂ => s + ((σ - 1 / 2 : ℝ) : ℂ))
    (analyticAt_id.add analyticAt_const)
    (by rw [hd.deriv]; exact one_ne_zero)
  simpa only [Function.comp_def, halfPlaneAnnihilator, sub_add_cancel] using h

private theorem shifted_green (σ x : ℝ) (ρ : ℂ) :
    ArithmeticInnerFunctionTheory.greenKernel ((x - σ + 1 / 2 : ℝ) : ℂ)
      (ρ - ((σ - 1 / 2 : ℝ) : ℂ)) = annihilatorGreenCost σ x ρ := by
  unfold ArithmeticInnerFunctionTheory.greenKernel annihilatorGreenCost
  have hn : ρ - ((σ - 1 / 2 : ℝ) : ℂ) + conj ((x - σ + 1 / 2 : ℝ) : ℂ) - 1 =
      ρ + ((x - 2 * σ : ℝ) : ℂ) := by
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  have hd : ρ - ((σ - 1 / 2 : ℝ) : ℂ) - ((x - σ + 1 / 2 : ℝ) : ℂ) =
      ρ - (x : ℂ) := by push_cast; ring
  rw [hn, hd]

private theorem greenCost_pos {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {σ x : ℝ} (hx : σ < x)
    (ρ : AnnihilatorZeroAbove P σ) : 0 < annihilatorGreenCost σ x ρ := by
  rw [← shifted_green]
  apply ArithmeticInnerFunctionTheory.greenKernel_pos
  · simp only [Complex.ofReal_re]
    linarith only [hx]
  · simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [ρ.2.2]
  · intro he
    have hr : (ρ : ℂ) = (x : ℂ) := by
      have he' := congrArg (fun z : ℂ => z + ((σ - 1 / 2 : ℝ) : ℂ)) he
      simpa only [sub_add_cancel, ← Complex.ofReal_add,
        show x - σ + 1 / 2 + (σ - 1 / 2) = x by ring] using he'
    exact eval_real_ne_zero hP x (hr ▸ ρ.2.1)

/-- The complete right-half-plane zero divisor has a finite Green budget,
bounded by the drop of the real logarithmic mass between two lines. -/
theorem zero_divisor_mass_budget {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {σ x : ℝ} (hx : σ < x) :
    Summable (fun ρ : AnnihilatorZeroAbove P σ =>
      (analyticOrderNatAt (fun s => dirichletEval s P) ρ : ℝ) * annihilatorGreenCost σ x ρ) ∧
    (∑' ρ : AnnihilatorZeroAbove P σ,
      (analyticOrderNatAt (fun s => dirichletEval s P) ρ : ℝ) * annihilatorGreenCost σ x ρ) ≤
        Real.log (1 + dirichletTailMass P σ) - Real.log (1 + dirichletTailMass P x) := by
  let E := halfPlaneAnnihilator P σ
  let w : ℂ := ((x - σ + 1 / 2 : ℝ) : ℂ)
  obtain ⟨hint, hsum⟩ := ArithmeticInnerFunctionTheory.hasSum_poissonJensen
    (halfPlaneAnnihilator_datum hP σ) (halfPlaneAnnihilator_centre hP hx)
  have htransport := (shiftedZeroEquiv P σ).hasSum_iff.mpr hsum
  have hfun : (fun ρ : AnnihilatorZeroAbove P σ =>
      (analyticOrderNatAt E ((shiftedZeroEquiv P σ) ρ) : ℝ) *
        ArithmeticInnerFunctionTheory.greenKernel w ((shiftedZeroEquiv P σ) ρ)) =
      (fun ρ : AnnihilatorZeroAbove P σ =>
        (analyticOrderNatAt (fun s => dirichletEval s P) ρ : ℝ) * annihilatorGreenCost σ x ρ) := by
    funext ρ
    change (analyticOrderNatAt (halfPlaneAnnihilator P σ)
      ((ρ : ℂ) - ((σ - 1 / 2 : ℝ) : ℂ)) : ℝ) *
      ArithmeticInnerFunctionTheory.greenKernel ((x - σ + 1 / 2 : ℝ) : ℂ)
        ((ρ : ℂ) - ((σ - 1 / 2 : ℝ) : ℂ)) = _
    rw [shifted_order, shifted_green]
  change HasSum (fun ρ : AnnihilatorZeroAbove P σ =>
    (analyticOrderNatAt E ((shiftedZeroEquiv P σ) ρ) : ℝ) *
      ArithmeticInnerFunctionTheory.greenKernel w ((shiftedZeroEquiv P σ) ρ)) _ at htransport
  rw [hfun] at htransport
  refine ⟨htransport.summable, ?_⟩
  rw [htransport.tsum_eq, halfPlaneAnnihilator_real, norm_eval_real hP]
  apply sub_le_sub_right
  have hk : (fun τ : ℝ => _root_.RHTower.halfPlanePoissonKernel w τ) =
      HTGeometry.halfPlanePoisson (x - σ) := by
    funext τ
    simp only [w, _root_.RHTower.halfPlanePoissonKernel, HTGeometry.halfPlanePoisson,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_sub_cancel_right]
  have hki : Integrable (fun τ : ℝ => _root_.RHTower.halfPlanePoissonKernel w τ) := by
    rw [hk]
    exact HTGeometry.integrable_halfPlanePoisson (sub_pos.mpr hx)
  have hpoint (τ : ℝ) :
      Real.log ‖E (1 / 2 + (τ : ℂ) * I)‖ ≤ Real.log (1 + dirichletTailMass P σ) := by
    have hb : ‖E (1 / 2 + (τ : ℂ) * I)‖ ≤ 1 + dirichletTailMass P σ := by
      apply norm_eval_le_mass hP
      change σ ≤ ((((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) + ((σ - 1 / 2 : ℝ) : ℂ)).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith
    by_cases hz : E (1 / 2 + (τ : ℂ) * I) = 0
    · rw [hz, norm_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith only [dirichletTailMass_nonneg P σ])
    · exact Real.log_le_log (norm_pos_iff.mpr hz) hb
  calc
    _ ≤ ∫ τ : ℝ, Real.log (1 + dirichletTailMass P σ) *
        _root_.RHTower.halfPlanePoissonKernel w τ := by
      apply integral_mono hint (hki.const_mul _)
      intro τ
      apply mul_le_mul_of_nonneg_right (hpoint τ)
      rw [congrFun hk τ]
      exact (HTGeometry.halfPlanePoisson_pos (sub_pos.mpr hx) τ).le
    _ = _ := by
      rw [integral_const_mul, hk, HTGeometry.integral_halfPlanePoisson (sub_pos.mpr hx), mul_one]

/-- Every finite sub-divisor inherits the same mass budget, with its exact multiplicities. -/
theorem finite_zero_divisor_mass_budget {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {σ x : ℝ} (hx : σ < x)
    (S : Finset (AnnihilatorZeroAbove P σ)) :
    (∑ ρ ∈ S, (analyticOrderNatAt (fun s => dirichletEval s P) ρ : ℝ) *
      annihilatorGreenCost σ x ρ) ≤
        Real.log (1 + dirichletTailMass P σ) - Real.log (1 + dirichletTailMass P x) := by
  have h := zero_divisor_mass_budget hP hx
  exact (h.1.sum_le_tsum S (fun ρ _ =>
    mul_nonneg (Nat.cast_nonneg _) (greenCost_pos hP hx ρ).le)).trans h.2

#print axioms zero_divisor_mass_budget
#print axioms finite_zero_divisor_mass_budget

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
