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
    _ ≤ _ := by linarith only [tailMass_antitone P hs]

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
    have hnonneg : 0 ≤ 1 + dirichletTailMass P σ := by
      linarith only [dirichletTailMass_nonneg P σ]
    have hc := mul_le_mul_of_nonneg_left hsq hnonneg
    exact hb.trans (by simpa only [mul_one] using hc)

private theorem halfPlaneAnnihilator_real (P : MvPolynomial (Fin 2) ℝ≥0) (σ x : ℝ) :
    halfPlaneAnnihilator P σ ((x - σ + 1 / 2 : ℝ) : ℂ) = dirichletEval (x : ℂ) P := by
  unfold halfPlaneAnnihilator
  have he : ((x - σ + 1 / 2 : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) = (x : ℂ) := by
    push_cast
    ring
  rw [he]

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
  change analyticOrderAt (fun s => dirichletEval (s + ((σ - 1 / 2 : ℝ) : ℂ)) P)
    (ρ - ((σ - 1 / 2 : ℝ) : ℂ)) = analyticOrderAt (fun s => dirichletEval s P) ρ
  have hd := (hasDerivAt_id (ρ - ((σ - 1 / 2 : ℝ) : ℂ))).add_const ((σ - 1 / 2 : ℝ) : ℂ)
  change HasDerivAt (fun s : ℂ => s + ((σ - 1 / 2 : ℝ) : ℂ)) 1
    (ρ - ((σ - 1 / 2 : ℝ) : ℂ)) at hd
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := fun s => dirichletEval s P)
    (z₀ := ρ - ((σ - 1 / 2 : ℝ) : ℂ))
    (g := fun s : ℂ => s + ((σ - 1 / 2 : ℝ) : ℂ))
    (analyticAt_id.add analyticAt_const)
    (by rw [hd.deriv]; exact one_ne_zero)
  simpa only [Function.comp_def, sub_add_cancel] using h

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
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
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


private theorem eval_conj (P : MvPolynomial (Fin 2) ℝ≥0) (s : ℂ) :
    dirichletEval (conj s) P = conj (dirichletEval s P) := by
  simp only [dirichletEval_eq_frequency_sum, map_sum, map_mul, ← Complex.exp_conj,
    map_neg, Complex.conj_ofReal]

private theorem order_conj (P : MvPolynomial (Fin 2) ℝ≥0) (ρ : ℂ) :
    analyticOrderNatAt (fun s => dirichletEval s P) (conj ρ) =
      analyticOrderNatAt (fun s => dirichletEval s P) ρ := by
  unfold analyticOrderNatAt
  congr 1
  exact _root_.RHTower.analyticOrderAt_conj_of_conjEquivariant (eval_conj P)
    ((differentiable_dirichletEval P).analyticAt ρ)
    ((differentiable_dirichletEval P).analyticAt (conj ρ))

private theorem greenCost_conj (σ x : ℝ) (ρ : ℂ) :
    annihilatorGreenCost σ x (conj ρ) = annihilatorGreenCost σ x ρ := by
  have hn : conj ρ + ((x - 2 * σ : ℝ) : ℂ) = conj (ρ + ((x - 2 * σ : ℝ) : ℂ)) := by
    rw [map_add, Complex.conj_ofReal]
  have hd : conj ρ - (x : ℂ) = conj (ρ - (x : ℂ)) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [annihilatorGreenCost, hn, hd, RCLike.norm_conj, RCLike.norm_conj]
  rfl

/-- A nonreal zero contributes twice its multiplicity-weighted Green cost,
because a positive Dirichlet polynomial has the conjugate zero as well. -/
theorem conjugate_zero_mass_cost {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {σ x : ℝ} (hx : σ < x) {ρ : ℂ}
    (hρ : σ < ρ.re) (hz : dirichletEval ρ P = 0) (hγ : ρ.im ≠ 0) :
    2 * (analyticOrderNatAt (fun s => dirichletEval s P) ρ : ℝ) *
      annihilatorGreenCost σ x ρ ≤
        Real.log (1 + dirichletTailMass P σ) - Real.log (1 + dirichletTailMass P x) := by
  classical
  let z : AnnihilatorZeroAbove P σ := ⟨ρ, hz, hρ⟩
  let zc : AnnihilatorZeroAbove P σ := ⟨conj ρ, by rw [eval_conj, hz, map_zero], by
    simpa only [Complex.conj_re] using hρ⟩
  have hne : z ≠ zc := by
    intro h
    have he := congrArg (fun z : AnnihilatorZeroAbove P σ => (z : ℂ).im) h
    change ρ.im = (conj ρ).im at he
    rw [Complex.conj_im] at he
    exact hγ (by linarith only [he])
  have hb := finite_zero_divisor_mass_budget hP hx ({z, zc} : Finset (AnnihilatorZeroAbove P σ))
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne), Finset.sum_singleton] at hb
  change (analyticOrderNatAt (fun s => dirichletEval s P) ρ : ℝ) * annihilatorGreenCost σ x ρ +
    (analyticOrderNatAt (fun s => dirichletEval s P) (conj ρ) : ℝ) *
      annihilatorGreenCost σ x (conj ρ) ≤ _ at hb
  rw [order_conj, greenCost_conj] at hb
  linarith only [hb]

private theorem eval_order_ne_top {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (ρ : ℂ) :
    analyticOrderAt (fun s => dirichletEval s P) ρ ≠ ⊤ := by
  intro ht
  have ha : AnalyticOnNhd ℂ (fun s => dirichletEval s P) Set.univ :=
    fun s _ => (differentiable_dirichletEval P).analyticAt s
  have he : (fun s => dirichletEval s P) =ᶠ[𝓝 ρ] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp ht] with s hs
    simpa using hs
  have hz := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ ρ) he
  exact eval_real_ne_zero hP 0 (by simpa using hz (Set.mem_univ (0 : ℂ)))

/-- Exponential mass base obtained by balancing the real observation point
against the distance of a zero from the boundary line. -/
def multiplicityMassBase (σ : ℝ) (ρ : ℂ) : ℝ :=
  (Real.sqrt ((ρ.re - σ) ^ 2 + ρ.im ^ 2) + (ρ.re - σ)) /
    (Real.sqrt ((ρ.re - σ) ^ 2 + ρ.im ^ 2) - (ρ.re - σ))

private theorem radius_gt_depth {σ : ℝ} {ρ : ℂ} (hρ : σ < ρ.re) (hγ : ρ.im ≠ 0) :
    ρ.re - σ < Real.sqrt ((ρ.re - σ) ^ 2 + ρ.im ^ 2) := by
  have hg : 0 < ρ.im ^ 2 := sq_pos_of_ne_zero hγ
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg (ρ.re - σ)) (sq_nonneg ρ.im))
  have hn := Real.sqrt_nonneg ((ρ.re - σ) ^ 2 + ρ.im ^ 2)
  nlinarith only [hg, hs, hn, hρ]

theorem multiplicityMassBase_gt_one {σ : ℝ} {ρ : ℂ}
    (hρ : σ < ρ.re) (hγ : ρ.im ≠ 0) : 1 < multiplicityMassBase σ ρ := by
  unfold multiplicityMassBase
  apply (one_lt_div (sub_pos.mpr (radius_gt_depth hρ hγ))).mpr
  linarith only [hρ]

private theorem two_green_eq_log_ratio (σ x : ℝ) (ρ : ℂ) :
    2 * annihilatorGreenCost σ x ρ =
      Real.log ((((ρ.re - σ) + (x - σ)) ^ 2 + ρ.im ^ 2) /
        (((ρ.re - σ) - (x - σ)) ^ 2 + ρ.im ^ 2)) := by
  have hn : ‖ρ + ((x - 2 * σ : ℝ) : ℂ)‖ ^ 2 =
      ((ρ.re - σ) + (x - σ)) ^ 2 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    ring
  have hd : ‖ρ - (x : ℂ)‖ ^ 2 = ((ρ.re - σ) - (x - σ)) ^ 2 + ρ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  calc
    _ = Real.log ((‖ρ + ((x - 2 * σ : ℝ) : ℂ)‖ / ‖ρ - (x : ℂ)‖) ^ 2) := by
      rw [Real.log_pow]
      norm_num [annihilatorGreenCost]
    _ = _ := by rw [div_pow, hn, hd]

private theorem balanced_green_cost {σ : ℝ} {ρ : ℂ} (hρ : σ < ρ.re) (hγ : ρ.im ≠ 0) :
    2 * annihilatorGreenCost σ
      (σ + Real.sqrt ((ρ.re - σ) ^ 2 + ρ.im ^ 2)) ρ =
        Real.log (multiplicityMassBase σ ρ) := by
  let δ := ρ.re - σ
  let R := Real.sqrt (δ ^ 2 + ρ.im ^ 2)
  have hR : δ < R := radius_gt_depth hρ hγ
  have hsq : R ^ 2 = δ ^ 2 + ρ.im ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg δ) (sq_nonneg ρ.im))
  have hγsq : 0 < ρ.im ^ 2 := sq_pos_of_ne_zero hγ
  rw [two_green_eq_log_ratio]
  change Real.log (((δ + (σ + R - σ)) ^ 2 + ρ.im ^ 2) /
    ((δ - (σ + R - σ)) ^ 2 + ρ.im ^ 2)) = Real.log ((R + δ) / (R - δ))
  rw [show σ + R - σ = R by ring]
  congr 1
  apply (div_eq_div_iff (by positivity : (δ - R) ^ 2 + ρ.im ^ 2 ≠ 0)
    (sub_pos.mpr hR).ne').mpr
  linear_combination 2 * δ * hsq

/-- The balanced point maximizes the real-axis Green test. The difference
of the squared norm ratios has numerator `2δ(t-R)²`. -/
theorem real_green_cost_le_balanced {σ : ℝ} {ρ : ℂ}
    (hρ : σ < ρ.re) (hγ : ρ.im ≠ 0) (x : ℝ) :
    2 * annihilatorGreenCost σ x ρ ≤ Real.log (multiplicityMassBase σ ρ) := by
  let δ := ρ.re - σ
  let t := x - σ
  let R := Real.sqrt (δ ^ 2 + ρ.im ^ 2)
  have hδ : 0 < δ := sub_pos.mpr hρ
  have hR : δ < R := radius_gt_depth hρ hγ
  have hsq : R ^ 2 = δ ^ 2 + ρ.im ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg δ) (sq_nonneg ρ.im))
  have hg : 0 < ρ.im ^ 2 := sq_pos_of_ne_zero hγ
  have hden : 0 < (δ - t) ^ 2 + ρ.im ^ 2 := by positivity
  have hnum : 0 < (δ + t) ^ 2 + ρ.im ^ 2 := by positivity
  rw [two_green_eq_log_ratio]
  change Real.log (((δ + t) ^ 2 + ρ.im ^ 2) / ((δ - t) ^ 2 + ρ.im ^ 2)) ≤
    Real.log ((R + δ) / (R - δ))
  apply Real.log_le_log (div_pos hnum hden)
  apply (div_le_div_iff₀ hden (sub_pos.mpr hR)).mpr
  have he : (R + δ) * ((δ - t) ^ 2 + ρ.im ^ 2) -
      ((δ + t) ^ 2 + ρ.im ^ 2) * (R - δ) = 2 * δ * (t - R) ^ 2 := by
    linear_combination -2 * δ * hsq
  have hn := mul_nonneg (mul_pos two_pos hδ).le (sq_nonneg (t - R))
  linarith only [he, hn]

/-- Multiplicity has an exponential mass cost at every fixed nonreal point
strictly right of the measurement line, without a frequency cutoff. -/
theorem zero_multiplicity_forces_exponential_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {σ : ℝ} {ρ : ℂ}
    (hρ : σ < ρ.re) (hz : dirichletEval ρ P = 0) (hγ : ρ.im ≠ 0) (n : ℕ)
    (hn : (n : ℕ∞) ≤ analyticOrderAt (fun s => dirichletEval s P) ρ) :
    multiplicityMassBase σ ρ ^ n ≤ 1 + dirichletTailMass P σ := by
  let x := σ + Real.sqrt ((ρ.re - σ) ^ 2 + ρ.im ^ 2)
  have hx : σ < x := by
    have hr := radius_gt_depth hρ hγ
    dsimp only [x]
    linarith only [hr, hρ]
  have hb := conjugate_zero_mass_cost hP hx hρ hz hγ
  have hm : (n : ℝ) ≤ (analyticOrderNatAt (fun s => dirichletEval s P) ρ : ℝ) := by
    have h := ENat.toNat_le_toNat hn (eval_order_ne_top hP ρ)
    rw [ENat.toNat_coe] at h
    exact_mod_cast h
  have hg : 0 < annihilatorGreenCost σ x ρ := greenCost_pos hP hx ⟨ρ, hz, hρ⟩
  have hl : 0 ≤ Real.log (1 + dirichletTailMass P x) :=
    Real.log_nonneg (by linarith only [dirichletTailMass_nonneg P x])
  have he := balanced_green_cost hρ hγ
  change 2 * annihilatorGreenCost σ x ρ = _ at he
  have hlog : (n : ℝ) * Real.log (multiplicityMassBase σ ρ) ≤
      Real.log (1 + dirichletTailMass P σ) := by
    rw [← he]
    have hm' := mul_le_mul_of_nonneg_right hm hg.le
    nlinarith only [hb, hm', hl]
  rw [← Real.log_pow] at hlog
  exact (Real.log_le_log_iff
    (pow_pos ((zero_lt_one.trans (multiplicityMassBase_gt_one hρ hγ))) n)
    (by linarith only [dirichletTailMass_nonneg P σ])).mp hlog

/-- Powers of the positive binomial realize every multiplicity with exponential
left-line mass, showing that exponential growth in the order is attainable. -/
theorem binomial_power_multiplicity_and_mass (σ β : ℝ) (n : ℕ) :
    MvPolynomial.constantCoeff (sharpBinomial β ^ n) = 1 ∧
    analyticOrderAt (fun s => dirichletEval s (sharpBinomial β ^ n))
      (sharpBinomialRoot β) = (n : ℕ∞) ∧
    dirichletTailMass (sharpBinomial β ^ n) σ =
      (1 + Real.exp (Real.log 2 * (β - σ))) ^ n - 1 := by
  have hc : MvPolynomial.constantCoeff (sharpBinomial β ^ n) = 1 := by
    rw [map_pow, sharpBinomial_constantCoeff, one_pow]
  have hsimple : analyticOrderAt (fun s => dirichletEval s (sharpBinomial β))
      (sharpBinomialRoot β) = 1 := by
    apply analyticOrderAt_eq_one_of_unit_tail_mass (sharpBinomial_constantCoeff β)
      (sharpBinomial_vanishes β)
    rw [sharpBinomialRoot_re, dirichletTailMass_sharpBinomial]
    simp only [sub_self, mul_zero, Real.exp_zero]
  refine ⟨hc, ?_, ?_⟩
  · have hf : (fun s => dirichletEval s (sharpBinomial β ^ n)) =
        (fun s => dirichletEval s (sharpBinomial β)) ^ n := by
      funext s
      exact map_pow _ _ _
    rw [hf, analyticOrderAt_pow ((differentiable_dirichletEval (sharpBinomial β)).analyticAt _), hsimple]
    simp
  · have he := norm_eval_real hc σ
    rw [map_pow, norm_pow, norm_eval_real (sharpBinomial_constantCoeff β),
      dirichletTailMass_sharpBinomial] at he
    linarith only [he]

#print axioms conjugate_zero_mass_cost
#print axioms real_green_cost_le_balanced
#print axioms zero_multiplicity_forces_exponential_mass
#print axioms binomial_power_multiplicity_and_mass

#print axioms zero_divisor_mass_budget
#print axioms finite_zero_divisor_mass_budget

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
