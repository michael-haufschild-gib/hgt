import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullMetricTwoJet

/-!
# Actual massless BM background in the upper-half-plane chart

The massless four-dimensional unit-radius Birmingham--Mokhtari metric is
`diag(-(r^(2 : ℕ)-1), (r^(2 : ℕ)-1)^(-1), r^(2 : ℕ)/y^(2 : ℕ), r^(2 : ℕ)/y^(2 : ℕ))` in coordinates `(t,r,x,y)`.
BM Eqs. (1)--(4) fix the background and cosmological convention:
https://arxiv.org/pdf/hep-th/0609028 .

Its explicit complete metric two-jet is identified with actual coordinate derivatives, and
its full Ricci, scalar, and Einstein contractions are proved symbolically. Nondegeneracy and
the vacuum equation follow everywhere on the exterior chart `r>1, y>0`. Global horizon descent,
nonlinear perturbation gauge completion, and causal boundary projection remain separate.
-/

namespace RHTower.D4BMBackground
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ContDiff
noncomputable section

/-- Static massless BM metric in the upper-half-plane horizon chart `(t,r,x,y)`. -/
def metric (r y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![-(r ^ 2 - 1), (r ^ 2 - 1)⁻¹, r ^ 2 * y⁻¹ ^ 2, r ^ 2 * y⁻¹ ^ 2]

private def firstDiagonal (r y : ℂ) (k : Fin 4) : Fin 4 → ℂ :=
  if k = 1 then ![-2*r, -2*r*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ), 2*r*y⁻¹^(2 : ℕ)]
  else if k = 3 then ![0, 0, -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ), -2*r^(2 : ℕ)*y⁻¹^(3 : ℕ)]
  else 0

private def secondDiagonal (r y : ℂ) (k l : Fin 4) : Fin 4 → ℂ :=
  if k = 1 ∧ l = 1 then ![-2, -2*(r^(2 : ℕ)-1)⁻¹^(2 : ℕ)+8*r^(2 : ℕ)*(r^(2 : ℕ)-1)⁻¹^(3 : ℕ),
    2*y⁻¹^(2 : ℕ), 2*y⁻¹^(2 : ℕ)]
  else if (k = 1 ∧ l = 3) ∨ (k = 3 ∧ l = 1) then ![0,0,-4*r*y⁻¹^(3 : ℕ),-4*r*y⁻¹^(3 : ℕ)]
  else if k = 3 ∧ l = 3 then ![0,0,6*r^(2 : ℕ)*y⁻¹^(4 : ℕ),6*r^(2 : ℕ)*y⁻¹^(4 : ℕ)]
  else 0

/-- Complete explicit background jet, including its mixed radial/horizon derivatives. -/
def jet (r y : ℂ) : CoordinateMetricTwoJet 4 ℂ where
  metric := metric r y
  first k := Matrix.diagonal (firstDiagonal r y k)
  second k l := Matrix.diagonal (secondDiagonal r y k l)

/-- Exact nondegenerate background determinant. -/
theorem metric_det (r y : ℂ) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (metric r y).det = -(r^(4 : ℕ) * y⁻¹^(4 : ℕ)) := by
  simp [metric, Matrix.det_diagonal, Fin.prod_univ_succ]
  field_simp
  ring

/-- Actual inverse, with every radial and horizon factor retained. -/
theorem metric_inverse (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (metric r y)⁻¹ = Matrix.diagonal ![-(r^(2 : ℕ)-1)⁻¹, r^(2 : ℕ)-1, y^(2 : ℕ)*r⁻¹^(2 : ℕ), y^(2 : ℕ)*r⁻¹^(2 : ℕ)] := by
  apply Matrix.inv_eq_left_inv
  rw [metric, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp
  all_goals ring

set_option maxHeartbeats 1600000 in
/-- Curvature of the full background, evaluated from the literal metric-jet contractions. -/
theorem jet_ricci (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    (jet r y).ricci i j = -3 * metric r y i j := by
  simp only [CoordinateMetricTwoJet.ricci, CoordinateMetricTwoJet.riemann,
    CoordinateMetricTwoJet.christoffelDerivative, CoordinateMetricTwoJet.christoffel,
    CoordinateMetricTwoJet.inverseDerivative, jet, metric_inverse r y hr hy hf]
  fin_cases i <;> fin_cases j
  all_goals simp [Fin.sum_univ_succ, Matrix.diagonal_apply,
    firstDiagonal, secondDiagonal, metric]
  all_goals field_simp
  all_goals ring



/-- The scalar curvature follows from the proved Ricci tensor and actual inverse. -/
theorem jet_scalar (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (jet r y).scalar = -12 := by
  simp only [CoordinateMetricTwoJet.scalar, jet_ricci r y hr hy hf]
  simp only [jet, metric_inverse r y hr hy hf]
  simp [Fin.sum_univ_succ, metric]
  field_simp
  ring

/-- Exact cosmological vacuum identity in the corpus curvature convention. -/
theorem jet_einstein (r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    (jet r y).einstein i j = 3 * metric r y i j := by
  rw [CoordinateMetricTwoJet.einstein, jet_ricci r y hr hy hf, jet_scalar r y hr hy hf]
  change -3 * metric r y i j - 1 / 2 * (-12) * metric r y i j = _
  ring

private def coordinateJet (v : ℂ) (k : Fin 4) : ScalarTwoJet (Fin 4) ℂ :=
  ⟨v, fun i => if i = k then 1 else 0, fun _ _ => 0⟩

private theorem coordinateJet_correct (x : Fin 4 → ℝ) (k : Fin 4) :
    ScalarTwoJet.ofField (fun z : Fin 4 → ℝ => (z k : ℂ)) x = coordinateJet (x k) k := by
  have hd (i : Fin 4) :
      ScalarTwoJet.coordDeriv i (fun z : Fin 4 → ℝ => (z k : ℂ)) =
        fun _ => if i = k then 1 else 0 := by
    funext z
    change fderiv ℝ (Complex.ofRealCLM.comp (ContinuousLinearMap.proj k)) z (Pi.single i 1) = _
    rw [ContinuousLinearMap.fderiv]
    by_cases hi : i = k
    · simp [hi]
    · simp [hi, Ne.symm hi]
  ext i j
  · rfl
  · exact congrFun (hd i) x
  · change ScalarTwoJet.coordDeriv i
      (ScalarTwoJet.coordDeriv j (fun z : Fin 4 → ℝ => (z k : ℂ))) x = 0
    rw [hd]
    simp [ScalarTwoJet.coordDeriv]

private abbrev Expr := ScalarTwoJet.Expression (Fin 4)
private def radial : Expr := .atom 1
private def height : Expr := .atom 3
private def blackening : Expr := (radial.mul radial).add (.constant (-1))
private def angular : Expr := (radial.mul radial).mul (height.mul height).inv
private def diagonalExpression : Fin 4 → Expr := ![blackening.neg, blackening.inv, angular, angular]
private def diagonalValues (r y : ℂ) : Fin 4 → ℂ :=
  ![-(r ^ 2 - 1), (r ^ 2 - 1)⁻¹, r ^ 2 * y⁻¹ ^ 2, r ^ 2 * y⁻¹ ^ 2]

private theorem diagonalExpression_eval (a : Fin 4 → ℂ) (i : Fin 4) :
    (diagonalExpression i).eval a = diagonalValues (a 1) (a 3) i := by
  fin_cases i <;> simp [diagonalExpression, blackening, angular, radial, height,
    ScalarTwoJet.Expression.eval, diagonalValues, pow_two, sub_eq_add_neg]

private theorem diagonalExpression_regular (a : Fin 4 → ℂ) (hy : a 3 ≠ 0)
    (hf : (a 1)^(2 : ℕ)-1 ≠ 0) (i : Fin 4) : (diagonalExpression i).Regular a := by
  have hf' : a 1 * a 1 + -1 ≠ 0 := by simpa [pow_two, sub_eq_add_neg] using hf
  fin_cases i <;> simp [diagonalExpression, blackening, angular, radial, height,
    ScalarTwoJet.Expression.Regular, ScalarTwoJet.Expression.eval, hy, hf']

private theorem diagonalExpression_jet (a : Fin 4 → ℂ) (hy : a 3 ≠ 0) (i : Fin 4) :
    (diagonalExpression i).evalJet (fun k => coordinateJet (a k) k) =
      ⟨diagonalValues (a 1) (a 3) i, fun k => firstDiagonal (a 1) (a 3) k i,
        fun k l => secondDiagonal (a 1) (a 3) k l i⟩ := by
  ext k l
  · rw [ScalarTwoJet.Expression.evalJet_value]
    exact diagonalExpression_eval a i
  · fin_cases i <;> fin_cases k <;>
      simp [diagonalExpression, blackening, angular, radial, height, firstDiagonal,
        ScalarTwoJet.Expression.evalJet, coordinateJet, ScalarTwoJet.mul, ScalarTwoJet.add,
        ScalarTwoJet.constant, ScalarTwoJet.neg, ScalarTwoJet.inv]
    all_goals ring_nf
    all_goals field_simp
  · fin_cases i <;> fin_cases k <;> fin_cases l <;>
      simp [diagonalExpression, blackening, angular, radial, height, secondDiagonal,
        ScalarTwoJet.Expression.evalJet, coordinateJet, ScalarTwoJet.mul, ScalarTwoJet.add,
        ScalarTwoJet.constant, ScalarTwoJet.neg, ScalarTwoJet.inv]
    all_goals ring_nf
    all_goals field_simp
    all_goals ring

set_option maxHeartbeats 800000 in
private theorem diagonalValues_jet (x : Fin 4 → ℝ) (hy : (x 3 : ℂ) ≠ 0)
    (hf : (x 1 : ℂ)^(2 : ℕ)-1 ≠ 0) (i : Fin 4) :
    ScalarTwoJet.ofField (fun z : Fin 4 → ℝ => diagonalValues (z 1) (z 3) i) x =
      ⟨diagonalValues (x 1) (x 3) i, fun k => firstDiagonal (x 1) (x 3) k i,
        fun k l => secondDiagonal (x 1) (x 3) k l i⟩ := by
  have ha (k : Fin 4) : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => (z k : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)).contDiffAt
  have h := ((diagonalExpression i).eval_jet_correct ha
    (diagonalExpression_regular (fun k => (x k : ℂ)) hy hf i)).2
  have heq : (fun z : Fin 4 → ℝ => (diagonalExpression i).eval (fun k => (z k : ℂ))) =
      fun z => diagonalValues (z 1) (z 3) i := by
    funext z
    exact diagonalExpression_eval _ i
  rw [heq] at h
  simp_rw [coordinateJet_correct] at h
  exact h.trans (diagonalExpression_jet _ hy i)

/-- The explicit background array is its actual full coordinate metric two-jet. -/
theorem jet_correct (x : Fin 4 → ℝ) (hy : (x 3 : ℂ) ≠ 0) (hf : (x 1 : ℂ)^(2 : ℕ)-1 ≠ 0) :
    jet (x 1) (x 3) =
      D4BMMetricReconstruction.ofMetricField (fun z => metric (z 1) (z 3)) x := by
  have hfield (i j : Fin 4) :
      ScalarTwoJet.ofField (fun z : Fin 4 → ℝ => metric (z 1) (z 3) i j) x =
        ⟨metric (x 1) (x 3) i j,
          fun k => Matrix.diagonal (firstDiagonal (x 1) (x 3) k) i j,
          fun k l => Matrix.diagonal (secondDiagonal (x 1) (x 3) k l) i j⟩ := by
    by_cases hij : i = j
    · subst j
      simpa [metric, diagonalValues] using diagonalValues_jet x hy hf i
    · simp [metric, hij, ScalarTwoJet.ofField_constant,
        ScalarTwoJet.constant]
  change CoordinateMetricTwoJet.mk _ _ _ = CoordinateMetricTwoJet.mk _ _ _
  congr 1
  · funext k i j
    exact (congrArg (fun J => J.first k) (hfield i j)).symm
  · funext k l i j
    exact (congrArg (fun J => J.second k l) (hfield i j)).symm

/-- The geometric exterior chart; no dynamical or spectral property is put into its definition. -/
abbrev ExteriorPoint := {x : Fin 4 → ℝ // 1 < x 1 ∧ 0 < x 3}

private theorem exterior_factors (p : ExteriorPoint) :
    (p.val 1 : ℂ) ≠ 0 ∧ (p.val 3 : ℂ) ≠ 0 ∧ (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
  have hr : p.val 1 ≠ 0 := ne_of_gt (lt_trans zero_lt_one p.property.1)
  have hy : p.val 3 ≠ 0 := ne_of_gt p.property.2
  have hf : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
  exact ⟨by exact_mod_cast hr, by exact_mod_cast hy, by exact_mod_cast hf⟩

/-- Nondegeneracy is proved from the explicit determinant on the physical exterior chart. -/
theorem exterior_metric_det_ne_zero (p : ExteriorPoint) :
    (metric (p.val 1) (p.val 3)).det ≠ 0 := by
  obtain ⟨hr,hy,hf⟩ := exterior_factors p
  rw [metric_det _ _ hf]
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 hr) (pow_ne_zero 4 (inv_ne_zero hy)))

/-- The actual metric has all local coordinate derivatives on its physical chart. -/
theorem exterior_metric_contDiffAt (p : ExteriorPoint) (i j : Fin 4) {n : ℕ∞ω} :
    ContDiffAt ℝ n (fun x : Fin 4 → ℝ => metric (x 1) (x 3) i j) p.val := by
  obtain ⟨_,hy,hf⟩ := exterior_factors p
  have hc (k : Fin 4) : ContDiffAt ℝ n (fun x : Fin 4 → ℝ => (x k : ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)).contDiffAt
  have hF : ContDiffAt ℝ n (fun x : Fin 4 → ℝ => (x 1 : ℂ)^(2 : ℕ)-1) p.val :=
    ((hc 1).pow 2).sub contDiffAt_const
  have hA : ContDiffAt ℝ n (fun x : Fin 4 → ℝ => (x 1 : ℂ)^(2 : ℕ)*(x 3 : ℂ)⁻¹^(2 : ℕ)) p.val :=
    ((hc 1).pow 2).mul (((hc 3).inv hy).pow 2)
  by_cases hij : i = j
  · subst j
    fin_cases i
    · simpa [metric] using hF.neg
    · change ContDiffAt ℝ n (fun x : Fin 4 → ℝ => ((x 1 : ℂ)^(2 : ℕ)-1)⁻¹) p.val
      exact hF.inv hf
    · simpa [metric] using hA
    · simpa [metric] using hA
  · simpa [metric, hij] using
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : Fin 4 → ℝ => (0 : ℂ)) p.val)

/-- Literal background field jet, on the physical upper-half-plane exterior chart. -/
def actualJet (p : ExteriorPoint) : CoordinateMetricTwoJet 4 ℂ :=
  D4BMMetricReconstruction.ofMetricField (fun x => metric (x 1) (x 3)) p.val

/-- Identification of every actual background derivative, with no supplied jet data. -/
theorem actualJet_eq (p : ExteriorPoint) : actualJet p = jet (p.val 1) (p.val 3) :=
  (jet_correct p.val (exterior_factors p).2.1 (exterior_factors p).2.2).symm

/-- The literal background solves the cosmological equation with `Lambda=-3` everywhere
in its physical chart. This uses the proved derivative realization and full curvature. -/
theorem exterior_vacuum (p : ExteriorPoint) (i j : Fin 4) :
    (actualJet p).einstein i j - 3 * (actualJet p).metric i j = 0 := by
  rw [actualJet_eq]
  obtain ⟨hr,hy,hf⟩ := exterior_factors p
  rw [jet_einstein _ _ hr hy hf]
  simp [jet]

/-- Actual Einstein variations of every order are admitted at this proved background. -/
theorem exterior_source_contDiffAt (p : ExteriorPoint) (i j : Fin 4) {n : ℕ∞ω} :
    ContDiffAt ℂ n (ComplexCoordinateMetricTwoJet.einsteinComponent i j)
      (ComplexCoordinateMetricTwoJet.toSpace (actualJet p)) := by
  apply ComplexCoordinateMetricTwoJet.contDiffAt_einsteinComponent
  exact exterior_metric_det_ne_zero p

end
end RHTower.D4BMBackground
