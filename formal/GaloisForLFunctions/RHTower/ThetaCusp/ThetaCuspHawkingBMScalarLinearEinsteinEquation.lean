import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalScalarMetric
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarLinearizedRicciJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCuspMetricSource

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry
open ScalarTwoJet D4BMMetricReconstruction
open Filter Topology
noncomputable section

private def angularLinear : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]

private theorem angularLinear_apply (x : Fin 4 → ℝ) : angularLinear x = angularPoint x := by
  ext i
  fin_cases i <;> rfl

private def projectedPartial (i : Fin 4) (S : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ :=
  if i = 2 then coordDeriv 0 S else if i = 3 then coordDeriv 1 S else fun _ => 0

private theorem lift_partial (S : (Fin 2 → ℝ) → ℂ) (x : Fin 4 → ℝ)
    (hS : DifferentiableAt ℝ S (angularPoint x)) (i : Fin 4) :
    coordDeriv i (fun y => S (angularPoint y)) x = projectedPartial i S (angularPoint x) := by
  have hmap (k : Fin 4) : angularLinear (Pi.single k 1) =
      if k = 2 then Pi.single 0 1 else if k = 3 then Pi.single 1 1 else 0 := by
    fin_cases k <;> ext j <;> fin_cases j <;> simp [angularLinear]
  have hf : DifferentiableAt ℝ S (angularLinear x) := by
    simpa only [angularLinear_apply] using hS
  have hd := hf.hasFDerivAt.comp x angularLinear.hasFDerivAt
  have he : (fun y => S (angularPoint y)) = S ∘ angularLinear := by
    funext y
    simp only [Function.comp_apply, angularLinear_apply]
  rw [he]
  change fderiv ℝ (S ∘ angularLinear) x (Pi.single i 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, hmap]
  fin_cases i <;> simp [projectedPartial, coordDeriv, angularLinear_apply]

private theorem projected_differentiable (S : (Fin 2 → ℝ) → ℂ) (u : Fin 2 → ℝ)
    (hS : ContDiffAt ℝ 2 S u) (i : Fin 4) : DifferentiableAt ℝ (projectedPartial i S) u := by
  fin_cases i
  · simp [projectedPartial]
  · simp [projectedPartial]
  · exact (D4BMHorizon.coordDeriv_hasFDerivAt hS 0).differentiableAt
  · exact (D4BMHorizon.coordDeriv_hasFDerivAt hS 1).differentiableAt

private theorem lift_second (S : (Fin 2 → ℝ) → ℂ) (x : Fin 4 → ℝ)
    (hS : ContDiffAt ℝ 2 S (angularPoint x)) (i j : Fin 4) :
    coordDeriv i (coordDeriv j (fun y => S (angularPoint y))) x =
      projectedPartial i (projectedPartial j S) (angularPoint x) := by
  have hf : ContDiffAt ℝ 2 S (angularLinear x) := by
    simpa only [angularLinear_apply] using hS
  have hv := (angularLinear.continuous.tendsto x).eventually (hf.eventually (by simp))
  have he : coordDeriv j (fun y => S (angularPoint y)) =ᶠ[nhds x]
      (fun y => projectedPartial j S (angularPoint y)) := by
    filter_upwards [hv] with y hy
    apply lift_partial
    simpa only [angularLinear_apply] using hy.differentiableAt (by norm_num)
  change fderiv ℝ _ x (Pi.single i 1) = _
  rw [he.fderiv_eq]
  exact lift_partial _ x (projected_differentiable S _ hS j) i

/-- Actual complete angular pullback jet, retaining both ordered mixed partials. -/
theorem angular_lift_jet (S : (Fin 2 → ℝ) → ℂ) (x : Fin 4 → ℝ)
    (hS : ContDiffAt ℝ 2 S (angularPoint x)) :
    ScalarTwoJet.ofField (fun y => S (angularPoint y)) x =
      ⟨S (angularPoint x), ![0,0,coordDeriv 0 S (angularPoint x),coordDeriv 1 S (angularPoint x)],
      !![0,0,0,0; 0,0,0,0;
        0,0,coordDeriv 0 (coordDeriv 0 S) (angularPoint x),coordDeriv 0 (coordDeriv 1 S) (angularPoint x);
        0,0,coordDeriv 1 (coordDeriv 0 S) (angularPoint x),coordDeriv 1 (coordDeriv 1 S) (angularPoint x)]⟩ := by
  ext i j
  · rfl
  · change coordDeriv i (fun y => S (angularPoint y)) x = _
    rw [lift_partial S x (hS.differentiableAt (by norm_num)) i]
    fin_cases i <;> rfl
  · change coordDeriv i (coordDeriv j (fun y => S (angularPoint y))) x = _
    rw [lift_second S x hS i j]
    fin_cases i <;> fin_cases j <;> simp [projectedPartial, coordDeriv]

private theorem angular_jet_of_laplacian (s : ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (p : D4BMBackground.ExteriorPoint) (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hL : D4BMHorizon.scalarLaplacian S (angularPoint p.val) =
      (s+1)*(s+2)*S (angularPoint p.val)) :
    ofField (fun x => S (angularPoint x)) p.val =
      angular s (p.val 3) (S (angularPoint p.val))
        (coordDeriv 0 S (angularPoint p.val)) (coordDeriv 1 S (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 S) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 1 S) (angularPoint p.val)) := by
  have hy : (p.val 3 : ℂ) ≠ 0 := by exact_mod_cast p.property.2.ne'
  rw [D4BMHorizon.scalarLaplacian_eq S _ p.property.2] at hL
  have hyy : coordDeriv 1 (coordDeriv 1 S) (angularPoint p.val) =
      (s+1)*(s+2)*S (angularPoint p.val)/(p.val 3 : ℂ)^(2 : ℕ) -
        coordDeriv 0 (coordDeriv 0 S) (angularPoint p.val) := by
    change (p.val 3 : ℂ)^(2 : ℕ) *
      (coordDeriv 0 (coordDeriv 0 S) (angularPoint p.val) +
        coordDeriv 1 (coordDeriv 1 S) (angularPoint p.val)) =
      (s+1)*(s+2)*S (angularPoint p.val) at hL
    field_simp
    linear_combination hL
  rw [angular_lift_jet S p.val hS]
  have hc := D4BMHorizon.coordDeriv_commute hS 1 0
  simp only [angular, hc, hyy]

private abbrev Expr := ScalarTwoJet.Expression (Fin 2)

private def radialExpression (s : ℂ) : Matrix (Fin 4) (Fin 4) Expr :=
  let R : Expr := .atom 0
  let Y : Expr := .atom 1
  let F := (R.mul R).add (.constant (-1))
  let T := (.constant (s*(s-3)/2) : Expr).add
    ((.constant (s*(s+1)/2) : Expr).mul (R.inv.mul R.inv))
  let M := (.constant (-s) : Expr).mul
    (((R.mul R).add (.constant (-s))).mul (R.mul F).inv)
  let A := ((R.mul R).neg.add (.constant (-s*(s+1)/2))).mul (Y.inv.mul Y.inv)
  let Z : Expr := .constant 0
  !![T,M,Z,Z; M,T.mul (F.inv.mul F.inv),Z,Z; Z,Z,A,Z; Z,Z,Z,A]

private theorem radialExpression_eval (s r y : ℂ) (i j : Fin 4) :
    (radialExpression s i j).eval ![r,y] = D4BMFundamentalScalarMetric.radialMatrix s r y i j := by
  fin_cases i <;> fin_cases j <;>
    simp [radialExpression, ScalarTwoJet.Expression.eval, D4BMFundamentalScalarMetric.radialMatrix,
      div_eq_mul_inv, mul_inv_rev, pow_two]
  all_goals ring_nf
  all_goals simp

private theorem radialExpression_evalJet (s r y : ℂ) (i j : Fin 4) :
    (radialExpression s i j).evalJet
      ![D4BMFundamentalScalarMetric.coordinateJet r 1, D4BMFundamentalScalarMetric.coordinateJet y 3] =
      radialEntries s r y i j := by
  fin_cases i <;> fin_cases j <;>
    simp [radialExpression, ScalarTwoJet.Expression.evalJet, radialEntries, coord,
      D4BMFundamentalScalarMetric.coordinateJet]

private theorem radialExpression_regular (s r y : ℂ) (hr : r ≠ 0) (hy : y ≠ 0)
    (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) : (radialExpression s i j).Regular ![r,y] := by
  have hf' : r*r + -1 ≠ 0 := by simpa [pow_two, sub_eq_add_neg] using hf
  fin_cases i <;> fin_cases j <;>
    simp [radialExpression, ScalarTwoJet.Expression.Regular, ScalarTwoJet.Expression.eval, hr, hy, hf']

private theorem radial_entry_correct (s : ℂ) (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => D4BMFundamentalScalarMetric.radialMatrix s (x 1) (x 3) i j) p.val ∧
    ofField (fun x : Fin 4 → ℝ => D4BMFundamentalScalarMetric.radialMatrix s (x 1) (x 3) i j) p.val =
      radialEntries s (p.val 1) (p.val 3) i j := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hy : (p.val 3 : ℂ) ≠ 0 := by exact_mod_cast p.property.2.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  let a : Fin 2 → (Fin 4 → ℝ) → ℂ := fun k x => ![(x 1 : ℂ),(x 3 : ℂ)] k
  have ha (k : Fin 2) : ContDiffAt ℝ 2 (a k) p.val := by
    fin_cases k <;> exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ _)).contDiffAt
  have hj : (fun k => ofField (a k) p.val) =
      ![D4BMFundamentalScalarMetric.coordinateJet (p.val 1) 1,
        D4BMFundamentalScalarMetric.coordinateJet (p.val 3) 3] := by
    funext k
    fin_cases k <;> exact D4BMFundamentalScalarMetric.coordinate_jet p.val _
  have he : (fun x => (radialExpression s i j).eval (fun k => a k x)) =
      fun x => D4BMFundamentalScalarMetric.radialMatrix s (x 1) (x 3) i j := by
    funext x
    exact radialExpression_eval s (x 1) (x 3) i j
  have h := (radialExpression s i j).eval_jet_correct ha
    (radialExpression_regular s (p.val 1) (p.val 3) hr hy hf i j)
  rw [he, hj, radialExpression_evalJet] at h
  exact h

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) :
    CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,
    fun k l i j => (J i j).second k l⟩

/-- The actual complete scalar field jet has exactly the derivative data used by
the verified all-component Einstein contraction. -/
theorem field_jet (s a : ℂ) (S : (Fin 2 → ℝ) → ℂ) (p : D4BMBackground.ExteriorPoint)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hL : D4BMHorizon.scalarLaplacian S (angularPoint p.val) =
      (s+1)*(s+2)*S (angularPoint p.val)) :
    ofMetricField (D4BMFundamentalScalarMetric.field s a S) p.val =
      scalarJet s (p.val 1) (p.val 3) (D4BMFundamentalScalarMetric.envelope s a p.val)
        (S (angularPoint p.val)) (coordDeriv 0 S (angularPoint p.val))
        (coordDeriv 1 S (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 S) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 1 S) (angularPoint p.val)) := by
  have hA := D4BMFundamentalScalarMetric.envelope_contDiffAt s a p 2
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift : ContDiffAt ℝ 2 (fun x => S (angularPoint x)) p.val := by
    simpa only [Function.comp_def] using hS.comp p.val hu.contDiffAt
  change assemble _ = assemble _
  congr 1
  funext i j
  change ofField (fun x => (D4BMFundamentalScalarMetric.envelope s a x * S (angularPoint x)) *
    D4BMFundamentalScalarMetric.radialMatrix s (x 1) (x 3) i j) p.val = _
  rw [ofField_mul (hA.mul hLift) (radial_entry_correct s p i j).1,
    ofField_mul hA hLift, D4BMFundamentalScalarMetric.envelope_jet,
    angular_jet_of_laplacian s S p hS hL, (radial_entry_correct s p i j).2]
  rfl

/-- The literal separated scalar metric satisfies every first-order cosmological
Einstein equation on the actual background. -/
theorem field_residual_zero (s a : ℂ) (S : (Fin 2 → ℝ) → ℂ) (p : D4BMBackground.ExteriorPoint)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hL : D4BMHorizon.scalarLaplacian S (angularPoint p.val) =
      (s+1)*(s+2)*S (angularPoint p.val)) (i j : Fin 4) :
    D4BMLinearizedEinsteinSource.residual p
      (ofMetricField (D4BMFundamentalScalarMetric.field s a S) p.val) i j = 0 := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hy : (p.val 3 : ℂ) ≠ 0 := by exact_mod_cast p.property.2.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  rw [D4BMLinearizedEinsteinSource.residual, D4BMBackground.actualJet_eq, field_jet s a S p hS hL]
  exact cosmological_component _ _ _ _ _ _ _ _ _ hr hy hf i j

private theorem ofField_congr_germ {f g : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (h : f =ᶠ[nhds x] g) : ofField f x = ofField g x := by
  have hD : fderiv ℝ f =ᶠ[nhds x] fderiv ℝ g := h.fderiv
  have hd (k : Fin 4) : coordDeriv k f =ᶠ[nhds x] coordDeriv k g := by
    filter_upwards [hD] with y hy
    exact congrArg (fun L => L (Pi.single k 1)) hy
  ext i j
  · exact h.self_of_nhds
  · change fderiv ℝ f x (Pi.single i 1) = fderiv ℝ g x (Pi.single i 1)
    rw [h.fderiv_eq]
  · change fderiv ℝ (coordDeriv j f) x (Pi.single i 1) =
      fderiv ℝ (coordDeriv j g) x (Pi.single i 1)
    rw [(hd j).fderiv_eq]

private theorem ofMetricField_congr_germ {f g : D4BMActualMetricSource.MetricField}
    {x : Fin 4 → ℝ} (h : ∀ i j, (fun y => f y i j) =ᶠ[nhds x] (fun y => g y i j)) :
    ofMetricField f x = ofMetricField g x := by
  change assemble _ = assemble _
  congr 1
  funext i j
  exact ofField_congr_germ (h i j)

private theorem reconstruction_jet (s a : ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (V : Fin 2 → (Fin 2 → ℝ) → ℂ) (p : D4BMBackground.ExteriorPoint) :
    ofMetricField (D4BMFundamentalMetric.perturbation (Complex.I*s)
      (D4BMFundamentalScalarMetric.harmonicParameter s) a 0 S V) p.val =
    ofMetricField (D4BMFundamentalScalarMetric.field s a S) p.val := by
  apply ofMetricField_congr_germ
  intro i j
  have hO : IsOpen {x : Fin 4 → ℝ | 1 < x 1 ∧ 0 < x 3} :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (continuous_apply 3))
  filter_upwards [hO.mem_nhds p.property] with x hx
  exact congrArg (fun M => M i j) (D4BMFundamentalScalarMetric.reconstruction_eq s a S V ⟨x,hx⟩)

/-- Every actual amplitude derivative of the original scalar KI Einstein source
vanishes when its horizon scalar satisfies the matched equation. -/
theorem reconstructed_source_first_zero (s a : ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (V : Fin 2 → (Fin 2 → ℝ) → ℂ) (p : D4BMBackground.ExteriorPoint)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val))
    (hL : D4BMHorizon.scalarLaplacian S (angularPoint p.val) =
      (s+1)*(s+2)*S (angularPoint p.val)) (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMFundamentalMetric.perturbation (Complex.I*s)
        (D4BMFundamentalScalarMetric.harmonicParameter s) a 0 S V) i j) 0 = 0 := by
  rw [(D4BMLinearizedEinsteinSource.fundamental_source_hasDerivAt p (Complex.I*s)
    (D4BMFundamentalScalarMetric.harmonicParameter s) a 0 S V hS hV i j).deriv,
    D4BMFundamentalMetric.fullJet_correct p (Complex.I*s)
      (D4BMFundamentalScalarMetric.harmonicParameter s) a 0 S V hS hV,
    reconstruction_jet s a S V p]
  exact field_residual_zero s a S p hS hL i j

private theorem literal_source_first_zero (s a u : ℂ) (p : D4BMBackground.ExteriorPoint)
    (hq : D4BMFundamentalScalarMetric.harmonicParameter s = D4BMLiteralCusp.scalarQ u)
    (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMLiteralCusp.perturbation (Complex.I*s) u a 0) i j) 0 = 0 := by
  unfold D4BMLiteralCusp.perturbation
  rw [← hq]
  apply reconstructed_source_first_zero s a (D4BMLiteralCusp.scalar u)
    (D4BMLiteralCusp.vector u) p
    (D4BMLiteralCusp.scalar_contDiffAt u 2 _ p.property.2)
    (D4BMLiteralCusp.vector_contDiffAt u 2 _ p.property.2)
  rw [D4BMLiteralCusp.scalar_equation u _ p.property.2, ← hq]
  unfold D4BMFundamentalScalarMetric.harmonicParameter
  ring

/-- The literal complete cusp scalar at the fundamental plus frequency satisfies
all first-order Einstein equations, with its angular equation and regularity discharged. -/
theorem literal_plus_source_first_zero (u a : ℂ) (p : D4BMBackground.ExteriorPoint)
    (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum u))
        u a 0) i j) 0 = 0 := by
  have hf : d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum u) =
      Complex.I*(-u-3/2) := by
    simp only [d4BMCausalQNMPlus, d4BMCausalDecay, D4BMLiteralCusp.radialMomentum,
      Nat.cast_zero, mul_zero, zero_add]
    ring
  rw [hf]
  apply literal_source_first_zero
  unfold D4BMFundamentalScalarMetric.harmonicParameter D4BMLiteralCusp.scalarQ
  ring

/-- The same literal scalar sector satisfies every first-order Einstein equation
at the fundamental minus frequency, with no supplied field-equation hypothesis. -/
theorem literal_minus_source_first_zero (u a : ℂ) (p : D4BMBackground.ExteriorPoint)
    (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum u))
        u a 0) i j) 0 = 0 := by
  have hf : d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum u) =
      Complex.I*(u-3/2) := by
    simp only [d4BMCausalQNMMinus, d4BMCausalDecay, D4BMLiteralCusp.radialMomentum,
      Nat.cast_zero, mul_zero, zero_add]
    ring
  rw [hf]
  apply literal_source_first_zero
  unfold D4BMFundamentalScalarMetric.harmonicParameter D4BMLiteralCusp.scalarQ
  ring

end
end RHTower.D4BMScalarLinearEquation
