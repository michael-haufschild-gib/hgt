import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularPotential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMForcedMetricField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMWeightedCorrectionDiscrepancy

/-!
# Actual mixed quadratic correction and its vanishing weighted residual

The ingoing contact is an actual metric field. Its full coordinate two-jet is
identified with the source-derived table. Adding the constructed particular
response solves every mixed quadratic Einstein component at the original rate.
This does not identify a switched causal correction or cancel the complete action.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMMixedQuadraticClosure
open D4BMHorizon D4BMAngularTwoTensor D4BMAngularTwo D4BMModularCore
open D4BMScalarLinearEquation D4BMMetricReconstruction D4BMFundamentalScalarMetric
open ComplexCoordinateMetricTwoJet D4BMQuadraticAngularSource
noncomputable section
set_option autoImplicit false

private theorem source_syy (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    coordDeriv 1 (coordDeriv 1 (source q)) z =
      (physicalRate q branch+1)*(physicalRate q branch+2)*source q z/(z 1:ℂ)^2-
        coordDeriv 0 (coordDeriv 0 (source q)) z := by
  have he := scalar_physical_equation q branch z hz
  change scalarLaplacian (source q) z =
    (physicalRate q branch+1)*(physicalRate q branch+2)*source q z at he
  rw [scalarLaplacian_eq _ z hz] at he
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  linear_combination he

private theorem source_sxyy (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    coordDeriv 0 (coordDeriv 1 (coordDeriv 1 (source q))) z =
      (physicalRate q branch+1)*(physicalRate q branch+2)*coordDeriv 0 (source q) z/(z 1:ℂ)^2-
        coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z := by
  have hs : ContDiffAt ℝ 3 (source q) z :=
    D4BMLiteralCusp.scalar_contDiffAt (D4BMGlobalAngularResponse.center q) 3 z hz
  have he : scalarLaplacian (source q) =ᶠ[𝓝 z]
      (fun w => (physicalRate q branch+1)*(physicalRate q branch+2)*source q w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact scalar_physical_equation q branch w hw
  have hd := congrArg (fun L => L (Pi.single 0 1)) (he.fderiv_eq (𝕜 := ℝ))
  change coordDeriv 0 (scalarLaplacian (source q)) z = _ at hd
  rw [scalarLaplacian_partial _ z hz hs 0] at hd
  rw [((hs.differentiableAt (by norm_num)).hasFDerivAt.const_mul
    ((physicalRate q branch+1)*(physicalRate q branch+2))).fderiv] at hd
  change (0:ℂ)*_+(z 1:ℂ)^2*(_+_) =
    (physicalRate q branch+1)*(physicalRate q branch+2)*coordDeriv 0 (source q) z at hd
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  linear_combination hd


private theorem partial_neg (i : Fin 2) (F : Field) :
    coordDeriv i (fun z => -F z) = fun z => -coordDeriv i F z := by
  funext z
  simp [coordDeriv]

private abbrev Expr := ScalarTwoJet.Expression (Fin 5)

private def contactExpr (s : ℂ) : Matrix (Fin 4) (Fin 4) Expr :=
  let R : Expr := .atom 0
  let F := (R.mul R).add (.constant (-1))
  let T := ((((.constant (s*(s+1)/2) : Expr).mul (.atom 1)).mul F).mul
    ((R.inv.mul R.inv).mul R.inv)).mul (.atom 2)
  let X := T.mul (.atom 3)
  let Y := T.mul (.atom 4)
  let Z : Expr := .constant 0
  !![Z,Z,X,Y; Z,Z,Z,Z; X,Z,Z,Z; Y,Z,Z,Z]

private def atoms (q : XiZeroCopy) (branch : Bool) (a : ℂ) (k : Fin 5) (x : Fin 4 → ℝ) : ℂ :=
  ![(x 1 : ℂ), envelope (2*physicalRate q branch) (a^2) x,
    source q (angularPoint x),
    D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q) 0 (angularPoint x),
    D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q) 1 (angularPoint x)] k

/-- Actual ingoing mixed contact, including its angular dependence. -/
def contactField (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => (contactExpr (physicalRate q branch) i j).eval (fun k => atoms q branch a k x)

private theorem atoms_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (k : Fin 5) :
    ContDiffAt ℝ 2 (atoms q branch a k) p.val := by
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> exact contDiff_apply ℝ ℝ _
  have hs := D4BMLiteralCusp.scalar_contDiffAt (D4BMGlobalAngularResponse.center q) 2
    (angularPoint p.val) p.property.2
  have hv := D4BMLiteralCusp.vector_contDiffAt (D4BMGlobalAngularResponse.center q) 2
    (angularPoint p.val) p.property.2
  fin_cases k
  · exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  · exact envelope_contDiffAt _ _ p 2
  · exact hs.comp p.val hu.contDiffAt
  · exact (hv 0).comp p.val hu.contDiffAt
  · exact (hv 1).comp p.val hu.contDiffAt

private theorem contact_regular (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    (contactExpr (physicalRate q branch) i j).Regular (fun k => atoms q branch a k p.val) := by
  have hr : (p.val 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [p.property.1])
  fin_cases i <;> fin_cases j <;>
    simp [contactExpr, ScalarTwoJet.Expression.Regular, ScalarTwoJet.Expression.eval, atoms, hr]

/-- All contact components have actual continuous second coordinate derivatives. -/
theorem contactField_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => contactField q branch a x i j) p.val :=
  ((contactExpr (physicalRate q branch) i j).eval_jet_correct
    (atoms_smooth q branch a p) (contact_regular q branch a p i j)).1

private def atomJets (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) : Fin 5 → ScalarTwoJet (Fin 4) ℂ :=
  let s := physicalRate q branch
  let z := angularPoint p.val
  let y : ℂ := p.val 3
  let S := source q z
  let Sx := coordDeriv 0 (source q) z
  let Sy := coordDeriv 1 (source q) z
  let Sxx := coordDeriv 0 (coordDeriv 0 (source q)) z
  let Sxy := coordDeriv 0 (coordDeriv 1 (source q)) z
  let Sxxx := coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z
  let Sxxy := coordDeriv 0 (coordDeriv 0 (coordDeriv 1 (source q))) z
  ![coord (p.val 1) 1,
    temporalRadial (2*s) (p.val 1) ((envelope s a p.val)^2),
    angular s y S Sx Sy Sxx Sxy,
    D4BMVectorLinearEquation.angular0 s y Sy Sxy ((s+1)*(s+2)*S/y^2-Sxx)
      (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx),
    D4BMVectorLinearEquation.angular1 s y (-Sx) Sxy (-Sxx)
      Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx)]

private theorem scalar_atom_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    ofField (atoms q branch a 2) p.val = atomJets q branch a p 2 := by
  let z := angularPoint p.val
  have hs : ContDiffAt ℝ 2 (source q) z := D4BMLiteralCusp.scalar_contDiffAt _ 2 z p.property.2
  have hyy := source_syy q branch z p.property.2
  have hc := D4BMHorizon.coordDeriv_commute hs 1 0
  have hz : z 1 = p.val 3 := rfl
  rw [hz] at hyy
  change ofField (fun x => source q (angularPoint x)) p.val =
    angular (physicalRate q branch) (p.val 3) _ _ _ _ _
  rw [angular_lift_jet (source q) p.val hs]
  simp only [angular, ← show z = angularPoint p.val from rfl, hc, hyy]

private theorem vector_atoms_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    ofField (atoms q branch a 3) p.val = atomJets q branch a p 3 ∧
    ofField (atoms q branch a 4) p.val = atomJets q branch a p 4 := by
  let z := angularPoint p.val
  have hyy := source_syy q branch z p.property.2
  have hxyy := source_sxyy q branch z p.property.2
  have hz : z 1 = p.val 3 := rfl
  rw [hz] at hyy hxyy
  have hv (i : Fin 2) : roughLaplacian
      (D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q)) i z =
      ((physicalRate q branch+1)*(physicalRate q branch+2)-1)*
        D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q) i z := by
    rw [D4BMLiteralCusp.vector_equation _ z p.property.2 i]
    have he := D4BMScalarSourceIdentification.eigenvalue_physicalRate q branch
    dsimp [eigenvalue] at he
    unfold d4HyperbolicHodgePairedVectorEigenvalue
    rw [← he]
    ring
  have hvec := D4BMVectorLinearEquation.angular_jets (physicalRate q branch)
    (D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q)) p
    (D4BMLiteralCusp.vector_contDiffAt _ 2 _ p.property.2)
    (D4BMLiteralCusp.vector_divergence _) hv
  simp only [source] at hyy hxyy
  constructor
  · change ofField (fun x => D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q) 0
      (angularPoint x)) p.val = D4BMVectorLinearEquation.angular0 (physicalRate q branch) (p.val 3) _ _ _ _ _ _
    rw [hvec.1]
    simp only [D4BMLiteralCusp.vector, coexact, Matrix.cons_val_zero, Matrix.cons_val_one, source]
    rw [hyy, hxyy, partial_neg]
  · change ofField (fun x => D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q) 1
      (angularPoint x)) p.val = D4BMVectorLinearEquation.angular1 (physicalRate q branch) (p.val 3) _ _ _ _ _
    rw [hvec.2]
    simp only [D4BMLiteralCusp.vector, coexact, Matrix.cons_val_zero, Matrix.cons_val_one, source]
    rw [hxyy, partial_neg]

private theorem atoms_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    (fun k => ofField (atoms q branch a k) p.val) = atomJets q branch a p := by
  funext k
  fin_cases k
  · exact coordinate_jet p.val 1
  · change ofField (envelope (2*physicalRate q branch) (a^2)) p.val =
      temporalRadial (2*physicalRate q branch) (p.val 1) (envelope (physicalRate q branch) a p.val^2)
    rw [envelope_jet, envelope_double]
    rfl
  · exact scalar_atom_jet q branch a p
  · exact (vector_atoms_jet q branch a p).1
  · exact (vector_atoms_jet q branch a p).2

/-- Original mixed contact table with every scalar jet supplied by the literal source. -/
def contactJet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) : CoordinateMetricTwoJet 4 ℂ :=
  let z := angularPoint p.val
  D4BMQuadraticMixedSource.correctionJet (physicalRate q branch) (p.val 1) (p.val 3)
    (envelope (physicalRate q branch) a p.val)
    (source q z) (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z)
    (coordDeriv 0 (coordDeriv 0 (source q)) z) (coordDeriv 0 (coordDeriv 1 (source q)) z)
    (coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z)
    (coordDeriv 0 (coordDeriv 0 (coordDeriv 1 (source q))) z)

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) :
    CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,
    fun k l i j => (J i j).second k l⟩

private theorem map_cross_matrix {α β : Type} (f : α → β) (X Y Z : α) (i j : Fin 4) :
    f (!![Z,Z,X,Y; Z,Z,Z,Z; X,Z,Z,Z; Y,Z,Z,Z] i j) =
      !![f Z,f Z,f X,f Y; f Z,f Z,f Z,f Z; f X,f Z,f Z,f Z; f Y,f Z,f Z,f Z] i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem contactExpr_jet (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    assemble (fun i j => (contactExpr s i j).evalJet
      ![coord r 1, temporalRadial (2*s) r (B^2), angular s y S Sx Sy Sxx Sxy,
        D4BMVectorLinearEquation.angular0 s y Sy Sxy ((s+1)*(s+2)*S/y^2-Sxx)
          (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx),
        D4BMVectorLinearEquation.angular1 s y (-Sx) Sxy (-Sxx)
          Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx)]) =
      D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy := by
  change assemble _ = assemble _
  congr 1
  funext i j
  unfold contactExpr
  exact map_cross_matrix (fun e : Expr => e.evalJet
    ![coord r 1, temporalRadial (2*s) r (B^2), angular s y S Sx Sy Sxx Sxy,
      D4BMVectorLinearEquation.angular0 s y Sy Sxy ((s+1)*(s+2)*S/y^2-Sxx)
        (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx),
      D4BMVectorLinearEquation.angular1 s y (-Sx) Sxy (-Sxx)
        Sxxy ((s+1)*(s+2)*Sx/y^2-Sxxx)]) _ _ _ i j

/-- The contact table is the actual metric field's full two-jet, not supplied jet data. -/
theorem contactField_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    ofMetricField (contactField q branch a) p.val = contactJet q branch a p := by
  let A := fun i j => (contactExpr (physicalRate q branch) i j).evalJet (atomJets q branch a p)
  have h : assemble (fun i j => ofField (fun x => contactField q branch a x i j) p.val) = assemble A := by
    congr 1
    funext i j
    exact (((contactExpr (physicalRate q branch) i j).eval_jet_correct
      (atoms_smooth q branch a p) (contact_regular q branch a p i j)).2).trans
        (congrArg (fun v => (contactExpr (physicalRate q branch) i j).evalJet v) (atoms_jet q branch a p))
  exact h.trans (contactExpr_jet _ _ _ _ _ _ _ _ _ _ _)

/-- The actual mixed contact has exactly the residual used by the forced tensor. -/
theorem contactField_einstein (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.MixedQuadratic.einstein (D4BMBackground.actualJet p)
      (ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch a 0) p.val)
      (ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch 0 a) p.val) i j +
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField (contactField q branch a) p.val) (-3) i j =
    literalMixedSource q branch (p.val 1) (envelope (physicalRate q branch) a p.val)
      (angularPoint p.val) i j := by
  have hr : (p.val 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [p.property.1])
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1 : ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^2-1 ≠ 0)
  have hs : ContDiffAt ℝ 2 (source q) (angularPoint p.val) :=
    D4BMLiteralCusp.scalar_contDiffAt _ 2 _ p.property.2
  have he : scalarLaplacian (source q) (angularPoint p.val) =
      (physicalRate q branch+1)*(physicalRate q branch+2)*source q (angularPoint p.val) :=
    scalar_physical_equation q branch _ p.property.2
  rw [D4BMBackground.actualJet_eq, contactField_jet,
    D4BMScalarSourceIdentification.physical_scalar_jet,
    D4BMScalarLinearEquation.field_jet _ _ _ p hs he,
    D4BMPhysicalAngularPotential.physical_coexact_jet, literalMixedSource_eq]
  exact D4BMQuadraticMixedSource.einstein_component _ _ _ _ _ _ _ _ _ _ _ hr hy hf i j

/-- Complete unswitched mixed particular correction, with its ingoing contact retained. -/
def mixedField (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => forcedMetricField q branch a x i j - (-1:ℂ)*contactField q branch a x i j

theorem mixedField_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => mixedField q branch a x i j) p.val :=
  (forcedMetricField_smooth q branch a p i j).sub
    (contDiffAt_const.mul (contactField_smooth q branch a p i j))

private theorem mixedField_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    ofMetricField (mixedField q branch a) p.val = metricJetCombination (-1)
      (ofMetricField (forcedMetricField q branch a) p.val)
      (ofMetricField (contactField q branch a) p.val) :=
  ofMetricField_combination (-1) _ _ p.val
    (forcedMetricField_smooth q branch a p) (contactField_smooth q branch a p)

/-- Source-produced vanishing of all sixteen actual mixed quadratic residuals. -/
theorem mixedField_einstein (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField (mixedField q branch a) p.val) (-3) i j +
    CoordinateMetricTwoJet.MixedQuadratic.einstein (D4BMBackground.actualJet p)
      (ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch a 0) p.val)
      (ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch 0 a) p.val) i j = 0 := by
  have hlin := cosmological_metricJetCombination (D4BMBackground.actualJet p)
    (ofMetricField (forcedMetricField q branch a) p.val)
    (ofMetricField (contactField q branch a) p.val)
    (D4BMBackground.exterior_metric_det_ne_zero p) (-1) (-3) i j
  rw [mixedField_jet, hlin]
  have hc := contactField_einstein q branch a p i j
  have hf := forcedMetricField_einstein q branch a p i j
  rw [← D4BMBackground.actualJet_eq] at hf
  linear_combination hc + hf

/-- The vanishing residual is the actual Einstein Hessian coefficient. -/
theorem mixedField_secondVariation (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    D4BMWeightedCorrectionDiscrepancy.linear p i j (toSpace (ofMetricField (mixedField q branch a) p.val)) +
    secondVariation (D4BMActualMetricSource.backgroundSpace p) i j
      (D4BMWeightedCorrectionDiscrepancy.mode p q branch a 0)
      (D4BMWeightedCorrectionDiscrepancy.mode p q branch 0 a) = 0 := by
  rw [D4BMWeightedCorrectionDiscrepancy.linear_original, ofSpace_toSpace]
  have h := mixedField_einstein q branch a p i j
  rw [CoordinateMetricTwoJet.MixedQuadratic.einstein_eq_secondVariation
    (D4BMBackground.actualJet p) _ _ (D4BMBackground.exterior_metric_det_ne_zero p)] at h
  rw [secondVariation_symm (toSpace (D4BMBackground.actualJet p))
    (D4BMBackground.exterior_metric_det_ne_zero p)] at h
  exact h

/-- Independent scalar/vector amplitudes multiply the source-produced mixed field. -/
def independentField (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ := (aS*aV) • mixedField q branch 1 x

/-- Independent amplitudes in the two actual pure-mode directions retain exact cancellation. -/
theorem independentField_secondVariation (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    D4BMWeightedCorrectionDiscrepancy.linear p i j
      (toSpace (ofMetricField (independentField q branch aS aV) p.val)) +
    secondVariation (D4BMActualMetricSource.backgroundSpace p) i j
      (aS • D4BMWeightedCorrectionDiscrepancy.mode p q branch 1 0)
      (aV • D4BMWeightedCorrectionDiscrepancy.mode p q branch 0 1) = 0 := by
  have hj := D4BMCorrectedMetricSource.fieldSpace_smul p (mixedField q branch 1)
    (mixedField_smooth q branch 1 p) (aS*aV)
  change toSpace (ofMetricField (independentField q branch aS aV) p.val) = _ at hj
  rw [hj]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have h := mixedField_secondVariation q branch 1 p i j
  change (aS*aV)*_+aV*(aS*_) = 0
  dsimp only [D4BMActualMetricSource.fieldSpace]
  linear_combination (aS*aV)*h

/-- Determinant and inverse-index weight changes annihilate the actual mixed residual. -/
theorem movingWeight_mixed_residual_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (H : ComplexMetricTwoJetSpace 4)
    (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (∑ i, ∑ j, D4BMWeightedCorrectionDiscrepancy.movingWeight p H M i j *
      (D4BMWeightedCorrectionDiscrepancy.linear p i j (toSpace (ofMetricField (mixedField q branch a) p.val)) +
       secondVariation (D4BMActualMetricSource.backgroundSpace p) i j
         (D4BMWeightedCorrectionDiscrepancy.mode p q branch a 0)
         (D4BMWeightedCorrectionDiscrepancy.mode p q branch 0 a))) = 0 := by
  simp only [mixedField_secondVariation, mul_zero, Finset.sum_const_zero]

end
end RHTower.D4BMMixedQuadraticClosure
