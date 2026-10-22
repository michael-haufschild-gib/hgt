import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralSourceReflection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMActionCubicCoefficient
import GaloisForLFunctions.HTGeometry.CoordinateMetricTestModeVariation

/-!
# Complete weighted correction discrepancy of the original Einstein source

The original physical Xi modes discharge the background and linearized equations.
Changing the complete quadratic and cubic correction jets then changes the actual
weighted cubic source by an affine expression. Its mixed amplitude derivative retains
both ++ and +- correction slots, the full Einstein Hessian, determinant-volume variation
and both inverse-index variations. Scalar and vector amplitudes remain independent.

These are local identities of the nonlinear source before integration. They neither
construct the differentiated causal corrections nor cancel a physical left-QNM action
or its horizon, cusp, characteristic and source-contact terms.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMWeightedCorrectionDiscrepancy
open D4BMBackground D4BMActualMetricSource D4BMMetricReconstruction
open ComplexCoordinateMetricTwoJet MetricPathDensity
noncomputable section
set_option autoImplicit false
local notation "Space" => ComplexMetricTwoJetSpace 4
local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

private def metricProjection (i j : Fin 4) : Space →L[ℂ] ℂ where
  toFun := fun q => q.1 i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := by fun_prop

/-- The original cosmological Einstein linearization on every complete jet entry. -/
def linear (p : ExteriorPoint) (i j : Fin 4) : Space →L[ℂ] ℂ :=
  fderiv ℂ (einsteinComponent i j) (backgroundSpace p)+(-3:ℂ) • metricProjection i j

theorem linear_original (p : ExteriorPoint) (A : Space) (i j : Fin 4) :
    linear p i j A=D4BMLinearizedEinsteinSource.residual p (ofSpace A) i j := by
  rw [D4BMLinearizedEinsteinSource.residual,CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv (actualJet p) _ (exterior_metric_det_ne_zero p)]
  rfl

/-- Complete jet of an original Xi mode, with independent scalar and vector amplitudes. -/
def mode (p : ExteriorPoint) (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ) : Space :=
  toSpace (ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch aS aV) p.val)

private theorem mode_linear_zero (p : ExteriorPoint) (q : XiZeroCopy) (branch : Bool)
    (aS aV : ℂ) (i j : Fin 4) : linear p i j (mode p q branch aS aV)=0 := by
  rw [linear_original,mode,ofSpace_toSpace]
  rw [← (D4BMLinearizedEinsteinSource.source_hasDerivAt p
    (D4BMLiteralCusp.physicalPerturbation q branch aS aV)
    (D4BMFullLinearEquation.literal_contDiffAt p (Complex.I*D4BMModularCore.physicalRate q branch)
      (D4BMGlobalAngularResponse.center q) aS aV) i j).deriv]
  exact D4BMLiteralCusp.physicalPerturbation_first_source_zero q branch aS aV p i j

/-- The original raised covariant test at the unchanged background. -/
def fixedWeight (p : ExteriorPoint) (M : Mat) (i j : Fin 4) : ℂ :=
  ((actualJet p).metric⁻¹*M*((actualJet p).metric⁻¹).transpose) i j

/-- Actual determinant-volume and inverse-index first weight variation. -/
def movingWeight (p : ExteriorPoint) (H : Space) (M : Mat) (i j : Fin 4) : ℂ :=
  testWeightSlope (actualJet p).metric H.1 M i j

private theorem movingWeight_derivative (p : ExteriorPoint) (P Q : Space) (M : Mat)
    (i j : Fin 4) : HasDerivAt (fun z : ℂ => movingWeight p (P+z • Q) M i j)
      (movingWeight p Q M i j) 0 := by
  have h := testWeightSlope_path_hasDerivAt (actualJet p).metric P.1 Q.1 0 0 M i j
  convert! h using 1
  funext z
  change testWeightSlope (actualJet p).metric (P.1+z • Q.1) M i j =
    testWeightSlope (actualJet p).metric (path P.1 Q.1 0 0 z) M i j
  simp only [path,smul_zero,add_zero]
  rfl

/-- Cubic coefficient of the original nonlinear volume-weighted Einstein source. -/
def coefficient (p : ExteriorPoint) (H K L : Space) (M : Mat) : ℂ :=
  iteratedDeriv 3 (CubicSource.pairedSource (actualJet p) (ofSpace H) (ofSpace K)
    (ofSpace L) (-3) M) 0/6

private theorem coefficient_eq (p : ExteriorPoint) (H K L : Space) (M : Mat)
    (hH : ∀ i j, linear p i j H=0) :
    coefficient p H K L M=∑ i,∑ j,
      (fixedWeight p M i j*(linear p i j L+
        secondVariation (backgroundSpace p) i j H K+thirdVariation (backgroundSpace p) i j H H H/6)+
      movingWeight p H M i j*(linear p i j K+secondVariation (backgroundSpace p) i j H H/2)) := by
  have hzero (i j : Fin 4) : (actualJet p).einstein i j+(-3:ℂ)*(actualJet p).metric i j=0 := by
    simpa only [neg_mul,sub_eq_add_neg] using exterior_vacuum p i j
  have hone (i j : Fin 4) : CoordinateMetricTwoJet.Linearization.cosmological
      (actualJet p) (ofSpace H) (-3) i j=0 := by
    change D4BMLinearizedEinsteinSource.residual p (ofSpace H) i j=0
    rw [← linear_original,hH]
  rw [coefficient,CubicSource.pairedSource_cubic _ _ _ _ (exterior_metric_det_ne_zero p) (-3) M hzero hone]
  simp only [toSpace_ofSpace]
  simp only [linear_original,D4BMLinearizedEinsteinSource.residual]
  rfl

/-- Original fixed-weight linear work of a complete cubic correction discrepancy. -/
def linearWork (p : ExteriorPoint) (B : Space) (M : Mat) : ℂ :=
  ∑ i,∑ j,fixedWeight p M i j*linear p i j B

/-- The Einstein Hessian work retains the moving-weight contraction with the full linear residual. -/
def correctionWork (p : ExteriorPoint) (H A : Space) (M : Mat) : ℂ :=
  ∑ i,∑ j,(fixedWeight p M i j*secondVariation (backgroundSpace p) i j H A+
    movingWeight p H M i j*linear p i j A)

private theorem coefficient_change (p : ExteriorPoint) (H K L A B : Space) (M : Mat)
    (hH : ∀ i j, linear p i j H=0) :
    coefficient p H (K+A) (L+B) M-coefficient p H K L M=
      linearWork p B M+correctionWork p H A M := by
  rw [coefficient_eq p H (K+A) (L+B) M hH,coefficient_eq p H K L M hH]
  simp only [map_add]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  simp only [linearWork,correctionWork,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Premise-free correction discrepancy for every original physical Xi branch and full test tensor. -/
theorem physical_coefficient_change (p : ExteriorPoint) (q : XiZeroCopy) (branch : Bool)
    (aS aV : ℂ) (K L A B : Space) (M : Mat) :
    coefficient p (mode p q branch aS aV) (K+A) (L+B) M-
      coefficient p (mode p q branch aS aV) K L M=
      linearWork p B M+correctionWork p (mode p q branch aS aV) A M :=
  coefficient_change p _ K L A B M (mode_linear_zero p q branch aS aV)

/-- Original independent mode path; both first fields satisfy the actual linear equation. -/
def firstPath (p : ExteriorPoint) (q : Fin 2 → XiZeroCopy) (branch : Fin 2 → Bool)
    (aS aV : Fin 2 → ℂ) (z : ℂ) : Space :=
  mode p (q 0) (branch 0) (aS 0) (aV 0)+z • mode p (q 1) (branch 1) (aS 1) (aV 1)

private theorem firstPath_linear_zero (p : ExteriorPoint) (q : Fin 2 → XiZeroCopy)
    (branch : Fin 2 → Bool) (aS aV : Fin 2 → ℂ) (z : ℂ) (i j : Fin 4) :
    linear p i j (firstPath p q branch aS aV z)=0 := by
  simp only [firstPath,map_add,map_smul,mode_linear_zero,smul_zero,add_zero]

/-- All four correction slots remain in the independent mode path before differentiation. -/
def correctionPath (K : Fin 4 → Space) (z : ℂ) : Space :=
  ComplexCubicPath.path (K 0) (K 1) (K 2) (K 3) z

private theorem correctionPath_add (K A : Fin 4 → Space) (z : ℂ) :
    correctionPath (K+A) z=correctionPath K z+correctionPath A z := by
  simp only [correctionPath,ComplexCubicPath.path,Pi.add_apply,smul_add]
  module

private theorem correctionPath_derivative (K : Fin 4 → Space) :
    HasDerivAt (correctionPath K) (K 1) 0 := by
  change HasDerivAt (ComplexCubicPath.path (K 0) (K 1) (K 2) (K 3)) (K 1) 0
  convert! ComplexCubicPath.path_hasDerivAt (K 0) (K 1) (K 2) (K 3) 0 using 1
  simp [ComplexCubicPath.velocity]

/-- Actual mixed amplitude coefficient of the nonlinear corrected-source discrepancy. -/
def mixedDiscrepancy (p : ExteriorPoint) (q : Fin 2 → XiZeroCopy) (branch : Fin 2 → Bool)
    (aS aV : Fin 2 → ℂ) (K L A B : Fin 4 → Space) (M : Mat) : ℂ :=
  deriv (fun z => coefficient p (firstPath p q branch aS aV z)
      (correctionPath (K+A) z) (correctionPath (L+B) z) M-
    coefficient p (firstPath p q branch aS aV z) (correctionPath K z) (correctionPath L z) M) 0

/-- Exact original weighted mixed-source change. The ++ and +- correction discrepancies each
retain their original weight/residual term; all unused slots disappear by actual differentiation. -/
theorem physical_mixed_discrepancy (p : ExteriorPoint) (q : Fin 2 → XiZeroCopy)
    (branch : Fin 2 → Bool) (aS aV : Fin 2 → ℂ) (K L A B : Fin 4 → Space) (M : Mat) :
    mixedDiscrepancy p q branch aS aV K L A B M=
      linearWork p (B 1) M+
      correctionWork p (mode p (q 0) (branch 0) (aS 0) (aV 0)) (A 1) M+
      correctionWork p (mode p (q 1) (branch 1) (aS 1) (aV 1)) (A 0) M := by
  let P := mode p (q 0) (branch 0) (aS 0) (aV 0)
  let Q := mode p (q 1) (branch 1) (aS 1) (aV 1)
  have hH : HasDerivAt (firstPath p q branch aS aV) Q 0 := by
    change HasDerivAt (fun z : ℂ => P+z • Q) Q 0
    convert! ((hasDerivAt_id (0:ℂ)).smul_const Q).const_add P using 1
    simp only [one_smul]
  have hA := correctionPath_derivative A
  have hB := correctionPath_derivative B
  have hW (i j : Fin 4) : HasDerivAt
      (fun z => movingWeight p (firstPath p q branch aS aV z) M i j)
      (movingWeight p Q M i j) 0 := by
    change HasDerivAt (fun z : ℂ => movingWeight p (P+z • Q) M i j)
      (movingWeight p Q M i j) 0
    exact movingWeight_derivative p P Q M i j
  have hS (i j : Fin 4) :=
    ((((hasDerivAt_const (0:ℂ) (secondVariation (backgroundSpace p) i j)).clm_apply hH).clm_apply hA).const_mul
      (fixedWeight p M i j))
  have hd (i j : Fin 4) :=
    (((linear p i j).hasFDerivAt.comp_hasDerivAt 0 hB).const_mul (fixedWeight p M i j)).add
      ((hS i j).add ((hW i j).mul ((linear p i j).hasFDerivAt.comp_hasDerivAt 0 hA)))
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd i j))
  have he : (fun z => coefficient p (firstPath p q branch aS aV z)
      (correctionPath (K+A) z) (correctionPath (L+B) z) M-
    coefficient p (firstPath p q branch aS aV z) (correctionPath K z) (correctionPath L z) M)=
      fun z => ∑ i,∑ j,(fixedWeight p M i j*linear p i j (correctionPath B z)+
        (fixedWeight p M i j*secondVariation (backgroundSpace p) i j
          (firstPath p q branch aS aV z) (correctionPath A z)+
          movingWeight p (firstPath p q branch aS aV z) M i j*linear p i j (correctionPath A z))) := by
    funext z
    rw [correctionPath_add,correctionPath_add,
      coefficient_change p _ _ _ _ _ M (firstPath_linear_zero p q branch aS aV z)]
    simp only [linearWork,correctionWork,← Finset.sum_add_distrib]
  rw [mixedDiscrepancy,he]
  have hh' := hh.deriv
  simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply] at hh'
  refine hh'.trans ?_
  simp only [correctionPath,ComplexCubicPath.path,firstPath,zero_smul,add_zero,
    zero_apply,zero_add,zero_pow (by decide : (2:ℕ)≠0),zero_pow (by decide : (3:ℕ)≠0),
    linearWork,correctionWork,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [P,Q]
  ring

end
end RHTower.D4BMWeightedCorrectionDiscrepancy
