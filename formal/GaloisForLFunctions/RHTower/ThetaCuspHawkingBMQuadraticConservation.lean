import GaloisForLFunctions.HTGeometry.ComplexMetricQuadraticConservation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralConservation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralSourceReflection

set_option autoImplicit false
namespace RHTower.D4BMQuadraticConservation
open GaloisForLFunctions.HTGeometry
open ComplexMetricField ComplexCoordinateMetricTwoJet D4BMBackground D4BMActualMetricSource D4BMMetricReconstruction
open Filter Topology
noncomputable section

/-- The fixed, original BM background field on the coordinate chart. -/
def backgroundField : Field 4 := fun x => metric (x 1) (x 3)

private theorem background_symm (x : Fin 4 → ℝ) (i j : Fin 4) :
    backgroundField x i j = backgroundField x j i := by
  by_cases hij : i = j
  · subst j; rfl
  · simp [backgroundField,metric,hij,Ne.symm hij]

private theorem exterior_neighborhood (p : ExteriorPoint) :
    ∀ᶠ x in 𝓝 p.val, 1 < x 1 ∧ 0 < x 3 := by
  have hr : IsOpen {x : Fin 4 → ℝ | 1 < x 1} := isOpen_lt continuous_const (continuous_apply 1)
  have hy : IsOpen {x : Fin 4 → ℝ | 0 < x 3} := isOpen_lt continuous_const (continuous_apply 3)
  have hR : ∀ᶠ x in 𝓝 p.val, 1 < x 1 := hr.mem_nhds p.property.1
  have hY : ∀ᶠ x in 𝓝 p.val, 0 < x 3 := hy.mem_nhds p.property.2
  exact hR.and hY

private theorem physical_smooth (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (i j : Fin 4) :
    ContDiffAt ℝ 3 (fun x => D4BMLiteralCusp.physicalPerturbation q b aS aV x i j) p.val :=
  D4BMLiteralMetricBianchi.literal_contDiffAt 3 p _ _ _ _ i j

private theorem actual_source_eq (p : ExteriorPoint) (h : Field 4) (i j : Fin 4) :
    affineSource backgroundField h (-3) p.val i j = source p h i j := by
  funext e
  change literalEinstein (perturbedMetric h e) (-3) p.val i j = _
  rw [← D4BMLiteralConservation.sourceField_eq_literalEinstein]
  rfl

/-- The original Einstein Hessian is background-conserved for every actual physical
theta-cusp mode. No source-conservation or reconstruction certificate is assumed. -/
theorem physical_hessian_conservation (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (j : Fin 4) :
    tensorDivergence backgroundField
      (hessianTensor backgroundField (D4BMLiteralCusp.physicalPerturbation q b aS aV))
      p.val j = 0 := by
  apply hessian_conservation backgroundField (D4BMLiteralCusp.physicalPerturbation q b aS aV) (-3) p.val
    (fun i j => exterior_metric_contDiffAt p i j) (physical_smooth p q b aS aV)
    (exterior_metric_det_ne_zero p) background_symm
    (D4BMLiteralConservation.literal_symm _ _ _ _)
  · filter_upwards [exterior_neighborhood p] with x hx
    intro i j
    have hv := exterior_vacuum (⟨x,hx⟩ : ExteriorPoint) i j
    change (actualJet (⟨x,hx⟩ : ExteriorPoint)).einstein i j+
      (-3)*(actualJet (⟨x,hx⟩ : ExteriorPoint)).metric i j = 0
    simpa only [neg_mul,sub_eq_add_neg] using hv
  · filter_upwards [exterior_neighborhood p] with x hx
    intro i j
    let r : ExteriorPoint := ⟨x,hx⟩
    have hd := affineSource_first backgroundField (D4BMLiteralCusp.physicalPerturbation q b aS aV)
      (-3) r.val (fun i j => exterior_metric_contDiffAt r i j)
      (fun i j => (physical_smooth r q b aS aV i j).of_le (by norm_num))
      (exterior_metric_det_ne_zero r) i j
    rw [actual_source_eq] at hd
    exact hd.symm.trans (D4BMLiteralCusp.physicalPerturbation_first_source_zero q b aS aV r i j)

/-- Original quadratic Taylor source as a field, with its factor one half. -/
def physicalQuadraticSource (q : XiZeroCopy) (b : Bool) (aS aV : ℂ) : Field 4 :=
  fun x => (1/2 : ℂ) • hessianTensor backgroundField (D4BMLiteralCusp.physicalPerturbation q b aS aV) x

/-- This tensor is the original field source's actual quadratic coefficient. -/
theorem physicalQuadraticSource_eq (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (i j : Fin 4) :
    physicalQuadraticSource q b aS aV p.val i j =
      iteratedDeriv 2 (source p (D4BMLiteralCusp.physicalPerturbation q b aS aV) i j) 0/2 := by
  rw [source_quadratic p _ (fun i j => (physical_smooth p q b aS aV i j).of_le (by norm_num))]
  change (1/2 : ℂ)*secondVariation (backgroundSpace p) i j
    (fieldSpace p (D4BMLiteralCusp.physicalPerturbation q b aS aV))
    (fieldSpace p (D4BMLiteralCusp.physicalPerturbation q b aS aV)) = _
  ring

/-- Original physical quadratic source conservation, with all metric and source hypotheses discharged. -/
theorem physical_quadratic_source_conservation (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (j : Fin 4) :
    tensorDivergence backgroundField (physicalQuadraticSource q b aS aV) p.val j = 0 := by
  have hs : ∀ i j, DifferentiableAt ℝ
      (fun x => hessianTensor backgroundField (D4BMLiteralCusp.physicalPerturbation q b aS aV) x i j) p.val :=
    fun i j => hessianField_differentiableAt backgroundField _ p.val
      (fun a b => exterior_metric_contDiffAt p a b) (physical_smooth p q b aS aV)
      (exterior_metric_det_ne_zero p) i j
  have hv := tensorDivergence_const_smul backgroundField
    (hessianTensor backgroundField (D4BMLiteralCusp.physicalPerturbation q b aS aV)) p.val hs (1/2) j
  change tensorDivergence backgroundField
    (fun x => (1/2 : ℂ) • hessianTensor backgroundField (D4BMLiteralCusp.physicalPerturbation q b aS aV) x) p.val j = 0
  rw [hv,physical_hessian_conservation,mul_zero]

end
end RHTower.D4BMQuadraticConservation
