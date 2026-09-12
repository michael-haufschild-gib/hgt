import GaloisForLFunctions.HTGeometry.CoordinateEinsteinOnShellPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCyclicActionBoundary

set_option autoImplicit false

/-!
# Actual quadratic theta-cusp Einstein pairing and its retained boundary defect

The physical modes satisfy the original background and linearized residual equations.
Their varying volume-weighted pairing therefore reduces to the actual Einstein Hessian.
The quadratic Taylor coefficient retains the factor one half. Its cyclicity defect is
exactly half the original boundary-divergence defect; no global flux cancellation or
causal/left-QNM incidence is assumed.
-/

open scoped ContDiff BigOperators
namespace RHTower.D4BMOnShellCyclicSource
open GaloisForLFunctions.HTGeometry
open EinsteinCyclicVariation EinsteinOnShellPairing ComplexCoordinateMetricTwoJet
open CoordinateMetricTwoJet.Linearization D4BMBackground D4BMCyclicAction
noncomputable section

private theorem mode_smooth (p : ExteriorPoint) (q : XiZeroCopy) (b : Bool)
    (aS aV : ℂ) (r s : Fin 4) :
    ContDiffAt ℝ 2 (fun x => D4BMLiteralCusp.physicalPerturbation q b aS aV x r s) p.val :=
  D4BMFullLinearEquation.literal_contDiffAt p
    (Complex.I * D4BMModularCore.physicalRate q b) (D4BMGlobalAngularResponse.center q) aS aV r s

private theorem linear_source_zero (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (k : Fin 3) (r s : Fin 4) :
    cosmological (actualJet p) (jets p q b aS aV k) (-3) r s = 0 := by
  have he : D4BMActualMetricSource.source p (modes q b aS aV k) r s =
      fun t => (affine (actualJet p) (jets p q b aS aV k) t).einstein r s +
        (-3) * (affine (actualJet p) (jets p q b aS aV k) t).metric r s := by
    funext t
    rw [D4BMActualMetricSource.source_eq p (modes q b aS aV k)
      (mode_smooth p (q k) (b k) (aS k) (aV k)) r s t]
    change (affine (actualJet p) (jets p q b aS aV k) t).einstein r s -
      3 * (affine (actualJet p) (jets p q b aS aV k) t).metric r s = _
    ring
  have hd := (cosmological_hasDerivAt (actualJet p) (jets p q b aS aV k)
    (exterior_metric_det_ne_zero p) (-3) r s).deriv
  rw [← he] at hd
  exact hd.symm.trans (D4BMLiteralCusp.physicalPerturbation_first_source_zero
    (q k) (b k) (aS k) (aV k) p r s)

/-- Full Einstein Hessian contracted against the original covariant test metric. -/
def hessianPairing (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i j k : Fin 3) : ℂ :=
  ∑ r, ∑ s,
    ((actualJet p).metric⁻¹ * (jets p q b aS aV k).metric *
      ((actualJet p).metric⁻¹).transpose) r s *
    secondVariation (toSpace (actualJet p)) r s
      (toSpace (jets p q b aS aV i)) (toSpace (jets p q b aS aV j))

/-- Pairing with the original quadratic Taylor source, whose convention is one half the Hessian. -/
def quadraticPairing (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i j k : Fin 3) : ℂ :=
  hessianPairing p q b aS aV i j k / 2

/-- No moving-volume or moving-index term survives the physical quadratic source pairing. -/
theorem physical_bulk_second_eq_hessian (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i j k : Fin 3) :
    parameterDeriv (parameterDeriv (bulk (actualJet p) (jets p q b aS aV) (-3) k) j) i 0 =
      hessianPairing p q b aS aV i j k := by
  apply bulk_second_eq_hessian
  · exact exterior_metric_det_ne_zero p
  · intro r s
    simpa only [neg_mul, sub_eq_add_neg] using exterior_vacuum p r s
  · exact linear_source_zero p q b aS aV

/-- The diagonal is the paired quadratic coefficient of the literal full field source,
fixing the Taylor normalization independently of the cyclic-action construction. -/
theorem quadraticPairing_diag_eq_sourceCoefficient (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i k : Fin 3) :
    quadraticPairing p q b aS aV i i k =
      ∑ r, ∑ s,
        ((actualJet p).metric⁻¹ * (jets p q b aS aV k).metric *
          ((actualJet p).metric⁻¹).transpose) r s *
        (iteratedDeriv 2 (D4BMActualMetricSource.source p (modes q b aS aV i) r s) 0 / 2) := by
  unfold quadraticPairing hessianPairing
  simp only [Finset.sum_div, mul_div_assoc]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [D4BMActualMetricSource.source_quadratic p (modes q b aS aV i)
    (mode_smooth p (q i) (b i) (aS i) (aV i)) r s]
  rfl

/-- Exact defect of the original physical quadratic source pairing. Its complete boundary
contribution is retained, with the same quadratic Taylor normalization. -/
theorem physical_quadratic_cyclicity_defect (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i j k : Fin 3) :
    quadraticPairing p q b aS aV i j k - quadraticPairing p q b aS aV i k j =
      (parameterDeriv (parameterDeriv (boundary (actualJet p) (jets p q b aS aV) k) j) i 0 -
        parameterDeriv (parameterDeriv (boundary (actualJet p) (jets p q b aS aV) j) k) i 0) / 2 := by
  have h := physical_cubicAction_cyclic p q b aS aV i j k
  unfold cubicAction at h
  rw [physical_bulk_second_eq_hessian p q b aS aV i j k,
    physical_bulk_second_eq_hessian p q b aS aV i k j] at h
  unfold quadraticPairing
  linear_combination (1/2:ℂ) * h

/-- The original quadratic pairing with its exact boundary term is cyclic on all physical modes. -/
theorem physical_quadratic_with_boundary_cyclic (p : ExteriorPoint) (q : Fin 3 → XiZeroCopy)
    (b : Fin 3 → Bool) (aS aV : Fin 3 → ℂ) (i j k : Fin 3) :
    quadraticPairing p q b aS aV i j k -
        parameterDeriv (parameterDeriv (boundary (actualJet p) (jets p q b aS aV) k) j) i 0 / 2 =
      quadraticPairing p q b aS aV i k j -
        parameterDeriv (parameterDeriv (boundary (actualJet p) (jets p q b aS aV) j) k) i 0 / 2 := by
  have h := physical_quadratic_cyclicity_defect p q b aS aV i j k
  linear_combination h

end
end RHTower.D4BMOnShellCyclicSource
