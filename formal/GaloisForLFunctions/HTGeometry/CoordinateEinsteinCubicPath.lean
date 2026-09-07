import GaloisForLFunctions.HTGeometry.ComplexCubicPathChainRule
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexLinearization

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet.CubicSource
open Filter Topology
noncomputable section
variable {d : ℕ}

/-- The actual cubic path in complete metric-jet coordinates. -/
def jet (J H K L : CoordinateMetricTwoJet d ℂ) (t : ℂ) : CoordinateMetricTwoJet d ℂ :=
  ofSpace (ComplexCubicPath.path (toSpace J) (toSpace H) (toSpace K) (toSpace L) t)

/-- The literal cosmological Einstein contraction along the corrected jet path. -/
def source (J H K L : CoordinateMetricTwoJet d ℂ) (Λ : ℂ) (i j : Fin d) (t : ℂ) : ℂ :=
  (jet J H K L t).einstein i j + Λ * (jet J H K L t).metric i j

private def metricProjection (i j : Fin d) : ComplexMetricTwoJetSpace d →L[ℂ] ℂ where
  toFun := fun q => q.1 i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := by fun_prop

private theorem first_add_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (A : E →L[ℂ] ℂ) (q : E) (hf : ContDiffAt ℂ 3 f q) :
    fderiv ℂ (fun x => f x + A x) q = fderiv ℂ f q + A := by
  rw [fderiv_fun_add (hf.differentiableAt (by norm_num)) A.differentiableAt,
    ContinuousLinearMap.fderiv]

private theorem second_add_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (A : E →L[ℂ] ℂ) (q : E) (hf : ContDiffAt ℂ 3 f q) :
    fderiv ℂ (fderiv ℂ (fun x => f x + A x)) q = fderiv ℂ (fderiv ℂ f) q := by
  have he : fderiv ℂ (fun x => f x + A x) =ᶠ[nhds q] (fun x => fderiv ℂ f x + A) := by
    filter_upwards [hf.eventually (by simp)] with x hx
    exact first_add_linear f A x hx
  rw [he.fderiv_eq, fderiv_add_const]

private theorem third_add_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (A : E →L[ℂ] ℂ) (q : E) (hf : ContDiffAt ℂ 3 f q) :
    fderiv ℂ (fderiv ℂ (fderiv ℂ (fun x => f x + A x))) q =
      fderiv ℂ (fderiv ℂ (fderiv ℂ f)) q := by
  have he : fderiv ℂ (fderiv ℂ (fun x => f x + A x)) =ᶠ[nhds q]
      fderiv ℂ (fderiv ℂ f) := by
    filter_upwards [hf.eventually (by simp)] with x hx
    exact second_add_linear f A x hx
  exact he.fderiv_eq

/-- The constant term is exactly the original cosmological Einstein contraction. -/
theorem source_at_zero (J H K L : CoordinateMetricTwoJet d ℂ) (Λ : ℂ) (i j : Fin d) :
    source J H K L Λ i j 0 = J.einstein i j + Λ * J.metric i j := by
  simp [source, jet, ComplexCubicPath.path]

/-- Higher-order correction fields do not change the actual first variation. -/
theorem linear_coefficient (J H K L : CoordinateMetricTwoJet d ℂ) (hJ : J.metric.det ≠ 0) (Λ : ℂ) (i j : Fin d) :
    deriv (source J H K L Λ i j) 0 = CoordinateMetricTwoJet.Linearization.cosmological J H Λ i j := by
  let A := Λ • metricProjection i j
  have hf := contDiffAt_einsteinComponent (n := 3) (toSpace J) hJ i j
  have hc := hf.add A.contDiff.contDiffAt
  change deriv (fun t => (fun x => einsteinComponent i j x + A x)
    (ComplexCubicPath.path (toSpace J) (toSpace H) (toSpace K) (toSpace L) t)) 0 = _
  rw [ComplexCubicPath.linear_coefficient _ _ _ _ _ hc, first_add_linear _ A _ hf]
  simp only [add_apply]
  change fderiv ℂ (einsteinComponent i j) (toSpace J) (toSpace H) + Λ * H.metric i j = _
  rw [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv J H hJ]

/-- The complete quadratic source includes the linear action on the quadratic correction. -/
theorem quadratic_coefficient (J H K L : CoordinateMetricTwoJet d ℂ) (hJ : J.metric.det ≠ 0) (Λ : ℂ) (i j : Fin d) :
    iteratedDeriv 2 (source J H K L Λ i j) 0 / 2 =
      CoordinateMetricTwoJet.Linearization.cosmological J K Λ i j +
        secondVariation (toSpace J) i j (toSpace H) (toSpace H) / 2 := by
  let A := Λ • metricProjection i j
  have hf := contDiffAt_einsteinComponent (n := 3) (toSpace J) hJ i j
  have hc := hf.add A.contDiff.contDiffAt
  change iteratedDeriv 2 (fun t => (fun x => einsteinComponent i j x + A x)
    (ComplexCubicPath.path (toSpace J) (toSpace H) (toSpace K) (toSpace L) t)) 0 / 2 = _
  rw [ComplexCubicPath.quadratic_coefficient _ _ _ _ _ hc,
    first_add_linear _ A _ hf, second_add_linear _ A _ hf]
  simp only [add_apply]
  change fderiv ℂ (einsteinComponent i j) (toSpace J) (toSpace K) + Λ * K.metric i j +
    secondVariation (toSpace J) i j (toSpace H) (toSpace H) / 2 = _
  rw [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv J K hJ]

/-- The complete cubic source retains both correction fields and their Hessian coupling. -/
theorem cubic_coefficient (J H K L : CoordinateMetricTwoJet d ℂ) (hJ : J.metric.det ≠ 0) (Λ : ℂ) (i j : Fin d) :
    iteratedDeriv 3 (source J H K L Λ i j) 0 / 6 =
      CoordinateMetricTwoJet.Linearization.cosmological J L Λ i j +
        secondVariation (toSpace J) i j (toSpace H) (toSpace K) +
        thirdVariation (toSpace J) i j (toSpace H) (toSpace H) (toSpace H) / 6 := by
  let A := Λ • metricProjection i j
  have hf := contDiffAt_einsteinComponent (n := 3) (toSpace J) hJ i j
  have hc := hf.add A.contDiff.contDiffAt
  change iteratedDeriv 3 (fun t => (fun x => einsteinComponent i j x + A x)
    (ComplexCubicPath.path (toSpace J) (toSpace H) (toSpace K) (toSpace L) t)) 0 / 6 = _
  rw [ComplexCubicPath.cubic_coefficient _ _ _ _ _ hc,
    first_add_linear _ A _ hf, second_add_linear _ A _ hf, third_add_linear _ A _ hf]
  simp only [add_apply]
  change fderiv ℂ (einsteinComponent i j) (toSpace J) (toSpace L) + Λ * L.metric i j +
    secondVariation (toSpace J) i j (toSpace H) (toSpace K) +
    thirdVariation (toSpace J) i j (toSpace H) (toSpace H) (toSpace H) / 6 = _
  rw [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv J L hJ]

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet.CubicSource
