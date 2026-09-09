import GaloisForLFunctions.HTGeometry.CoordinateMetricPathDensity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet.CubicSource
open MetricPathDensity
noncomputable section
variable {d : ℕ}
local notation "Jet" => CoordinateMetricTwoJet d ℂ
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

/-- Volume-weighted contraction of the original covariant source with a fixed covariant test. -/
def pairedSource (J H K L : Jet) (Λ : ℂ) (M : Mat) (t : ℂ) : ℂ :=
  ∑ i, ∑ j, testWeight J.metric H.metric K.metric L.metric M t i j *
    source J H K L Λ i j t

/-- Regularity comes from the original rational Einstein contraction and polynomial metric path. -/
theorem source_contDiffAt (J H K L : Jet) (hJ : J.metric.det ≠ 0) (Λ : ℂ) (i j : Fin d) :
    ContDiffAt ℂ 3 (source J H K L Λ i j) 0 := by
  let f : ComplexMetricTwoJetSpace d → ℂ := fun q => einsteinComponent i j q + Λ * q.1 i j
  have hf : ContDiffAt ℂ 3 f (toSpace J) :=
    (contDiffAt_einsteinComponent (toSpace J) hJ i j).add (by fun_prop)
  have hp : ContDiffAt ℂ 3
      (ComplexCubicPath.path (toSpace J) (toSpace H) (toSpace K) (toSpace L)) 0 := by
    unfold ComplexCubicPath.path
    fun_prop
  have hz : ComplexCubicPath.path (toSpace J) (toSpace H) (toSpace K) (toSpace L) 0 = toSpace J := by
    simp [ComplexCubicPath.path]
  exact (hz ▸ hf).comp 0 hp

private theorem cubic_product (f g : ℂ → ℂ) (hf : ContDiffAt ℂ 3 f 0)
    (hg : ContDiffAt ℂ 3 g 0) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 0) :
    iteratedDeriv 3 (fun t => f t * g t) 0 / 6 =
      f 0 * (iteratedDeriv 3 g 0 / 6) + deriv f 0 * (iteratedDeriv 2 g 0 / 2) := by
  rw [iteratedDeriv_fun_mul hf hg]
  simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hg0, hg1]
  ring

/-- The cubic paired source retains the changing pairing against the complete quadratic residual. -/
theorem pairedSource_cubic (J H K L : Jet) (hJ : J.metric.det ≠ 0) (Λ : ℂ) (M : Mat)
    (hzero : ∀ i j, J.einstein i j + Λ * J.metric i j = 0)
    (hfirst : ∀ i j, CoordinateMetricTwoJet.Linearization.cosmological J H Λ i j = 0) :
    iteratedDeriv 3 (pairedSource J H K L Λ M) 0 / 6 =
      ∑ i, ∑ j,
        ((J.metric⁻¹ * M * (J.metric⁻¹).transpose) i j *
          (CoordinateMetricTwoJet.Linearization.cosmological J L Λ i j +
            secondVariation (toSpace J) i j (toSpace H) (toSpace K) +
            thirdVariation (toSpace J) i j (toSpace H) (toSpace H) (toSpace H) / 6) +
        testWeightSlope J.metric H.metric M i j *
          (CoordinateMetricTwoJet.Linearization.cosmological J K Λ i j +
            secondVariation (toSpace J) i j (toSpace H) (toSpace H) / 2)) := by
  have hw := testWeight_contDiffAt J.metric H.metric K.metric L.metric M hJ
  have he := source_contDiffAt J H K L hJ Λ
  have hi (i j : Fin d) := cubic_product
    (fun t => testWeight J.metric H.metric K.metric L.metric M t i j)
    (source J H K L Λ i j) (hw i j) (he i j)
    ((source_at_zero J H K L Λ i j).trans (hzero i j))
    ((linear_coefficient J H K L hJ Λ i j).trans (hfirst i j))
  unfold pairedSource
  rw [iteratedDeriv_fun_sum (fun i _ => ContDiffAt.sum (fun j _ => (hw i j).mul (he i j)))]
  simp_rw [iteratedDeriv_fun_sum (fun j _ => (hw _ j).mul (he _ j)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hi i j, testWeight_zero _ _ _ _ _ hJ,
    (testWeight_hasDerivAt J.metric H.metric K.metric L.metric M hJ i j).deriv,
    cubic_coefficient J H K L hJ Λ i j, quadratic_coefficient J H K L hJ Λ i j]

/-- Once every quadratic residual component vanishes, the bulk cubic coefficient is unchanged
by the varying volume and index raising. No boundary-current assertion is included. -/
theorem pairedSource_cubic_of_quadratic_zero (J H K L : Jet) (hJ : J.metric.det ≠ 0)
    (Λ : ℂ) (M : Mat)
    (hzero : ∀ i j, J.einstein i j + Λ * J.metric i j = 0)
    (hfirst : ∀ i j, CoordinateMetricTwoJet.Linearization.cosmological J H Λ i j = 0)
    (hsecond : ∀ i j, CoordinateMetricTwoJet.Linearization.cosmological J K Λ i j +
      secondVariation (toSpace J) i j (toSpace H) (toSpace H) / 2 = 0) :
    iteratedDeriv 3 (pairedSource J H K L Λ M) 0 / 6 =
      ∑ i, ∑ j, (J.metric⁻¹ * M * (J.metric⁻¹).transpose) i j *
        (CoordinateMetricTwoJet.Linearization.cosmological J L Λ i j +
          secondVariation (toSpace J) i j (toSpace H) (toSpace K) +
          thirdVariation (toSpace J) i j (toSpace H) (toSpace H) (toSpace H) / 6) := by
  simp only [pairedSource_cubic J H K L hJ Λ M hzero hfirst, hsecond, mul_zero, add_zero]

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet.CubicSource
