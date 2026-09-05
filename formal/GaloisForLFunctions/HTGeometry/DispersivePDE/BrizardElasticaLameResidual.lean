import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaLameSpectrum
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPlanar
import Mathlib.Tactic

/-!
# Self-consistency audit of the printed Lamé NLS field

Section VII inserts `k₀ dn(u|m)` into NLS while the elastica curvature entering the nonlinear
term has square `k₀²(1-(m/q₀)sn²)`.  The two amplitudes agree only on special loci.  Exact
algebra exposes the residual left by using the printed `dn` field in the nonlinear equation.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

abbrev PositiveLameScale := {q : ℝ // 0 < q}

noncomputable def printedLameEpsilonSq (m : ℝ) (q : PositiveLameScale) : ℝ :=
  1 - m / (2 * (q : ℝ))

/-- Dimensionless coefficient of the NLS residual after the printed Lamé substitution. -/
noncomputable def printedLameReducedResidual
    (m : ℝ) (q : PositiveLameScale) (sn dn : ℝ) : ℝ :=
  -(printedLameEpsilonSq m q / 2) * dn +
    (2 * m * sn ^ 2 - m) / (4 * (q : ℝ)) * dn + dn ^ 3 / 2

/-- Unconditional split into Jacobi-identity error and amplitude-mismatch error. -/
theorem printedLameReducedResidual_decomposition
    (m : ℝ) (q : PositiveLameScale) (sn dn : ℝ) :
    printedLameReducedResidual m q sn dn =
      dn / 2 * (dn ^ 2 + m * sn ^ 2 - 1) +
      dn * m * (1 - (q : ℝ)) / (2 * (q : ℝ)) * sn ^ 2 := by
  rw [printedLameReducedResidual, printedLameEpsilonSq]
  field_simp [ne_of_gt q.property]
  ring

/-- One point satisfying the standard Jacobi identity `dn² + m sn² = 1`. -/
structure JacobiLamePoint (m : ℝ) where
  sn : ℝ
  dn : ℝ
  quadratic : dn ^ 2 + m * sn ^ 2 = 1

/-- On genuine Jacobi data, only the `q₀` amplitude mismatch remains. -/
theorem printedLameReducedResidual_eq_defect
    (m : ℝ) (q : PositiveLameScale) (J : JacobiLamePoint m) :
    printedLameReducedResidual m q J.sn J.dn =
      J.dn * m * (1 - (q : ℝ)) / (2 * (q : ℝ)) * J.sn ^ 2 := by
  rw [printedLameReducedResidual_decomposition, J.quadratic]
  ring

/-- Point where neither Jacobi factor masks the printed residual. -/
structure NondegenerateJacobiLamePoint (m : ℝ) extends JacobiLamePoint m where
  sn_ne_zero : sn ≠ 0
  dn_ne_zero : dn ≠ 0

/-- For nonzero modulus and nondegenerate Jacobi values, printed field solves only at `q₀=1`. -/
theorem printedLameReducedResidual_eq_zero_iff
    (m : ℝˣ) (q : PositiveLameScale)
    (J : NondegenerateJacobiLamePoint (m : ℝ)) :
    printedLameReducedResidual (m : ℝ) q J.sn J.dn = 0 ↔ (q : ℝ) = 1 := by
  rw [printedLameReducedResidual_eq_defect]
  have hfactor : J.dn * (m : ℝ) / (2 * (q : ℝ)) * J.sn ^ 2 ≠ 0 := by
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero J.dn_ne_zero m.ne_zero)
        (mul_ne_zero two_ne_zero (ne_of_gt q.property)))
      (pow_ne_zero 2 J.sn_ne_zero)
  have hrearrange :
      J.dn * (m : ℝ) * (1 - (q : ℝ)) / (2 * (q : ℝ)) * J.sn ^ 2 =
        (J.dn * (m : ℝ) / (2 * (q : ℝ)) * J.sn ^ 2) *
          (1 - (q : ℝ)) := by ring
  rw [hrearrange, mul_eq_zero]
  simp only [hfactor, false_or]
  constructor <;> intro h <;> linarith

/-- The paper's corrected elastica amplitude square differs from `dn²` by the same wall factor. -/
theorem elasticaAmplitudeSq_sub_dnSq
    (m : ℝ) (q : PositiveLameScale) (J : JacobiLamePoint m) :
    (1 - m / (q : ℝ) * J.sn ^ 2) - J.dn ^ 2 =
      m * ((q : ℝ) - 1) / (q : ℝ) * J.sn ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := ne_of_gt q.property
  field_simp [hq]
  have hdn : J.dn ^ 2 = 1 - m * J.sn ^ 2 := by
    linarith [J.quadratic]
  rw [hdn]
  ring

/-- In particular, every nondegenerate admissible torsionless point has nonzero printed residual. -/
theorem planar_printedLameReducedResidual_ne_zero
    (m : PlanarTravelingModulus)
    (J : NondegenerateJacobiLamePoint (m : ℝ)) :
    printedLameReducedResidual (m : ℝ) ⟨m, m.property.1⟩ J.sn J.dn ≠ 0 := by
  have hmpos : 0 < (m : ℝ) := m.property.1
  have hmle : (m : ℝ) ≤ 1 / 2 := m.property.2
  let mu : ℝˣ := Units.mk0 (m : ℝ) (ne_of_gt hmpos)
  let q : PositiveLameScale := ⟨m, hmpos⟩
  have hclass := printedLameReducedResidual_eq_zero_iff mu q J
  intro hzero
  have hzero' : printedLameReducedResidual (mu : ℝ) q J.sn J.dn = 0 := by
    simpa [mu, q] using hzero
  have hmone := hclass.mp hzero'
  change (m : ℝ) = 1 at hmone
  linarith

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
