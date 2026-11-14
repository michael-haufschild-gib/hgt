import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialMonomialDerivative
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.CarlemanLogCutoff
import GaloisForLFunctions.HTGeometry.Probability.BlockSphereMellin

/-!
# Radial Carleman concentration in higher complex dimension

A fixed smooth annular cutoff times powers of one complex coordinate separates into radial
and angular factors. At the critical conjugate exponents, the radial factors are independent
of degree. The unequal angular concentration rates obstruct a uniform radial estimate.
-/

open MeasureTheory Set Metric Filter Topology

noncomputable section
namespace GaloisForLFunctions.HTGeometry

local instance (n : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))

/-- The complex Hilbert space with one distinguished coordinate and `n` transverse coordinates. -/
abbrev RadialCarlemanSpace (n : ℕ) := BlockSpace ℂ (EuclideanSpace ℂ (Fin n))

/-- A fixed annular profile multiplied by a holomorphic coordinate power. -/
def radialCarlemanTest (n m : ℕ) : RadialCarlemanSpace n → ℂ :=
  radialComplexMonomial (EuclideanSpace ℂ (Fin n)) m carlemanLogCutoff

/-- Weighted integral norm of a scalar field in radial Carleman coordinates. -/
def radialCarlemanNorm (n : ℕ) (p τ : ℝ) (f : RadialCarlemanSpace n → ℂ) : ℝ :=
  (∫ x : RadialCarlemanSpace n, (‖x‖ ^ (-τ) * ‖f x‖) ^ p) ^ (1 / p)

/-- Weighted integral norm of the antiholomorphic differential. -/
def radialCarlemanDbarNorm (n : ℕ) (p τ : ℝ) (f : RadialCarlemanSpace n → ℂ) : ℝ :=
  (∫ x : RadialCarlemanSpace n,
    (‖x‖ ^ (-τ) * ‖_root_.HTGeometry.dbarDifferential f x‖) ^ p) ^ (1 / p)

/-- The real dimension of the complex orthogonal sum. -/
theorem radialCarlemanSpace_finrank (n : ℕ) :
    Module.finrank ℝ (RadialCarlemanSpace n) = 2 + 2 * n := by
  have hv : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin n)),
      Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_fin]
  rw [RadialCarlemanSpace, blockSpace_finrank, Complex.finrank_real_complex, hv]

theorem radialCarlemanSpace_real_finrank (n : ℕ) :
    (Module.finrank ℝ (RadialCarlemanSpace n) : ℝ) = 2 * ((n : ℝ) + 1) := by
  rw [radialCarlemanSpace_finrank]
  push_cast
  ring

/-- Complex and real-coordinate models give the same spherical Mellin moment. -/
theorem complexHilbertSphereMellin_eq (n : ℕ) {s : ℝ} (hs : -1 < s) :
    complexBlockSphereMellin (EuclideanSpace ℂ (Fin n)) s = complexSphereMellin n s := by
  rw [complexBlockSphereMellin_eq _ hs, complexSphereMellin_eq_gamma n hs,
    radialCarlemanSpace_real_finrank]
  have he : 2 * ((n : ℝ) + 1) / 2 = (n : ℝ) + 1 := by ring
  rw [he, Real.Gamma_nat_eq_factorial]
  congr 2
  ring

/-- Degree-independent radial factor in the weighted function norm. -/
def radialCarlemanAmplitude (n : ℕ) (p : ℝ) : ℝ :=
  (((volume : Measure (RadialCarlemanSpace n)).toSphere).real univ *
    ∫ t : ℝ, |carlemanLogCutoff t| ^ p) ^ (1 / p)

/-- Degree-independent radial factor in the weighted differential norm. -/
def radialCarlemanDefect (n : ℕ) (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (((volume : Measure (RadialCarlemanSpace n)).toSphere).real univ *
      ∫ t : ℝ, |deriv carlemanLogCutoff t| ^ p) ^ (1 / p)

theorem radialCarlemanAmplitude_pos (n : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < radialCarlemanAmplitude n p := by
  apply Real.rpow_pos_of_pos
  exact mul_pos (complexBlock_sphere_mass_pos (EuclideanSpace ℂ (Fin n)))
    (integral_carlemanLogCutoff_rpow_pos hp)

end GaloisForLFunctions.HTGeometry
