import DifferentialGeometry.Analysis.Spectral.Scalar.PoissonExistence
import GaloisForLFunctions.HTGeometry.CompactMeanZeroLaplacian

/-!
# Smooth Green inversion on the compact mean-zero space

The geometric Laplacian becomes a linear equivalence on smooth mean-zero
functions on a compact, connected, boundaryless Riemannian manifold of positive
dimension. Its inverse supplies both Green identities used by endpoint dressing.
The analytic producer is the upstream smooth Poisson theorem, including its
regularity proof. Green inversion is symmetric for the Riemannian L² pairing;
its quadratic form equals the negative Dirichlet energy of the solution.
These statements concern linear maps on smooth functions;
they do not assert boundedness, causality or a mass-shifted inverse.
-/

noncomputable section
open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff
namespace HTGeometry.CompactPoissonGreen
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

variable [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [NeZero (Module.finrank ℝ E)] [ConnectedSpace M]

/-- Smooth Poisson existence and uniqueness make the mean-zero Laplacian bijective. -/
theorem laplacian_bijective (g : SmoothRiemannianMetric I M) :
    Function.Bijective (laplacian g) := by
  constructor
  · intro f h hfh
    obtain ⟨u, hu, huniq⟩ := existsUnique_meanZero_smooth_poisson g
      (laplacian g f).1 (laplacian g f).2
    apply Subtype.ext
    apply (huniq f.1 ⟨f.2, fun _ => rfl⟩).trans
    symm
    apply huniq h.1
    refine ⟨h.2, ?_⟩
    intro x
    exact congrArg (fun v : meanZero g => v.1 x) hfh.symm
  · intro q
    obtain ⟨f, hf, _⟩ := existsUnique_meanZero_smooth_poisson g q.1 q.2
    refine ⟨⟨f, hf.1⟩, ?_⟩
    apply Subtype.ext
    exact ContMDiffMap.ext hf.2

/-- The geometric Laplacian as a linear equivalence on smooth mean-zero functions. -/
def laplacianEquiv (g : SmoothRiemannianMetric I M) : meanZero g ≃ₗ[ℝ] meanZero g :=
  LinearEquiv.ofBijective (laplacian g) (laplacian_bijective g)

/-- The normalized smooth inverse of `Δ_g = div_g grad_g`. -/
def green (g : SmoothRiemannianMetric I M) : Module.End ℝ (meanZero g) :=
  (laplacianEquiv g).symm.toLinearMap

theorem laplacian_green_apply (g : SmoothRiemannianMetric I M) (q : meanZero g) :
    laplacian g (green g q) = q :=
  (laplacianEquiv g).apply_symm_apply q

theorem green_laplacian_apply (g : SmoothRiemannianMetric I M) (f : meanZero g) :
    green g (laplacian g f) = f :=
  (laplacianEquiv g).symm_apply_apply f

theorem laplacian_green (g : SmoothRiemannianMetric I M) : laplacian g * green g = 1 := by
  apply LinearMap.ext
  intro q
  exact laplacian_green_apply g q

theorem green_laplacian (g : SmoothRiemannianMetric I M) : green g * laplacian g = 1 := by
  apply LinearMap.ext
  intro f
  exact green_laplacian_apply g f

/-- Reciprocity for the compact smooth Green inverse in the Riemannian L² pairing. -/
theorem green_symmetric (g : SmoothRiemannianMetric I M) (q r : meanZero g) :
    l2Pairing g (green g q) r = l2Pairing g q (green g r) := by
  simpa only [laplacian_green_apply] using
    (laplacian_symmetric g (green g q) (green g r)).symm

/-- The Green quadratic form equals the negative Dirichlet energy of its solution. -/
theorem green_energy (g : SmoothRiemannianMetric I M) (q : meanZero g) :
    l2Pairing g (green g q) q = -dirichletPairing g (green g q) (green g q) := by
  simpa only [laplacian_green_apply] using
    l2Pairing_laplacian g (green g q) (green g q)

theorem green_nonpositive (g : SmoothRiemannianMetric I M) (q : meanZero g) :
    l2Pairing g (green g q) q ≤ 0 := by
  rw [green_energy]
  exact neg_nonpos.mpr (dirichletPairing_self_nonneg g (green g q))

end HTGeometry.CompactPoissonGreen
