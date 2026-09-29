import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities

/-!
# The geometric Laplacian on smooth mean-zero functions

On a compact Hausdorff smooth Riemannian manifold, integration defines a
mean-zero submodule of smooth real functions. For boundaryless manifolds,
the divergence theorem makes the geometric Laplacian an endomorphism of
this submodule. Neither connectedness nor positive dimension is required
for these constructions; those hypotheses belong to the Poisson inverse.
The first Green identity also gives symmetry and nonpositivity for the
Riemannian L² pairing, with the full Dirichlet energy retained.
-/

noncomputable section
open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff
namespace HTGeometry.CompactPoissonGreen
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

theorem laplacian_const_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    ΔG g (c • f) x = c * ΔG g f x := by
  have hgrad : gradG g (c • f) = smoothSmul (fun _ => c) contMDiff_const (gradG g f) := by
    ext y
    change gradFun g (c • (f : M → ℝ)) y = c • gradFun g f y
    exact gradFun_const_smul g c (f.contMDiff.mdifferentiable (by simp) y)
  rw [Δ_g_def, hgrad, divergence_g_smoothSmul, tangentSectionAction_const, add_zero]
  rfl

variable [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [I.Boundaryless] in
theorem integrable_smooth (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) := by
  letI := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact f.contMDiff.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def meanZero (g : SmoothRiemannianMetric I M) : Submodule ℝ C^∞⟮I, M; ℝ⟯ where
  carrier := {f | (∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh
    change (∫ x, f x + h x ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0
    rw [integral_add (integrable_smooth g f) (integrable_smooth g h), hf, hh, add_zero]
  smul_mem' := by
    intro c f hf
    change (∫ x, c * f x ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0
    rw [integral_const_mul, hf, mul_zero]

def laplacian (g : SmoothRiemannianMetric I M) : Module.End ℝ (meanZero g) where
  toFun f := ⟨⟨ΔG g f.1, Δ_g_contMDiff g f.1⟩,
    integral_divergence_eq_zero_of_compact g (gradG g f.1)⟩
  map_add' f h := by
    apply Subtype.ext
    apply ContMDiffMap.ext
    intro x
    exact Δ_g_add g f.1 h.1 x
  map_smul' c f := by
    apply Subtype.ext
    apply ContMDiffMap.ext
    intro x
    change ΔG g (c • f.1) x = c * ΔG g f.1 x
    exact laplacian_const_smul g c f.1 x

/-- Riemannian L² pairing of smooth mean-zero real functions. -/
def l2Pairing (g : SmoothRiemannianMetric I M) (f h : meanZero g) : ℝ :=
  ∫ x, f.1 x * h.1 x ∂riemannianVolumeMeasure (I := I) (M := M) g

/-- Metric gradient pairing, with the geometric Laplacian sign convention. -/
def dirichletPairing (g : SmoothRiemannianMetric I M) (f h : meanZero g) : ℝ :=
  ∫ x, g.inner x (gradG g f.1 x) (gradG g h.1 x)
    ∂riemannianVolumeMeasure (I := I) (M := M) g

omit [I.Boundaryless] in
theorem l2Pairing_symm (g : SmoothRiemannianMetric I M) (f h : meanZero g) :
    l2Pairing g f h = l2Pairing g h f := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => mul_comm _ _

theorem dirichletPairing_symm (g : SmoothRiemannianMetric I M) (f h : meanZero g) :
    dirichletPairing g f h = dirichletPairing g h f := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => g.symm x _ _

/-- The first Green identity on the smooth mean-zero space. -/
theorem l2Pairing_laplacian (g : SmoothRiemannianMetric I M) (f h : meanZero g) :
    l2Pairing g f (laplacian g h) = -dirichletPairing g f h := by
  have green_identity := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    g f.1.contMDiff h.1.contMDiff (HasCompactSupport.of_compactSpace _)
  have hf : (⟨(f.1 : M → ℝ), f.1.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) = f.1 := by
    ext x
    rfl
  have hh : (⟨(h.1 : M → ℝ), h.1.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) = h.1 := by
    ext x
    rfl
  rw [hf, hh] at green_identity
  change dirichletPairing g f h = -l2Pairing g f (laplacian g h) at green_identity
  simpa only [neg_neg] using (congrArg (fun r : ℝ => -r) green_identity).symm

/-- Symmetry of the geometric Laplacian for the Riemannian L² pairing. -/
theorem laplacian_symmetric (g : SmoothRiemannianMetric I M) (f h : meanZero g) :
    l2Pairing g (laplacian g f) h = l2Pairing g f (laplacian g h) := by
  rw [l2Pairing_symm g (laplacian g f) h, l2Pairing_laplacian,
    dirichletPairing_symm, l2Pairing_laplacian]

theorem dirichletPairing_self_nonneg (g : SmoothRiemannianMetric I M) (f : meanZero g) :
    0 ≤ dirichletPairing g f f := by
  exact integral_nonneg fun x => metric_inner_self_nonneg g x _

theorem laplacian_nonpositive (g : SmoothRiemannianMetric I M) (f : meanZero g) :
    l2Pairing g f (laplacian g f) ≤ 0 := by
  rw [l2Pairing_laplacian]
  exact neg_nonpos.mpr (dirichletPairing_self_nonneg g f)

end HTGeometry.CompactPoissonGreen
