import GaloisForLFunctions.HTGeometry.CompactPoissonGreen

/-!
# The exact radical of compact Green heights

The Green height on smooth mean-zero sources is strictly negative away
from zero. Vanishing Dirichlet energy forces the smooth gradient to vanish
pointwise, and Poisson uniqueness then removes the constant ambiguity.
This supplies the radical statement in the Green-energy mechanism behind
Du, Corollary 9.32, for the existing geometric Poisson inverse.
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
  [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [NeZero (Module.finrank ℝ E)] [ConnectedSpace M]

/-- The normalized smooth Dirichlet form has no radical. -/
theorem dirichletPairing_self_eq_zero_iff (g : SmoothRiemannianMetric I M)
    (f : meanZero g) : dirichletPairing g f f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    letI := riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    letI := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
    have hcont := continuous_inner_gradFun_self g f.1
    have hint : Integrable (fun x => g.inner x (gradFun g f.1 x) (gradFun g f.1 x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hae : (fun x => g.inner x (gradFun g f.1 x) (gradFun g f.1 x))
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] (fun _ => (0 : ℝ)) := by
      apply (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => metric_inner_self_nonneg g x _)) hint).mp
      simpa only [dirichletPairing, grad_g_apply] using hz
    have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq
      (μ := riemannianVolumeMeasure (I := I) (M := M) g)
      (U := Set.univ) (by rw [MeasureTheory.Measure.restrict_univ]; exact hae)
      isOpen_univ hcont.continuousOn continuous_zero.continuousOn
    have hgrad : gradG g f.1 = 0 := by
      ext x
      rw [grad_g_apply]
      by_contra hne
      exact (ne_of_gt (g.pos x _ hne)) (heq (Set.mem_univ x))
    have hlap : laplacian g f = 0 := by
      apply Subtype.ext
      apply ContMDiffMap.ext
      intro x
      change ΔG g f.1 x = 0
      rw [Δ_g_def, hgrad]
      exact divergence_g_zero g x
    apply (laplacian_bijective g).1
    simpa only [map_zero] using hlap
  · rintro rfl
    have h := l2Pairing_laplacian g 0 0
    simpa [l2Pairing] using h.symm

/-- Zero Green height is equivalent to zero source, with no spectral assumption. -/
theorem green_height_eq_zero_iff (g : SmoothRiemannianMetric I M) (q : meanZero g) :
    l2Pairing g (green g q) q = 0 ↔ q = 0 := by
  rw [green_energy, neg_eq_zero, dirichletPairing_self_eq_zero_iff]
  constructor
  · intro h
    have heq := congrArg (laplacian g) h
    simpa only [laplacian_green_apply, map_zero] using heq
  · rintro rfl
    exact map_zero _

/-- Every nonzero normalized source has strictly negative Green height. -/
theorem green_height_neg_iff (g : SmoothRiemannianMetric I M) (q : meanZero g) :
    l2Pairing g (green g q) q < 0 ↔ q ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, green_height_eq_zero_iff]
  exact and_iff_right (green_nonpositive g q)

/-- The full bilinear radical agrees with the zero-source kernel. -/
theorem green_height_radical (g : SmoothRiemannianMetric I M) (q : meanZero g) :
    (∀ r : meanZero g, l2Pairing g (green g q) r = 0) ↔ q = 0 := by
  constructor
  · intro h
    exact (green_height_eq_zero_iff g q).mp (h q)
  · rintro rfl
    intro r
    simp [l2Pairing]

#print axioms dirichletPairing_self_eq_zero_iff
#print axioms green_height_eq_zero_iff
#print axioms green_height_neg_iff
#print axioms green_height_radical

end HTGeometry.CompactPoissonGreen
