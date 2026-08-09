import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CrossedModule
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.HigherPeriodSpencer

/-!
# Twisted-module higher Ambrose--Singer--Spencer law

The lower transport may be noncommutative, but it acts linearly on the finite-dimensional higher
coefficient fibre.  This file combines the exact period-generation theorem with monodromy
equivariance, analytic Spencer generation, absence of a uniform jet cutoff, and the zero-boundary
crossed-module realization.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.TwistedModuleHigherAmbroseSingerSpencer

open HigherPeriodSpencer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Higher-period data together with nonabelian lower monodromy on its coefficient fibre. -/
structure TwistedModuleField (G ι σ : Type*) [Group G] extends
    PeriodGeometry (V := V) ι σ where
  monodromy : G →* (V ≃ₗ[ℝ] V)
  curvatureIndexAction : G →* Equiv.Perm ι
  curvature_equivariant : ∀ g i,
    monodromy g (toPeriodGeometry.curvatureValue i) =
      toPeriodGeometry.curvatureValue (curvatureIndexAction g i)

namespace TwistedModuleField

variable {G ι σ : Type*} [Group G] (T : TwistedModuleField (V := V) G ι σ)

omit [FiniteDimensional ℝ V] in
/-- Lower monodromy preserves the transported higher-curvature span. -/
theorem monodromy_mem_curvatureSpan (g : G) {v : V}
    (hv : v ∈ T.toPeriodGeometry.curvatureSpan) :
    T.monodromy g v ∈ T.toPeriodGeometry.curvatureSpan := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      rw [T.curvature_equivariant]
      exact Submodule.subset_span (Set.mem_range_self _)
  | zero => simpa only [map_zero] using T.toPeriodGeometry.curvatureSpan.zero_mem
  | add x y _ _ hx hy => simpa using T.toPeriodGeometry.curvatureSpan.add_mem hx hy
  | smul c x _ hx => simpa using T.toPeriodGeometry.curvatureSpan.smul_mem c hx

omit [FiniteDimensional ℝ V] in
/-- The curvature span is equivariant under the full lower holonomy group. -/
theorem monodromy_curvatureSpan (g : G) :
    Submodule.map (T.monodromy g).toLinearMap T.toPeriodGeometry.curvatureSpan =
      T.toPeriodGeometry.curvatureSpan := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact T.monodromy_mem_curvatureSpan g hv
  · intro v hv
    have hinv := T.monodromy_mem_curvatureSpan g⁻¹ hv
    refine ⟨T.monodromy g⁻¹ v, hinv, ?_⟩
    rw [T.monodromy.map_inv]
    exact (T.monodromy g).apply_symm_apply v

/-- Curvature values generate restricted higher holonomy in the twisted coefficient fibre. -/
theorem higher_ambroseSinger :
    T.toPeriodGeometry.restrictedAlgebra =
      Submodule.span ℝ (Set.range T.toPeriodGeometry.curvatureValue) :=
  T.toPeriodGeometry.higher_ambroseSinger

end TwistedModuleField

/-- Analytic twisted-module generation is exactly the common analytic Spencer theorem. -/
theorem analytic_higher_ambroseSinger_spencer
    {ι σ κ : Type*} (A : AnalyticSpencerGeometry (V := V) ι σ κ) :
    A.toPeriodGeometry.restrictedAlgebra = A.jetSpan :=
  A.higher_ambroseSinger_spencer

/-- There is no coefficient-independent finite Spencer cutoff. -/
theorem no_uniform_finite_jet_cutoff (N : ℕ) :
    Submodule.span ℝ (HigherPeriodSpencer.delayedJet N '' Set.Iio N) = ⊥ ∧
      Submodule.span ℝ (Set.range (HigherPeriodSpencer.delayedJet N)) = ⊤ :=
  HigherPeriodSpencer.no_uniform_finite_jet_cutoff N

section ZeroBoundaryRealization

open CrossedModule

variable {G₁ G₂ G₃ H₂ H₃ : Type*}
variable [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
variable [AddCommGroup H₂] [AddCommGroup H₃]
variable [Module ℝ G₁] [Module ℝ G₂] [Module ℝ G₃]
variable [Module ℝ H₂] [Module ℝ H₃]

/-- With zero crossed-module boundary, fake flatness is ordinary flatness of the lower
connection. -/
theorem lower_flat_of_zero_boundary
    (D : DifferentialCrossedModuleCalculus G₁ G₂ G₃ H₂ H₃)
    (hboundary : D.boundary₂ = 0) (A : G₁) (B : H₂)
    (hfake : D.fakeCurvature A B = 0) :
    D.curvature A = 0 := by
  rw [DifferentialCrossedModuleCalculus.fakeCurvature, hboundary] at hfake
  simpa using hfake

/-- In the zero-boundary realization, the three-curvature has zero boundary automatically. -/
theorem threeCurvature_boundary_zero
    (D : DifferentialCrossedModuleCalculus G₁ G₂ G₃ H₂ H₃)
    (hboundary : D.boundary₃ = 0) (A : G₁) (B : H₂) :
    D.boundary₃ (D.threeCurvature A B) = 0 := by
  rw [hboundary]
  rfl

end ZeroBoundaryRealization

section FlatAmbiguity

/-- Full higher holonomy may carry a flat component invisible to local curvature. -/
def localCurvatureProjection {F : Type*} (x : V × F) : V := x.1

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Distinct flat characters can have identical local curvature data. -/
theorem flat_character_independent {F : Type*} {f₀ f₁ : F} (hf : f₀ ≠ f₁) (v : V) :
    localCurvatureProjection (v, f₀) = localCurvatureProjection (v, f₁) ∧
      (v, f₀) ≠ (v, f₁) := by
  refine ⟨rfl, ?_⟩
  intro h
  exact hf (Prod.mk.inj h).2

end FlatAmbiguity

end HTGeometry.NomologicalHomotopyGeometry.TwistedModuleHigherAmbroseSingerSpencer
