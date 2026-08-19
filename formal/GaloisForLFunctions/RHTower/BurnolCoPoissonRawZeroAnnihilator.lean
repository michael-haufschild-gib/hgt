import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin

/-!
# Raw co-Poisson zero annihilator

Burnol's co-Poisson Mellin identity gives every literal window-source vector a
factor `zeta(w)`.  This module takes the topological closure of exactly those
raw source vectors and proves that, at a zero in the right half of the critical
strip, the completed Mellin Riesz evaluator annihilates that entire closed
space.

This is intentionally distinct from `burnolCoPoissonSourceSpace`: the latter
also adjoins cosine transforms to enforce Fourier invariance.  Zero
annihilation of that cosine-closed enlargement is not established here, so
this is not a relabelling of Burnol's full Theorems 3.1--3.3.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Literal co-Poisson source vectors, before adjoining their cosine transforms. -/
def burnolCoPoissonRawSourceSet (b : ℝ) : Set evenSubspace :=
  {f | ∃ src : BurnolCoPoissonSource b, f = (src.vector : evenSubspace)}

/-- Algebraic raw co-Poisson span. -/
def burnolCoPoissonRawAlgebraicSourceSpace (b : ℝ) : Submodule ℂ evenSubspace :=
  Submodule.span ℂ (burnolCoPoissonRawSourceSet b)

/-- Closed raw co-Poisson source space. -/
def burnolCoPoissonRawSourceSpace (b : ℝ) : Submodule ℂ evenSubspace :=
  (burnolCoPoissonRawAlgebraicSourceSpace b).topologicalClosure

theorem burnolCoPoissonRawAlgebraicSourceSpace_le_soninExtendedSpace (b : ℝ) :
    burnolCoPoissonRawAlgebraicSourceSpace b ≤ soninExtendedSpace b := by
  rw [burnolCoPoissonRawAlgebraicSourceSpace, Submodule.span_le]
  rintro f ⟨src, rfl⟩
  exact src.vector.property

theorem isClosed_burnolCoPoissonRawSourceSpace (b : ℝ) :
    IsClosed (burnolCoPoissonRawSourceSpace b : Set evenSubspace) :=
  (burnolCoPoissonRawAlgebraicSourceSpace b).isClosed_topologicalClosure

theorem burnolCoPoissonRawSourceSpace_le_soninExtendedSpace
    {b : ℝ} (hb : 0 < b) :
    burnolCoPoissonRawSourceSpace b ≤ soninExtendedSpace b := by
  exact (burnolCoPoissonRawAlgebraicSourceSpace b).topologicalClosure_minimal
    (burnolCoPoissonRawAlgebraicSourceSpace_le_soninExtendedSpace b)
    (isClosed_soninExtendedSpace hb)

/-- At a zeta zero in the right half-strip, the completed Mellin Riesz
evaluator annihilates the closed span of all literal co-Poisson source
vectors. -/
theorem burnolExtendedSoninEvaluationVector_mem_rawSource_orthogonal
    {b : ℝ} {w : ℂ} (hb : 0 < b) (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (hz : riemannZeta w = 0) :
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) ∈
      (burnolCoPoissonRawSourceSpace b)ᗮ := by
  let E : evenSubspace := burnolExtendedSoninEvaluationVector w b hlo hhi hb
  let K : Submodule ℂ evenSubspace := Submodule.span ℂ ({E} : Set evenSubspace)
  have hraw : burnolCoPoissonRawAlgebraicSourceSpace b ≤ Kᗮ := by
    rw [burnolCoPoissonRawAlgebraicSourceSpace, Submodule.span_le]
    rintro f ⟨src, rfl⟩
    change ∀ u ∈ K, ⟪u, (src.vector : evenSubspace)⟫_ℂ = 0
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪u, (src.vector : evenSubspace)⟫_ℂ = 0)
      ?_ ?_ ?_ ?_ hu
    · intro x hx
      have hxE : x = E := by simpa only [Set.mem_singleton_iff] using hx
      rw [hxE]
      dsimp [E]
      exact inner_burnolExtendedSoninEvaluationVector_source_eq_zero hb src hlo hhi hz
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx
      rw [inner_smul_left, hx, mul_zero]
  have hclosure : burnolCoPoissonRawSourceSpace b ≤ Kᗮ := by
    rw [burnolCoPoissonRawSourceSpace]
    exact (burnolCoPoissonRawAlgebraicSourceSpace b).topologicalClosure_minimal hraw
      (Submodule.isClosed_orthogonal K)
  rw [Submodule.mem_orthogonal']
  intro x hx
  have hxK : x ∈ Kᗮ := hclosure hx
  rw [Submodule.mem_orthogonal] at hxK
  exact hxK E (Submodule.subset_span (by simp))

end RHTower
