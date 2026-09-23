import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreProjection

/-!
# Finite-deck core splice

The finite product-grid witness is supported on precisely the finite core in the
modular cell measure.  Therefore core cutoff fixes it.  This is the algebraic
bridge from a local chart approximation to an ambient finite-dimensional
approximant.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The finite-core cutoff fixes every finite product-grid step. -/
theorem finiteGridCoreProjection_apply_deckGridStep {N M K : ℕ}
    {a c hx hy : ℝ} (C : ℕ → ℕ → DeckSpace N) :
    finiteGridCoreProjection (N := N) (M := M) (K := K) a c hx hy
      (deckGridStep (N := N) (M := M) (K := K) a c hx hy C) =
        deckGridStep (N := N) (M := M) (K := K) a c hx hy C := by
  classical
  apply Lp.ext
  have hproj := MeasureTheory.lpBoundedSmulCLM_coeFn (p := 2) (μ := cellMeasure)
    (H := DeckSpace N) (measurable_finiteGridCoreCutoff (M := M) (K := K) a c hx hy)
    (by positivity) (norm_finiteGridCoreCutoff_le_one (M := M) (K := K) a c hx hy)
    (deckGridStep (N := N) (M := M) (K := K) a c hx hy C)
  have hstep := deckGridStep_coeFn (N := N) (M := M) (K := K) a c hx hy C
  filter_upwards [hproj, hstep,
    ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hproj hstep hfd
  change
    ((MeasureTheory.lpBoundedSmulCLM (p := 2) (μ := cellMeasure) (H := DeckSpace N)
      (measurable_finiteGridCoreCutoff (M := M) (K := K) a c hx hy) (by positivity)
      (norm_finiteGridCoreCutoff_le_one (M := M) (K := K) a c hx hy)
      (deckGridStep (N := N) (M := M) (K := K) a c hx hy C) : DeckL2 N) :
        ℍ → DeckSpace N) z = _
  rw [hproj, hstep]
  by_cases hcore : z ∈ fdUpperChartGridCore (M := M) (K := K) a c hx hy
  · simp [finiteGridCoreCutoff, hcore]
  · rw [show finiteGridCoreCutoff (M := M) (K := K) a c hx hy z = 0 by
      simp [finiteGridCoreCutoff, hcore], zero_smul]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [Set.indicator_of_notMem]
    intro hcell
    apply hcore
    unfold fdUpperChartGridCore
    exact Set.mem_iUnion.mpr ⟨i, hfd, hcell⟩

/-- Passing a literal difference to `DeckL2` is the difference of the two
classes, including when the second field is an arbitrary finite grid step. -/
theorem toDeckL2_sub_deckGridStep {N M K : ℕ} {a c hx hy : ℝ}
    (F : ℍ → DeckSpace N) (hF : MemLp F 2 cellMeasure)
    (C : ℕ → ℕ → DeckSpace N) :
    toDeckL2 (F - ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
      ℍ → DeckSpace N)) (hF.sub (Lp.memLp _)) =
      toDeckL2 F hF - deckGridStep (N := N) (M := M) (K := K) a c hx hy C := by
  apply Lp.ext
  filter_upwards [(hF.sub (Lp.memLp _)).coeFn_toLp, hF.coeFn_toLp,
    Lp.coeFn_sub (toDeckL2 F hF)
      (deckGridStep (N := N) (M := M) (K := K) a c hx hy C)] with z hsub hFz hco
  change
    (((hF.sub (Lp.memLp _)).toLp
      (F - ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
        ℍ → DeckSpace N)) : DeckL2 N) : ℍ → DeckSpace N) z = _
  rw [hsub, hco]
  change F z - ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
      ℍ → DeckSpace N) z =
    ((hF.toLp F : DeckL2 N) : ℍ → DeckSpace N) z -
      ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
        ℍ → DeckSpace N) z
  rw [hFz]

/-- The distance from the cutoff of a field to its finite grid witness is
exactly the literal `L²` error on the core. -/
theorem normSq_finiteGridCoreProjection_sub_deckGridStep {N M K : ℕ}
    {a c hx hy : ℝ} (F : ℍ → DeckSpace N) (hF : MemLp F 2 cellMeasure)
    (C : ℕ → ℕ → DeckSpace N) :
    ‖finiteGridCoreProjection (N := N) (M := M) (K := K) a c hx hy
        (toDeckL2 F hF) - deckGridStep (N := N) (M := M) (K := K) a c hx hy C‖ ^ (2 : ℕ) =
      ∫ z in fdUpperChartGridCore (M := M) (K := K) a c hx hy,
        ‖F z - ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
          ℍ → DeckSpace N) z‖ ^ (2 : ℕ) := by
  conv_lhs => rw [← finiteGridCoreProjection_apply_deckGridStep C]
  rw [← map_sub,
    ← toDeckL2_sub_deckGridStep F hF C]
  exact normSq_finiteGridCoreProjection_toDeckL2 a c hx hy
    (F - ((deckGridStep (N := N) (M := M) (K := K) a c hx hy C : DeckL2 N) :
      ℍ → DeckSpace N)) (hF.sub (Lp.memLp _))

/-- The Poincaré grid witness becomes a finite-dimensional ambient approximation
after exact core cutoff. -/
theorem exists_grid_coreProjection_hyperbolic_error_le {N : ℕ} {ε a c hx hy : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hεc : ε ≤ c) (hhx : 0 < hx) (hhy : 0 < hy)
    (F : formPreDomain N) (M K : ℕ) :
    ∃ C : ℕ → ℕ → DeckSpace N,
      ‖finiteGridCoreProjection (N := N) (M := M) (K := K) a c hx hy
          (toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F)) -
        deckGridStep (N := N) (M := M) (K := K) a c hx hy C‖ ^ (2 : ℕ) ≤
        (c ^ (2 : ℕ))⁻¹ *
          (8 * hx ^ (2 : ℕ) *
            (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
              ∫ x in Set.Ioc a (a + (M : ℝ) * hx),
                retractedDeckEnergyX ε F (x, y)) +
          2 * hy ^ (2 : ℕ) *
            (∫ x in Set.Ioc a (a + (M : ℝ) * hx),
              ∫ y in Set.Ioc c (c + (K : ℝ) * hy),
                retractedDeckEnergyY ε F (x, y))) := by
  obtain ⟨C, hC⟩ := exists_grid_fdUpperChartGridCore_hyperbolic_error_le
    hε hc hεc hhx hhy F M K
  refine ⟨C, ?_⟩
  rw [normSq_finiteGridCoreProjection_sub_deckGridStep]
  exact hC

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
