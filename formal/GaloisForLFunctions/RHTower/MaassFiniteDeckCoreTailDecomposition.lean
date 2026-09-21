import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreSplice
import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreTailPartition
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTail

/-!
# Finite-deck core--tail decomposition

The reciprocal finite core and the strict cusp tail partition the modular cell
almost everywhere.  Their bounded multipliers therefore sum to the identity
on `DeckL2`.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Every point of the reciprocal finite core lies at or below its prescribed
tail height. -/
theorem im_le_coreTailHeight_of_mem_fdUpperChartGridCore {M K : ℕ}
    (z : ℍ) (hz : z ∈ fdUpperChartGridCore (M := M) (K := K)
      (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)) :
    z.im ≤ Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹ := by
  have hnonneg : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
  rw [fdUpperChartGridCore_eq_fd_inter_upperChartGridCore,
    upperChartGridCore_eq_coordinateRect] at hz
  · exact hz.2.2.2
  · exact hnonneg
  · exact hnonneg

/-- A point strictly above the reciprocal core height cannot belong to that
finite core. -/
theorem not_mem_fdUpperChartGridCore_of_coreTail_lt {M K : ℕ}
    (z : ℍ) (htail : Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹ < z.im) :
    z ∉ fdUpperChartGridCore (M := M) (K := K)
      (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) := by
  intro hcore
  exact (not_le_of_gt htail)
    (im_le_coreTailHeight_of_mem_fdUpperChartGridCore z hcore)

/-- On the modular cell, the reciprocal finite-core and strict-tail cutoffs
sum to one almost everywhere. -/
theorem finiteGridCoreCutoff_add_cuspTailCutoff_ae_eq_one {M K : ℕ} (hM : 0 < M) :
    ∀ᵐ z ∂cellMeasure,
      finiteGridCoreCutoff (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) z +
        cuspTailCutoff (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) z = 1 := by
  filter_upwards [ae_mem_fdo] with z hz
  rcases fdo_mem_fdUpperChartGridCore_or_tail hM z hz with hcore | htail
  · have hnotail : ¬ Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹ < z.im :=
      not_lt_of_ge (im_le_coreTailHeight_of_mem_fdUpperChartGridCore z hcore)
    simp [finiteGridCoreCutoff, hcore, cuspTailCutoff, hnotail]
  · have hncore := not_mem_fdUpperChartGridCore_of_coreTail_lt z htail
    simp [finiteGridCoreCutoff, hncore, cuspTailCutoff, htail]

/-- Core cutoff plus cusp-tail cutoff is exactly the identity on the modular
`L²` space. -/
theorem finiteGridCoreProjection_add_cuspTailProjection_eq_id {N M K : ℕ}
    (hM : 0 < M) :
    finiteGridCoreProjection (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) +
      cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) =
        ContinuousLinearMap.id ℂ (DeckL2 N) := by
  apply ContinuousLinearMap.ext
  intro w
  apply Lp.ext
  have hcore :
      ((finiteGridCoreProjection (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) w : DeckL2 N) :
          ℍ → DeckSpace N) =ᵐ[cellMeasure]
        fun z => finiteGridCoreCutoff (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) z •
          ((w : DeckL2 N) : ℍ → DeckSpace N) z := by
    exact MeasureTheory.lpBoundedSmulCLM_coeFn (p := 2) (μ := cellMeasure)
      (H := DeckSpace N)
      (measurable_finiteGridCoreCutoff (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)) (by positivity)
      (norm_finiteGridCoreCutoff_le_one (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)) w
  have htail :
      ((cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) w : DeckL2 N) :
          ℍ → DeckSpace N) =ᵐ[cellMeasure]
        fun z => cuspTailCutoff (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) z •
          ((w : DeckL2 N) : ℍ → DeckSpace N) z := by
    exact MeasureTheory.lpBoundedSmulCLM_coeFn (p := 2) (μ := cellMeasure)
      (H := DeckSpace N)
      (measurable_cuspTailCutoff (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹))
      (by positivity)
      (norm_cuspTailCutoff_le_one (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)) w
  filter_upwards [Lp.coeFn_add
      (finiteGridCoreProjection (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) w)
      (cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) w),
    hcore, htail,
    finiteGridCoreCutoff_add_cuspTailCutoff_ae_eq_one (M := M) (K := K) hM]
      with z hadd hcore htail hcut
  change
    ((↑(finiteGridCoreProjection (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) w +
      cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) w) :
        ℍ → DeckSpace N) z) = ((w : DeckL2 N) : ℍ → DeckSpace N) z
  rw [hadd]
  change
    ((finiteGridCoreProjection (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) w : DeckL2 N) :
        ℍ → DeckSpace N) z +
      ((cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) w : DeckL2 N) :
        ℍ → DeckSpace N) z = ((w : DeckL2 N) : ℍ → DeckSpace N) z
  rw [hcore, htail, ← add_smul, hcut, one_smul]

/-- The global grid error splits into its exact finite-core error plus its
cusp-tail error.  This is the analytic splice used before the two estimates
are made quantitatively small. -/
theorem norm_sub_deckGridStep_le_core_add_tail {N M K : ℕ} (hM : 0 < M)
    (u : DeckL2 N) (C : ℕ → ℕ → DeckSpace N) :
    ‖u - deckGridStep (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ ≤
      ‖finiteGridCoreProjection (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) u -
        deckGridStep (N := N) (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ +
        ‖cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) u‖ := by
  have hsplit := congrArg (fun T : DeckL2 N →L[ℂ] DeckL2 N => T u)
    (finiteGridCoreProjection_add_cuspTailProjection_eq_id (N := N)
      (M := M) (K := K) hM)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] at hsplit
  calc
    ‖u - deckGridStep (N := N) (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ =
        ‖(finiteGridCoreProjection (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) u +
          cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) u) -
          deckGridStep (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ := by
          rw [hsplit]
    _ = ‖(finiteGridCoreProjection (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) u -
          deckGridStep (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C) +
          cuspTailProjection N (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹) u‖ := by
          congr 1
          abel
    _ ≤ _ := norm_add_le _ _

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
