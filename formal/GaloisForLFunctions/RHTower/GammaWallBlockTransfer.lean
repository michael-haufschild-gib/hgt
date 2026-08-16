import GaloisForLFunctions.RHTower.WallBlockSeries
import GaloisForLFunctions.RHTower.GammaWallTerminalBlockSource

/-!
# From the block norm to the block-solution series

The block source norm `N_σ` is an `ℝ≥0∞`-valued sum of `L²` norms of the weighted blocks; the block
Hardy transfer wants the same data as a real-valued summability statement about
`√(∫‖g_k‖²)`.  Converting between them is exactly `ENNReal.summable_toReal` once each block norm is
seen to be finite — which it is, being one term of a convergent sum.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `k`-th weighted block of a physical source. -/
def gammaWallBlockPiece (σ : ℝ) (J : ℝ → X) (k : ℤ) : ℝ → X :=
  (Icc (k : ℝ) ((k : ℝ) + 1)).indicator fun y => Real.exp (σ * y) • J y

theorem gammaWallBlockPiece_supp (σ : ℝ) (J : ℝ → X) (k : ℤ) :
    ∀ L : ℝ, L ∉ Icc (k : ℝ) ((k : ℝ) + 1) → gammaWallBlockPiece σ J k L = 0 :=
  fun _ hL => Set.indicator_of_notMem hL _

theorem stronglyMeasurable_gammaWallBlockPiece {σ : ℝ} {J : ℝ → X}
    (hJm : StronglyMeasurable J) (k : ℤ) :
    StronglyMeasurable (gammaWallBlockPiece σ J k) := by
  refine StronglyMeasurable.indicator ?_ measurableSet_Icc
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).stronglyMeasurable.smul hJm

/-- Each block of a source with finite block norm is square integrable. -/
theorem memLp_gammaWallBlockPiece {σ : ℝ} {J : ℝ → X}
    (hJm : StronglyMeasurable J) (hfin : gammaWallBlockNorm σ J < ⊤) (k : ℤ) :
    MemLp (gammaWallBlockPiece σ J k) 2 (volume : Measure ℝ) := by
  have hterm : ENNReal.ofReal (Real.exp (max 0 (-(k : ℝ)))) *
      eLpNorm (fun L => Real.exp (σ * L) • J L) 2
        (volume.restrict (Icc (k : ℝ) ((k : ℝ) + 1))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin.ne ?_
    rw [gammaWallBlockNorm]
    exact ENNReal.le_tsum k
  have hne : ENNReal.ofReal (Real.exp (max 0 (-(k : ℝ)))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hfin' : eLpNorm (fun L => Real.exp (σ * L) • J L) 2
      (volume.restrict (Icc (k : ℝ) ((k : ℝ) + 1))) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hne] at hterm
    exact hterm rfl
  refine ⟨(stronglyMeasurable_gammaWallBlockPiece hJm k).aestronglyMeasurable, ?_⟩
  rw [gammaWallBlockPiece, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
  exact lt_top_iff_ne_top.mpr hfin'

theorem eLpNorm_gammaWallBlockPiece_toReal {σ : ℝ} {J : ℝ → X}
    (hJm : StronglyMeasurable J) (hfin : gammaWallBlockNorm σ J < ⊤) (k : ℤ) :
    (ENNReal.ofReal (Real.exp (max 0 (-(k : ℝ)))) *
        eLpNorm (fun L => Real.exp (σ * L) • J L) 2
          (volume.restrict (Icc (k : ℝ) ((k : ℝ) + 1)))).toReal
      = Real.exp (max 0 (-(k : ℝ)))
        * Real.sqrt (∫ L : ℝ, ‖gammaWallBlockPiece σ J k L‖ ^ 2) := by
  have hmem := memLp_gammaWallBlockPiece hJm hfin k
  have hsq : Integrable (fun L : ℝ => ‖gammaWallBlockPiece σ J k L‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hrestrict : eLpNorm (fun L => Real.exp (σ * L) • J L) 2
      (volume.restrict (Icc (k : ℝ) ((k : ℝ) + 1)))
      = eLpNorm (gammaWallBlockPiece σ J k) 2 (volume : Measure ℝ) := by
    rw [gammaWallBlockPiece, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
  have hval : eLpNorm (gammaWallBlockPiece σ J k) 2 (volume : Measure ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ L : ℝ, ‖gammaWallBlockPiece σ J k L‖ ^ 2)) := by
    rw [eLpNorm_two_eq_sq, lintegral_enorm_sq_eq_ofReal_integral hsq,
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => by positivity) (by norm_num)]
    congr 1
    exact (Real.sqrt_eq_rpow _).symm
  rw [hrestrict, hval, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (by positivity)]

/-- **The block-solution series is summable when the block norm is finite.** -/
theorem summable_gammaWallBlockPiece_norm {σ : ℝ} {J : ℝ → X}
    (hJm : StronglyMeasurable J) (hfin : gammaWallBlockNorm σ J < ⊤) :
    Summable fun k : ℤ => Real.exp (max 0 (-(k : ℝ)))
      * Real.sqrt (∫ L : ℝ, ‖gammaWallBlockPiece σ J k L‖ ^ 2) := by
  have h := ENNReal.summable_toReal (f := fun k : ℤ =>
    ENNReal.ofReal (Real.exp (max 0 (-(k : ℝ)))) *
      eLpNorm (fun L => Real.exp (σ * L) • J L) 2
        (volume.restrict (Icc (k : ℝ) ((k : ℝ) + 1)))) (by
      rw [← gammaWallBlockNorm]
      exact hfin.ne)
  refine h.congr fun k => ?_
  exact eLpNorm_gammaWallBlockPiece_toReal hJm hfin k


/-! ## `(16)`: the block Hardy transfer for a physical source -/

section Transfer

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [Nontrivial Y]

variable {E : ℂ → ℂ} {T : Y →L[ℂ] Y}

/-- **`(16)`: a physical source in the block class produces a convergent block-solution series.**
The weighted `L²` norms of the blocks are exactly the terms of the block norm, so finiteness of the
latter is the summability hypothesis of the Gamma-wall block Hardy theorem. -/
theorem summable_blockSolutions_of_gammaWallBlockNorm
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {J : ℝ → Y} (hJm : StronglyMeasurable J) (hfin : gammaWallBlockNorm σ J < ⊤) :
    Summable fun k : ℤ =>
      (memLp_forcedProfile_blockSource hEdiff hE hEne hT hσ0 hσ1
        (memLp_gammaWallBlockPiece hJm hfin k)
        (stronglyMeasurable_gammaWallBlockPiece hJm k)
        (gammaWallBlockPiece_supp σ J k) (0 : Y)).toLp _ :=
  summable_blockSolutions hEdiff hE hEne hT hσ0 hσ1
    (fun k => memLp_gammaWallBlockPiece hJm hfin k)
    (fun k => stronglyMeasurable_gammaWallBlockPiece hJm k)
    (fun k => gammaWallBlockPiece_supp σ J k)
    (summable_gammaWallBlockPiece_norm hJm hfin)

end Transfer

end GaloisForLFunctions.RHTower
