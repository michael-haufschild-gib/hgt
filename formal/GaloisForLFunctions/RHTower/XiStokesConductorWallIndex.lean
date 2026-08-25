import GaloisForLFunctions.RHTower.HedenmalmStokesOrientedFirstTraceQuantizedJump

/-!
# Xi Stokes--conductor wall index

The all-prime oriented Stokes current has one-sided wall limits `4` and `-4`.
Weighting it by exact Xi multiplicity couples wild source asymptotics to the
tame integral conductor.  The resulting jump is `8m`, so its normalized jump
recovers multiplicity exactly.

Consequently no continuous neutral-wall completion can preserve a nonzero
conductor normalization.  A viable completion must add a polar countercurrent
or lose the tame multiplicity coordinate.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Wild first-trace current weighted by the tame Xi conductor multiplicity. -/
def xiStokesConductorWallCurrent (rho : XiDivisorSupport) (t : ℝ) : ℝ :=
  (xiSupportMultiplicity rho : ℝ) *
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t

@[simp]
theorem xiStokesConductorWallCurrent_zero (rho : XiDivisorSupport) :
    xiStokesConductorWallCurrent rho 0 = 0 := by
  simp [xiStokesConductorWallCurrent]

/-- Right-wall wild charge is four times exact tame multiplicity. -/
theorem tendsto_xiStokesConductorWallCurrent_nhdsGT_zero
    (rho : XiDivisorSupport) :
    Tendsto (xiStokesConductorWallCurrent rho)
      (𝓝[>] (0 : ℝ)) (𝓝 ((xiSupportMultiplicity rho : ℝ) * 4)) := by
  change Tendsto
    (fun t => (xiSupportMultiplicity rho : ℝ) *
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t)
    (𝓝[>] (0 : ℝ)) (𝓝 ((xiSupportMultiplicity rho : ℝ) * 4))
  exact
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.const_mul
      (xiSupportMultiplicity rho : ℝ)

/-- Left-wall wild charge is minus four times exact tame multiplicity. -/
theorem tendsto_xiStokesConductorWallCurrent_nhdsLT_zero
    (rho : XiDivisorSupport) :
    Tendsto (xiStokesConductorWallCurrent rho)
      (𝓝[<] (0 : ℝ)) (𝓝 ((xiSupportMultiplicity rho : ℝ) * (-4))) := by
  change Tendsto
    (fun t => (xiSupportMultiplicity rho : ℝ) *
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t)
    (𝓝[<] (0 : ℝ)) (𝓝 ((xiSupportMultiplicity rho : ℝ) * (-4)))
  exact
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsLT_zero.const_mul
      (xiSupportMultiplicity rho : ℝ)

/-- The normalized wild wall jump recovers the tame conductor multiplicity exactly. -/
theorem xiStokesConductorWallJump_div_eight_eq_multiplicity
    (rho : XiDivisorSupport) :
    (((xiSupportMultiplicity rho : ℝ) * 4 -
        (xiSupportMultiplicity rho : ℝ) * (-4)) / 8) =
      (xiSupportMultiplicity rho : ℝ) := by
  ring

/--
Any gauge whose right-wall limit is finite and whose gauged Stokes current tends
to zero must itself vanish at the wall.  Thus a nonzero conductor normalization
cannot regularize the wild current by multiplication alone.
-/
theorem stokesConductorGauge_limit_eq_zero_of_product_tendsto_zero
    (g : ℝ → ℝ) {L : ℝ}
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hzero : Tendsto
      (fun t => g t *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    L = 0 := by
  have hproduct : Tendsto
      (fun t => g t *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent t)
      (𝓝[>] (0 : ℝ)) (𝓝 (L * 4)) :=
    hg.mul
      tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  have heq : (0 : ℝ) = L * 4 := tendsto_nhds_unique hzero hproduct
  linarith

/-- Multiplicity-preserving wild current has an unavoidable wall discontinuity. -/
theorem not_continuousAt_xiStokesConductorWallCurrent_zero
    (rho : XiDivisorSupport) :
    ¬ ContinuousAt (xiStokesConductorWallCurrent rho) 0 := by
  intro hcontinuous
  have hzero : Tendsto (xiStokesConductorWallCurrent rho)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hquantized := tendsto_xiStokesConductorWallCurrent_nhdsGT_zero rho
  have heq : (0 : ℝ) = (xiSupportMultiplicity rho : ℝ) * 4 :=
    tendsto_nhds_unique hzero hquantized
  have hm : (0 : ℝ) < (xiSupportMultiplicity rho : ℝ) := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  nlinarith

/--
No other continuous wall value can repair the defect while agreeing with the
multiplicity-preserving current on a punctured right neighborhood.
-/
theorem no_continuousAt_extension_xiStokesConductorWallCurrent
    (rho : XiDivisorSupport) (F : ℝ → ℝ)
    (hF0 : F 0 = 0)
    (hagrees : F =ᶠ[𝓝[>] (0 : ℝ)] xiStokesConductorWallCurrent rho) :
    ¬ ContinuousAt F 0 := by
  intro hcontinuous
  have hzero : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [hF0] using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hquantized : Tendsto F (𝓝[>] (0 : ℝ))
      (𝓝 ((xiSupportMultiplicity rho : ℝ) * 4)) :=
    (tendsto_xiStokesConductorWallCurrent_nhdsGT_zero rho).congr' hagrees.symm
  have heq : (0 : ℝ) = (xiSupportMultiplicity rho : ℝ) * 4 :=
    tendsto_nhds_unique hzero hquantized
  have hm : (0 : ℝ) < (xiSupportMultiplicity rho : ℝ) := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  nlinarith

end

end RHTower
