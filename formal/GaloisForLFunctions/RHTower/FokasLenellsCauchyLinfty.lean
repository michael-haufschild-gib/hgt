import GaloisForLFunctions.RHTower.FokasLenellsCauchyModulation

/-!
# An isometric L-infinity family of Cauchy-compressed multipliers

The Cauchy projection used in the paper preserves the exact norm of every
bounded measurable multiplier. Its range is closed in operator norm, and
convergence in that range is exactly essential-supremum convergence.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
namespace RHTower.FokasLenells
noncomputable section

/-- Cauchy-compressed multiplication as a continuous linear family in its L-infinity symbol. -/
def cauchyLinftyMultiplier : Lp ℂ ∞ (volume : Measure ℝ) →L[ℂ] (SoninL2 →L[ℂ] SoninL2) :=
  ((ContinuousLinearMap.compL ℂ SoninL2 SoninL2 SoninL2) negativeCauchy).comp lineLinftyMultiplier

/-- The family acts by the actual signed Cauchy compression. -/
theorem cauchyLinftyMultiplier_apply (g : Lp ℂ ∞ (volume : Measure ℝ)) :
    cauchyLinftyMultiplier g = negativeCauchy.comp (lineLinftyMultiplier g) := rfl

/-- Exact norm preservation for arbitrary measurable bounded data. -/
theorem norm_cauchyLinftyMultiplier (g : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖cauchyLinftyMultiplier g‖ = ‖g‖ :=
  norm_negativeCauchy_comp_lineLinftyMultiplier g

/-- The Cauchy family is a linear isometry of ordinary L-infinity data. -/
def cauchyLinftyMultiplierIsometry : Lp ℂ ∞ (volume : Measure ℝ) →ₗᵢ[ℂ] (SoninL2 →L[ℂ] SoninL2) :=
  { cauchyLinftyMultiplier.toLinearMap with norm_map' := norm_cauchyLinftyMultiplier }

/-- Compression preserves the full distance between any two symbols. -/
theorem dist_cauchyLinftyMultiplier (g h : Lp ℂ ∞ (volume : Measure ℝ)) :
    dist (cauchyLinftyMultiplier g) (cauchyLinftyMultiplier h) = dist g h :=
  cauchyLinftyMultiplierIsometry.isometry.dist_eq g h

/-- No bounded symbol is lost by passing to its Cauchy-compressed operator. -/
theorem cauchyLinftyMultiplier_injective : Function.Injective cauchyLinftyMultiplier :=
  cauchyLinftyMultiplierIsometry.injective

/-- Equality after Cauchy compression detects exactly almost-everywhere equality. -/
theorem cauchyLinftyMultiplier_eq_iff_ae (g h : Lp ℂ ∞ (volume : Measure ℝ)) :
    cauchyLinftyMultiplier g = cauchyLinftyMultiplier h ↔ (g : ℝ → ℂ) =ᵐ[volume] h := by
  constructor
  · intro he
    rw [cauchyLinftyMultiplier_injective he]
  · intro he
    exact congrArg cauchyLinftyMultiplier (Lp.ext he)

/-- Every operator-norm limit of this family is again a Cauchy-compressed bounded multiplier. -/
theorem isClosed_range_cauchyLinftyMultiplier : IsClosed (range cauchyLinftyMultiplier) :=
  cauchyLinftyMultiplierIsometry.isometry.isClosedEmbedding.isClosed_range

/-- Convergence after compression is equivalent to essential-supremum convergence of the symbols. -/
theorem tendsto_cauchyLinftyMultiplier_iff {ι : Type*} (l : Filter ι)
    (g : ι → Lp ℂ ∞ (volume : Measure ℝ)) (h : Lp ℂ ∞ (volume : Measure ℝ)) :
    Tendsto (fun i => cauchyLinftyMultiplier (g i)) l (𝓝 (cauchyLinftyMultiplier h)) ↔
      Tendsto g l (𝓝 h) :=
  cauchyLinftyMultiplierIsometry.isometry.tendsto_nhds_iff.symm

/-- The norm condition used in the small-norm inverse argument is sharp for scalar symbols. -/
theorem norm_cauchyLinftyMultiplier_lt_one_iff (g : Lp ℂ ∞ (volume : Measure ℝ)) :
    ‖cauchyLinftyMultiplier g‖ < 1 ↔ ‖g‖ < 1 := by
  rw [norm_cauchyLinftyMultiplier]

end
end RHTower.FokasLenells
