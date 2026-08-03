import GaloisForLFunctions.HTGeometry.BarnesMultiLadderRatio
import GaloisForLFunctions.HTGeometry.BarnesSourceRepresentative
import GaloisForLFunctions.HTGeometry.RationalCorrectionDA

/-!
# One ladder step is differentially algebraic

The multi-period ladder defect is a ratio of polynomials off the poles, and all three of its terms —
the translated source, the source, and the deleted-frame source — have punctured representatives.
Hence the defect is the corresponding element of the coordinate field, and therefore differentially
algebraic:

```text
σ_{ω_j} Ψ_ω - Ψ_ω + Ψ_{ω^{(j)}}   is DA over ℂ(z).
```

This is the ladder relation `x_j Ψ_N = -Ψ_{N-1}` modulo the differentially algebraic sector, for the
Barnes source itself.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **One ladder step, modulo the differentially algebraic sector.**  The translation defect of the
Barnes source differs from the deleted-frame source by a rational function. -/
theorem differentialAlgebraicOver_barnesSource_ladder_step (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (j : ι) [Nonempty {i : ι // i ≠ j}] :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv (ω j) (barnesSourceLogDerivMero ω hω)
          - barnesSourceLogDerivMero ω hω
        + barnesSourceLogDerivMero (deletedFrame ω j) (deletedFrame_im_pos hω j)) := by
  have hne : (Polynomial.X + Polynomial.C (ω j) : Polynomial ℂ) ≠ 0 :=
    Polynomial.X_add_C_ne_zero (ω j)
  refine differentialAlgebraicOver_of_hasPuncturedMeromorphicRep_ratio
    (p := barnesLadderNumerator ω j) (q := Polynomial.X + Polynomial.C (ω j)) hne ?_
  refine (((hasPuncturedMeromorphicRep_addTranslation_barnesSourceLogDerivMero ω hω
      (ω j)).sub (hasPuncturedMeromorphicRep_barnesSourceLogDerivMero ω hω)).add
    (hasPuncturedMeromorphicRep_barnesSourceLogDerivMero (deletedFrame ω j)
      (deletedFrame_im_pos hω j))).congr_fun ?_
  intro z₀
  have hshift := (tendsto_nhdsNE_add (ω j) z₀).eventually
    (eventually_nhdsNE_conePeriod_add_ne_zero ω hω (z₀ + ω j))
  filter_upwards [eventually_nhdsNE_conePeriod_add_ne_zero ω hω z₀, hshift,
    eventually_nhdsNE_conePeriod_add_ne_zero (deletedFrame ω j) (deletedFrame_im_pos hω j) z₀]
    with w hw hw' hwD
  show (logDeriv (barnesConeProduct ω) (w + ω j) - logDeriv (barnesConeProduct ω) w)
      + logDeriv (barnesConeProduct (deletedFrame ω j)) w
    = (barnesLadderNumerator ω j).eval w / (Polynomial.X + Polynomial.C (ω j)).eval w
  exact barnesSource_ladder_ratio ω hω j hw hw' hwD

end

end GaloisForLFunctions.HTGeometry
