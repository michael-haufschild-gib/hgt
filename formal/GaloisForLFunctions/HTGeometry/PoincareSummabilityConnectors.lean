import GaloisForLFunctions.HTGeometry.QuasiAbelianPositiveFactorJetAmple

/-!
# Exposed normal-summability connectors for Poincare series

Positive-factor construction already proves normal convergence through bundled
`GaussianFlatIntegerLatticeSeedsNormallySummable` interface. This module exposes its strongest
direct mathlib-shaped consequence: one Gaussian scale works simultaneously for every target and
every polynomial multiplier in finite interpolation packet.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- **Uniform Gaussian Poincare summability law.** An Abe-positive presentation supplies one
positive Gaussian scale at which every explicit flat-separator seed in packet is locally normally
summable, uniformly over chosen target and polynomial multiplier. -/
theorem AbePositiveFactorPresentation.exists_gaussianScale_summableLocallyUniformlyOn
    {d : ℕ} (P : AbePositiveFactorPresentation.{u} d)
    (I : Type u) [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (m : ℕ) (hm : 0 < m) :
    ∃ σ : Fin d → ℝ, (∀ c, 0 < σ c) ∧
      ∀ (target : I) (Q : MvPolynomial (Fin d) ℂ),
        let S := flatIntegerLatticePacketSeparatorData w hdistinct target m hm
        let D := gaussianFlatSeedData σ (w target) hm
        SummableLocallyUniformlyOn
          (fun γ ↦ poincareTerm P.factor
            (multivariateEntireMul S.bump
              (multivariateEntireMul D.damping
                (mvPolynomialMultivariateEntire Q))) γ)
          Set.univ := by
  exact P.gaussianFlatSeedsNormallySummable I w hdistinct m hm

end

end GaloisForLFunctions.HTGeometry
