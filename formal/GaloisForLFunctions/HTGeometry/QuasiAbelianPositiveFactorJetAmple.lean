import GaloisForLFunctions.HTGeometry.QuasiAbelianIntegerLatticePoincareInterpolation
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareGaussianMajorant

/-!
# Positive integer-lattice factors are all-order jet ample

An `AbePositiveFactorPresentation` records an actual automorphic cocycle together with Abe's
conclusion-free analytic positivity certificate: every explicit Gaussian-flat packet seed has a
compact-uniform polynomial-Gaussian majorant.  The majorant proves normal convergence; explicit
separators and the Poincare summation theorem then prove arbitrary finite mixed-jet interpolation.

No field of this structure assumes section existence, jet surjectivity, or a derivative limit.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Quantitative positive-factor presentation in standard integer-lattice coordinates.  This is
the exact analytic estimate produced by the positive Hermitian form in Abe's base case. -/
structure AbePositiveFactorPresentation (d : ℕ) where
  factor : AutomorphicFactor d (standardIntegerLattice d)
  gaussianMajorant :
    ∀ (I : Type u) [Fintype I] [DecidableEq I]
      (w : I → Fin d → ℂ)
      (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
      (m : ℕ) (hm : 0 < m),
      ∃ σ : Fin d → ℝ, (∀ c, 0 < σ c) ∧
        ∀ (target : I) (P : MvPolynomial (Fin d) ℂ),
          let S := flatIntegerLatticePacketSeparatorData w hdistinct target m hm
          let D := gaussianFlatSeedData σ (w target) hm
          let seed := multivariateEntireMul S.bump
            (multivariateEntireMul D.damping (mvPolynomialMultivariateEntire P))
          ∃ (A : Fin d → ℕ) (decay : Fin d → ℝ),
            (∀ c, 0 < decay c) ∧
            ∀ K : Set (Fin d → ℂ), IsCompact K →
              ∃ C : ℝ, 0 ≤ C ∧ ∀ k x, x ∈ K →
                ‖poincareTerm factor seed (standardIntegerLatticeEquiv d k) x‖ ≤
                  C * polynomialGaussianLatticeWeight (Fin d) A decay k

/-- Abe's polynomial-Gaussian positivity estimate proves local normal convergence for every
literal Gaussian-flat interpolation seed. -/
theorem AbePositiveFactorPresentation.gaussianFlatSeedsNormallySummable
    {d : ℕ} (P : AbePositiveFactorPresentation.{u} d) :
    AutomorphicFactor.GaussianFlatIntegerLatticeSeedsNormallySummable.{u} P.factor := by
  intro I _ _ w hdistinct m hm
  obtain ⟨σ, hσ, hmajor⟩ := P.gaussianMajorant I w hdistinct m hm
  refine ⟨σ, hσ, ?_⟩
  intro target Q
  let S := flatIntegerLatticePacketSeparatorData w hdistinct target m hm
  let D := gaussianFlatSeedData σ (w target) hm
  let seed := multivariateEntireMul S.bump
    (multivariateEntireMul D.damping (mvPolynomialMultivariateEntire Q))
  obtain ⟨A, decay, hdecay, hbound⟩ := hmajor target Q
  have hinteger : SummableLocallyUniformlyOn
      (fun k : Fin d → ℤ ↦
        poincareTerm P.factor seed (standardIntegerLatticeEquiv d k)) Set.univ := by
    apply summableLocallyUniformlyOn_of_polynomialGaussianLattice_bound
      (fun k : Fin d → ℤ ↦
        poincareTerm P.factor seed (standardIntegerLatticeEquiv d k))
      Set.univ isOpen_univ A decay hdecay
    intro K hKuniv hK
    exact hbound K hK
  have hlattice :=
    GaloisForLFunctions.HTGeometry.SummableLocallyUniformlyOn.comp_injective_open
      isOpen_univ hinteger (standardIntegerLatticeEquiv d).symm.injective
  simpa only [Equiv.apply_symm_apply, S, D, seed] using hlattice

/-- **Fixed positive factor, every finite jet order.**  A standard integer-lattice positive
presentation interpolates every finite packet of arbitrary mixed jets with one fixed factor. -/
theorem AbePositiveFactorPresentation.jetAmpleEveryFiniteOrder
    {d : ℕ} (P : AbePositiveFactorPresentation.{u} d) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} P.factor :=
  P.factor.jetAmpleEveryFiniteOrder_standardIntegerLattice
    P.gaussianFlatSeedsNormallySummable

end

end GaloisForLFunctions.HTGeometry
