import GaloisForLFunctions.RHTower.VonMangoldtGammaTwoBoundaryGramCollapseLaw
import GaloisForLFunctions.RHTower.VonMangoldtGammaToeplitzHankelApertureLaw

/-!
# Von Mangoldt two-boundary aperture blindness universality

The canonical two-boundary balanced Cauchy Gram is constant in the finite von Mangoldt source
aperture: every aperture maps to the zero Gram.  The raw bivariate moment row nevertheless
separates every nonempty aperture from the empty one through its exact Toeplitz--Hankel
shift-invariance classification.  Thus balancing erases a source datum that the raw reporter
detects sharply.
-/

namespace RHTower

/-- The canonical two-boundary balanced Gram is independent of source aperture. -/
theorem finiteVonMangoldtTwoBoundaryBalancedGram_aperture_constant
    (M₁ M₂ N : ℕ) :
    finiteVonMangoldtAllDepthBalancedCauchyGram
        M₁ N vonMangoldtTwoBoundaryPacket =
      finiteVonMangoldtAllDepthBalancedCauchyGram
        M₂ N vonMangoldtTwoBoundaryPacket := by
  rw [finiteVonMangoldtAllDepthBalancedCauchyGram_twoBoundary_eq_zero,
    finiteVonMangoldtAllDepthBalancedCauchyGram_twoBoundary_eq_zero]

/-- The aperture-to-canonical-two-boundary-balanced-Gram reporter is noninjective at every depth. -/
theorem finiteVonMangoldtTwoBoundaryBalancedGram_aperture_not_injective
    (N : ℕ) :
    ¬Function.Injective
      (fun M : ℕ =>
        finiteVonMangoldtAllDepthBalancedCauchyGram
          M N vonMangoldtTwoBoundaryPacket) := by
  intro hinj
  have h01 : (0 : ℕ) = 1 :=
    hinj (finiteVonMangoldtTwoBoundaryBalancedGram_aperture_constant 0 1 N)
  omega

/-- **Von Mangoldt two-boundary aperture blindness law.** Every nonempty aperture collides with
the empty aperture under the canonical balanced Gram, while the corresponding raw moment rows are
distinct.  Raw Toeplitz--Hankel shift invariance is the separator. -/
theorem finiteVonMangoldt_nonemptyAperture_balancedCollision_rawSeparation
    (M N : ℕ) (hM : M ≠ 0) (x : ℝ) (a : ℕ) :
    finiteVonMangoldtAllDepthBalancedCauchyGram
        M N vonMangoldtTwoBoundaryPacket =
      finiteVonMangoldtAllDepthBalancedCauchyGram
        0 N vonMangoldtTwoBoundaryPacket ∧
      (fun b => finiteVonMangoldtGammaBivariateMoment M x a b) ≠
        (fun b => finiteVonMangoldtGammaBivariateMoment 0 x a b) := by
  refine ⟨finiteVonMangoldtTwoBoundaryBalancedGram_aperture_constant M 0 N, ?_⟩
  intro heq
  have hshift0 : HTGeometry.HankelShiftInvariant
      (fun b => finiteVonMangoldtGammaBivariateMoment 0 x a b) :=
    (finiteVonMangoldtGammaBivariateMoment_hankelShiftInvariant_iff 0 x a).2 rfl
  have hshiftM : HTGeometry.HankelShiftInvariant
      (fun b => finiteVonMangoldtGammaBivariateMoment M x a b) := by
    rw [heq]
    exact hshift0
  exact hM
    ((finiteVonMangoldtGammaBivariateMoment_hankelShiftInvariant_iff M x a).1 hshiftM)

end RHTower
