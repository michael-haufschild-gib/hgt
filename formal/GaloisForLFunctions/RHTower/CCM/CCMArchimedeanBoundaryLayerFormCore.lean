import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanFormDomainEquivalence
import GaloisForLFunctions.RHTower.Suzuki.SuzukiBoundaryLayerFormCore

/-!
# Boundary-layer form core for the exact CCM archimedean weight

The boundary-layer approximation from Connes--Consani's Laurent-core argument was previously
available only in Suzuki's asymptotic logarithmic form norm.  The global form-domain equivalence
transports it to the literal digamma weight `2 * theta'`.  Thus every zero-extended aperture mode
is an exact CCM form vector and is approximated by the source's smooth endpoint cutoffs in the
complete exact form norm.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform ContDiff

noncomputable section

namespace RHTower

def ccmArchimedeanApertureModeFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) : CCMArchimedeanFormDomain a :=
  ccmLogFormToArchimedean a (suzukiApertureModeFormVector a κ)

def ccmArchimedeanBoundaryApproximantFormVector
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) : CCMArchimedeanFormDomain a :=
  ccmLogFormToArchimedean a (suzukiBoundaryApproximantFormVector a κ m)

theorem ccmArchimedeanFormEmbedding_logFormToArchimedean
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ccmArchimedeanFormEmbedding a (ccmLogFormToArchimedean a f) =
      suzukiHlogFormEmbedding a f := by
  change ccmArchimedeanFourierToTime (ccmLogToArchimedean f.1) =
    suzukiHlogFourierToTime f.1
  exact ccmArchimedeanFourierToTime_logToArchimedean f.1

theorem ccmArchimedeanFormEmbedding_apertureModeFormVector_coeFn
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    (ccmArchimedeanFormEmbedding a
      (ccmArchimedeanApertureModeFormVector a κ) : ℝ → ℂ)
      =ᵐ[volume] suzukiApertureModeCutoff a.1 κ := by
  rw [ccmArchimedeanApertureModeFormVector,
    ccmArchimedeanFormEmbedding_logFormToArchimedean]
  exact suzukiHlogFormEmbedding_apertureModeFormVector_coeFn a κ

theorem ccmArchimedeanFormEmbedding_boundaryApproximantFormVector_coeFn
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    (ccmArchimedeanFormEmbedding a
      (ccmArchimedeanBoundaryApproximantFormVector a κ m) : ℝ → ℂ)
      =ᵐ[volume]
        suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ := by
  rw [ccmArchimedeanBoundaryApproximantFormVector,
    ccmArchimedeanFormEmbedding_logFormToArchimedean]
  exact suzukiHlogFormEmbedding_boundaryApproximantFormVector_coeFn a κ m

/-- Exact-digamma version of Connes--Consani equation (3.2). -/
theorem ccmEquationThreeTwo_exactArchimedeanFormCore
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    (∀ m : ℕ,
      ContDiff ℝ (⊤ : ℕ∞)
        (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ) ∧
      HasCompactSupport
        (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ) ∧
      tsupport (suzukiBoundaryApproximant a.1 (suzukiBoundaryWidth a.1 m) κ) ⊆
        Icc (-a.1) a.1) ∧
    (ccmArchimedeanFormEmbedding a
      (ccmArchimedeanApertureModeFormVector a κ) : ℝ → ℂ)
      =ᵐ[volume] suzukiApertureModeCutoff a.1 κ ∧
    Tendsto (fun m : ℕ => ‖ccmArchimedeanApertureModeFormVector a κ -
      ccmArchimedeanBoundaryApproximantFormVector a κ m‖) atTop (𝓝 0) := by
  have hsuzuki := suzukiEquationThreeTwo_hlogFormCore a κ
  refine ⟨hsuzuki.1, ccmArchimedeanFormEmbedding_apertureModeFormVector_coeFn a κ, ?_⟩
  have hbound : ∀ m : ℕ,
      ‖ccmArchimedeanApertureModeFormVector a κ -
          ccmArchimedeanBoundaryApproximantFormVector a κ m‖ ≤
        ‖ccmLogFormToArchimedean a‖ *
          ‖suzukiApertureModeFormVector a κ -
            suzukiBoundaryApproximantFormVector a κ m‖ := by
    intro m
    rw [ccmArchimedeanApertureModeFormVector,
      ccmArchimedeanBoundaryApproximantFormVector, ← map_sub]
    exact (ccmLogFormToArchimedean a).le_opNorm _
  apply squeeze_zero (fun m => norm_nonneg _) hbound
  simpa only [mul_zero] using
    (hsuzuki.2.2.const_mul ‖ccmLogFormToArchimedean a‖)

end RHTower
