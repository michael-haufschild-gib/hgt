import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
import GaloisForLFunctions.HTGeometry.ModularDirichletFormIntegrationByParts

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace MaassCongruenceL2
noncomputable section

def component {N : ℕ} (F : ℍ → DeckSpace N) (q : Deck N) : ℍ → ℂ := fun z => F z q

theorem component_c1 {N : ℕ} (F : formPreDomain N) (q : Deck N) :
    GaloisForLFunctions.HTGeometry.IsChartC1 (component (F : ℍ → DeckSpace N) q) := by
  have h := ((EuclideanSpace.proj q).restrictScalars ℝ).contDiff.comp_contDiffOn
    (formPreDomain.c1 F)
  change ContDiffOn ℝ 1 (((EuclideanSpace.proj q).restrictScalars ℝ) ∘
    chartFun (F : ℍ → DeckSpace N)) GaloisForLFunctions.HTGeometry.upperSet
  exact h

theorem component_hypGradX {N : ℕ} (F : formPreDomain N) (q : Deck N) (z : ℍ) :
    GaloisForLFunctions.HTGeometry.hypGradX (component (F : ℍ → DeckSpace N) q) z =
      hypGradX (F : ℍ → DeckSpace N) z q := by
  have hc := component_c1 F q
  have hf := (formPreDomain.c1 F).differentiableOn one_ne_zero |>.differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hp := ((EuclideanSpace.proj q).restrictScalars ℝ).hasFDerivAt.comp (z : ℂ) hf.hasFDerivAt
  have h := congrArg (fun L => L (1 : ℂ)) hp.fderiv
  change (z.im : ℂ) * (fderiv ℝ (((EuclideanSpace.proj q).restrictScalars ℝ) ∘
    chartFun (F : ℍ → DeckSpace N)) (z : ℂ) 1) =
      ((z.im : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (z : ℂ) 1) q
  rw [h]
  rfl
end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace MaassCongruenceL2
noncomputable section

theorem component_hypGradY {N : ℕ} (F : formPreDomain N) (q : Deck N) (z : ℍ) :
    GaloisForLFunctions.HTGeometry.hypGradY (component (F : ℍ → DeckSpace N) q) z =
      hypGradY (F : ℍ → DeckSpace N) z q := by
  have hf := (formPreDomain.c1 F).differentiableOn one_ne_zero |>.differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hp := ((EuclideanSpace.proj q).restrictScalars ℝ).hasFDerivAt.comp (z : ℂ) hf.hasFDerivAt
  have h := congrArg (fun L => L Complex.I) hp.fderiv
  change (z.im : ℂ) * (fderiv ℝ (((EuclideanSpace.proj q).restrictScalars ℝ) ∘
    chartFun (F : ℍ → DeckSpace N)) (z : ℂ) Complex.I) =
      ((z.im : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (z : ℂ) Complex.I) q
  rw [h]
  rfl

/-- Scalar L² carrier for one finite-deck coordinate. -/
abbrev ComponentL2 := Lp ℂ 2 cellMeasure

/-- Continuous L² projection to a single finite-deck coordinate. -/
def componentL2 (N : ℕ) (q : Deck N) : DeckL2 N →L[ℂ] ComponentL2 :=
  (EuclideanSpace.proj q).compLpL 2 cellMeasure

theorem component_testWeight_hypGradX {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hU : tsupport φ ⊆ GaloisForLFunctions.HTGeometry.fdoImage) :
    ∫ z in fd, (z.im : ℂ) * φ z * (hypGradX (F : ℍ → DeckSpace N) z q) ∂volume =
      - ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z 1) * (F : ℍ → DeckSpace N) z q ∂volume := by
  have h := GaloisForLFunctions.HTGeometry.setIntegral_fd_testWeight_hypGradX
    (component_c1 F q) hφ hs hU
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with z
    rw [component_hypGradX F q]
  · congr 1

theorem component_testWeight_hypGradY {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hU : tsupport φ ⊆ GaloisForLFunctions.HTGeometry.fdoImage) :
    ∫ z in fd, (z.im : ℂ) * φ z * (hypGradY (F : ℍ → DeckSpace N) z q) ∂volume =
      - ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z Complex.I) * (F : ℍ → DeckSpace N) z q ∂volume := by
  have h := GaloisForLFunctions.HTGeometry.setIntegral_fd_testWeight_hypGradY
    (component_c1 F q) hφ hs hU
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with z
    rw [component_hypGradY F q]
  · congr 1
end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
