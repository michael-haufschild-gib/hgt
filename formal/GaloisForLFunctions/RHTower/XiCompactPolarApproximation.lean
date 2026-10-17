import GaloisForLFunctions.RHTower.XiCompactSpectralSource
import GaloisForLFunctions.HTGeometry.ClosedCoreFiniteConstraints

/-! # Exact polar cancellation during absolute spectral approximation -/

open Complex MeasureTheory Filter Topology Set Zeta23
noncomputable section
namespace RHTower
open WeilSpectral

def compactXiPolarObservation : compactXiTests →ₗ[ℂ] (ℂ × ℂ) :=
  (compactXiFourier (I/2)).prod (compactXiFourier (-I/2))

def compactXiPolarTests : Submodule ℂ compactXiTests := compactXiPolarObservation.ker

def compactXiPolarEvaluation : compactXiPolarTests →ₗ[ℂ] lp (fun _ : XiZeroCopy => ℂ) 2 :=
  compactXiEvaluation.comp compactXiPolarTests.subtype

theorem compactXiPolarEvaluation_apply (f : compactXiPolarTests) (q : XiZeroCopy) :
    compactXiPolarEvaluation f q = paperFT (f : compactXiTests) (xiSpectralPoint q) :=
  compactXiEvaluation_apply _ _

theorem complexXiAugment_mem_closure {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hr : ExpDecayTest (fun x => (f x).re)) (hi : ExpDecayTest (fun x => (f x).im)) :
    (complexXiEvaluation f hr hi, (paperFT f (I/2), paperFT f (-I/2))) ∈
      compactXiAugment.range.topologicalClosure := by
  apply compactXiAugment.range.isClosed_topologicalClosure.mem_of_tendsto
    (complexXiTruncation_augmented_tendsto hf hr hi)
  exact Eventually.of_forall fun L => compactXiAugment.range.le_topologicalClosure
    ⟨complexXiTruncation f hf L, rfl⟩

theorem exists_compactXiPolar_spectral_approximation {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hr : ExpDecayTest (fun x => (f x).re))
    (hi : ExpDecayTest (fun x => (f x).im))
    (hp : paperFT f (I/2) = 0) (hm : paperFT f (-I/2) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : compactXiPolarTests, ‖compactXiPolarEvaluation g - complexXiEvaluation f hr hi‖ < ε := by
  let x := (complexXiEvaluation f hr hi, (paperFT f (I/2), paperFT f (-I/2)))
  obtain ⟨y, ⟨g, rfl⟩, he, hn⟩ :=
    GaloisForLFunctions.HTGeometry.exists_closedCore_approximation_same_finiteObservation
      compactXiAugment.range
      (ContinuousLinearMap.snd ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) (ℂ × ℂ))
      (complexXiAugment_mem_closure hf hr hi) hε
  have hg : g ∈ compactXiPolarTests := by
    change compactXiPolarObservation g = 0
    change compactXiPolarObservation g = (paperFT f (I/2), paperFT f (-I/2)) at he
    rw [he]
    exact Prod.ext hp hm
  refine ⟨⟨g, hg⟩, ?_⟩
  exact (norm_fst_le (compactXiAugment g-x)).trans_lt hn

theorem complexXiEvaluation_mem_compactPolar_closure {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hr : ExpDecayTest (fun x => (f x).re))
    (hi : ExpDecayTest (fun x => (f x).im))
    (hp : paperFT f (I/2) = 0) (hm : paperFT f (-I/2) = 0) :
    complexXiEvaluation f hr hi ∈ compactXiPolarEvaluation.range.topologicalClosure := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_compactXiPolar_spectral_approximation hf hr hi hp hm hε
  exact ⟨compactXiPolarEvaluation g, ⟨g, rfl⟩, by simpa [dist_eq_norm, norm_sub_rev] using hg⟩

end RHTower
