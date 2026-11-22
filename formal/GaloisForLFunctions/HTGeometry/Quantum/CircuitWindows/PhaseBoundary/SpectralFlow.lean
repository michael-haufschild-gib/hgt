import GaloisForLFunctions.HTGeometry.ProjectiveSpectralCircuitHardIntervalLaw
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Analytic matrix entries on every translated relative-phase trajectory -/
open Matrix Filter Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

private theorem translated_character {d : ℕ} (E : Fin (d+1) → ℝ) (x : Fin d → UnitAddCircle)
    (k : Fin (d+1)) (t : ℝ) :
    fourier 1 (RHTower.zeroAnchoredPhase d (RHTower.projectivePhysicalPhaseFlow E t+x) k) =
      Complex.exp (((t*Fin.cases 0 (RHTower.zeroProjectiveFrequency E) k:ℝ):ℂ)*Complex.I) *
        fourier 1 (RHTower.zeroAnchoredPhase d x k) := by
  rw [←RHTower.fourier_projectiveChoiPhase_eq_exp]
  have h (u v : Fin d → UnitAddCircle) : RHTower.zeroAnchoredPhase d (u+v) k =
      RHTower.zeroAnchoredPhase d u k + RHTower.zeroAnchoredPhase d v k := by
    refine Fin.cases ?_ (fun j => ?_) k
    · change 0=(0:UnitAddCircle)+0
      rw [add_zero]
    · rfl
  simp only [h,fourier_one,AddCircle.toCircle_add,Circle.coe_mul]

private theorem analytic_character {d : ℕ} (E : Fin (d+1) → ℝ) (x : Fin d → UnitAddCircle)
    (k : Fin (d+1)) (u : ℝ) :
    AnalyticAt ℝ (fun t => fourier 1 (RHTower.zeroAnchoredPhase d (RHTower.projectivePhysicalPhaseFlow E t+x) k)) u := by
  simp_rw [translated_character]
  apply AnalyticAt.mul _ analyticAt_const
  apply (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
  apply AnalyticAt.mul _ analyticAt_const
  exact (Complex.ofRealCLM.analyticAt _).comp (analyticAt_id.mul analyticAt_const)

/-- In a fixed eigenbasis every shifted matrix entry is a finite sum of
complex exponentials with real frequencies. -/
theorem spectral_entries_analytic {N d : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin N → Bool) ℂ) (E : Fin (d+1) → ℝ) (x : Fin d → UnitAddCircle)
    (i j : Fin N → Bool) :
    let val (t : ℝ) := projectiveSpectralMatrix e V (RHTower.projectivePhysicalPhaseFlow E t+x) i j
    AnalyticOnNhd ℝ (fun t => (val t).re) univ ∧ AnalyticOnNhd ℝ (fun t => (val t).im) univ := by
  intro val
  have h (t : ℝ) : AnalyticAt ℝ val t := by
    dsimp only [val,projectiveSpectralMatrix]
    have he (u : ℝ) : ((V.val * diagonal (fun k => fourier 1 (RHTower.zeroAnchoredPhase d
        (RHTower.projectivePhysicalPhaseFlow E u+x) (e k)))) * (V⁻¹).val) i j =
        ∑ k, (V.val i k * fourier 1 (RHTower.zeroAnchoredPhase d
          (RHTower.projectivePhysicalPhaseFlow E u+x) (e k))) * (V⁻¹).val k j := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal]
    simp_rw [he]
    apply Finset.analyticAt_fun_sum
    intro k _
    exact (analyticAt_const.mul (analytic_character E x (e k) t)).mul analyticAt_const
  exact ⟨fun t _ => (Complex.reCLM.analyticAt _).comp (h t),fun t _ => (Complex.imCLM.analyticAt _).comp (h t)⟩

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
