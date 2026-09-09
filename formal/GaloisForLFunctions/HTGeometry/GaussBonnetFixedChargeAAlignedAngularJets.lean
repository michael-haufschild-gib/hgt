import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAAlignedAngularSmooth
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Joint regularity of all angular derivatives

A partial derivative is the full derivative evaluated on the fixed
angle direction (0,1). This keeps smoothness in both the coefficient
state and the angle. Induction gives joint smoothness of every angular
jet, and every actual physical state lies in the proved smooth domain.
-/
noncomputable section
open Real Filter Set
open scoped Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

private theorem aligned_smooth_slice_deriv {f : EGBAlignedForceState × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (egbFixedChargeAAlignedSmoothDomain ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : EGBAlignedForceState × ℝ => deriv (fun x => f (p.1, x)) p.2)
      (egbFixedChargeAAlignedSmoothDomain ×ˢ univ) := by
  have ho : IsOpen (egbFixedChargeAAlignedSmoothDomain ×ˢ (univ : Set ℝ)) :=
    egbFixedChargeAAlignedSmoothDomain_isOpen.prod isOpen_univ
  have hdf := hf.fderiv_of_isOpen ho (m := ∞) (by simp)
  have heval := hdf.clm_apply (contDiffOn_const :
    ContDiffOn ℝ ∞ (fun _ : EGBAlignedForceState × ℝ => ((0 : EGBAlignedForceState), (1 : ℝ)))
      (egbFixedChargeAAlignedSmoothDomain ×ˢ univ))
  apply heval.congr
  intro p hp
  have hd := (hf.contDiffAt (ho.mem_nhds hp)).differentiableAt (by simp)
  have hs : HasDerivAt (fun x : ℝ => (p.1, x)) ((0 : EGBAlignedForceState), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hd.hasFDerivAt.comp_hasDerivAt p.2 hs).deriv

theorem egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_contDiffOn (w φ : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun p : EGBAlignedForceState × ℝ =>
      iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ p.1) p.2)
      (egbFixedChargeAAlignedSmoothDomain ×ˢ univ) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using egbFixedChargeAAlignedAngularCorrection_contDiffOn w φ
  | succ n ih =>
      simpa only [iteratedDeriv_succ] using aligned_smooth_slice_deriv ih

theorem egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_continuousOn (w φ : ℝ) (n : ℕ) :
    ContinuousOn (fun p : EGBAlignedForceState × ℝ =>
      iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ p.1) p.2)
      (egbFixedChargeAAlignedSmoothDomain ×ˢ univ) :=
  (egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_contDiffOn w φ n).continuousOn

theorem egbFixedChargeAAlignedAngularCorrection_actual_contDiff (w φ τ l : ℝ) :
    ContDiff ℝ ∞ (egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l)) := by
  rw [← contDiffOn_univ]
  apply (egbFixedChargeAAlignedAngularCorrection_contDiffOn w φ).comp
    (f := fun x : ℝ => (egbFixedChargeAAlignedForceState w φ τ l, x))
  · fun_prop
  · intro x hx
    exact ⟨egbFixedChargeAAlignedForceState_mem_smoothDomain w φ τ l, mem_univ _⟩

theorem egbFixedChargeAAlignedAngularCorrection_actual_iteratedDeriv_contDiff (w φ τ l : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l))) := by
  rw [← contDiffOn_univ]
  apply (egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_contDiffOn w φ n).comp
    (f := fun x : ℝ => (egbFixedChargeAAlignedForceState w φ τ l, x))
  · fun_prop
  · intro x hx
    exact ⟨egbFixedChargeAAlignedForceState_mem_smoothDomain w φ τ l, mem_univ _⟩

theorem egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_critical (w φ : ℝ) (n : ℕ) (ψ : ℝ) :
    iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceCriticalState w φ)) ψ = 0 := by
  have hf : egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceCriticalState w φ) = fun _ : ℝ => 0 :=
    funext (egbFixedChargeAAlignedAngularCorrection_critical w φ)
  rw [hf]
  exact iteratedDeriv_fun_const_zero

end GaloisForLFunctions.HTGeometry
