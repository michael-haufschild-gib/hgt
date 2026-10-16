import GaloisForLFunctions.RHTower.DeningerMeyerMellinStripControl
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Nonlinear reconstruction in the original Meyer source

Every entire scalar operation, after subtracting its value at zero, preserves
the actual all-weight source. The proof uses strip reconstruction, not an
assumption that a prescribed infinite spectral packet is admissible.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem deningerEntire_dslope {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (c : ℂ) :
    Differentiable ℂ (dslope φ c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (s := univ) (by simp)).mpr hφ.differentiableOn

namespace DeningerEntireMellinRegular

variable {F G : ℂ → ℂ}

theorem strip_bound (hF : DeningerEntireMellinRegular F) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hF (a-1) (b+1)).decay a b (by linarith) (by linarith) 0
  refine ⟨max 0 C, le_max_left _ _, fun s ha hb => ?_⟩
  have hs : ‖F s‖ ≤ C := by simpa using hC s ha hb
  exact hs.trans (le_max_right _ _)

/-- Strip-bounded entire multipliers preserve the original reconstruction class. -/
theorem mul_of_strip_bounded (hF : DeningerEntireMellinRegular F)
    (hG : Differentiable ℂ G)
    (hB : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖G s‖ ≤ C) :
    DeningerEntireMellinRegular (fun s => F s * G s) := by
  intro α β
  refine ⟨fun s _ _ => (hF.differentiable s).mul (hG s), fun a b ha hb K => ?_⟩
  obtain ⟨C, hC⟩ := (hF α β).decay a b ha hb K
  obtain ⟨B, hB₀, hB⟩ := hB a b
  refine ⟨C*B, fun s hs ht => ?_⟩
  calc ‖F s * G s‖ = ‖F s‖ * ‖G s‖ := norm_mul _ _
    _ ≤ ‖F s‖ * B := mul_le_mul_of_nonneg_left (hB s hs ht) (norm_nonneg _)
    _ ≤ (C / (1+s.im^2)^K) * B := mul_le_mul_of_nonneg_right (hC s hs ht) hB₀
    _ = C*B / (1+s.im^2)^K := by ring

theorem mul (hF : DeningerEntireMellinRegular F)
    (hG : DeningerEntireMellinRegular G) :
    DeningerEntireMellinRegular (fun s => F s * G s) :=
  hF.mul_of_strip_bounded hG.differentiable hG.strip_bound

/-- Entire nonlinear operations preserve strip regularity after centering at zero. -/
theorem entire_comp_sub (hF : DeningerEntireMellinRegular F)
    {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) :
    DeningerEntireMellinRegular (fun s => φ (F s) - φ 0) := by
  have hd := deningerEntire_dslope hφ 0
  have hreg := hF.mul_of_strip_bounded (hd.comp hF.differentiable) (by
    intro a b
    obtain ⟨C, hC₀, hC⟩ := hF.strip_bound a b
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) C).exists_bound_of_continuousOn
      hd.continuous.continuousOn
    refine ⟨max 0 B, le_max_left _ _, fun s hs ht => ?_⟩
    apply (hB (F s) ?_).trans (le_max_right _ _)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hC s hs ht)
  convert hreg using 1
  ext s
  simpa only [sub_zero, smul_eq_mul, Function.comp_apply] using
    (sub_smul_dslope φ 0 (F s)).symm

end DeningerEntireMellinRegular

/-- Literal source realizing an entire nonlinear operation on its Mellin transform. -/
def deningerMeyerEntireApply (φ : ℂ → ℂ) (hφ : Differentiable ℂ φ)
    (g : DeningerMeyerStrongLogTarget) : DeningerMeyerStrongLogTarget :=
  deningerMeyerInverseMellinSource
    (fun s => φ (deningerMeyerStrongLogMellin g s) - φ 0)
    ((deningerMeyerStrongLogMellin_entireRegular g).entire_comp_sub hφ)

@[simp] theorem deningerMeyerEntireApply_mellin (φ : ℂ → ℂ)
    (hφ : Differentiable ℂ φ) (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerEntireApply φ hφ g) s =
      φ (deningerMeyerStrongLogMellin g s) - φ 0 :=
  deningerMeyerInverseMellinSource_mellin _ _

/-- The full exponential correction is an original source, without a smallness condition. -/
def deningerMeyerSourceExp (g : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerEntireApply Complex.exp Complex.differentiable_exp g

@[simp] theorem deningerMeyerSourceExp_mellin
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerSourceExp g) s =
      Complex.exp (deningerMeyerStrongLogMellin g s) - 1 := by
  simp [deningerMeyerSourceExp]

end
end RHTower
