import GaloisForLFunctions.HTGeometry.GomesDilatonCommutatorRecovery

/-!
# Reconstruction from actual Schwartz commutator observations

The invisible-kernel experiment of arXiv:2607.24901v1 section 4 now uses the literal
operators already present in the corpus. Their entire commutator is determined by its
action on the one fixed, everywhere-nonzero Gaussian probe. The exact ambiguity remains
affine; adding the two origin jets gives faithful reconstruction of the profile.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The actual difference of the two factor orders, as a continuous Schwartz operator. -/
def gomesDilatonCommutatorCLM (H : ℝ[X]) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (dilatonSuperchargeCLM H).comp (dilatonAdjointChargeCLM H) -
    (dilatonAdjointChargeCLM H).comp (dilatonSuperchargeCLM H)

/-- The previously reconstructed polynomial is exactly the multiplier of this actual operator. -/
theorem gomesDilatonCommutatorCLM_apply (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    gomesDilatonCommutatorCLM H ψ x =
      (((gomesDilatonCommutatorRecord H).eval x : ℝ) : ℂ) * ψ x := by
  change (dilatonSuperchargeCLM H (dilatonAdjointChargeCLM H ψ) -
    dilatonAdjointChargeCLM H (dilatonSuperchargeCLM H ψ)) x = _
  rw [gomesDilatonDual_commutator_apply, gomesDilatonCommutatorRecord_apply]
  simp only [eval_neg, Complex.ofReal_neg]

/-- Observe the commutator on the corpus's fixed nonvanishing Gaussian. -/
def gomesDilatonGaussianProbe (H : ℝ[X]) : 𝓢(ℝ, ℂ) :=
  gomesDilatonCommutatorCLM H gaussianSchwartz

/-- The Gaussian readout is the record polynomial times the fixed Gaussian profile. -/
theorem gomesDilatonGaussianProbe_apply (H : ℝ[X]) (x : ℝ) :
    gomesDilatonGaussianProbe H x =
      (((gomesDilatonCommutatorRecord H).eval x : ℝ) : ℂ) * gaussianSchwartz x :=
  gomesDilatonCommutatorCLM_apply H gaussianSchwartz x

/-- The single complete Gaussian readout determines the entire polynomial commutator record. -/
theorem gomesDilatonGaussianProbe_eq_iff (H K : ℝ[X]) :
    gomesDilatonGaussianProbe H = gomesDilatonGaussianProbe K ↔
      gomesDilatonCommutatorRecord H = gomesDilatonCommutatorRecord K := by
  constructor
  · intro h
    apply Polynomial.funext
    intro x
    have hx := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ x) h
    rw [gomesDilatonGaussianProbe_apply, gomesDilatonGaussianProbe_apply] at hx
    have hg : gaussianSchwartz x ≠ 0 := by
      rw [gaussianSchwartz_apply]
      exact Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
    have he := mul_right_cancel₀ hg hx
    exact_mod_cast he
  · intro h
    ext x
    simp only [gomesDilatonGaussianProbe_apply, h]

/-- Equality of the actual operators is exactly equality of their polynomial records. -/
theorem gomesDilatonCommutatorCLM_eq_iff (H K : ℝ[X]) :
    gomesDilatonCommutatorCLM H = gomesDilatonCommutatorCLM K ↔
      gomesDilatonCommutatorRecord H = gomesDilatonCommutatorRecord K := by
  constructor
  · intro h
    apply (gomesDilatonGaussianProbe_eq_iff H K).mp
    exact congrArg (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T gaussianSchwartz) h
  · intro h
    ext ψ x
    simp only [gomesDilatonCommutatorCLM_apply, h]

/-- One Gaussian experiment captures all information in the full Schwartz commutator. -/
theorem gomesDilatonGaussianProbe_operator_iff (H K : ℝ[X]) :
    gomesDilatonGaussianProbe H = gomesDilatonGaussianProbe K ↔
      gomesDilatonCommutatorCLM H = gomesDilatonCommutatorCLM K := by
  rw [gomesDilatonGaussianProbe_eq_iff, gomesDilatonCommutatorCLM_eq_iff]

/-- The exact invisible sector persists at the level of actual operator observations. -/
theorem gomesDilatonCommutatorCLM_affine_iff (H K : ℝ[X]) :
    gomesDilatonCommutatorCLM H = gomesDilatonCommutatorCLM K ↔
      ∃ d e : ℝ, H = K + C d * X + C e := by
  rw [gomesDilatonCommutatorCLM_eq_iff, gomesDilatonCommutatorRecord_eq_iff]

/-- Pointwise division by the nonvanishing probe gives the exact record value. -/
theorem gomesDilatonGaussianProbe_readout (H : ℝ[X]) (x : ℝ) :
    gomesDilatonGaussianProbe H x / gaussianSchwartz x =
      (((gomesDilatonCommutatorRecord H).eval x : ℝ) : ℂ) := by
  rw [gomesDilatonGaussianProbe_apply]
  have hg : gaussianSchwartz x ≠ 0 := by
    rw [gaussianSchwartz_apply]
    exact Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
  exact mul_div_cancel_right₀ _ hg

/-- Adding the two missing origin jets makes the actual Gaussian observation faithful. -/
theorem gomesDilatonGaussianProbe_origin_injective :
    Function.Injective (fun H : ℝ[X] => (gomesDilatonGaussianProbe H, H.eval 0, H.derivative.eval 0)) := by
  intro H K h
  apply (gomesDilatonCommutatorRecord_origin_iff H K).mp
  exact ⟨(gomesDilatonGaussianProbe_eq_iff H K).mp (congrArg Prod.fst h),
    congrArg (fun r => r.2.1) h, congrArg (fun r => r.2.2) h⟩

/-- Explicit rebuilding realizes every polynomial multiplication commutator on all Schwartz states. -/
theorem gomesDilatonRebuild_commutator_apply (P : ℝ[X]) (v s : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    gomesDilatonCommutatorCLM (gomesDilatonRebuild P v s) ψ x = ((P.eval x : ℝ) : ℂ) * ψ x := by
  rw [gomesDilatonCommutatorCLM_apply, gomesDilatonRebuild_record]

/-- The full operator inverse problem has a unique solution once the two origin jets are supplied. -/
theorem gomesDilatonRebuild_operator_unique (P H : ℝ[X]) (v s : ℝ) :
    (gomesDilatonCommutatorCLM H = gomesDilatonCommutatorCLM (gomesDilatonRebuild P v s) ∧
      H.eval 0 = v ∧ H.derivative.eval 0 = s) ↔ H = gomesDilatonRebuild P v s := by
  rw [gomesDilatonCommutatorCLM_eq_iff, gomesDilatonRebuild_record, gomesDilatonRebuild_unique]

end GaloisForLFunctions.HTGeometry
