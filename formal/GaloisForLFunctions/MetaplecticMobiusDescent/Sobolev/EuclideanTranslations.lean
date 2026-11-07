/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license; see LICENSE and NOTICE in the parent directory.
Adapted from rellich-kondrachov, Euclidean translation proofs.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.EuclideanEnergy
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Translation and the pointwise gradient bound

Translation preserves the compactly supported `C¹` class and acts isometrically
on `L²` for an invariant measure. The fundamental theorem of calculus along
`x+t a` bounds the increment by the integral of the gradient along the segment.
-/

namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev

open scoped ENNReal MeasureTheory Topology
open MeasureTheory

section Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Translate a function by `a` (right translation): `x ↦ f (x + a)`. -/
def translate {F : Type*} (a : E) (f : E → F) : E → F :=
  fun x => f (x + a)

omit [CompleteSpace E] in
lemma contDiff_translate {f : E → ℝ} (hf : ContDiff ℝ 1 f) (a : E) :
    ContDiff ℝ 1 (translate (E := E) a f) := by
  exact hf.comp (contDiff_id.add contDiff_const)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_translate {F : Type*} [Zero F] {f : E → F}
    (hf : HasCompactSupport f) (a : E) : HasCompactSupport (translate (E := E) a f) := by
  exact hf.comp_homeomorph (Homeomorph.addRight a)

lemma grad_translate (a : E) (f : E → ℝ) (x : E) :
    grad (E := E) (translate (E := E) a f) x = grad (E := E) f (x + a) := by
  classical
  simp [grad]
  exact (fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) a)

omit [CompleteSpace E] in
lemma mem_C1c_translate {f : E → ℝ} (hf : f ∈ C1c (E := E)) (a : E) :
    translate (E := E) a f ∈ C1c (E := E) :=
  ⟨contDiff_translate (E := E) hf.1 a, hasCompactSupport_translate (E := E) hf.2 a⟩

/-- Translation as a linear endomorphism of `C¹_c`. -/
noncomputable def translateC1c (a : E) : ↥(C1c (E := E)) →ₗ[ℝ] ↥(C1c (E := E)) where
  toFun f := ⟨translate (E := E) a f.1, mem_C1c_translate (E := E) (f := f.1) f.2 a⟩
  map_add' f g := by
    ext x
    simp [translate]
  map_smul' c f := by
    ext x
    simp [translate]

end Topology

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddE_SobolevEuclideanTranslation : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant]

/-- Translation on `L²` as a linear isometry, under an additive right-invariant measure. -/
noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))

variable [IsFiniteMeasureOnCompacts μ]

omit [CompleteSpace E] in
lemma translateL2_toL2 (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) =
      toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    exact
      (memLp_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
  exact h₁.trans h₂.symm

lemma translateL2_toL2Grad (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) =
      toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hf :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2Grad (μ := μ) (E := E) f : E → E) (x + a)) =ᵐ[μ]
          fun x => grad (E := E) f.1 (x + a) := by
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact
      (translateL2_ae_eq (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hTo :
        (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
          grad (E := E) (translate (E := E) a f.1) :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
    have hGrad :
        grad (E := E) (translate (E := E) a f.1) = fun x => grad (E := E) f.1 (x + a) := by
      funext x
      exact grad_translate (E := E) a f.1 x
    exact hTo.trans (by simp [hGrad])
  exact h₁.trans h₂.symm

end Measure

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimate :
    MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimate :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimate :
    OpensMeasurableSpace E := by
  infer_instance

/-! ## Derivative along a translated line -/

/-- The affine line `t ↦ x + t • a`. -/
def line (x a : E) (t : ℝ) : E :=
  x + t • a

lemma hasDerivAt_line (x a : E) (t : ℝ) :
    HasDerivAt (line (x := x) (a := a)) a t := by
  have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const a
  exact HasDerivAt.const_add x hsmul

lemma deriv_line (x a : E) (t : ℝ) :
    deriv (line (x := x) (a := a)) t = a :=
  (hasDerivAt_line (x := x) (a := a) t).deriv

lemma hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl

lemma deriv_comp_line {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a :=
  (hasDerivAt_comp_line (hf := hf) (x := x) (a := a) t).deriv

/-! ## Pointwise translation bound via the gradient -/

section

variable [CompleteSpace E]

lemma enorm_fderiv_apply_le_enorm_grad_mul (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opENorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    exact
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁

lemma enorm_deriv_comp_line_le (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this

lemma enorm_sub_le_enorm_mul_lintegral_grad (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Icc (0 : ℝ) 1) := by
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by simp)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := fun t : ℝ => f (x + t • a))
        (a := (0 : ℝ)) (b := 1) hCont (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    refine (ae_of_all _ fun t => ?_)
    simpa [line, mul_assoc, mul_left_comm, mul_comm] using
      (enorm_deriv_comp_line_le (x := x) (a := a) (f := f) hf (t := t))
  have :
      (∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine this.trans ?_
  have hMeas :
      Measurable fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ := by
    have hgradCont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) (by
      exact hf)
    exact (hgradCont.comp (by
      have : Continuous (fun t : ℝ => x + t • a) := by
        fun_prop
      exact this)).measurable.enorm
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Icc (0 : ℝ) 1)) (r := ‖a‖ₑ)
        (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)

end

end

#print axioms translateL2
#print axioms translateL2_toL2Grad
#print axioms enorm_sub_le_enorm_mul_lintegral_grad

end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev
