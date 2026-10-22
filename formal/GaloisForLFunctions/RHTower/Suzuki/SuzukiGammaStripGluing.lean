import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaStripBranch
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHalfLogScatteringKernel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaHalfLineClassification
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Upper-strip gluing of the two homogeneous Gamma channels

On the upper unit strip the homogeneous Gamma solution is the holomorphic function

`H(z) = z^{-1/2} e^{iγz} [Γ(1+iz)/Γ(1-iz)]^{1/2} e^{-izT/2} c`,

with the principal half-power and the Gamma-ratio branch normalised at the origin.  Its boundary
value on the positive axis is the positive channel with vector `c`, and on the negative axis the
principal half-power contributes the factor `-i`, so the boundary value there is the negative
channel with vector `-i c`.  Since the transport is invertible, the two real-frequency channels are
boundary values of one holomorphic strip solution exactly when `c₋ = -i c₊`, which by the kernel of
the half-log scattering map is exactly the vanishing of the endpoint trace.
-/

open Set Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The Gamma strip transport `Q(z) = e^{iγz}[Γ(1+iz)/Γ(1-iz)]^{1/2}e^{-izT/2}`. -/
def stripTransport (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) : X →L[ℂ] X :=
  (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z) •
    NormedSpace.exp ((-(Complex.I / 2) * z) • T)

/-- The homogeneous strip solution `H(z) = z^{-1/2}Q(z)c`. -/
def stripSolution (E : ℂ → ℂ) (T : X →L[ℂ] X) (c : X) (z : ℂ) : X :=
  (z ^ (-(1 : ℂ) / 2)) • stripTransport E T z c

omit [CompleteSpace X] in
theorem stripTransport_apply (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) (c : X) :
    stripTransport E T z c
      = (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z)
        • (NormedSpace.exp ((-(Complex.I / 2) * z) • T) c) := rfl

/-- The transport is invertible wherever the branch does not vanish. -/
theorem stripTransport_injective {E : ℂ → ℂ} {T : X →L[ℂ] X} {z : ℂ} (hz : E z ≠ 0) :
    Function.Injective (stripTransport E T z) := by
  intro v w hvw
  have hsub : stripTransport E T z (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  rw [stripTransport_apply] at hsub
  have hscal : (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) hz
  have hexp : NormedSpace.exp ((-(Complex.I / 2) * z) • T) (v - w) = 0 :=
    (smul_eq_zero.mp hsub).resolve_left hscal
  have hinv : NormedSpace.exp (-((-(Complex.I / 2) * z) • T))
      * NormedSpace.exp ((-(Complex.I / 2) * z) • T) = 1 := by
    letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
    have hc : Commute (-((-(Complex.I / 2) * z) • T)) ((-(Complex.I / 2) * z) • T) :=
      (Commute.refl _).neg_left
    have hadd := NormedSpace.exp_add_of_commute hc
    rw [neg_add_cancel, NormedSpace.exp_zero] at hadd
    exact hadd.symm
  have happ : (NormedSpace.exp (-((-(Complex.I / 2) * z) • T))
      * NormedSpace.exp ((-(Complex.I / 2) * z) • T)) (v - w) = v - w := by
    rw [hinv]
    rfl
  have : v - w = 0 := by
    have hcomp : (NormedSpace.exp (-((-(Complex.I / 2) * z) • T))
        * NormedSpace.exp ((-(Complex.I / 2) * z) • T)) (v - w)
        = NormedSpace.exp (-((-(Complex.I / 2) * z) • T))
            (NormedSpace.exp ((-(Complex.I / 2) * z) • T) (v - w)) := rfl
    rw [hcomp, hexp, map_zero] at happ
    exact happ.symm
  exact sub_eq_zero.mp this

theorem cpow_neg_half_ofReal_pos {η : ℝ} (hη : 0 < η) :
    ((η : ℂ)) ^ (-(1 : ℂ) / 2) = ((η ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  rw [show (-(1 : ℂ) / 2) = (((-(1 : ℝ) / 2 : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_cpow hη.le]

theorem cpow_neg_half_ofReal_neg {η : ℝ} (hη : η < 0) :
    ((η : ℂ)) ^ (-(1 : ℂ) / 2) = (-Complex.I) * (((-η) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  have hne : ((η : ℂ)) ≠ 0 := by simpa using ne_of_lt hη
  have hpos : (0 : ℝ) < -η := by linarith
  have hlog : Complex.log (η : ℂ) = (Real.log (-η) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    rw [show Complex.log (η : ℂ) = ((Real.log ‖(η : ℂ)‖ : ℝ) : ℂ)
        + ((Complex.arg (η : ℂ) : ℝ) : ℂ) * Complex.I from rfl,
      Complex.arg_ofReal_of_neg hη, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hη]
  rw [Complex.cpow_def, if_neg hne, hlog]
  have hsplit : (((Real.log (-η) : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I) * (-(1 : ℂ) / 2)
      = (((Real.log (-η) * (-(1 : ℝ) / 2) : ℝ)) : ℂ)
        + (-((Real.pi : ℂ) / 2) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
  have hrpow : ((-η) ^ (-(1 : ℝ) / 2) : ℝ) = Real.exp (Real.log (-η) * (-(1 : ℝ) / 2)) :=
    Real.rpow_def_of_pos hpos _
  have hexpI : Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I) = -Complex.I := by
    rw [Complex.exp_mul_I]
    have h1 : Complex.cos (-((Real.pi : ℂ) / 2)) = 0 := by
      rw [Complex.cos_neg]
      simp
    have h2 : Complex.sin (-((Real.pi : ℂ) / 2)) = -1 := by
      rw [Complex.sin_neg]
      simp
    rw [h1, h2]
    ring
  rw [hexpI, hrpow]
  push_cast
  ring

omit [CompleteSpace X] in
theorem stripSolution_ofReal_pos (E : ℂ → ℂ) (T : X →L[ℂ] X) (c : X) {η : ℝ} (hη : 0 < η) :
    stripSolution E T c (η : ℂ)
      = ((η ^ (-(1 : ℝ) / 2) : ℝ)) • stripTransport E T (η : ℂ) c := by
  rw [stripSolution, cpow_neg_half_ofReal_pos hη, ← ofReal_smul_eq]

omit [CompleteSpace X] in
theorem stripSolution_ofReal_neg (E : ℂ → ℂ) (T : X →L[ℂ] X) (c : X) {η : ℝ} (hη : η < 0) :
    stripSolution E T c (η : ℂ)
      = (((-η) ^ (-(1 : ℝ) / 2) : ℝ))
        • stripTransport E T (η : ℂ) ((-Complex.I) • c) := by
  rw [stripSolution, cpow_neg_half_ofReal_neg hη, map_smul, ← ofReal_smul_eq, smul_smul]
  congr 1
  ring

/-- The strip transport applied to a fixed vector is holomorphic where the branch is. -/
theorem differentiableAt_stripTransport_apply {E : ℂ → ℂ} (T : X →L[ℂ] X) (c : X) {z : ℂ}
    (hE : DifferentiableAt ℂ E z) :
    DifferentiableAt ℂ (fun w : ℂ => stripTransport E T w c) z := by
  have hscalar : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * w) * E w) z :=
    ((differentiableAt_id.const_mul _).cexp).mul hE
  have hopexp : DifferentiableAt ℂ
      (fun w : ℂ => NormedSpace.exp ((-(Complex.I / 2) * w) • T)) z := by
    have hbase := hasDerivAt_exp_smul_const (𝕂 := ℂ) T (-(Complex.I / 2) * z)
    have hlin : HasDerivAt (fun w : ℂ => -(Complex.I / 2) * w) (-(Complex.I / 2)) z := by
      simpa using (hasDerivAt_id z).const_mul (-(Complex.I / 2))
    have hcomp : HasDerivAt (fun w : ℂ => NormedSpace.exp ((-(Complex.I / 2) * w) • T))
        ((-(Complex.I / 2)) • (NormedSpace.exp ((-(Complex.I / 2) * z) • T) * T)) z :=
      HasDerivAt.scomp z hbase hlin
    exact hcomp.differentiableAt
  have hvec : DifferentiableAt ℂ
      (fun w : ℂ => NormedSpace.exp ((-(Complex.I / 2) * w) • T) c) z :=
    hopexp.clm_apply (differentiableAt_const c)
  have hfun : (fun w : ℂ => stripTransport E T w c)
      = fun w : ℂ => (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * w) * E w)
        • (NormedSpace.exp ((-(Complex.I / 2) * w) • T) c) :=
    funext fun w => stripTransport_apply E T w c
  rw [hfun]
  exact hscalar.smul hvec

/-- **The strip solution is holomorphic on the upper unit strip.** -/
theorem differentiableOn_stripSolution {E : ℂ → ℂ} (hE : DifferentiableOn ℂ E (imStrip (-1) 1))
    (T : X →L[ℂ] X) (c : X) :
    DifferentiableOn ℂ (stripSolution E T c) (imStrip 0 1) := by
  intro z hz
  have hz' : z ∈ imStrip (-1) 1 := ⟨by linarith [hz.1], hz.2⟩
  have hEz : DifferentiableAt ℂ E z :=
    hE.differentiableAt ((isOpen_imStrip (-1) 1).mem_nhds hz')
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz.1))
  have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ (-(1 : ℂ) / 2)) z :=
    differentiableAt_id.cpow_const hslit
  exact (hpow.smul (differentiableAt_stripTransport_apply T c hEz)).differentiableWithinAt

/-- **The upper-strip gluing criterion.**  The negative channel is the boundary value of the
holomorphic strip solution carrying the positive channel exactly when `c₋ = -i c₊`. -/
theorem stripSolution_glue_iff {E : ℂ → ℂ} {T : X →L[ℂ] X}
    (hE : E ((-1 : ℝ) : ℂ) ≠ 0) (cp cm : X) :
    (∀ η : ℝ, η < 0 → stripSolution E T cp (η : ℂ)
        = (((-η) ^ (-(1 : ℝ) / 2) : ℝ)) • stripTransport E T (η : ℂ) cm)
      ↔ cm = (-Complex.I) • cp := by
  constructor
  · intro h
    have h1 := h (-1) (by norm_num)
    rw [stripSolution_ofReal_neg E T cp (by norm_num : (-1 : ℝ) < 0)] at h1
    have hscal : (((1 : ℝ)) ^ (-(1 : ℝ) / 2) : ℝ) ≠ 0 := by
      rw [Real.one_rpow]
      norm_num
    have hone : (-(-1 : ℝ)) = (1 : ℝ) := by norm_num
    rw [hone] at h1
    have h2 : stripTransport E T ((-1 : ℝ) : ℂ) ((-Complex.I) • cp)
        = stripTransport E T ((-1 : ℝ) : ℂ) cm := by
      have := sub_eq_zero.mpr h1
      rw [← smul_sub] at this
      have h3 := (smul_eq_zero.mp this).resolve_left hscal
      exact sub_eq_zero.mp h3
    exact (stripTransport_injective hE h2).symm
  · intro h η hη
    rw [stripSolution_ofReal_neg E T cp hη, h]

/-- **Zero endpoint trace is exactly upper-strip gluing.** -/
theorem halfLogScatter_eq_zero_iff_glue {E : ℂ → ℂ} {T : X →L[ℂ] X}
    (hE : E ((-1 : ℝ) : ℂ) ≠ 0) (cp cm : X) :
    halfLogScatter cp cm = 0
      ↔ (∀ η : ℝ, η < 0 → stripSolution E T cp (η : ℂ)
          = (((-η) ^ (-(1 : ℝ) / 2) : ℝ)) • stripTransport E T (η : ℂ) cm) := by
  rw [halfLogScatter_eq_zero_iff, stripSolution_glue_iff hE]

end

end GaloisForLFunctions.RHTower
