import GaloisForLFunctions.RHTower.ConnesKernelTracePairing
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Convolution kernels as Hilbert–Schmidt kernel operators

§V (21) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `r_Λ^t (x,y) = ρ_Λ(x) · ρ̂_Λ(x-y)`.

An operator of that shape — multiply by `a`, after convolving with `b` — is the kernel operator of
the field `x ↦ a(x)·⟪c(·-x), _⟫` with `c(y) = conj b(-y)`.  The field is strongly measurable
because translation is norm continuous on `L²` (mathlib's `DomAddAct` action), and it is square
integrable because each `‖field x‖ = |a x|·‖c‖`.  So the cut-off operator of §V is a genuine
Hilbert–Schmidt kernel operator over the *additive Haar measure of the line*, and the trace
identity of `ConnesKernelTracePairing` applies to it.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance factOneLeTwoConv : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance factTwoNeTopConv : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- Translation of an `L²` function on the line. -/
def connesL2Translate (v : ℝ) (c : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  DomAddAct.mk (-v) +ᵥ c

theorem connesL2Translate_ae (v : ℝ) (c : Lp ℂ 2 (volume : Measure ℝ)) :
    (connesL2Translate v c : ℝ → ℂ) =ᵐ[volume] fun x => (c : ℝ → ℂ) (x - v) := by
  have h := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-v)) c
  refine h.trans ?_
  filter_upwards with x
  have hv : (DomAddAct.mk.symm (DomAddAct.mk (-v)) : ℝ) +ᵥ x = x - v := by
    simp only [Equiv.symm_apply_apply, vadd_eq_add]
    ring
  rw [hv]

theorem norm_connesL2Translate (v : ℝ) (c : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖connesL2Translate v c‖ = ‖c‖ := by
  rw [connesL2Translate, Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-v)) c)]
  congr 1
  have hmp : MeasurePreserving (fun x : ℝ => -v + x) volume volume :=
    measurePreserving_add_left volume (-v)
  exact (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable c) hmp)

theorem continuous_connesL2Translate (c : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous fun v : ℝ => connesL2Translate v c := by
  have hmk : Continuous fun v : ℝ => (DomAddAct.mk (-v) : DomAddAct ℝ) :=
    DomAddAct.continuous_mk.comp continuous_neg
  exact continuous_vadd.comp (hmk.prodMk continuous_const)

/-- **§V (21), the field.**  The kernel field of the operator `ξ ↦ a·(k ⋆ ξ)`. -/
def connesConvField (a : ℝ → ℂ) (c : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) :
    (Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ :=
  a x • (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ)) (connesL2Translate x c))

theorem norm_connesConvField (a : ℝ → ℂ) (c : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) :
    ‖connesConvField a c x‖ = ‖a x‖ * ‖c‖ := by
  rw [connesConvField, norm_smul,
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))).norm_map,
    norm_connesL2Translate]

theorem continuous_connesConvFieldBase (c : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous fun x : ℝ =>
      (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ)) (connesL2Translate x c)) :=
  (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))).continuous.comp
    (continuous_connesL2Translate c)

theorem memLp_connesConvField {a : ℝ → ℂ} (ha : MemLp a 2 (volume : Measure ℝ))
    (c : Lp ℂ 2 (volume : Measure ℝ)) : MemLp (connesConvField a c) 2 (volume : Measure ℝ) := by
  refine ⟨ha.1.smul (continuous_connesConvFieldBase c).aestronglyMeasurable, ?_⟩
  have hnorm : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖connesConvField a c x‖ = ‖((‖c‖ : ℂ)) * a x‖ := by
    filter_upwards with x
    rw [norm_connesConvField, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c)]
    ring
  rw [eLpNorm_congr_norm_ae hnorm]
  exact (ha.const_mul ((‖c‖ : ℂ))).2

/-- **§V (21).**  The kernel field of the cut-off operator, as an element of `L²`. -/
def connesConvKernel {a : ℝ → ℂ} (ha : MemLp a 2 (volume : Measure ℝ))
    (c : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ((Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ) 2 (volume : Measure ℝ) :=
  (memLp_connesConvField ha c).toLp (connesConvField a c)

/-- The kernel operator of a convolution field acts by `ξ ↦ a·⟪c(·-x), ξ⟫`. -/
theorem connesKernelOperator_convKernel {a : ℝ → ℂ} (ha : MemLp a 2 (volume : Measure ℝ))
    (c : Lp ℂ 2 (volume : Measure ℝ)) (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    (connesKernelOperator volume (connesConvKernel ha c) ξ : ℝ → ℂ)
      =ᵐ[volume] fun x => a x * (inner ℂ (connesL2Translate x c) ξ : ℂ) := by
  refine (connesKernelApply_ae volume (connesConvKernel ha c) ξ).trans ?_
  filter_upwards [(memLp_connesConvField ha c).coeFn_toLp] with x hx
  show ((connesConvKernel ha c : ℝ → (Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ) x) ξ = _
  rw [show (connesConvKernel ha c : ℝ → (Lp ℂ 2 (volume : Measure ℝ)) →L[ℂ] ℂ) x
      = connesConvField a c x from hx, connesConvField]
  simp only [smul_apply, smul_eq_mul]
  rfl

/-- **§V (21), integral form.**  The cut-off operator is an honest kernel operator: it acts by
integration against `k(x,y) = conj (c (y - x))`, multiplied by `a(x)`.  With
`c(y) = conj (ρ̂_Λ (-y))` and `a = ρ_Λ` this is Connes' `r_Λ^t(x,y) = ρ_Λ(x) ρ̂_Λ(x-y)`. -/
theorem connesKernelOperator_convKernel_integral {a : ℝ → ℂ} (ha : MemLp a 2 (volume : Measure ℝ))
    (c : Lp ℂ 2 (volume : Measure ℝ)) (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    (connesKernelOperator volume (connesConvKernel ha c) ξ : ℝ → ℂ)
      =ᵐ[volume] fun x => a x *
        ∫ y : ℝ, (starRingEnd ℂ) ((c : ℝ → ℂ) (y - x)) * (ξ : ℝ → ℂ) y := by
  refine (connesKernelOperator_convKernel ha c ξ).trans ?_
  filter_upwards with x
  congr 1
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [connesL2Translate_ae x c] with y hy
  rw [hy, RCLike.inner_apply]
  ring

end

end GaloisForLFunctions.RHTower
