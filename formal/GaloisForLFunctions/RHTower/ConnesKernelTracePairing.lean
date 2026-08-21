import GaloisForLFunctions.RHTower.ConnesKernelOperatorGeneral
import GaloisForLFunctions.RHTower.KernelOperatorPolarization

/-!
# The Hilbert–Schmidt pairing of kernel operators over an arbitrary base measure

§V (23) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `Trace (R_Λ T) = ∫∫ k(x,y) r_Λ^t(x,y) dx dy`.

The corpus owns `opTrace (A ∘L B) = hsInner (A†) B` for arbitrary continuous linear maps, and the
polarized kernel energy `hsInner (T_K) (T_L) = ∫ ⟪k_x, l_x⟫` for a *finite* base measure.  This
file removes the finiteness: with the kernel operator rebuilt over an arbitrary measure, the
polarization argument — Parseval on the fibre, then Fubini through
`integral_tsum_of_summable_integral_norm` — goes through unchanged.  Combining the two identities
is exactly (23).
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance factTwoNeTopConnesKernelPairing : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (μ : Measure α)

omit [CompleteSpace E] in
/-- The pointwise polarization: the inner product of two images is the integral of the pointwise
pairing of the two fields. -/
theorem connes_inner_kernelApply (K L : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    (inner ℂ (connesKernelApply μ K e) (connesKernelApply μ L e) : ℂ)
      = ∫ x, (inner ℂ (K x e) (L x e) : ℂ) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [connesKernelApply_ae μ K e, connesKernelApply_ae μ L e] with x h1 h2
  show (inner ℂ ((connesKernelApply μ K e : α → ℂ) x)
    ((connesKernelApply μ L e : α → ℂ) x) : ℂ) = _
  rw [h1, h2]

/-- **Polarized Hilbert–Schmidt energy of a kernel operator, arbitrary base measure.** -/
theorem connes_hsInner_kernelOperator [TopologicalSpace.SeparableSpace E]
    (K L : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.hsInner (connesKernelOperator μ K) (connesKernelOperator μ L)
      = ∫ x, (inner ℂ ((InnerProductSpace.toDual ℂ E).symm (L x))
          ((InnerProductSpace.toDual ℂ E).symm (K x)) : ℂ) ∂μ := by
  let b := ContinuousLinearMap.hsBasis ℂ E
  letI : Countable (exists_hilbertBasis ℂ E).choose := b.orthonormal.countable_index
  have hKhs := isHilbertSchmidt_connesKernelOperator μ K
  have hLhs := isHilbertSchmidt_connesKernelOperator μ L
  have hsqKint : ∀ i, Integrable (fun x => ‖K x (b i)‖ ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq_norm (connes_memLp_kernel_apply μ K (b i)).1).mp
      (connes_memLp_kernel_apply μ K (b i))
  have hsqLint : ∀ i, Integrable (fun x => ‖L x (b i)‖ ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq_norm (connes_memLp_kernel_apply μ L (b i)).1).mp
      (connes_memLp_kernel_apply μ L (b i))
  have hint : ∀ i, Integrable (fun x => (inner ℂ (K x (b i)) (L x (b i)) : ℂ)) μ := by
    intro i
    have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      ((connes_memLp_kernel_apply μ K (b i)).toLp (fun x => K x (b i)))
      ((connes_memLp_kernel_apply μ L (b i)).toLp (fun x => L x (b i)))
    refine h.congr ?_
    filter_upwards [(connes_memLp_kernel_apply μ K (b i)).coeFn_toLp,
      (connes_memLp_kernel_apply μ L (b i)).coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have hsqK : Summable (fun i => ∫ x, ‖K x (b i)‖ ^ 2 ∂μ) :=
    (hKhs.summable b).congr fun i => norm_connesKernelApply_sq μ K (b i)
  have hsqL : Summable (fun i => ∫ x, ‖L x (b i)‖ ^ 2 ∂μ) :=
    (hLhs.summable b).congr fun i => norm_connesKernelApply_sq μ L (b i)
  have hsumNorm : Summable (fun i => ∫ x, ‖(inner ℂ (K x (b i)) (L x (b i)) : ℂ)‖ ∂μ) := by
    refine Summable.of_nonneg_of_le
      (fun i => integral_nonneg fun x => norm_nonneg _) (fun i => ?_)
      ((hsqK.add hsqL).div_const 2)
    have hb : ∀ x, ‖(inner ℂ (K x (b i)) (L x (b i)) : ℂ)‖
        ≤ (‖K x (b i)‖ ^ 2 + ‖L x (b i)‖ ^ 2) / 2 := by
      intro x
      calc ‖(inner ℂ (K x (b i)) (L x (b i)) : ℂ)‖ ≤ ‖K x (b i)‖ * ‖L x (b i)‖ :=
            norm_inner_le_norm _ _
        _ ≤ (‖K x (b i)‖ ^ 2 + ‖L x (b i)‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖K x (b i)‖ - ‖L x (b i)‖)]
    have hdom : Integrable (fun x => (‖K x (b i)‖ ^ 2 + ‖L x (b i)‖ ^ 2) / 2) μ := by
      simpa using ((hsqKint i).add (hsqLint i)).div_const 2
    have hle := integral_mono ((hint i).norm) hdom hb
    calc (∫ x, ‖(inner ℂ (K x (b i)) (L x (b i)) : ℂ)‖ ∂μ)
        ≤ ∫ x, (‖K x (b i)‖ ^ 2 + ‖L x (b i)‖ ^ 2) / 2 ∂μ := hle
      _ = ((∫ x, ‖K x (b i)‖ ^ 2 ∂μ) + ∫ x, ‖L x (b i)‖ ^ 2 ∂μ) / 2 := by
          rw [integral_div, MeasureTheory.integral_add (hsqKint i) (hsqLint i)]
  rw [ContinuousLinearMap.hsInner]
  calc ∑' i, (inner ℂ (connesKernelOperator μ K (b i))
        (connesKernelOperator μ L (b i)) : ℂ)
      = ∑' i, ∫ x, (inner ℂ (K x (b i)) (L x (b i)) : ℂ) ∂μ :=
        tsum_congr fun i => connes_inner_kernelApply μ K L (b i)
    _ = ∫ x, ∑' i, (inner ℂ (K x (b i)) (L x (b i)) : ℂ) ∂μ :=
        integral_tsum_of_summable_integral_norm hint hsumNorm
    _ = ∫ x, (inner ℂ ((InnerProductSpace.toDual ℂ E).symm (L x))
          ((InnerProductSpace.toDual ℂ E).symm (K x)) : ℂ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        set yK : E := (InnerProductSpace.toDual ℂ E).symm (K x) with hyK
        set yL : E := (InnerProductSpace.toDual ℂ E).symm (L x) with hyL
        have hKb : ∀ i, K x (b i) = (inner ℂ yK (b i) : ℂ) := fun i => by
          rw [hyK, InnerProductSpace.toDual_symm_apply]
        have hLb : ∀ i, L x (b i) = (inner ℂ yL (b i) : ℂ) := fun i => by
          rw [hyL, InnerProductSpace.toDual_symm_apply]
        have hterm : ∀ i, (inner ℂ (K x (b i)) (L x (b i)) : ℂ)
            = (inner ℂ yL (b i) : ℂ) * (inner ℂ (b i) yK : ℂ) := by
          intro i
          rw [hKb i, hLb i, RCLike.inner_apply', inner_conj_symm]
          ring
        show (∑' i, (inner ℂ (K x (b i)) (L x (b i)) : ℂ)) = (inner ℂ yL yK : ℂ)
        rw [tsum_congr hterm]
        exact b.tsum_inner_mul_inner yL yK

/-- **§V (23).**  The trace of the composition of any continuous linear map with a kernel operator
is the Hilbert–Schmidt pairing of the adjoint with the kernel operator; when the adjoint is itself
a kernel operator this is Connes' `∫∫ k(x,y) r^t(x,y) dx dy`, now over an arbitrary base measure. -/
theorem connes_opTrace_comp_kernelOperator
    (A : Lp ℂ 2 μ →L[ℂ] E) (L : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.opTrace (A ∘L connesKernelOperator μ L)
      = ContinuousLinearMap.hsInner (ContinuousLinearMap.adjoint A) (connesKernelOperator μ L) :=
  ContinuousLinearMap.opTrace_comp_eq_hsInner A (connesKernelOperator μ L)

/-- **§V (23), hypothesis-free form.**  The trace of the composition of the adjoint of one kernel
operator with another is the integral of the pointwise pairing of the two kernel fields.  This is
Connes' `Trace(R_Λ T) = ∫∫ k(x,y) r_Λ^t(x,y) dx dy` over an arbitrary base measure. -/
theorem connes_opTrace_adjoint_kernel [TopologicalSpace.SeparableSpace E]
    (K L : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.opTrace
        ((ContinuousLinearMap.adjoint (connesKernelOperator μ K)) ∘L
          (connesKernelOperator μ L))
      = ∫ x, (inner ℂ ((InnerProductSpace.toDual ℂ E).symm (L x))
          ((InnerProductSpace.toDual ℂ E).symm (K x)) : ℂ) ∂μ := by
  rw [connes_opTrace_comp_kernelOperator μ (ContinuousLinearMap.adjoint
      (connesKernelOperator μ K)) L,
    ContinuousLinearMap.adjoint_adjoint, connes_hsInner_kernelOperator μ K L]

end

end GaloisForLFunctions.RHTower
