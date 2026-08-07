import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# Polarization of the Hilbert–Schmidt energy of a kernel operator

`hsNormSq_kernelOperator_eq_norm_sq` computes the Hilbert–Schmidt energy of a kernel operator as
the `L²` energy of its field.  This file polarizes that identity: the Hilbert–Schmidt inner product
of two kernel operators is the integral of the pointwise pairing of the two fields, read through
the Riesz isometry.  Because `E →L[ℂ] ℂ` carries no inner product instance the pairing is written
on the Riesz vectors, where the conjugate linearity of `toDual.symm` exchanges the two arguments.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

section Kernel

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (μ : Measure α) [IsFiniteMeasure μ]

omit [CompleteSpace E] in
/-- The pointwise polarization of a kernel operator: the inner product of the two images is the
integral of the pointwise pairing of the two fields. -/
theorem inner_kernelOperator_apply (K L : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    (inner ℂ (kernelOperator (E := E) μ K e) (kernelOperator (E := E) μ L e) : ℂ)
      = ∫ x, (inner ℂ (K x e) (L x e) : ℂ) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hK := (evalBilinear (𝕜 := ℂ) (E := E)).coeFn_holder
    (r := (2 : ENNReal)) K (Lp.const ∞ μ e)
  have hL := (evalBilinear (𝕜 := ℂ) (E := E)).coeFn_holder
    (r := (2 : ENNReal)) L (Lp.const ∞ μ e)
  have hconst := Lp.coeFn_const (p := ∞) μ e
  filter_upwards [hK, hL, hconst] with x hKx hLx hcx
  show (inner ℂ ((kernelOperator (E := E) μ K e : Lp ℂ 2 μ) x)
      ((kernelOperator (E := E) μ L e : Lp ℂ 2 μ) x) : ℂ) = _
  rw [kernelOperator, kernelOperatorMap_apply, kernelOperator, kernelOperatorMap_apply,
    hKx, hLx, hcx]
  simp [evalBilinear]


omit [CompleteSpace E] in
/-- The diagonal case: the squared norm of the image is the energy of the field. -/
theorem norm_sq_kernelOperator_apply (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    ‖kernelOperator (E := E) μ K e‖ ^ 2 = ∫ x, ‖K x e‖ ^ 2 ∂μ := by
  have h := inner_kernelOperator_apply μ K K e
  have hlhs : (inner ℂ (kernelOperator (E := E) μ K e)
      (kernelOperator (E := E) μ K e) : ℂ)
      = ((‖kernelOperator (E := E) μ K e‖ ^ 2 : ℝ) : ℂ) := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (kernelOperator (E := E) μ K e)
    push_cast
    exact this
  have hrhs : (∫ x, (inner ℂ (K x e) (K x e) : ℂ) ∂μ)
      = ((∫ x, ‖K x e‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := ℂ) (K x e)
    push_cast
    exact h2
  rw [hlhs, hrhs] at h
  exact_mod_cast h

/-- **Polarized Hilbert--Schmidt energy of a kernel operator.**  The Hilbert--Schmidt inner
product of two kernel operators is the integral of the pointwise pairing of their fields, read on
the Riesz vectors. -/
theorem hsInner_kernelOperator [TopologicalSpace.SeparableSpace E]
    (K L : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.hsInner (kernelOperator (E := E) μ K) (kernelOperator (E := E) μ L)
      = ∫ x, (inner ℂ ((InnerProductSpace.toDual ℂ E).symm (L x))
          ((InnerProductSpace.toDual ℂ E).symm (K x)) : ℂ) ∂μ := by
  let b := ContinuousLinearMap.hsBasis ℂ E
  letI : Countable (exists_hilbertBasis ℂ E).choose := b.orthonormal.countable_index
  have hKhs := isHilbertSchmidt_kernelOperator (E := E) μ K
  have hLhs := isHilbertSchmidt_kernelOperator (E := E) μ L
  have hMK : ∀ i, MemLp (fun x => K x (b i)) 2 μ := fun i =>
    (Lp.memLp K).continuousLinearMap_comp (ContinuousLinearMap.apply ℂ ℂ (b i))
  have hML : ∀ i, MemLp (fun x => L x (b i)) 2 μ := fun i =>
    (Lp.memLp L).continuousLinearMap_comp (ContinuousLinearMap.apply ℂ ℂ (b i))
  have hsqKint : ∀ i, Integrable (fun x => ‖K x (b i)‖ ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq_norm (hMK i).1).mp (hMK i)
  have hsqLint : ∀ i, Integrable (fun x => ‖L x (b i)‖ ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq_norm (hML i).1).mp (hML i)
  have hint : ∀ i, Integrable (fun x => (inner ℂ (K x (b i)) (L x (b i)) : ℂ)) μ := by
    intro i
    have h := MeasureTheory.L2.integrable_inner ((hMK i).toLp _) ((hML i).toLp _)
    refine h.congr ?_
    filter_upwards [(hMK i).coeFn_toLp, (hML i).coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have hsqK : Summable (fun i => ∫ x, ‖K x (b i)‖ ^ 2 ∂μ) :=
    (hKhs.summable b).congr fun i => norm_sq_kernelOperator_apply μ K (b i)
  have hsqL : Summable (fun i => ∫ x, ‖L x (b i)‖ ^ 2 ∂μ) :=
    (hLhs.summable b).congr fun i => norm_sq_kernelOperator_apply μ L (b i)
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
    have hle := integral_mono ((hint i).norm)
      ((hsqKint i).add (hsqLint i)).div_const 2 hb
    calc (∫ x, ‖(inner ℂ (K x (b i)) (L x (b i)) : ℂ)‖ ∂μ)
        ≤ ∫ x, (‖K x (b i)‖ ^ 2 + ‖L x (b i)‖ ^ 2) / 2 ∂μ := hle
      _ = ((∫ x, ‖K x (b i)‖ ^ 2 ∂μ) + ∫ x, ‖L x (b i)‖ ^ 2 ∂μ) / 2 := by
          rw [integral_div, MeasureTheory.integral_add (hsqKint i) (hsqLint i)]
  rw [ContinuousLinearMap.hsInner]
  calc ∑' i, (inner ℂ (kernelOperator (E := E) μ K (b i))
        (kernelOperator (E := E) μ L (b i)) : ℂ)
      = ∑' i, ∫ x, (inner ℂ (K x (b i)) (L x (b i)) : ℂ) ∂μ :=
        tsum_congr fun i => inner_kernelOperator_apply μ K L (b i)
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
        show (∑' i, (inner ℂ (K x (b i)) (L x (b i)) : ℂ))
          = (inner ℂ yL yK : ℂ)
        rw [tsum_congr hterm]
        exact b.tsum_inner_mul_inner yL yK

end Kernel

end

end RHTower
