import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# Hilbert–Schmidt kernel operators over an arbitrary base measure

§V (19)-(24) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

needs the Hilbert–Schmidt kernel calculus on a *local field*, whose additive Haar measure is
infinite.  The corpus's kernel-operator layer is built with `Lp.const ∞ μ e`, which forces the
base measure to be finite.  The constant field is only a device to apply Hölder, and it can be
avoided: for a square-integrable field `K` of continuous functionals the function `x ↦ K x e`
is already in `L²` because `‖K x e‖ ≤ ‖K x‖ ‖e‖` pointwise.  Rebuilding the kernel operator that
way removes the finiteness assumption entirely, and the Hilbert–Schmidt kernel theorem together
with the exact energy identity go through verbatim.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance factTwoNeTopConnesKernel : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (μ : Measure α)

/-- Evaluating a square-integrable field of functionals at a fixed vector stays square
integrable. -/
theorem connes_memLp_kernel_apply (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    MemLp (fun x => K x e) 2 μ :=
  (Lp.memLp K).continuousLinearMap_comp (ContinuousLinearMap.apply ℂ ℂ e)

/-- The image of a vector under the kernel operator, over an arbitrary base measure. -/
def connesKernelApply (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) : Lp ℂ 2 μ :=
  (connes_memLp_kernel_apply μ K e).toLp _

theorem connesKernelApply_ae (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    (connesKernelApply μ K e : α → ℂ) =ᵐ[μ] fun x => K x e :=
  MemLp.coeFn_toLp _

theorem connesKernelApply_add (K : Lp (E →L[ℂ] ℂ) 2 μ) (e f : E) :
    connesKernelApply μ K (e + f) = connesKernelApply μ K e + connesKernelApply μ K f := by
  refine Lp.ext ?_
  filter_upwards [connesKernelApply_ae μ K (e + f), connesKernelApply_ae μ K e,
    connesKernelApply_ae μ K f,
    Lp.coeFn_add (connesKernelApply μ K e) (connesKernelApply μ K f)] with x h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.add_apply]
  rw [h2, h3, map_add]

theorem connesKernelApply_smul (K : Lp (E →L[ℂ] ℂ) 2 μ) (c : ℂ) (e : E) :
    connesKernelApply μ K (c • e) = c • connesKernelApply μ K e := by
  refine Lp.ext ?_
  filter_upwards [connesKernelApply_ae μ K (c • e), connesKernelApply_ae μ K e,
    Lp.coeFn_smul c (connesKernelApply μ K e)] with x h1 h2 h3
  rw [h1, h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, map_smul]
  simp

theorem norm_connesKernelApply_le (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    ‖connesKernelApply μ K e‖ ≤ ‖K‖ * ‖e‖ := by
  have hae : (connesKernelApply μ K e : α → ℂ) =ᵐ[μ] fun x => K x e :=
    connesKernelApply_ae μ K e
  rw [Lp.norm_def, eLpNorm_congr_ae hae]
  have hmono : eLpNorm (fun x => K x e) 2 μ ≤ eLpNorm (fun x => ‖e‖ • ‖K x‖) 2 μ := by
    refine eLpNorm_mono_ae ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), smul_eq_mul]
    exact le_trans ((K x).le_opNorm e) (by rw [mul_comm])
  have hsmul : eLpNorm (fun x => ‖e‖ • ‖K x‖) 2 μ
      = ENNReal.ofReal ‖e‖ * eLpNorm (fun x => ‖K x‖) 2 μ := by
    have hfun : (fun x => ‖e‖ • ‖(K : α → E →L[ℂ] ℂ) x‖)
        = ‖e‖ • (fun x => ‖(K : α → E →L[ℂ] ℂ) x‖) := rfl
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (norm_nonneg e)]
  have hnormK : eLpNorm (fun x => ‖K x‖) 2 μ = eLpNorm (K : α → E →L[ℂ] ℂ) 2 μ :=
    eLpNorm_norm _
  rw [hsmul, hnormK] at hmono
  have hfin : eLpNorm (K : α → E →L[ℂ] ℂ) 2 μ ≠ ∞ := (Lp.memLp K).2.ne
  have := ENNReal.toReal_mono
    (by exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hmono
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg e)] at this
  calc (eLpNorm (fun x => K x e) 2 μ).toReal
      ≤ ‖e‖ * (eLpNorm (K : α → E →L[ℂ] ℂ) 2 μ).toReal := this
    _ = ‖K‖ * ‖e‖ := by rw [Lp.norm_def]; ring

/-- **The kernel operator over an arbitrary base measure.** -/
def connesKernelOperator (K : Lp (E →L[ℂ] ℂ) 2 μ) : E →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := connesKernelApply μ K
      map_add' := connesKernelApply_add μ K
      map_smul' := fun c e => connesKernelApply_smul μ K c e }
    ‖K‖ (norm_connesKernelApply_le μ K)

@[simp] theorem connesKernelOperator_apply (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    connesKernelOperator μ K e = connesKernelApply μ K e := rfl

/-- The `L²` energy of a field of functionals. -/
theorem connes_norm_l2_sq (K : Lp (E →L[ℂ] ℂ) 2 μ) : ‖K‖ ^ 2 = ∫ x, ‖K x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable K),
    lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable K)]
  norm_num [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  exact integral_nonneg fun x => sq_nonneg _

/-- The energy of one image of the kernel operator. -/
theorem norm_connesKernelApply_sq (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    ‖connesKernelApply μ K e‖ ^ 2 = ∫ x, ‖K x e‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  rw [← integral_re (L2.integrable_inner
    (connesKernelApply μ K e) (connesKernelApply μ K e))]
  apply integral_congr_ae
  filter_upwards [connesKernelApply_ae μ K e] with x hx
  rw [hx]
  simp
  norm_cast

/-- **Hilbert–Schmidt kernel theorem over an arbitrary base measure.** -/
theorem isHilbertSchmidt_connesKernelOperator [CompleteSpace E] (K : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.IsHilbertSchmidt (connesKernelOperator μ K) := by
  let b := ContinuousLinearMap.hsBasis ℂ E
  show Summable (fun i => ‖connesKernelOperator μ K (b i)‖ ^ 2)
  apply summable_of_sum_le (fun i => sq_nonneg _) (c := ‖K‖ ^ 2)
  intro u
  simp_rw [connesKernelOperator_apply, norm_connesKernelApply_sq μ K]
  rw [← integral_finsetSum]
  rw [connes_norm_l2_sq μ K]
  · apply integral_mono_ae
    · exact integrable_finsetSum _ fun i _ =>
        (memLp_two_iff_integrable_sq_norm
          (connes_memLp_kernel_apply μ K (b i)).1).mp
          (connes_memLp_kernel_apply μ K (b i))
    · exact (memLp_two_iff_integrable_sq_norm (Lp.memLp K).1).mp (Lp.memLp K)
    · exact Filter.Eventually.of_forall fun x => by
        let y : E := (InnerProductSpace.toDual ℂ E).symm (K x)
        calc
          ∑ i ∈ u, ‖K x (b i)‖ ^ 2 = ∑ i ∈ u, ‖inner ℂ y (b i)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [InnerProductSpace.toDual_symm_apply]
          _ = ∑ i ∈ u, ‖inner ℂ (b i) y‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_inner_symm]
          _ ≤ ‖y‖ ^ 2 := b.orthonormal.sum_inner_products_le y
          _ = ‖K x‖ ^ 2 := by rw [(InnerProductSpace.toDual ℂ E).symm.norm_map]
  · intro i _
    exact (memLp_two_iff_integrable_sq_norm
      (connes_memLp_kernel_apply μ K (b i)).1).mp
      (connes_memLp_kernel_apply μ K (b i))

end

end GaloisForLFunctions.RHTower
