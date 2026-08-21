import GaloisForLFunctions.RHTower.ConnesKernelTracePairing

/-!
# The trace pairing against an operator with only `L²` rows

§V (19)/(23) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`U(h)` has kernel `h(x/y)/(ρ|y|)`; its rows `b(x,·)` are square integrable for a.e. `x` (the
substitution `u = x/y` gives `‖b(x,·)‖² = ‖h‖²/|x|`), but the field `x ↦ b(x,·)` is *not* square
integrable, so `U(h)` is not Hilbert–Schmidt and the kernel pairing of
`ConnesKernelTracePairing` does not apply to it.

It applies nonetheless to the *pairing*: if one factor is a genuine Hilbert–Schmidt kernel
operator with field `K` and the other merely has `L²` rows `L x`, then Bessel's inequality and
Cauchy–Schwarz bound the basis sum of the two matrix entries by `‖K x‖ ‖L x‖` uniformly in the
finite index set, so the exchange of sum and integral is legitimate as soon as
`∫ ‖K x‖ ‖L x‖ dμ < ∞`.  That integrability is exactly what holds in Connes' situation, where
`‖K x‖ = ρ_Λ(x)‖ρ̂_Λ‖` and `‖L x‖ = ‖h‖/√|x|`, whose product is integrable on `|x| ≤ Λ`.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance factTwoNeTopFieldPairing : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (μ : Measure α)

omit [CompleteSpace E] in
/-- **Bessel plus Cauchy–Schwarz.**  On any finite set of orthonormal indices the sum of the
products of the two matrix entries is bounded by the product of the norms. -/
theorem connes_finset_inner_bound {ι : Type*} (b : HilbertBasis ι ℂ E) (u : Finset ι) (v w : E) :
    ∑ i ∈ u, ‖(inner ℂ v (b i) : ℂ)‖ * ‖(inner ℂ (b i) w : ℂ)‖ ≤ ‖v‖ * ‖w‖ := by
  have hv0 : ∑ i ∈ u, ‖(inner ℂ (b i) v : ℂ)‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    b.orthonormal.sum_inner_products_le v
  have hveq : ∑ i ∈ u, ‖(inner ℂ v (b i) : ℂ)‖ ^ 2
      = ∑ i ∈ u, ‖(inner ℂ (b i) v : ℂ)‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [norm_inner_symm]
  have hv : ∑ i ∈ u, ‖(inner ℂ v (b i) : ℂ)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hveq]; exact hv0
  have hw : ∑ i ∈ u, ‖(inner ℂ (b i) w : ℂ)‖ ^ 2 ≤ ‖w‖ ^ 2 :=
    b.orthonormal.sum_inner_products_le w
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq u
    (fun i => ‖(inner ℂ v (b i) : ℂ)‖) (fun i => ‖(inner ℂ (b i) w : ℂ)‖)
  have hnn : (0 : ℝ) ≤ ∑ i ∈ u, ‖(inner ℂ v (b i) : ℂ)‖ * ‖(inner ℂ (b i) w : ℂ)‖ :=
    Finset.sum_nonneg fun i _ => by positivity
  have hB : (0 : ℝ) ≤ ∑ i ∈ u, ‖(inner ℂ (b i) w : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hprod : (∑ i ∈ u, ‖(inner ℂ v (b i) : ℂ)‖ * ‖(inner ℂ (b i) w : ℂ)‖) ^ 2
      ≤ (‖v‖ * ‖w‖) ^ 2 := by
    calc (∑ i ∈ u, ‖(inner ℂ v (b i) : ℂ)‖ * ‖(inner ℂ (b i) w : ℂ)‖) ^ 2
        ≤ (∑ i ∈ u, ‖(inner ℂ v (b i) : ℂ)‖ ^ 2) *
            ∑ i ∈ u, ‖(inner ℂ (b i) w : ℂ)‖ ^ 2 := hcs
      _ ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 := mul_le_mul hv hw hB (by positivity)
      _ = (‖v‖ * ‖w‖) ^ 2 := by ring
  have hsq := Real.sqrt_le_sqrt hprod
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq (by positivity)] at hsq

/-- **§V (19)/(23).**  The Hilbert–Schmidt pairing of a kernel operator with any operator whose
rows are square integrable is the integral of the pointwise pairing of the two row fields, as
soon as the product of the row norms is integrable.  The second operator need not be
Hilbert–Schmidt. -/
theorem connes_hsInner_kernelOperator_field [TopologicalSpace.SeparableSpace E]
    (K : Lp (E →L[ℂ] ℂ) 2 μ) (B : E →L[ℂ] Lp ℂ 2 μ) (L : α → E)
    (hL : ∀ e : E, ((B e : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => (inner ℂ (L x) e : ℂ))
    (hLmeas : AEStronglyMeasurable L μ)
    (hint : Integrable (fun x => ‖(K : α → E →L[ℂ] ℂ) x‖ * ‖L x‖) μ) :
    ContinuousLinearMap.hsInner (connesKernelOperator μ K) B
      = ∫ x, (inner ℂ (L x)
          ((InnerProductSpace.toDual ℂ E).symm ((K : α → E →L[ℂ] ℂ) x)) : ℂ) ∂μ := by
  let b := ContinuousLinearMap.hsBasis ℂ E
  letI : Countable (exists_hilbertBasis ℂ E).choose := b.orthonormal.countable_index
  set kf : α → E := fun x => (InnerProductSpace.toDual ℂ E).symm
    ((K : α → E →L[ℂ] ℂ) x) with hkf
  have hkfnorm : ∀ x, ‖kf x‖ = ‖(K : α → E →L[ℂ] ℂ) x‖ := fun x =>
    (InnerProductSpace.toDual ℂ E).symm.norm_map _
  have hkfmeas : AEStronglyMeasurable kf μ :=
    (InnerProductSpace.toDual ℂ E).symm.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable K)
  set F : (exists_hilbertBasis ℂ E).choose → α → ℂ := fun i x =>
    (inner ℂ (L x) (b i) : ℂ) * (inner ℂ (b i) (kf x) : ℂ) with hF
  have hFmeas : ∀ i, AEStronglyMeasurable (F i) μ := by
    intro i
    exact (hLmeas.inner aestronglyMeasurable_const).mul
      (aestronglyMeasurable_const.inner hkfmeas)
  have hbnorm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hFptbound : ∀ i x, ‖F i x‖ ≤ ‖L x‖ * ‖kf x‖ := by
    intro i x
    rw [hF, norm_mul]
    have h1 : ‖(inner ℂ (L x) (b i) : ℂ)‖ ≤ ‖L x‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) (L x) (b i)
      rwa [hbnorm i, mul_one] at this
    have h2 : ‖(inner ℂ (b i) (kf x) : ℂ)‖ ≤ ‖kf x‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) (b i) (kf x)
      rwa [hbnorm i, one_mul] at this
    exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  have hmaj : Integrable (fun x => ‖L x‖ * ‖kf x‖) μ := by
    refine hint.congr ?_
    filter_upwards with x
    rw [hkfnorm x, mul_comm]
  have hFint : ∀ i, Integrable (F i) μ := by
    intro i
    refine Integrable.mono hmaj (hFmeas i) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hFptbound i x
  have hFsum : Summable fun i => ∫ x, ‖F i x‖ ∂μ := by
    refine summable_of_sum_le (fun i => integral_nonneg fun x => norm_nonneg _)
      (c := ∫ x, ‖L x‖ * ‖kf x‖ ∂μ) ?_
    intro u
    have hsum : (∑ i ∈ u, ∫ x, ‖F i x‖ ∂μ) = ∫ x, ∑ i ∈ u, ‖F i x‖ ∂μ :=
      (integral_finsetSum u fun i _ => (hFint i).norm).symm
    rw [hsum]
    refine integral_mono (integrable_finsetSum u fun i _ => (hFint i).norm) hmaj ?_
    intro x
    calc (∑ i ∈ u, ‖F i x‖)
        = ∑ i ∈ u, ‖(inner ℂ (L x) (b i) : ℂ)‖ * ‖(inner ℂ (b i) (kf x) : ℂ)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hF, norm_mul]
      _ ≤ ‖L x‖ * ‖kf x‖ := connes_finset_inner_bound b u (L x) (kf x)
  have hterm : ∀ i,
      (inner ℂ (connesKernelOperator μ K (b i)) (B (b i)) : ℂ) = ∫ x, F i x ∂μ := by
    intro i
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [connesKernelApply_ae μ K (b i), hL (b i)] with x h1 h2
    show (inner ℂ ((connesKernelApply μ K (b i) : α → ℂ) x)
      ((B (b i) : α → ℂ) x) : ℂ) = F i x
    rw [h1, h2, hF]
    have hKx : ((K : α → E →L[ℂ] ℂ) x) (b i) = (inner ℂ (kf x) (b i) : ℂ) := by
      rw [hkf, InnerProductSpace.toDual_symm_apply]
    rw [hKx, RCLike.inner_apply', inner_conj_symm]
    ring
  rw [ContinuousLinearMap.hsInner]
  calc (∑' i, (inner ℂ (connesKernelOperator μ K (b i)) (B (b i)) : ℂ))
      = ∑' i, ∫ x, F i x ∂μ := tsum_congr hterm
    _ = ∫ x, ∑' i, F i x ∂μ :=
        integral_tsum_of_summable_integral_norm hFint hFsum
    _ = ∫ x, (inner ℂ (L x) (kf x) : ℂ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact b.tsum_inner_mul_inner (L x) (kf x)

/-- **The hypotheses of the field pairing have models.**  Two Hilbert–Schmidt kernel operators
satisfy them: the row field of the second is `(toDual)⁻¹ ∘ L'`, and the product of the row norms
is integrable by Hölder.  The value agrees with the polarized energy of
`ConnesKernelTracePairing`, so the field pairing genuinely extends it. -/
theorem connes_hsInner_kernelOperator_field_of_kernel [TopologicalSpace.SeparableSpace E]
    (K L' : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.hsInner (connesKernelOperator μ K) (connesKernelOperator μ L')
      = ∫ x, (inner ℂ ((InnerProductSpace.toDual ℂ E).symm ((L' : α → E →L[ℂ] ℂ) x))
          ((InnerProductSpace.toDual ℂ E).symm ((K : α → E →L[ℂ] ℂ) x)) : ℂ) ∂μ := by
  set Lf : α → E := fun x => (InnerProductSpace.toDual ℂ E).symm
    ((L' : α → E →L[ℂ] ℂ) x) with hLf
  have hLmeas : AEStronglyMeasurable Lf μ :=
    (InnerProductSpace.toDual ℂ E).symm.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable L')
  have hLnorm : ∀ x, ‖Lf x‖ = ‖(L' : α → E →L[ℂ] ℂ) x‖ := fun x =>
    (InnerProductSpace.toDual ℂ E).symm.norm_map _
  have hL : ∀ e : E, ((connesKernelOperator μ L' e : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] fun x => (inner ℂ (Lf x) e : ℂ) := by
    intro e
    filter_upwards [connesKernelApply_ae μ L' e] with x hx
    show ((connesKernelApply μ L' e : α → ℂ) x) = _
    rw [hx, hLf, InnerProductSpace.toDual_symm_apply]
  have hKmem : MemLp (fun x => ‖(K : α → E →L[ℂ] ℂ) x‖) 2 μ :=
    (Lp.memLp K).norm
  have hLmem : MemLp (fun x => ‖(L' : α → E →L[ℂ] ℂ) x‖) 2 μ :=
    (Lp.memLp L').norm
  have hint : Integrable (fun x => ‖(K : α → E →L[ℂ] ℂ) x‖ * ‖Lf x‖) μ := by
    have hprod : Integrable
        (fun x => ‖(K : α → E →L[ℂ] ℂ) x‖ * ‖(L' : α → E →L[ℂ] ℂ) x‖) μ := by
      have h := MemLp.integrable_mul hKmem hLmem
      exact h.congr (Filter.Eventually.of_forall fun x => rfl)
    refine hprod.congr ?_
    filter_upwards with x
    rw [hLnorm x]
  exact connes_hsInner_kernelOperator_field μ K (connesKernelOperator μ L') Lf hL hLmeas hint

end

end GaloisForLFunctions.RHTower
