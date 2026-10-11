import GaloisForLFunctions.HTGeometry.QuadraticTransportCost

/-! Signed quadratic cancellation removes the half-line support requirement from quantile transport. -/

open MeasureTheory GaloisForLFunctions.HTGeometry Filter Set
open scoped Topology

noncomputable section
namespace RHTower

theorem finiteWeil_signed_quadratic_error_bound (x y : ℝ) :
    (x - y) ^ 2 ≤ 2 * |x ^ 2 - y ^ 2| + min ((x - y) ^ 2) (4 * y ^ 2) := by
  by_cases h : (x - y) ^ 2 ≤ 4 * y ^ 2
  · rw [min_eq_left h]
    nlinarith only [abs_nonneg (x ^ 2 - y ^ 2)]
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
    nlinarith only [le_abs_self (x ^ 2 - y ^ 2), sq_nonneg (x + y)]

theorem finiteWeil_tendsto_integral_signed_sq_sub {α : Type*} [MeasurableSpace α]
    {m : Measure α} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → α → ℝ} {g : α → ℝ}
    (hfm : ∀ i, AEStronglyMeasurable (f i) m) (hgm : AEStronglyMeasurable g m)
    (hfi : ∀ i, Integrable (fun x => f i x ^ 2) m) (hgi : Integrable (fun x => g x ^ 2) m)
    (hae : ∀ᵐ x ∂m, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hmom : Tendsto (fun i => ∫ x, f i x ^ 2 ∂m) l (𝓝 (∫ x, g x ^ 2 ∂m))) :
    Tendsto (fun i => ∫ x, (f i x - g x) ^ 2 ∂m) l (𝓝 0) := by
  let H (i : ι) (x : α) := min ((f i x - g x) ^ 2) (4 * g x ^ 2)
  have hH0 (i : ι) (x : α) : 0 ≤ H i x := by
    exact le_min (sq_nonneg _) (by positivity)
  have hHm (i : ι) : AEStronglyMeasurable (H i) m :=
    ((((hfm i).sub hgm).pow 2).aemeasurable.min
      ((hgi.const_mul 4).aemeasurable)).aestronglyMeasurable
  have hHbound (i : ι) (x : α) : ‖H i x‖ ≤ 4 * g x ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 i x)]
    exact min_le_right _ _
  have hHi (i : ι) : Integrable (H i) m := by
    refine (hgi.const_mul 4).mono (hHm i) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hH0 i x),
      abs_of_nonneg (by positivity : 0 ≤ 4 * g x ^ 2)]
    exact min_le_right _ _
  have hHlim : Tendsto (fun i => ∫ x, H i x ∂m) l (𝓝 0) := by
    have h : Tendsto (fun i => ∫ x, H i x ∂m) l (𝓝 (∫ _ : α, (0 : ℝ) ∂m)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => 4 * g x ^ 2)
        (Eventually.of_forall hHm)
        (Eventually.of_forall fun i => Eventually.of_forall (hHbound i)) (hgi.const_mul 4) ?_
      filter_upwards [hae] with x hx
      have h := ((hx.sub (tendsto_const_nhds (x := g x))).pow 2).min
        (tendsto_const_nhds (x := 4 * g x ^ 2))
      rw [sub_self, show (0 : ℝ) ^ 2 = 0 by norm_num,
        min_eq_left (by positivity : (0 : ℝ) ≤ 4 * g x ^ 2)] at h
      exact h
    simpa only [integral_zero] using h
  have hsq : Tendsto (fun i => ∫ x, |f i x ^ 2 - g x ^ 2| ∂m) l (𝓝 0) := by
    refine tendsto_integral_abs_sub_of_tendsto hfi hgi
      (fun i => Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall fun x => sq_nonneg _) ?_ hmom
    filter_upwards [hae] with x hx
    exact hx.pow 2
  have hdiff (i : ι) : Integrable (fun x => (f i x - g x) ^ 2) m := by
    refine (((hfi i).const_mul 2).add (hgi.const_mul 2)).mono
      (((hfm i).sub hgm).pow 2) (Eventually.of_forall fun x => ?_)
    change ‖(f i x - g x) ^ 2‖ ≤ ‖2 * f i x ^ 2 + 2 * g x ^ 2‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ 2 * f i x ^ 2 + 2 * g x ^ 2)]
    simpa only [sq_abs] using sq_abs_sub_le_two_mul_sq_add (f i x) (g x)
  have hlim : Tendsto (fun i => 2 * (∫ x, |f i x ^ 2 - g x ^ 2| ∂m) + ∫ x, H i x ∂m)
      l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hsq.const_mul 2).add hHlim
  refine squeeze_zero (fun i => integral_nonneg fun x => sq_nonneg _) (fun i => ?_) hlim
  calc
    _ ≤ ∫ x, 2 * |f i x ^ 2 - g x ^ 2| + H i x ∂m :=
      integral_mono (hdiff i) ((((hfi i).sub hgi).abs.const_mul 2).add (hHi i))
        (fun x => finiteWeil_signed_quadratic_error_bound (f i x) (g x))
    _ = _ := by
      have hi : Integrable (fun x => 2 * |f i x ^ 2 - g x ^ 2|) m :=
        ((hfi i).sub hgi).abs.const_mul 2
      rw [integral_add hi (hHi i), integral_const_mul]

theorem finiteWeil_tendsto_monotoneCoupling_signed_sq {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μ : ι → Measure ℝ) (ν : Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (hint : ∀ i, Integrable (fun x : ℝ => x ^ 2) (μ i))
    (hintν : Integrable (fun x : ℝ => x ^ 2) ν)
    (hae : ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun i => quantile (μ i) p) l (𝓝 (quantile ν p)))
    (hmom : Tendsto (fun i => ∫ x, x ^ 2 ∂(μ i)) l (𝓝 (∫ x, x ^ 2 ∂ν))) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ i) ν)) l (𝓝 0) := by
  have hmomQ : Tendsto (fun i => ∫ p in Ioo (0 : ℝ) 1, quantile (μ i) p ^ 2) l
      (𝓝 (∫ p in Ioo (0 : ℝ) 1, quantile ν p ^ 2)) := by
    rw [integral_quantile_sq_eq_second_moment ν]
    exact hmom.congr fun i => (integral_quantile_sq_eq_second_moment (μ i)).symm
  have h := finiteWeil_tendsto_integral_signed_sq_sub
    (fun i => (measurable_quantile (μ i)).aestronglyMeasurable)
    (measurable_quantile ν).aestronglyMeasurable
    (fun i => integrableOn_quantile_sq (μ i) (hint i)) (integrableOn_quantile_sq ν hintν) hae hmomQ
  refine h.congr fun i => ?_
  rw [integral_monotoneCoupling_sq_sub]
  simp only [sq_abs]

end RHTower
