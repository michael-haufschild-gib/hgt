import GaloisForLFunctions.RHTower.FokasLenellsUniformRH

/-!
# The Cauchy reconstruction as a contracting Hardy semigroup

The one-sided Fourier multiplier behind the paper's Cauchy operator composes
by adding nonnegative heights. Its two half-plane components annihilate one
another, are self-adjoint contractions, and vanish strongly at infinite height.
The actual RH slices are obtained by applying this propagation to their own
Hardy boundary corrections. Thus the analytic realization inherits semigroup
dissipation and strong decay, in addition to pointwise normalization.
-/

open MeasureTheory Complex Matrix Set Filter Topology
namespace RHTower.FokasLenells
noncomputable section

/-- Adding absolute heights multiplies the one-sided exponential symbols exactly. -/
theorem cauchyDamping_mul (upper : Bool) (h k s : ℝ) :
    cauchyDamping upper h s*cauchyDamping upper k s = cauchyDamping upper (|h|+|k|) s := by
  by_cases hs : s ∈ cauchyRay upper
  · simp only [cauchyDamping,Set.indicator_of_mem hs,abs_of_nonneg (add_nonneg (abs_nonneg h) (abs_nonneg k))]
    rw [← Complex.ofReal_mul,← Real.exp_add]
    apply congrArg (fun r : ℝ => (Real.exp r : ℂ))
    ring
  · simp only [cauchyDamping,Set.indicator_of_notMem hs,zero_mul]

/-- The two Hardy rays are disjoint, so opposite damping symbols annihilate each other. -/
theorem cauchyDamping_opposite_mul (upper : Bool) (h k s : ℝ) :
    cauchyDamping (!upper) h s*cauchyDamping upper k s = 0 := by
  by_cases hs : s ∈ cauchyRay upper
  · have hn : s ∉ cauchyRay (!upper) := by
      cases upper <;> simp only [cauchyRay,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        Set.mem_Ioi,Set.mem_Iio] at hs ⊢ <;> linarith
    rw [cauchyDamping,Set.indicator_of_notMem hn,zero_mul]
  · simp only [cauchyDamping,Set.indicator_of_notMem hs,mul_zero]

/-- The datum multipliers form a semigroup after height is made nonnegative. -/
theorem dampedCauchyDatum_composition (upper : Bool) (h k : ℝ) (u : SoninL2) :
    dampedCauchyDatum upper h (dampedCauchyDatum upper k u) = dampedCauchyDatum upper (|h|+|k|) u := by
  apply Lp.ext
  filter_upwards [dampedCauchyDatum_ae upper h (dampedCauchyDatum upper k u),
    dampedCauchyDatum_ae upper k u,dampedCauchyDatum_ae upper (|h|+|k|) u] with s h1 h2 h3
  rw [h1,h2,h3,← mul_assoc,cauchyDamping_mul]

theorem dampedCauchyDatum_opposite_composition (upper : Bool) (h k : ℝ) (u : SoninL2) :
    dampedCauchyDatum (!upper) h (dampedCauchyDatum upper k u) = 0 := by
  apply Lp.ext
  filter_upwards [dampedCauchyDatum_ae (!upper) h (dampedCauchyDatum upper k u),
    dampedCauchyDatum_ae upper k u,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with s h1 h2 h0
  rw [h1,h2,h0,← mul_assoc,cauchyDamping_opposite_mul,zero_mul]
  rfl

/-- The real one-sided multiplier is self-adjoint on the corpus's L² carrier. -/
theorem dampedCauchyDatum_inner (upper : Bool) (h : ℝ) (u v : SoninL2) :
    inner ℂ (dampedCauchyDatum upper h u) v = inner ℂ u (dampedCauchyDatum upper h v) := by
  apply lpBoundedMulCLM_inner_real (measurable_cauchyDamping upper h) zero_le_one
    (norm_cauchyDamping_le_one upper h)
  intro s
  by_cases hs : s ∈ cauchyRay upper
  · simp only [cauchyDamping,Set.indicator_of_mem hs,Complex.conj_ofReal]
  · simp only [cauchyDamping,Set.indicator_of_notMem hs,map_zero]

/-- Unsigned propagation into a fixed Hardy half-plane. -/
def hardyPropagation (upper : Bool) (h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  fourierUnitary.toLinearIsometry.toContinuousLinearMap.comp
    ((dampedCauchyDatum upper h).comp fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap)

theorem hardyPropagation_bound (upper : Bool) (h : ℝ) (u : SoninL2) :
    ‖hardyPropagation upper h u‖ ≤ ‖u‖ := by
  change ‖fourierUnitary (dampedCauchyDatum upper h (fourierUnitary.symm u))‖ ≤ _
  simpa only [fourierUnitary.norm_map,fourierUnitary.symm.norm_map] using
    dampedCauchyDatum_bound upper h (fourierUnitary.symm u)

/-- Fourier transport preserves the exact height composition law. -/
theorem hardyPropagation_composition (upper : Bool) (h k : ℝ) (u : SoninL2) :
    hardyPropagation upper h (hardyPropagation upper k u) = hardyPropagation upper (|h|+|k|) u := by
  change fourierUnitary (dampedCauchyDatum upper h (fourierUnitary.symm
    (fourierUnitary (dampedCauchyDatum upper k (fourierUnitary.symm u))))) = _
  rw [fourierUnitary.symm_apply_apply,dampedCauchyDatum_composition]
  rfl

theorem hardyPropagation_opposite_composition (upper : Bool) (h k : ℝ) (u : SoninL2) :
    hardyPropagation (!upper) h (hardyPropagation upper k u) = 0 := by
  change fourierUnitary (dampedCauchyDatum (!upper) h (fourierUnitary.symm
    (fourierUnitary (dampedCauchyDatum upper k (fourierUnitary.symm u))))) = 0
  rw [fourierUnitary.symm_apply_apply,dampedCauchyDatum_opposite_composition,map_zero]

/-- The Hardy propagation is self-adjoint in the physical L² coordinate. -/
theorem hardyPropagation_inner (upper : Bool) (h : ℝ) (u v : SoninL2) :
    inner ℂ (hardyPropagation upper h u) v = inner ℂ u (hardyPropagation upper h v) := by
  rw [← fourierUnitary.symm.inner_map_map (hardyPropagation upper h u) v,
    ← fourierUnitary.symm.inner_map_map u (hardyPropagation upper h v)]
  change inner ℂ (fourierUnitary.symm (fourierUnitary (dampedCauchyDatum upper h (fourierUnitary.symm u))))
      (fourierUnitary.symm v) = inner ℂ (fourierUnitary.symm u)
      (fourierUnitary.symm (fourierUnitary (dampedCauchyDatum upper h (fourierUnitary.symm v))))
  simp only [fourierUnitary.symm_apply_apply,dampedCauchyDatum_inner]

/-- Advancing the nonnegative height cannot increase Hardy L² energy. -/
theorem hardyPropagation_height_dissipation (upper : Bool) (h k : ℝ) (u : SoninL2) :
    ‖hardyPropagation upper (|h|+|k|) u‖ ≤ ‖hardyPropagation upper k u‖ := by
  rw [← hardyPropagation_composition]
  exact hardyPropagation_bound upper h _

/-- The Cauchy trace is the Hardy propagation with the lower-half-plane Plemelj sign. -/
theorem cauchyTrace_eq_signed_propagation (u : SoninL2) (upper : Bool) (h : ℝ) :
    cauchyTrace u upper h = (if upper then (1:ℂ) else -1) • hardyPropagation upper h u := rfl

/-- Both Hardy components together reproduce the identity at height zero. -/
theorem hardyPropagation_zero_sum (u : SoninL2) :
    hardyPropagation true 0 u+hardyPropagation false 0 u = u := by
  change fourierUnitary (dampedCauchyDatum true 0 (fourierUnitary.symm u))+
    fourierUnitary (dampedCauchyDatum false 0 (fourierUnitary.symm u)) = u
  rw [← map_add,dampedCauchyDatum_zero,dampedCauchyDatum_zero]
  simp only [cauchyRay,Bool.false_eq_true,↓reduceIte]
  rw [cauchyRayCutoff_sum,fourierUnitary.apply_symm_apply]

/-- Every fixed one-sided damping symbol vanishes at infinite height, including the omitted spectral origin. -/
theorem cauchyDamping_tendsto_atTop (upper : Bool) (s : ℝ) :
    Tendsto (fun h => cauchyDamping upper h s) atTop (𝓝 0) := by
  by_cases hs : s ∈ cauchyRay upper
  · have hn : s ≠ 0 := by
      cases upper <;> simp only [cauchyRay,Bool.false_eq_true,↓reduceIte,Set.mem_Ioi,Set.mem_Iio] at hs
      · exact hs.ne'
      · exact hs.ne
    have hc : -2*Real.pi*|s| < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hn)
    have ht : Tendsto (fun h : ℝ => -2*Real.pi*h*|s|) atTop atBot := by
      convert (tendsto_id.const_mul_atTop_of_neg hc : Tendsto (fun h : ℝ => (-2*Real.pi*|s|)*h) atTop atBot) using 1
      funext h
      ring
    have he := (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp ht)
    have hh : (fun h : ℝ => ((Real.exp (-2*Real.pi*h*|s|) : ℝ) : ℂ)) =ᶠ[atTop]
        (fun h => cauchyDamping upper h s) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with h hh
      rw [cauchyDamping,Set.indicator_of_mem hs,abs_of_nonneg hh]
    simpa only [Complex.ofReal_zero] using he.congr' hh
  · simp only [cauchyDamping,Set.indicator_of_notMem hs]
    exact tendsto_const_nhds

/-- Dominated multiplier convergence gives strong vanishing of every L² datum at infinite height. -/
theorem dampedCauchyDatum_tendsto_atTop (upper : Bool) (u : SoninL2) :
    Tendsto (fun h => dampedCauchyDatum upper h u) atTop (𝓝 0) := by
  let Z := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_const (a := (0:ℂ))) zero_le_one (fun s : ℝ => by simp)
  have hz : Z u = 0 := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (measurable_const (a := (0:ℂ))) zero_le_one (fun s : ℝ => by simp) u,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with s hs h0
    rw [hs,h0,zero_mul]
    rfl
  have ht := tendsto_lpBoundedMulCLM_apply (measurable_cauchyDamping upper)
    (measurable_const (a := (0:ℂ))) zero_le_one (norm_cauchyDamping_le_one upper)
    (fun s : ℝ => by simp) (cauchyDamping_tendsto_atTop upper) u
  change Tendsto (fun h => dampedCauchyDatum upper h u) atTop (𝓝 (Z u)) at ht
  rwa [hz] at ht

theorem hardyPropagation_tendsto_atTop (upper : Bool) (u : SoninL2) :
    Tendsto (fun h => hardyPropagation upper h u) atTop (𝓝 0) := by
  have ht := (fourierUnitary.continuous.tendsto 0).comp
    (dampedCauchyDatum_tendsto_atTop upper (fourierUnitary.symm u))
  change Tendsto (fun h => hardyPropagation upper h u) atTop (𝓝 (fourierUnitary 0)) at ht
  simpa only [map_zero] using ht

/-- Cauchy traces disappear strongly at infinite height, for every L² input. -/
theorem cauchyTrace_tendsto_atTop (u : SoninL2) (upper : Bool) :
    Tendsto (fun h => cauchyTrace u upper h) atTop (𝓝 0) := by
  have ht := (hardyPropagation_tendsto_atTop upper u).const_smul (if upper then (1:ℂ) else -1)
  simpa only [smul_zero,cauchyTrace_eq_signed_propagation] using ht

/-- The actual horizontal slices of a Cauchy integral vanish in L² at infinite logarithmic height. -/
theorem cauchySlice_tendsto_atTop (u : SoninL2) (upper : Bool) :
    Tendsto (fun a => cauchySlice u upper a) atTop (𝓝 0) := by
  exact ((cauchyTrace_tendsto_atTop u upper).comp Real.tendsto_exp_atTop).congr
    (fun a => (cauchySlice_eq_trace u upper a).symm)

/-- Every row of the actual normalized RH reconstruction tends to zero in the Hardy L² norm at vertical infinity. -/
theorem directAnalyticSlice_tendsto_atTop (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (fun a => directAnalyticSlice q t x i upper a) atTop (𝓝 0) :=
  (cauchySlice_tendsto_atTop (directRHDensity q t x i).1 upper).prodMk_nhds
    (cauchySlice_tendsto_atTop (directRHDensity q t x i).2 upper)


/-- The propagation depends only on nonnegative height. -/
theorem hardyPropagation_abs (upper : Bool) (h : ℝ) (u : SoninL2) :
    hardyPropagation upper |h| u = hardyPropagation upper h u := by
  have hd : dampedCauchyDatum upper |h| = dampedCauchyDatum upper h := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [dampedCauchyDatum_ae upper |h| v,dampedCauchyDatum_ae upper h v] with s h1 h2
    rw [h1,h2]
    simp only [cauchyDamping,abs_abs]
  change fourierUnitary (dampedCauchyDatum upper |h| (fourierUnitary.symm u)) = _
  rw [hd]
  rfl

/-- The Cauchy trace at every height is uniquely determined by propagating its own Hardy boundary value. -/
theorem cauchyTrace_eq_propagated_boundary (u : SoninL2) (upper : Bool) (h : ℝ) :
    cauchyTrace u upper h = hardyPropagation upper h (cauchyTrace u upper 0) := by
  rw [cauchyTrace_eq_signed_propagation,cauchyTrace_eq_signed_propagation,map_smul,
    hardyPropagation_composition,abs_zero,add_zero,hardyPropagation_abs]

/-- Each actual RH slice is the Hardy propagation of its own uniquely constructed boundary correction. -/
theorem directAnalyticSlice_eq_boundary_propagation (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directAnalyticSlice q t x i upper a =
      let b := if upper then directUpperCorrection q t x i else directLowerCorrection q t x i
      (hardyPropagation upper (Real.exp a) b.1,hardyPropagation upper (Real.exp a) b.2) := by
  have he := directTrace_zero q t x i upper
  apply Prod.ext
  · change cauchySlice (directRHDensity q t x i).1 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.fst he)
  · change cauchySlice (directRHDensity q t x i).2 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.snd he)

/-- Every interior Hardy norm is bounded by the norm of the corresponding actual boundary correction. -/
theorem directAnalyticSlice_boundary_norm_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSlice q t x i upper a‖ ≤
      ‖if upper then directUpperCorrection q t x i else directLowerCorrection q t x i‖ := by
  rw [directAnalyticSlice_eq_boundary_propagation]
  exact max_le_max (hardyPropagation_bound upper (Real.exp a) _) (hardyPropagation_bound upper (Real.exp a) _)

end
end RHTower.FokasLenells
