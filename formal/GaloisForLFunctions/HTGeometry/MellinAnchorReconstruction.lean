import GaloisForLFunctions.HTGeometry.FormationScopeCountermodels
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Anchor-separated reconstruction on the multiplicative monoid `[0, 1]`

On `K = [0, 1]` with multiplication, the Mellin characters `χ_s(α) = ∫ x^s dα(x)`,
`Re s > 0`, are continuous characters of `M([0, 1])`, since `(xy)^s = x^s y^s`.  For a positive
measure, `s ↦ χ_s(α)` is holomorphic on `Re s > 0` (differentiation under the integral,
`|x^s log x| < 1/Re s` on `(0, 1]`).

**Theorem 7.1.**  Let `F = Exp_⋆(zγ) ⋆ Π_j (δ_1 + zα_j)` and `F' = Exp_⋆(zγ') ⋆ Π_k (δ_1 + zβ_k)`
be decorated formations with positive dust and atoms, summable masses and atoms without mass at
`0`, and suppose that for some `t₀ > 0` the anchors `χ_{t₀}` of the nonzero atoms are pairwise
distinct within each formation.  If `F = F'`, the nonzero atoms correspond bijectively and the
dusts agree.

Applying `χ_t` gives `χ_t(F(z)) = e^{z χ_t(γ)} Π_j (1 + z χ_t(α_j))`, whose zeros are the points
`-1/χ_t(α_j)`.  At `t₀` the anchors match each nonzero atom `α_j` with a unique `β_k`.  Only
finitely many `β_k` have mass `≥ χ_{t₀}(α_j)/2`; by continuity in `t`, for `t` near `t₀` the zero
`-1/χ_t(α_j)` of `χ_t(F)` can only be matched by `β_k` itself, so `χ_t(α_j) = χ_t(β_k)` near `t₀`.
By the identity theorem they agree on `Re s > 0`, in particular at `s = 1, 2, …`; with no mass at
`0`, the substitution `x = e^{-u}` and Laplace determinacy give `α_j = β_k`.  Finally the first
cumulant `γ + Σ_j α_j` is determined by `F`, so the dusts agree.

The zero-atom exclusion is load-bearing: `χ_t(δ_0) = 0`, so `δ_{1/2} + δ_0` and `δ_{1/2}` have the
same Mellin images but different formations.
-/

open Filter Topology NormedSpace MeasureTheory Set Complex
open scoped unitInterval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

open MeasureAlgebra LaplaceTomography

attribute [local instance] ratAlgebra

/-! ### Mellin characters -/

/-- `x ↦ x^s` on `[0, 1]`, continuous for `Re s > 0`. -/
def powFun (s : ℂ) (hs : 0 < s.re) : C(I, ℂ) :=
  ⟨fun x => ((x : ℝ) : ℂ) ^ s, continuous_iff_continuousAt.2 fun x =>
    (continuousAt_cpow_const_of_re_pos (Or.inl (by simpa using x.2.1)) hs).comp
      (continuous_ofReal.comp continuous_subtype_val).continuousAt⟩

@[simp] theorem powFun_apply (s : ℂ) (hs : 0 < s.re) (x : I) :
    powFun s hs x = ((x : ℝ) : ℂ) ^ s := rfl

theorem norm_powFun_apply_le (s : ℂ) (hs : 0 < s.re) (x : I) : ‖powFun s hs x‖ ≤ 1 := by
  rw [powFun_apply]
  rcases eq_or_lt_of_le x.2.1 with h | h
  · rw [← h, ofReal_zero, zero_cpow (by rintro rfl; simp at hs), norm_zero]
    exact zero_le_one
  · rw [norm_cpow_eq_rpow_re_of_pos h]
    exact Real.rpow_le_one h.le x.2.2 hs.le

theorem norm_powFun_le (s : ℂ) (hs : 0 < s.re) : ‖powFun s hs‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 (norm_powFun_apply_le s hs)

theorem rightTransform_powFun (Ψ : MeasureAlgebra I) (s : ℂ) (hs : 0 < s.re) :
    rightTransform Ψ (powFun s hs) = Ψ (powFun s hs) • powFun s hs := by
  ext x
  rw [rightTransform_apply, ContinuousMap.smul_apply, smul_eq_mul, powFun_apply]
  have h : shift (powFun s hs) x = ((x : ℝ) : ℂ) ^ s • powFun s hs := by
    ext y
    rw [shift_apply, ContinuousMap.smul_apply, smul_eq_mul, powFun_apply, powFun_apply,
      Set.Icc.coe_mul, ofReal_mul, mul_cpow_ofReal_nonneg x.2.1 y.2.1]
  rw [h, map_smul, smul_eq_mul, mul_comm]

/-- The Mellin character `χ_s(Φ) = Φ(x^s)`, `Re s > 0`. -/
def mellinChar (s : ℂ) (hs : 0 < s.re) : MeasureAlgebra I →+* ℂ where
  toFun Φ := Φ (powFun s hs)
  map_one' := by simp
  map_mul' Φ Ψ := by rw [mul_apply, rightTransform_powFun, map_smul, smul_eq_mul, mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl

theorem mellinChar_apply (s : ℂ) (hs : 0 < s.re) (Φ : MeasureAlgebra I) :
    mellinChar s hs Φ = Φ (powFun s hs) := rfl

theorem norm_mellinChar_le (s : ℂ) (hs : 0 < s.re) (Φ : MeasureAlgebra I) :
    ‖mellinChar s hs Φ‖ ≤ ‖Φ‖ :=
  (le_opNorm Φ _).trans <| by
    simpa using mul_le_mul_of_nonneg_left (norm_powFun_le s hs) (norm_nonneg Φ)

theorem continuous_mellinChar (s : ℂ) (hs : 0 < s.re) : Continuous (mellinChar s hs) :=
  (evalAt (powFun s hs)).continuous

/-- The Mellin transform `s ↦ χ_s(Φ)` on `Re s > 0` (and `0` elsewhere). -/
def mellin (Φ : MeasureAlgebra I) (s : ℂ) : ℂ :=
  if hs : 0 < s.re then mellinChar s hs Φ else 0

theorem mellin_of_re_pos (Φ : MeasureAlgebra I) {s : ℂ} (hs : 0 < s.re) :
    mellin Φ s = mellinChar s hs Φ := dif_pos hs

theorem norm_mellin_le (Φ : MeasureAlgebra I) (s : ℂ) : ‖mellin Φ s‖ ≤ ‖Φ‖ := by
  unfold mellin
  split_ifs with hs
  · exact norm_mellinChar_le s hs Φ
  · simp

/-! ### Positive measures: integral form, positivity, holomorphy -/

theorem mellin_ofMeasure (μ : FiniteMeasure I) {s : ℂ} (hs : 0 < s.re) :
    mellin (ofMeasure μ) s = ∫ x, ((x : ℝ) : ℂ) ^ s ∂(μ : Measure I) := by
  rw [mellin_of_re_pos _ hs, mellinChar_apply, ofMeasure_apply]
  rfl

/-- For a real exponent the Mellin transform of a positive measure is `∫ x^t dμ ≥ 0`. -/
theorem mellin_ofMeasure_real (μ : FiniteMeasure I) {t : ℝ} (ht : 0 < t) :
    mellin (ofMeasure μ) t = ((∫ x, (x : ℝ) ^ t ∂(μ : Measure I) : ℝ) : ℂ) := by
  rw [mellin_ofMeasure μ (by simpa using ht), show ((∫ x, (x : ℝ) ^ t ∂(μ : Measure I) : ℝ) : ℂ) =
    ∫ x, (((x : ℝ) ^ t : ℝ) : ℂ) ∂(μ : Measure I) from integral_ofReal.symm]
  exact integral_congr_ae (ae_of_all _ fun x => (ofReal_cpow x.2.1 t).symm)

/-- A nonzero positive measure without mass at `0` has positive Mellin transform at real
`t > 0`. -/
theorem mellin_ofMeasure_pos (μ : FiniteMeasure I) (hμ : μ ≠ 0)
    (h0 : (μ : Measure I) {0} = 0) {t : ℝ} (ht : 0 < t) :
    0 < ∫ x, (x : ℝ) ^ t ∂(μ : Measure I) := by
  have hint : Integrable (fun x : I => (x : ℝ) ^ t) (μ : Measure I) :=
    Integrable.of_bound ((continuous_subtype_val.rpow_const fun _ =>
      Or.inr ht.le).aestronglyMeasurable) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg x.2.1 t)]
      exact Real.rpow_le_one x.2.1 x.2.2 ht.le)
  rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x => Real.rpow_nonneg x.2.1 t) hint]
  have hsupp : Function.support (fun x : I => (x : ℝ) ^ t) = {0}ᶜ := by
    ext x
    simp only [Function.mem_support, ne_eq, mem_compl_iff, mem_singleton_iff]
    rw [Real.rpow_eq_zero x.2.1 ht.ne']
    exact ⟨fun h hx => h (by rw [hx]; rfl), fun h hx => h (Subtype.ext hx)⟩
  rw [hsupp, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), h0, tsub_zero]
  refine pos_iff_ne_zero.2 fun h => hμ ?_
  exact (FiniteMeasure.mass_zero_iff μ).1 (by
    have := FiniteMeasure.ennreal_mass (μ := μ)
    rw [h] at this
    exact_mod_cast this)

/-- The Mellin transform of a finite positive measure is holomorphic on `Re s > 0`. -/
theorem differentiableOn_mellin_ofMeasure (μ : FiniteMeasure I) :
    DifferentiableOn ℂ (mellin (ofMeasure μ)) {s | 0 < s.re} := by
  intro s₀ hs₀
  set a := s₀.re
  have ha : 0 < a := hs₀
  have hball : ∀ s ∈ Metric.ball s₀ (a / 2), a / 2 < s.re := fun s hs => by
    have h1 := abs_re_le_norm (s - s₀)
    rw [← dist_eq_norm, sub_re] at h1
    have h2 := Metric.mem_ball.1 hs
    have := neg_abs_le (s.re - s₀.re)
    linarith
  set F : ℂ → I → ℂ := fun s x => ((x : ℝ) : ℂ) ^ s
  set F' : ℂ → I → ℂ := fun s x => ((x : ℝ) : ℂ) ^ s * log ((x : ℝ) : ℂ)
  have hderiv : ∀ x : I, ∀ s ∈ Metric.ball s₀ (a / 2), HasDerivAt (fun s => F s x) (F' s x) s := by
    intro x s hs
    have hs0 : s ≠ 0 := fun h => by have := hball s hs; rw [h, zero_re] at this; linarith
    rcases eq_or_lt_of_le x.2.1 with hx | hx
    · have hx' : ((x : ℝ) : ℂ) = 0 := by rw [← hx]; simp
      simp only [F, F', hx', log_zero, mul_zero]
      refine (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hs] with s' hs'
      exact zero_cpow fun h => by have := hball s' hs'; rw [h, zero_re] at this; linarith
    · exact (hasStrictDerivAt_const_cpow (Or.inl (by exact_mod_cast hx.ne'))).hasDerivAt
  have hbound : ∀ x : I, ∀ s ∈ Metric.ball s₀ (a / 2), ‖F' s x‖ ≤ 2 / a := by
    intro x s hs
    rcases eq_or_lt_of_le x.2.1 with hx | hx
    · have hx' : ((x : ℝ) : ℂ) = 0 := by rw [← hx]; simp
      simp only [F', hx', log_zero, mul_zero, norm_zero]
      positivity
    · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, ← ofReal_log hx.le, norm_real,
        Real.norm_eq_abs]
      have h1 := Real.abs_log_mul_self_rpow_lt (x : ℝ) s.re hx x.2.2 (by linarith [hball s hs])
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)] at h1
      calc (x : ℝ) ^ s.re * |Real.log x| = |Real.log x| * (x : ℝ) ^ s.re := mul_comm _ _
        _ ≤ 1 / s.re := h1.le
        _ ≤ 2 / a := by
            rw [div_le_div_iff₀ (by linarith [hball s hs]) ha]
            linarith [hball s hs]
  have hmeas : ∀ s, AEStronglyMeasurable (F s) (μ : Measure I) := fun s =>
    (Measurable.pow_const (by fun_prop) s).aestronglyMeasurable
  have hint : Integrable (F s₀) (μ : Measure I) := by
    refine Integrable.of_bound (hmeas s₀) 1 (ae_of_all _ fun x => ?_)
    exact norm_powFun_apply_le s₀ ha x
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ : Measure I))
    (F := F) (F' := F') (x₀ := s₀) (bound := fun _ => 2 / a)
    (Metric.ball_mem_nhds s₀ (by positivity))
    (Eventually.of_forall hmeas) hint
    (((Measurable.pow_const (by fun_prop) s₀).mul
      (measurable_log.comp (by fun_prop))).aestronglyMeasurable)
    (ae_of_all _ fun x s hs => hbound x s hs) (integrable_const _)
    (ae_of_all _ fun x s hs => hderiv x s hs)
  refine (h.2.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs₀] with s hs
  exact mellin_ofMeasure μ hs

/-! ### Uniqueness from local agreement -/

theorem isOpen_re_pos : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re

/-- Agreement on real points near `t₀` gives frequent agreement in the punctured complex
neighbourhood of `t₀`. -/
theorem frequently_eq_of_eventually_real {f g : ℂ → ℂ} {t₀ : ℝ}
    (h : ∀ᶠ t : ℝ in 𝓝 t₀, f t = g t) : ∃ᶠ s in 𝓝[≠] (t₀ : ℂ), f s = g s := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhdsWithin_iff.1 hU
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.1 h
  set d := min r ε / 2
  have hd : 0 < d := by positivity
  have hdr : d < r := by have := min_le_left r ε; simp only [d]; linarith
  have hdε : d < ε := by have := min_le_right r ε; simp only [d]; linarith
  refine ⟨((t₀ + d : ℝ) : ℂ), hrU ⟨?_, ?_⟩, hεh ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      add_sub_cancel_left, abs_of_pos hd]
    exact hdr
  · rw [mem_compl_singleton_iff, Ne, ofReal_inj]
    linarith
  · rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hd]
    exact hdε

/-- **Identity theorem for Mellin transforms**: agreement near a real point `t₀ > 0` gives
agreement on the whole half-plane `Re s > 0`. -/
theorem mellin_eqOn_of_eventually_eq {μ ν : FiniteMeasure I} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ᶠ t : ℝ in 𝓝 t₀, mellin (ofMeasure μ) t = mellin (ofMeasure ν) t) :
    EqOn (mellin (ofMeasure μ)) (mellin (ofMeasure ν)) {s | 0 < s.re} :=
  AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    ((differentiableOn_mellin_ofMeasure μ).analyticOnNhd isOpen_re_pos)
    ((differentiableOn_mellin_ofMeasure ν).analyticOnNhd isOpen_re_pos)
    (convex_halfSpace_re_gt 0).isPreconnected (by simpa using ht₀)
    (frequently_eq_of_eventually_real h)

theorem range_compactify : (range compactify)ᶜ = {(0 : I)} := by
  ext x
  simp only [mem_compl_iff, mem_range, not_exists, mem_singleton_iff]
  constructor
  · intro h
    by_contra hx
    have hpos : 0 < (x : ℝ) := lt_of_le_of_ne x.2.1 fun h' => hx (Subtype.ext h'.symm)
    refine h (Real.toNNReal (-Real.log x)) (Subtype.ext ?_)
    simp only [compactify]
    rw [Real.coe_toNNReal _ (neg_nonneg.2 (Real.log_nonpos x.2.1 x.2.2)), neg_neg,
      Real.exp_log hpos]
  · rintro rfl u hu
    have := congrArg Subtype.val hu
    simp only [compactify] at this
    exact (Real.exp_pos _).ne' this

/-- **Moment determinacy without the mass**: finite measures on `[0, 1]` without mass at `0`
whose moments of order `n ≥ 1` agree are equal (substitute `x = e^{-u}`). -/
theorem measure_eq_of_moments_succ {μ ν : Measure I} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ {0} = 0) (hν : ν {0} = 0)
    (h : ∀ n : ℕ, 1 ≤ n → ∫ x, (x : ℝ) ^ n ∂μ = ∫ x, (x : ℝ) ^ n ∂ν) : μ = ν := by
  have hres : ∀ ρ : Measure I, ρ {0} = 0 → (ρ.comap compactify).map compactify = ρ := by
    intro ρ hρ
    rw [measurableEmbedding_compactify.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem (ae_iff.2 ?_)
    rw [show {a | a ∉ range compactify} = (range compactify)ᶜ from rfl, range_compactify]
    exact hρ
  have hfin : ∀ ρ : Measure I, IsFiniteMeasure ρ → IsFiniteMeasure (ρ.comap compactify) :=
    fun ρ _ => ⟨by
      rw [measurableEmbedding_compactify.comap_apply]
      exact measure_lt_top _ _⟩
  haveI := hfin μ inferInstance
  haveI := hfin ν inferInstance
  have hc : μ.comap compactify = ν.comap compactify :=
    measure_eq_of_laplace_eq_succ fun n hn => by
      rw [← integral_pow_map_compactify, ← integral_pow_map_compactify, hres μ hμ, hres ν hν]
      exact h n hn
  rw [← hres μ hμ, ← hres ν hν, hc]

/-- Two finite measures without mass at `0` whose Mellin transforms agree near a real `t₀ > 0`
are equal. -/
theorem eq_of_mellin_eventually_eq {μ ν : FiniteMeasure I} (hμ : (μ : Measure I) {0} = 0)
    (hν : (ν : Measure I) {0} = 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ᶠ t : ℝ in 𝓝 t₀, mellin (ofMeasure μ) t = mellin (ofMeasure ν) t) : μ = ν := by
  have hEq := mellin_eqOn_of_eventually_eq ht₀ h
  have hmom : ∀ n : ℕ, 1 ≤ n →
      ∫ x, (x : ℝ) ^ n ∂(μ : Measure I) = ∫ x, (x : ℝ) ^ n ∂(ν : Measure I) := fun n hn => by
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := hEq (show (0 : ℝ) < ((n : ℝ) : ℂ).re by simpa using hpos)
    rw [mellin_ofMeasure_real μ hpos, mellin_ofMeasure_real ν hpos, ofReal_inj] at h1
    simpa only [Real.rpow_natCast] using h1
  exact FiniteMeasure.toMeasure_injective (measure_eq_of_moments_succ hμ hν hmom)

/-! ### Zeros of the Mellin images of a formation -/

/-- An absolutely convergent product `Π_j (1 + a_j)` vanishes exactly when a factor does. -/
theorem tprod_one_add_eq_zero_iff {a : ℕ → ℂ} (ha : Summable fun j => ‖a j‖) :
    ∏' j, (1 + a j) = 0 ↔ ∃ j, 1 + a j = 0 := by
  constructor
  · intro h
    by_contra hne
    exact tprod_one_add_ne_zero_of_summable (fun j hj => hne ⟨j, hj⟩) ha h
  · rintro ⟨j, hj⟩
    have hprod := (multipliable_one_add_of_summable ha).hasProd.tendsto_prod_nat
    refine tendsto_nhds_unique hprod (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop j] with n hn
    exact (Finset.prod_eq_zero (Finset.mem_range.2 hn) hj).symm

theorem mellinChar_smul (s : ℂ) (hs : 0 < s.re) (c : ℂ) (Φ : MeasureAlgebra I) :
    mellinChar s hs (c • Φ) = c * mellinChar s hs Φ := rfl

/-- `χ_s(F(z)) = e^{z χ_s(γ)} Π_j (1 + z χ_s(α_j))`. -/
theorem mellinChar_decorated {γ : MeasureAlgebra I} {α : ℕ → MeasureAlgebra I}
    (hα : Summable fun j => ‖α j‖) (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    mellinChar s hs (decorated γ α z) =
      Complex.exp (z * mellinChar s hs γ) * ∏' j, (1 + z * mellinChar s hs (α j)) := by
  have hprod := (multipliable_formation hα z).hasProd.map (mellinChar s hs)
    (continuous_mellinChar s hs)
  rw [decorated, map_mul, character_exp _ (continuous_mellinChar s hs), mellinChar_smul,
    ← hprod.tprod_eq]
  congr 1
  refine tprod_congr fun j => ?_
  simp [mellinChar_smul]

theorem summable_mellinChar {α : ℕ → MeasureAlgebra I} (hα : Summable fun j => ‖α j‖)
    (s : ℂ) (hs : 0 < s.re) (z : ℂ) : Summable fun j => ‖z * mellinChar s hs (α j)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_mellinChar_le s hs (α j)) (norm_nonneg z))
    (hα.mul_left ‖z‖)

/-- The zeros of `χ_s(F(z))` are the points `-1/χ_s(α_j)`, whatever the dust. -/
theorem mellinChar_decorated_eq_zero_iff {γ : MeasureAlgebra I} {α : ℕ → MeasureAlgebra I}
    (hα : Summable fun j => ‖α j‖) (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    mellinChar s hs (decorated γ α z) = 0 ↔ ∃ j, 1 + z * mellinChar s hs (α j) = 0 := by
  rw [mellinChar_decorated hα, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
  exact tprod_one_add_eq_zero_iff (summable_mellinChar hα s hs z)

/-- Equal formations have equal zero sets: every nonzero anchor `χ_s(α_j)` is an anchor
`χ_s(β_k)`. -/
theorem exists_mellinChar_eq {γ γ' : MeasureAlgebra I} {α β : ℕ → MeasureAlgebra I}
    (hα : Summable fun j => ‖α j‖) (hβ : Summable fun k => ‖β k‖)
    (hF : decorated γ α = decorated γ' β) (s : ℂ) (hs : 0 < s.re) {j : ℕ}
    (hj : mellinChar s hs (α j) ≠ 0) : ∃ k, mellinChar s hs (β k) = mellinChar s hs (α j) := by
  set c := mellinChar s hs (α j)
  have h0 : mellinChar s hs (decorated γ α (-c⁻¹)) = 0 :=
    (mellinChar_decorated_eq_zero_iff hα s hs _).2 ⟨j, by field_simp; ring⟩
  rw [hF] at h0
  obtain ⟨k, hk⟩ := (mellinChar_decorated_eq_zero_iff hβ s hs _).1 h0
  refine ⟨k, ?_⟩
  have h1 : c - mellinChar s hs (β k) = 0 := by
    have := congrArg (· * c) hk
    simp only [zero_mul] at this
    rw [← this]
    field_simp
    ring
  exact (sub_eq_zero.1 h1).symm

/-! ### Local matching of anchors and Theorem 7.1 -/

section Reconstruction

variable {γ γ' : MeasureAlgebra I} {α β : ℕ → MeasureAlgebra I}

theorem continuousAt_mellin_real {Φ : MeasureAlgebra I} (hΦ : IsPositive Φ) {t₀ : ℝ}
    (ht₀ : 0 < t₀) : ContinuousAt (fun t : ℝ => mellin Φ t) t₀ := by
  rw [← ofMeasure_toFiniteMeasure hΦ]
  exact ((differentiableOn_mellin_ofMeasure _).differentiableAt
    (isOpen_re_pos.mem_nhds (by simpa using ht₀))).continuousAt.comp continuous_ofReal.continuousAt

/-- A nonzero positive atom without mass at `0` has a positive real anchor. -/
theorem mellin_pos {Φ : MeasureAlgebra I} (hΦ : IsPositive Φ) (hΦ0 : Φ ≠ 0)
    (h0 : (toFiniteMeasure hΦ : Measure I) {0} = 0) {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ mellin Φ t = r := by
  refine ⟨_, mellin_ofMeasure_pos (toFiniteMeasure hΦ) (fun h => hΦ0 ?_) h0 ht, ?_⟩
  · rw [← ofMeasure_toFiniteMeasure hΦ, h, ofMeasure_zero]
  · rw [← mellin_ofMeasure_real _ ht, ofMeasure_toFiniteMeasure]

/-- **Local anchor matching.**  A nonzero atom `α_j` is matched, for all `t` near `t₀`, by a
single nonzero atom `β_k`: `χ_t(α_j) = χ_t(β_k)`. -/
theorem exists_eventually_mellin_eq (hα : ∀ j, IsPositive (α j)) (hβ : ∀ k, IsPositive (β k))
    (hsα : Summable fun j => ‖α j‖) (hsβ : Summable fun k => ‖β k‖)
    (hα0 : ∀ j, (toFiniteMeasure (hα j) : Measure I) {0} = 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hsepβ : ∀ i k, β i ≠ 0 → β k ≠ 0 → i ≠ k → mellin (β i) t₀ ≠ mellin (β k) t₀)
    (hF : decorated γ α = decorated γ' β) {j : ℕ} (hj : α j ≠ 0) :
    ∃ k, β k ≠ 0 ∧ ∀ᶠ t : ℝ in 𝓝 t₀, mellin (α j) t = mellin (β k) t := by
  have ht₀' : 0 < ((t₀ : ℂ)).re := by simpa using ht₀
  obtain ⟨r, hr, hc⟩ := mellin_pos (hα j) hj (hα0 j) ht₀
  have hcj : mellinChar _ ht₀' (α j) ≠ 0 := by
    rw [← mellin_of_re_pos _ ht₀', hc]; exact_mod_cast hr.ne'
  obtain ⟨k₀, hk₀⟩ := exists_mellinChar_eq hsα hsβ hF _ ht₀' hcj
  rw [← mellin_of_re_pos _ ht₀', ← mellin_of_re_pos _ ht₀'] at hk₀
  have hk₀0 : β k₀ ≠ 0 := by
    rintro h
    rw [h, hc] at hk₀
    simp [mellin, mellinChar_apply] at hk₀
    exact hr.ne' (by exact_mod_cast hk₀.symm)
  refine ⟨k₀, hk₀0, ?_⟩
  -- only finitely many atoms are heavy enough to reach the anchor
  have hB : {k | ¬ ‖β k‖ < r / 2}.Finite :=
    Filter.eventually_cofinite.1 (hsβ.tendsto_cofinite_zero.eventually (gt_mem_nhds (half_pos hr)))
  have hcont : ∀ k, ContinuousAt (fun t : ℝ => mellin (β k) t) t₀ := fun k =>
    continuousAt_mellin_real (hβ k) ht₀
  have hcontα := continuousAt_mellin_real (hα j) ht₀
  have hsep : ∀ k ∈ {k | ¬ ‖β k‖ < r / 2} \ {k₀},
      ∀ᶠ t : ℝ in 𝓝 t₀, mellin (β k) t ≠ mellin (α j) t := by
    intro k hk
    have hne : mellin (β k) t₀ ≠ mellin (α j) t₀ := by
      rw [← hk₀]
      by_cases hk0 : β k = 0
      · rw [hk0, hk₀, hc]
        simp [mellin, mellinChar_apply]
        exact_mod_cast hr.ne
      · exact hsepβ k k₀ hk0 hk₀0 (by simpa using hk.2)
    exact ((hcont k).sub hcontα).eventually_ne (sub_ne_zero.2 hne) |>.mono fun t ht h =>
      ht (sub_eq_zero.2 h)
  have hbig : ∀ᶠ t : ℝ in 𝓝 t₀, r / 2 < ‖mellin (α j) t‖ := by
    have := hcontα.norm.eventually (lt_mem_nhds (show r / 2 < ‖mellin (α j) t₀‖ by
      rw [hc, norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith))
    exact this
  filter_upwards [(hB.sdiff).eventually_all.2 hsep, hbig, lt_mem_nhds ht₀] with t hsept hbigt htpos
  have htpos' : 0 < ((t : ℂ)).re := by simpa using htpos
  have hne : mellinChar _ htpos' (α j) ≠ 0 := by
    rw [← mellin_of_re_pos _ htpos']
    intro h
    rw [h, norm_zero] at hbigt
    linarith
  obtain ⟨k, hk⟩ := exists_mellinChar_eq hsα hsβ hF _ htpos' hne
  rw [← mellin_of_re_pos _ htpos', ← mellin_of_re_pos _ htpos'] at hk
  by_cases hkB : ‖β k‖ < r / 2
  · exfalso
    have := (norm_mellin_le (β k) t).trans_lt hkB
    rw [hk] at this
    linarith
  · by_cases hkk : k = k₀
    · rw [← hkk, hk]
    · exact absurd hk (hsept k ⟨hkB, hkk⟩)

/-- Matched atoms are equal: their Mellin transforms agree near `t₀`, hence everywhere, hence
their moments of order `≥ 1` agree. -/
theorem eq_of_eventually_mellin_eq {Φ Ψ : MeasureAlgebra I} (hΦ : IsPositive Φ)
    (hΨ : IsPositive Ψ) (hΦ0 : (toFiniteMeasure hΦ : Measure I) {0} = 0)
    (hΨ0 : (toFiniteMeasure hΨ : Measure I) {0} = 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ᶠ t : ℝ in 𝓝 t₀, mellin Φ t = mellin Ψ t) : Φ = Ψ := by
  rw [← ofMeasure_toFiniteMeasure hΦ, ← ofMeasure_toFiniteMeasure hΨ] at h ⊢
  rw [eq_of_mellin_eventually_eq hΦ0 hΨ0 ht₀ h]

/-- Anchor separation makes the nonzero atoms pairwise distinct. -/
theorem injOn_of_anchor {α : ℕ → MeasureAlgebra I} {t₀ : ℝ}
    (hsep : ∀ i k, α i ≠ 0 → α k ≠ 0 → i ≠ k → mellin (α i) t₀ ≠ mellin (α k) t₀) :
    InjOn α {j | α j ≠ 0} := fun i hi k hk h => by
  by_contra hik
  exact hsep i k hi hk hik (by rw [h])

theorem image_subset_of_decorated_eq (hα : ∀ j, IsPositive (α j))
    (hβ : ∀ k, IsPositive (β k)) (hsα : Summable fun j => ‖α j‖)
    (hsβ : Summable fun k => ‖β k‖) (hα0 : ∀ j, (toFiniteMeasure (hα j) : Measure I) {0} = 0)
    (hβ0 : ∀ k, (toFiniteMeasure (hβ k) : Measure I) {0} = 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hsepβ : ∀ i k, β i ≠ 0 → β k ≠ 0 → i ≠ k → mellin (β i) t₀ ≠ mellin (β k) t₀)
    (hF : decorated γ α = decorated γ' β) :
    α '' {j | α j ≠ 0} ⊆ β '' {k | β k ≠ 0} := by
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨k, hk, hev⟩ := exists_eventually_mellin_eq hα hβ hsα hsβ hα0 ht₀ hsepβ hF hj
  exact ⟨k, hk, (eq_of_eventually_mellin_eq (hα j) (hβ k) (hα0 j) (hβ0 k) ht₀ hev).symm⟩

/-- **Theorem 7.1 (anchor-separated decorated reconstruction).**  Two decorated formations on
`[0, 1]` with positive atoms, summable masses, atoms without mass at `0`, and pairwise
distinct anchors `χ_{t₀}` of the nonzero atoms within each formation, that are equal as
measure-valued functions, have the same nonzero atoms (bijectively) and the same dust.  The dust
need not be positive. -/
theorem anchor_reconstruction (hα : ∀ j, IsPositive (α j)) (hβ : ∀ k, IsPositive (β k))
    (hsα : Summable fun j => ‖α j‖) (hsβ : Summable fun k => ‖β k‖)
    (hα0 : ∀ j, (toFiniteMeasure (hα j) : Measure I) {0} = 0)
    (hβ0 : ∀ k, (toFiniteMeasure (hβ k) : Measure I) {0} = 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hsepα : ∀ i k, α i ≠ 0 → α k ≠ 0 → i ≠ k → mellin (α i) t₀ ≠ mellin (α k) t₀)
    (hsepβ : ∀ i k, β i ≠ 0 → β k ≠ 0 → i ≠ k → mellin (β i) t₀ ≠ mellin (β k) t₀)
    (hF : decorated γ α = decorated γ' β) :
    (∃ e : {j // α j ≠ 0} ≃ {k // β k ≠ 0}, ∀ j, β (e j) = α j) ∧ γ = γ' := by
  have h1 := image_subset_of_decorated_eq hα hβ hsα hsβ hα0 hβ0 ht₀ hsepβ hF
  have h2 := image_subset_of_decorated_eq hβ hα hsβ hsα hβ0 hα0 ht₀ hsepα hF.symm
  have hinjα := injOn_of_anchor hsepα
  have hinjβ := injOn_of_anchor hsepβ
  -- the matching map
  have hmatch : ∀ j : {j // α j ≠ 0}, ∃ k : {k // β k ≠ 0}, β k = α j := fun j => by
    obtain ⟨k, hk, hkj⟩ := h1 ⟨j, j.2, rfl⟩
    exact ⟨⟨k, hk⟩, hkj⟩
  choose f hf using hmatch
  have hfinj : Function.Injective f := fun i j hij => Subtype.ext (hinjα i.2 j.2 (by
    rw [← hf i, ← hf j, hij]))
  have hfsurj : Function.Surjective f := fun k => by
    obtain ⟨j, hj, hjk⟩ := h2 ⟨k, k.2, rfl⟩
    refine ⟨⟨j, hj⟩, Subtype.ext (hinjβ (f ⟨j, hj⟩).2 k.2 ?_)⟩
    rw [hf, hjk]
  set e := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨⟨e, fun j => hf j⟩, ?_⟩
  -- the dusts agree through the first cumulant
  obtain ⟨htot, -⟩ := total_and_powerSums_eq_of_decorated_eq hsα hsβ one_pos
    fun z _ => congrFun hF z
  have hsum : ∑' j, α j = ∑' k, β k := by
    rw [← tsum_subtype_eq_of_support_subset (s := {j | α j ≠ 0}) (fun j hj => hj),
      ← tsum_subtype_eq_of_support_subset (s := {k | β k ≠ 0}) (fun k hk => hk)]
    calc ∑' x : {j | α j ≠ 0}, α x = ∑' x : {j // α j ≠ 0}, β (e x) :=
          tsum_congr fun x => (hf x).symm
      _ = ∑' y : {k // β k ≠ 0}, β y := e.tsum_eq fun y => β y
  rw [hsum] at htot
  exact add_right_cancel htot

end Reconstruction

/-! ### The zero-atom exclusion is load-bearing -/

/-- Mellin characters annihilate the Dirac mass at the absorbing zero. -/
theorem mellinChar_dirac_zero (s : ℂ) (hs : 0 < s.re) :
    mellinChar s hs (ofMeasure (diracMeasure (0 : I))) = 0 := by
  rw [mellinChar_apply, ofMeasure_diracMeasure, powFun_apply]
  simp only [Set.Icc.coe_zero, ofReal_zero]
  exact zero_cpow fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs

/-- **Countermodel 8.**  The single-atom formations with atoms `δ_{1/2} + δ_0` and `δ_{1/2}` have
the same image under every Mellin character, yet differ. -/
theorem zeroAtom_counterexample :
    let a : MeasureAlgebra I := ofMeasure (diracMeasure ⟨1 / 2, by norm_num, by norm_num⟩)
    let b : MeasureAlgebra I := ofMeasure (diracMeasure (0 : I))
    (∀ (s : ℂ) (hs : 0 < s.re) (z : ℂ), mellinChar s hs (formation ![a + b] z) =
      mellinChar s hs (formation ![a] z)) ∧ formation ![a + b] ≠ formation ![a] := by
  intro a b
  refine ⟨fun s hs z => ?_, fun h => ?_⟩
  · simp [formation, mellinChar_smul, map_add, mellinChar_dirac_zero s hs, b]
  · have := congrArg (fun F => massHom (F 1)) h
    simp [formation, massHom_apply, a, b, ofMeasure_diracMeasure] at this

end GaloisForLFunctions.HTGeometry.FormationDust
