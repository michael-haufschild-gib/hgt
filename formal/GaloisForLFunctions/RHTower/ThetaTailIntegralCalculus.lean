import GaloisForLFunctions.RHTower.ThetaTailScalingAsymptotics

/-!
# Tail-integral calculus at the theta tail

For `f` with the theta tail, let `(I g)(x) = ∫₀^∞ g(x+t) dt` and say `g = O(e^{-2Px} f)` when
`‖g‖ ≤ C e^{-2Px} f` near `+∞`.

* `I` gains one order and the outward sine operator `T_β g = β ∫₀^∞ sin(βt) g(x+t) dt` gains two.
* **Shear Fubini**: `∫₀^∞ φ(u) ∫₀^∞ ψ(s) g(x+u+s) = ∫₀^∞ (∫₀^t φ(u) ψ(t−u) du) g(x+t)`; hence
  Cauchy's formula `I²g = ∫₀^∞ t g(·+t)` and the **resolvent identity** `T_β g = β² I²(g − T_β g)`.
* **Tail series**: `g ∼ Σ a_m I^m f` means `g − Σ_{m<P} a_m I^m f = O(e^{-2Px} f)` for all `P`.
  Then `I g ∼ X a` and `T_β g ∼ σ_β a` with `σ_β = β²X²/(1 + β²X²)`.
* A list division `T_L f` has symbol `∏ σ_β`, and the partial-fraction combination realizing `e`
  has a symbol `ρ` with `ρ · ∏(1 + β²X²) = ∏β² · X^{2|L|} e(−1/X²)`: the expansion at `w = 0` of
  `e(−1/w²)/P_L(−1/w²)`, i.e. the Laurent expansion of `e(−s²)/P_L(−s²)` at `s = ∞`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Tail integrals and relative smallness -/

section General

variable {E : Type*} [NormedAddCommGroup E]

/-- `g = O(e^{-2Px} f)` at `+∞`. -/
def TailSmall (f : ℝ → ℝ) (P : ℕ) (g : ℝ → E) : Prop :=
  ∃ C, ∀ᶠ x in atTop, ‖g x‖ ≤ C * Real.exp (-(2 * P * x)) * f x

section Integral

variable [NormedSpace ℝ E]

/-- The tail integral `(I g)(x) = ∫₀^∞ g(x+t) dt = ∫_x^∞ g`. -/
def tailIntegral (g : ℝ → E) (x : ℝ) : E := ∫ t in Ioi (0 : ℝ), g (x + t)

theorem stronglyMeasurable_tailIntegral {g : ℝ → E} (hg : StronglyMeasurable g) :
    StronglyMeasurable (tailIntegral g) :=
  (hg.comp_measurable (measurable_fst.add measurable_snd)).integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))

theorem tailIntegral_congr {g g' : ℝ → E} {X x : ℝ} (h : ∀ y, X ≤ y → g y = g' y) (hx : X ≤ x) :
    tailIntegral g x = tailIntegral g' x :=
  setIntegral_congr_fun measurableSet_Ioi fun t ht => h _ (by have : (0 : ℝ) < t := ht; linarith)

end Integral

namespace TailSmall

variable {f : ℝ → ℝ} {P : ℕ} {g g' : ℝ → E}

theorem congr (h : TailSmall f P g) (h' : ∀ᶠ x in atTop, g x = g' x) : TailSmall f P g' := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, by filter_upwards [hC, h'] with x hx hx'; rwa [← hx']⟩

theorem zero : TailSmall f P (0 : ℝ → E) := ⟨0, Eventually.of_forall fun x => by simp⟩

theorem add (h : TailSmall f P g) (h' : TailSmall f P g') : TailSmall f P fun x => g x + g' x := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', ?_⟩
  filter_upwards [hC, hC'] with x hx hx'
  calc ‖g x + g' x‖ ≤ ‖g x‖ + ‖g' x‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem const_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] (h : TailSmall f P g) (c : 𝕜) :
    TailSmall f P fun x => c • g x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖c‖ * C, ?_⟩
  filter_upwards [hC] with x hx
  rw [norm_smul]
  calc ‖c‖ * ‖g x‖ ≤ ‖c‖ * (C * Real.exp (-(2 * P * x)) * f x) :=
        mul_le_mul_of_nonneg_left hx (norm_nonneg c)
    _ = _ := by ring

theorem neg (h : TailSmall f P g) : TailSmall f P fun x => -g x := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, by filter_upwards [hC] with x hx; rwa [norm_neg]⟩

theorem sub (h : TailSmall f P g) (h' : TailSmall f P g') : TailSmall f P fun x => g x - g' x :=
  (h.add h'.neg).congr (Eventually.of_forall fun x => by simp [sub_eq_add_neg])

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → E} (h : ∀ i ∈ s, TailSmall f P (G i)) :
    TailSmall f P fun x => ∑ i ∈ s, G i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (zero (f := f) (P := P)).congr (Eventually.of_forall fun x => by simp)
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr (Eventually.of_forall fun x => ?_)
    rw [Finset.sum_insert hi]

theorem mono {P' : ℕ} (h : TailSmall f P g) (hP : P' ≤ P) (hf : ∀ᶠ x in atTop, 0 ≤ f x) :
    TailSmall f P' g := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|C|, ?_⟩
  filter_upwards [hC, hf, eventually_ge_atTop (0 : ℝ)] with x hx hfx hx0
  have hPP : (P' : ℝ) ≤ P := by exact_mod_cast hP
  have he : Real.exp (-(2 * P * x)) ≤ Real.exp (-(2 * P' * x)) := Real.exp_le_exp.2 (by nlinarith)
  calc ‖g x‖ ≤ C * Real.exp (-(2 * P * x)) * f x := hx
    _ ≤ |C| * Real.exp (-(2 * P' * x)) * f x := by
        gcongr
        exact le_abs_self C

/-- **Weighted tail integrals.**  If `g = O(e^{-2Px} f)` then for large `x`
`∫₀^∞ t^m e^{ct} ‖g(x+t)‖ dt ≤ K e^{-2(P+m+1)x} f(x)`. -/
theorem weighted [NormedSpace ℝ E] (hf : ThetaTypeTail f) (hg : StronglyMeasurable g)
    (h : TailSmall f P g) (m : ℕ) (c : ℝ) :
    ∃ K X : ℝ, 0 ≤ X ∧ ∀ x, X ≤ x →
      IntegrableOn (fun t => t ^ m * Real.exp (c * t) * ‖g (x + t)‖) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (c * t) * ‖g (x + t)‖ ≤
        K * Real.exp (-(2 * ((P + m + 1 : ℕ) : ℝ) * x)) * f x := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hC
  obtain ⟨K₀, X₂, hK⟩ := hf.exists_integral_le m c
  obtain ⟨C₀, B, X₀, -, hX₀, hsh⟩ := hf.shift
  refine ⟨|C| * K₀, max X₀ (max X₁ X₂), le_max_of_le_left hX₀, fun x hx => ?_⟩
  have hx0 : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx2 : X₂ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  obtain ⟨hint, hle⟩ := hK x hx2
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hbd : ∀ t ∈ Ioi (0 : ℝ), t ^ m * Real.exp (c * t) * ‖g (x + t)‖ ≤
      |C| * Real.exp (-(2 * P * x)) * (t ^ m * Real.exp (c * t) * f (x + t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hft := (hsh (x + t) (by linarith)).1
    have hg' := hX₁ (x + t) (by linarith)
    have hexp : Real.exp (-(2 * P * (x + t))) ≤ Real.exp (-(2 * P * x)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 : ‖g (x + t)‖ ≤ |C| * Real.exp (-(2 * P * x)) * f (x + t) := by
      refine hg'.trans ?_
      gcongr
      exact le_abs_self C
    calc t ^ m * Real.exp (c * t) * ‖g (x + t)‖ ≤
          t ^ m * Real.exp (c * t) * (|C| * Real.exp (-(2 * P * x)) * f (x + t)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (fun t => t ^ m * Real.exp (c * t) * ‖g (x + t)‖)
      (volume.restrict (Ioi 0)) :=
    (((by fun_prop : Continuous fun t : ℝ => t ^ m * Real.exp (c * t)).stronglyMeasurable).mul
      (hg.comp_measurable (measurable_const_add x)).norm).aestronglyMeasurable
  have hint' : IntegrableOn (fun t => t ^ m * Real.exp (c * t) * ‖g (x + t)‖) (Ioi 0) :=
    (hint.const_mul (|C| * Real.exp (-(2 * P * x)))).mono' hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (by have : (0 : ℝ) < t := ht; positivity)]
        exact hbd t ht)
  refine ⟨hint', ?_⟩
  calc ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (c * t) * ‖g (x + t)‖
      ≤ ∫ t in Ioi (0 : ℝ), |C| * Real.exp (-(2 * P * x)) * (t ^ m * Real.exp (c * t) * f (x + t)) :=
        setIntegral_mono_on hint' (hint.const_mul _) measurableSet_Ioi hbd
    _ = |C| * Real.exp (-(2 * P * x)) * ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (c * t) * f (x + t) :=
        integral_const_mul _ _
    _ ≤ |C| * Real.exp (-(2 * P * x)) * (K₀ * Real.exp (-(2 * (m + 1) * x)) * f x) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by
        have : Real.exp (-(2 * P * x)) * Real.exp (-(2 * (m + 1) * x)) =
            Real.exp (-(2 * ((P + m + 1 : ℕ) : ℝ) * x)) := by
          rw [← Real.exp_add]; push_cast; ring_nf
        rw [← this]; ring

theorem integrableOn [NormedSpace ℝ E] (hf : ThetaTypeTail f) (hg : StronglyMeasurable g)
    (h : TailSmall f P g) : ∀ᶠ x in atTop, IntegrableOn (fun t => g (x + t)) (Ioi 0) := by
  obtain ⟨K, X, -, hK⟩ := h.weighted hf hg 0 0
  filter_upwards [eventually_ge_atTop X] with x hx
  have hi := (hK x hx).1
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul] at hi
  exact (integrable_norm_iff (hg.comp_measurable (measurable_const_add x)).aestronglyMeasurable).1 hi

/-- The tail integral gains one order. -/
theorem tailIntegral [NormedSpace ℝ E] (hf : ThetaTypeTail f) (hg : StronglyMeasurable g)
    (h : TailSmall f P g) : TailSmall f (P + 1) (RHTower.tailIntegral g) := by
  obtain ⟨K, X, -, hK⟩ := h.weighted hf hg 0 0
  refine ⟨K, eventually_atTop.2 ⟨X, fun x hx => ?_⟩⟩
  obtain ⟨-, hle⟩ := hK x hx
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul, add_zero] at hle
  exact (norm_integral_le_integral_norm _).trans hle

end TailSmall

/-- Relative smallness of the base itself. -/
theorem ThetaTypeTail.tailSmall_zero {f : ℝ → ℝ} (hf : ThetaTypeTail f) :
    TailSmall f 0 fun x => (f x : ℂ) := by
  refine ⟨1, ?_⟩
  filter_upwards [hf.eventually_pos] with x hx
  simp [Complex.norm_real, abs_of_pos hx]

/-- The outward sine Green operator gains two orders. -/
theorem TailSmall.outwardSine {f : ℝ → ℝ} {P : ℕ} {g : ℝ → ℂ} (hf : ThetaTypeTail f)
    (hg : StronglyMeasurable g) (h : TailSmall f P g) (β : ℂ) :
    TailSmall f (P + 2) (RHTower.outwardSine β g) := by
  obtain ⟨K, X, hX, hK⟩ := h.weighted hf hg 1 |β.im|
  refine ⟨‖β‖ * (‖β‖ * K), eventually_atTop.2 ⟨X, fun x hx => ?_⟩⟩
  obtain ⟨hi, hle⟩ := hK x hx
  have hb : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))), ‖Complex.sin (β * t) * g (x + t)‖ ≤
      ‖β‖ * (t ^ 1 * Real.exp (|β.im| * t) * ‖g (x + t)‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [norm_mul, pow_one]
    calc ‖Complex.sin (β * t)‖ * ‖g (x + t)‖ ≤ ‖β‖ * t * Real.exp (|β.im| * t) * ‖g (x + t)‖ :=
          mul_le_mul_of_nonneg_right (norm_csin_mul_ofReal_le_mul_exp β ht0) (norm_nonneg _)
      _ = _ := by ring
  unfold RHTower.outwardSine
  rw [norm_mul]
  calc ‖β‖ * ‖∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * g (x + t)‖
      ≤ ‖β‖ * ∫ t in Ioi (0 : ℝ), ‖β‖ * (t ^ 1 * Real.exp (|β.im| * t) * ‖g (x + t)‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le (hi.const_mul _) hb) (norm_nonneg _)
    _ = ‖β‖ * (‖β‖ * ∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (|β.im| * t) * ‖g (x + t)‖) := by
        rw [integral_const_mul]
    _ ≤ ‖β‖ * (‖β‖ * (K * Real.exp (-(2 * ((P + 1 + 1 : ℕ) : ℝ) * x)) * f x)) := by
        gcongr
    _ = _ := by ring

end General

/-! ## The shear identity and the resolvent of the outward sine operator -/

/-- **Shear Fubini on the quarter plane.**  For kernels of exponential growth,
`∫₀^∞ φ(u) ∫₀^∞ ψ(s) g(x+u+s) ds du = ∫₀^∞ (∫₀^t φ(u) ψ(t−u) du) g(x+t) dt`. -/
theorem integral_Ioi_shear {φ ψ : ℝ → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ) {A a : ℝ}
    (hφb : ∀ u, 0 ≤ u → ‖φ u‖ ≤ A * Real.exp (a * u))
    (hψb : ∀ s, 0 ≤ s → ‖ψ s‖ ≤ A * Real.exp (a * s))
    {g : ℝ → ℂ} (hg : StronglyMeasurable g) {x : ℝ}
    (hint : IntegrableOn (fun t => t * Real.exp (a * t) * ‖g (x + t)‖) (Ioi 0)) :
    ∫ u in Ioi (0 : ℝ), φ u * ∫ s in Ioi (0 : ℝ), ψ s * g (x + u + s) =
      ∫ t in Ioi (0 : ℝ), (∫ u in (0 : ℝ)..t, φ u * ψ (t - u)) * g (x + t) := by
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set H : ℝ × ℝ → ℂ := {p : ℝ × ℝ | p.1 < p.2}.indicator
    fun p => φ p.1 * ψ (p.2 - p.1) * g (x + p.2) with hH
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hφb 0 le_rfl)
    simpa using this
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  have hHm : StronglyMeasurable H :=
    ((((hφ.comp continuous_fst).stronglyMeasurable).mul
      ((hψ.comp (continuous_snd.sub continuous_fst)).stronglyMeasurable)).mul
      (hg.comp_measurable ((measurable_const_add x).comp measurable_snd))).indicator hS
  have hHpt : ∀ u t, H (u, t) = (Iio t).indicator (fun u => φ u * ψ (t - u) * g (x + t)) u := by
    intro u t
    simp only [hH, Set.indicator, mem_setOf_eq, mem_Iio]
  -- the inner shift
  have h1 : ∀ u ∈ Ioi (0 : ℝ),
      φ u * ∫ s in Ioi (0 : ℝ), ψ s * g (x + u + s) = ∫ t in Ioi (0 : ℝ), H (u, t) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hshift : ∫ s in Ioi (0 : ℝ), ψ s * g (x + u + s) =
        ∫ t in Ioi (0 : ℝ), (Ioi u).indicator (fun t => ψ (t - u) * g (x + t)) t := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
        ← integral_add_right_eq_self (fun t => (Ioi (0 : ℝ)).indicator
          (fun t => (Ioi u).indicator (fun t => ψ (t - u) * g (x + t)) t) t) u]
      congr 1
      funext s
      by_cases hs : 0 < s
      · have h2 : s + u ∈ Ioi u := by simp [hs]
        have h3 : s + u ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
        rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), indicator_of_mem h3, indicator_of_mem h2,
          add_sub_cancel_right]
        ring_nf
      · have h2 : s + u ∉ Ioi u := by simp only [mem_Ioi]; linarith
        rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
        by_cases h3 : s + u ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem h3, indicator_of_notMem h2]
        · rw [indicator_of_notMem h3]
    rw [hshift, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hHpt, Set.indicator, mem_Ioi, mem_Iio]
    split_ifs <;> ring
  -- the inner integral after the swap
  have h4 : ∀ t ∈ Ioi (0 : ℝ),
      ∫ u in Ioi (0 : ℝ), H (u, t) = (∫ u in (0 : ℝ)..t, φ u * ψ (t - u)) * g (x + t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [hHpt]
    rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, intervalIntegral.integral_of_le ht0.le,
      integral_Ioc_eq_integral_Ioo, ← integral_mul_const]
  -- integrability on the product
  have hHint : Integrable H (μ.prod μ) := by
    rw [integrable_prod_iff' hHm.aestronglyMeasurable]
    have hfin : ∀ t, μ (Iio t) < ∞ := fun t => by
      rw [hμ, Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hbd : ∀ t, ∀ᵐ u ∂μ, ‖H (u, t)‖ ≤
        (Iio t).indicator (fun _ => A ^ 2 * Real.exp (a * t) * ‖g (x + t)‖) u := by
      intro t
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      rw [hHpt]
      by_cases hut : u < t
      · rw [indicator_of_mem (show u ∈ Iio t from hut), indicator_of_mem (show u ∈ Iio t from hut),
          norm_mul, norm_mul]
        have e1 := hφb u hu0.le
        have e2 := hψb (t - u) (by linarith)
        have e3 : Real.exp (a * u) * Real.exp (a * (t - u)) = Real.exp (a * t) := by
          rw [← Real.exp_add]; ring_nf
        calc ‖φ u‖ * ‖ψ (t - u)‖ * ‖g (x + t)‖ ≤
            (A * Real.exp (a * u)) * (A * Real.exp (a * (t - u))) * ‖g (x + t)‖ := by
              gcongr
          _ = _ := by rw [← e3]; ring
      · rw [indicator_of_notMem (show u ∉ Iio t from hut),
          indicator_of_notMem (show u ∉ Iio t from hut), norm_zero]
    have hbint : ∀ t, Integrable
        ((Iio t).indicator fun _ => A ^ 2 * Real.exp (a * t) * ‖g (x + t)‖) μ := fun t =>
      (integrable_indicator_iff measurableSet_Iio).2 (integrableOn_const (hfin t).ne)
    refine ⟨Eventually.of_forall fun t => (hbint t).mono'
      (hHm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable (hbd t), ?_⟩
    refine (hint.const_mul (A ^ 2)).mono' (hHm.norm.integral_prod_left' (μ := μ)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
    calc ∫ u, ‖H (u, t)‖ ∂μ ≤ ∫ u, (Iio t).indicator
          (fun _ => A ^ 2 * Real.exp (a * t) * ‖g (x + t)‖) u ∂μ :=
          integral_mono_ae (hHm.norm.comp_measurable (measurable_id.prodMk measurable_const)
            |>.aestronglyMeasurable |> fun hm => (hbint t).mono' hm
              (by filter_upwards [hbd t] with u hu; rwa [norm_norm])) (hbint t) (hbd t)
      _ = A ^ 2 * (t * Real.exp (a * t) * ‖g (x + t)‖) := by
          rw [integral_indicator measurableSet_Iio, setIntegral_const, hμ,
            Measure.real, Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          ring
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun u t => H (u, t)) hHint
  calc ∫ u in Ioi (0 : ℝ), φ u * ∫ s in Ioi (0 : ℝ), ψ s * g (x + u + s)
      = ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H (u, t) := setIntegral_congr_fun measurableSet_Ioi h1
    _ = ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (u, t) := hswap
    _ = _ := setIntegral_congr_fun measurableSet_Ioi h4

/-- **Cauchy's formula for the double tail integral.**  `I²g(x) = ∫₀^∞ t g(x+t) dt`. -/
theorem TailSmall.tailIntegral_tailIntegral {f : ℝ → ℝ} {P : ℕ} {g : ℝ → ℂ} (hf : ThetaTypeTail f)
    (hg : StronglyMeasurable g) (h : TailSmall f P g) :
    ∀ᶠ x in atTop, RHTower.tailIntegral (RHTower.tailIntegral g) x =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) * g (x + t) := by
  obtain ⟨K, X, -, hK⟩ := h.weighted hf hg 1 0
  filter_upwards [eventually_ge_atTop X] with x hx
  have hi := (hK x hx).1
  have hs := integral_Ioi_shear (φ := fun _ => (1 : ℂ)) (ψ := fun _ => (1 : ℂ)) continuous_const
    continuous_const (A := 1) (a := 0) (fun u _ => by simp) (fun s _ => by simp) hg (x := x)
    (by simpa using hi)
  simp only [one_mul, intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one] at hs
  exact hs

theorem mul_intervalIntegral_mul_sin_sub (β : ℂ) (t : ℝ) :
    β * ∫ u in (0 : ℝ)..t, (u : ℂ) * (β * Complex.sin (β * ((t - u : ℝ) : ℂ))) =
      β * t - Complex.sin (β * t) := by
  rw [← intervalIntegral.integral_const_mul]
  have hd : ∀ u ∈ uIcc (0 : ℝ) t, HasDerivAt (fun u : ℝ => β * (u : ℂ) * Complex.cos (β * ((t : ℂ) - u)) +
      Complex.sin (β * ((t : ℂ) - u))) (β * ((u : ℂ) * (β * Complex.sin (β * ((t - u : ℝ) : ℂ))))) u := by
    intro u _
    have h1 := hasDerivAt_ccos_mul_sub β t u
    have h2 := hasDerivAt_csin_mul_sub β t u
    have h3 : HasDerivAt (fun u : ℝ => β * (u : ℂ)) β u := by
      simpa using ((hasDerivAt_id u).ofReal_comp).const_mul β
    refine ((h3.mul h1).add h2).congr_deriv ?_
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u : ℝ =>
      β * ((u : ℂ) * (β * Complex.sin (β * ((t - u : ℝ) : ℂ))))).intervalIntegrable _ _)]
  simp

/-- **The resolvent identity** `T_β g = β² I²(g − T_β g)`, i.e. `(1 + β²I²) T_β = β² I²`. -/
theorem TailSmall.outwardSine_resolvent {f : ℝ → ℝ} {P : ℕ} {g : ℝ → ℂ} (hf : ThetaTypeTail f)
    (hg : StronglyMeasurable g) (h : TailSmall f P g) (β : ℂ) :
    ∀ᶠ x in atTop, RHTower.outwardSine β g x = β ^ 2 *
      (RHTower.tailIntegral (RHTower.tailIntegral g) x -
        RHTower.tailIntegral (RHTower.tailIntegral (RHTower.outwardSine β g)) x) := by
  have hT := h.outwardSine hf hg β
  have hTm := stronglyMeasurable_outwardSine hg β
  set a := max 1 ‖β‖ with ha
  have ha1 : 1 ≤ a := le_max_left _ _
  have hβa : ‖β‖ ≤ a := le_max_right _ _
  obtain ⟨K₁, X₁, -, hK₁⟩ := h.weighted hf hg 1 a
  obtain ⟨K₀, X₀, -, hK₀⟩ := h.weighted hf hg 0 a
  filter_upwards [h.tailIntegral_tailIntegral hf hg, hT.tailIntegral_tailIntegral hf hTm,
    eventually_ge_atTop (max X₀ X₁)] with x hx1 hx2 hxX
  have hi1 := (hK₁ x ((le_max_right _ _).trans hxX)).1
  have hi0 := (hK₀ x ((le_max_left _ _).trans hxX)).1
  simp only [pow_one] at hi1
  simp only [pow_zero, one_mul] at hi0
  have hgm : AEStronglyMeasurable (fun t => g (x + t)) (volume.restrict (Ioi 0)) :=
    (hg.comp_measurable (measurable_const_add x)).aestronglyMeasurable
  have hexp : ∀ t : ℝ, 0 ≤ t → Real.exp (|β.im| * t) ≤ Real.exp (a * t) := fun t ht =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm β).trans hβa) ht)
  have hint_t : IntegrableOn (fun t : ℝ => (t : ℂ) * g (x + t)) (Ioi 0) := by
    refine hi1.mono' ((Complex.continuous_ofReal.aestronglyMeasurable).mul hgm) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ht0 (Real.one_le_exp (by positivity)))
      (norm_nonneg _)
  have hint_s : IntegrableOn (fun t : ℝ => Complex.sin (β * t) * g (x + t)) (Ioi 0) := by
    refine hi0.mono' ((by fun_prop : Continuous fun t : ℝ => Complex.sin (β * t)).aestronglyMeasurable.mul
      hgm) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ((norm_csin_mul_ofReal_le β t).trans ?_) (norm_nonneg _)
    rw [abs_of_nonneg ht0]
    exact hexp t ht0
  have hsh := integral_Ioi_shear (φ := fun u => (u : ℂ)) (ψ := fun s => β * Complex.sin (β * s))
    Complex.continuous_ofReal (by fun_prop) (A := a) (a := a)
    (fun u hu => by
      rw [Complex.norm_real, Real.norm_of_nonneg hu]
      calc u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
        _ ≤ Real.exp (a * u) := Real.exp_le_exp.2 (le_mul_of_one_le_left hu ha1)
        _ ≤ a * Real.exp (a * u) := le_mul_of_one_le_left (Real.exp_pos _).le ha1)
    (fun s hs => by
      rw [norm_mul]
      refine mul_le_mul hβa ((norm_csin_mul_ofReal_le β s).trans ?_) (norm_nonneg _) (by linarith)
      rw [abs_of_nonneg hs]
      exact hexp s hs) hg (x := x) hi1
  have hL : ∫ u in Ioi (0 : ℝ), (u : ℂ) * RHTower.outwardSine β g (x + u) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) * ∫ s in Ioi (0 : ℝ), β * Complex.sin (β * s) * g (x + u + s) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold RHTower.outwardSine
    rw [← integral_const_mul]
    simp_rw [mul_assoc]
  rw [hx1, hx2, hL, hsh]
  have hJ : β ^ 2 * ∫ t in Ioi (0 : ℝ), (∫ u in (0 : ℝ)..t,
      (u : ℂ) * (β * Complex.sin (β * ((t - u : ℝ) : ℂ)))) * g (x + t) =
      β * ∫ t in Ioi (0 : ℝ), (β * (t : ℂ) - Complex.sin (β * t)) * g (x + t) := by
    rw [pow_two, mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← mul_intervalIntegral_mul_sin_sub β t]
    ring
  have hsplit : ∫ t in Ioi (0 : ℝ), (β * (t : ℂ) - Complex.sin (β * t)) * g (x + t) =
      β * (∫ t in Ioi (0 : ℝ), (t : ℂ) * g (x + t)) -
        ∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * g (x + t) := by
    rw [← integral_const_mul, ← integral_sub (hint_t.const_mul β) hint_s]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [mul_sub, hJ, hsplit]
  unfold RHTower.outwardSine
  ring

/-! ## Tail-integral series -/

section Series

variable {f : ℝ → ℝ}

/-- The truncated tail series `Σ_{m<P} a_m (I^m f)(x)`. -/
def tailSeries (f : ℝ → ℝ) (a : PowerSeries ℂ) (P : ℕ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.range P, PowerSeries.coeff m a * tailIntegral^[m] (fun y => (f y : ℂ)) x

/-- `g ∼ Σ a_m I^m f`: every truncation is exact to the next order in `e^{-2x}`. -/
def HasTailSeries (f : ℝ → ℝ) (g : ℝ → ℂ) (a : PowerSeries ℂ) : Prop :=
  ∀ P, TailSmall f P fun x => g x - tailSeries f a P x

theorem stronglyMeasurable_iterate_tailIntegral (hf : ThetaTypeTail f) (m : ℕ) :
    StronglyMeasurable (tailIntegral^[m] fun y => (f y : ℂ)) := by
  induction m with
  | zero => exact (Complex.continuous_ofReal.comp hf.continuous).stronglyMeasurable
  | succ m ih =>
    rw [Function.iterate_succ']
    exact stronglyMeasurable_tailIntegral ih

theorem tailSmall_iterate_tailIntegral (hf : ThetaTypeTail f) (m : ℕ) :
    TailSmall f m (tailIntegral^[m] fun y => (f y : ℂ)) := by
  induction m with
  | zero => exact hf.tailSmall_zero
  | succ m ih =>
    rw [Function.iterate_succ']
    exact ih.tailIntegral hf (stronglyMeasurable_iterate_tailIntegral hf m)

theorem ThetaTypeTail.eventually_nonneg (hf : ThetaTypeTail f) : ∀ᶠ x in atTop, 0 ≤ f x :=
  hf.eventually_pos.mono fun _ hx => hx.le

theorem stronglyMeasurable_tailSeries (hf : ThetaTypeTail f) (a : PowerSeries ℂ) (P : ℕ) :
    StronglyMeasurable (tailSeries f a P) := by
  unfold tailSeries
  exact Finset.stronglyMeasurable_fun_sum _ fun m _ =>
    stronglyMeasurable_const.mul (stronglyMeasurable_iterate_tailIntegral hf m)

theorem tailSmall_tailSeries (hf : ThetaTypeTail f) (a : PowerSeries ℂ) (P : ℕ) :
    TailSmall f 0 (tailSeries f a P) :=
  TailSmall.sum _ fun m _ => ((tailSmall_iterate_tailIntegral hf m).const_smul
    (PowerSeries.coeff m a)).mono (Nat.zero_le _) hf.eventually_nonneg

theorem tailSeries_add (a b : PowerSeries ℂ) (P : ℕ) (x : ℝ) :
    tailSeries f (a + b) P x = tailSeries f a P x + tailSeries f b P x := by
  simp only [tailSeries, map_add, add_mul, Finset.sum_add_distrib]

theorem tailSeries_sub (a b : PowerSeries ℂ) (P : ℕ) (x : ℝ) :
    tailSeries f (a - b) P x = tailSeries f a P x - tailSeries f b P x := by
  simp only [tailSeries, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem tailSeries_C_mul (c : ℂ) (a : PowerSeries ℂ) (P : ℕ) (x : ℝ) :
    tailSeries f (PowerSeries.C c * a) P x = c * tailSeries f a P x := by
  simp only [tailSeries, PowerSeries.coeff_C_mul, Finset.mul_sum, mul_assoc]

theorem tailSeries_eq_zero {a : PowerSeries ℂ} {P : ℕ} (h : ∀ m < P, PowerSeries.coeff m a = 0)
    (x : ℝ) : tailSeries f a P x = 0 :=
  Finset.sum_eq_zero fun m hm => by rw [h m (Finset.mem_range.1 hm), zero_mul]

theorem tailIntegral_tailSeries (hf : ThetaTypeTail f) (a : PowerSeries ℂ) (P : ℕ) :
    ∀ᶠ x in atTop, tailIntegral (tailSeries f a P) x =
      tailSeries f (PowerSeries.X * a) (P + 1) x := by
  have hi : ∀ᶠ x in atTop, ∀ m ∈ Finset.range P,
      IntegrableOn (fun t => (tailIntegral^[m] fun y => (f y : ℂ)) (x + t)) (Ioi 0) :=
    (Filter.eventually_all_finset _).2 fun m _ =>
      (tailSmall_iterate_tailIntegral hf m).integrableOn hf (stronglyMeasurable_iterate_tailIntegral hf m)
  filter_upwards [hi] with x hx
  unfold tailIntegral tailSeries
  rw [integral_finsetSum _ fun m hm => (hx m hm).const_mul _, Finset.sum_range_succ',
    PowerSeries.coeff_zero_X_mul, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, PowerSeries.coeff_succ_X_mul, Function.iterate_succ_apply']
  rfl

theorem tailIntegral_sub_eventually (hf : ThetaTypeTail f) {g g' : ℝ → ℂ} {P P' : ℕ}
    (hg : StronglyMeasurable g) (hg' : StronglyMeasurable g') (h : TailSmall f P g)
    (h' : TailSmall f P' g') :
    ∀ᶠ x in atTop, tailIntegral (fun y => g y - g' y) x = tailIntegral g x - tailIntegral g' x := by
  filter_upwards [h.integrableOn hf hg, h'.integrableOn hf hg'] with x hx hx'
  exact integral_sub hx hx'

namespace HasTailSeries

variable {g g' : ℝ → ℂ} {a b : PowerSeries ℂ}

theorem congr (h : HasTailSeries f g a) (h' : ∀ᶠ x in atTop, g x = g' x) : HasTailSeries f g' a :=
  fun P => (h P).congr (h'.mono fun x hx => by rw [hx])

theorem tailSmall (h : HasTailSeries f g a) : TailSmall f 0 g :=
  (h 0).congr (Eventually.of_forall fun x => by simp [tailSeries])

theorem add (h : HasTailSeries f g a) (h' : HasTailSeries f g' b) :
    HasTailSeries f (fun x => g x + g' x) (a + b) := fun P =>
  ((h P).add (h' P)).congr (Eventually.of_forall fun x => by rw [tailSeries_add]; ring)

theorem sub (h : HasTailSeries f g a) (h' : HasTailSeries f g' b) :
    HasTailSeries f (fun x => g x - g' x) (a - b) := fun P =>
  ((h P).sub (h' P)).congr (Eventually.of_forall fun x => by rw [tailSeries_sub]; ring)

theorem const_mul (h : HasTailSeries f g a) (c : ℂ) :
    HasTailSeries f (fun x => c * g x) (PowerSeries.C c * a) := fun P =>
  ((h P).const_smul c).congr (Eventually.of_forall fun x => by
    rw [tailSeries_C_mul, smul_eq_mul]; ring)

theorem tailIntegral (hf : ThetaTypeTail f) (hg : StronglyMeasurable g) (h : HasTailSeries f g a) :
    HasTailSeries f (RHTower.tailIntegral g) (PowerSeries.X * a) := by
  intro P
  cases P with
  | zero =>
    exact ((h.tailSmall.tailIntegral hf hg).mono (Nat.zero_le _) hf.eventually_nonneg).congr
      (Eventually.of_forall fun x => by simp [tailSeries])
  | succ P =>
    have hs := stronglyMeasurable_tailSeries hf a P
    refine ((h P).tailIntegral hf (hg.sub hs)).congr ?_
    filter_upwards [tailIntegral_sub_eventually hf hg hs h.tailSmall (tailSmall_tailSeries hf a P),
      tailIntegral_tailSeries hf a P] with x hx hx'
    exact hx.trans (by rw [hx'])

theorem iterate_tailIntegral (hf : ThetaTypeTail f) (hg : StronglyMeasurable g)
    (h : HasTailSeries f g a) (n : ℕ) :
    HasTailSeries f (RHTower.tailIntegral^[n] g) (PowerSeries.X ^ n * a) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ', pow_succ', mul_assoc]
    have hm : StronglyMeasurable (RHTower.tailIntegral^[n] g) := by
      clear ih
      induction n with
      | zero => exact hg
      | succ n ihn => rw [Function.iterate_succ']; exact stronglyMeasurable_tailIntegral ihn
    exact ih.tailIntegral hf hm

end HasTailSeries

theorem hasTailSeries_base (hf : ThetaTypeTail f) : HasTailSeries f (fun x => (f x : ℂ)) 1 := by
  intro P
  cases P with
  | zero => exact hf.tailSmall_zero.congr (Eventually.of_forall fun x => by simp [tailSeries])
  | succ P =>
    refine TailSmall.zero.congr (Eventually.of_forall fun x => ?_)
    simp only [tailSeries, PowerSeries.coeff_one, Finset.sum_range_succ', ite_mul, one_mul, zero_mul,
      Nat.add_one_ne_zero, if_false, Finset.sum_const_zero, zero_add, if_true,
      Function.iterate_zero, id, Pi.zero_apply, sub_self]

/-- The symbol `σ_β = β²X²/(1 + β²X²)` of the outward sine operator. -/
def sineSymbol (β : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2 * (1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2)⁻¹

theorem sineSymbol_mul (β : ℂ) :
    sineSymbol β * (1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2) =
      PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2 := by
  unfold sineSymbol
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]

theorem coeff_sineSymbol_mul_of_lt (β : ℂ) (a : PowerSeries ℂ) {m : ℕ} (hm : m < 2) :
    PowerSeries.coeff m (sineSymbol β * a) = 0 := by
  have : sineSymbol β * a = PowerSeries.X ^ 2 * (PowerSeries.C (β ^ 2) *
      (1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2)⁻¹ * a) := by
    unfold sineSymbol; ring
  rw [this, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem tailIntegral_tailIntegral_tailSeries (hf : ThetaTypeTail f) (a : PowerSeries ℂ) (P : ℕ) :
    ∀ᶠ x in atTop, tailIntegral (tailIntegral (tailSeries f a P)) x =
      tailSeries f (PowerSeries.X * (PowerSeries.X * a)) (P + 2) x := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 (tailIntegral_tailSeries hf a P)
  filter_upwards [eventually_ge_atTop X, tailIntegral_tailSeries hf (PowerSeries.X * a) (P + 1)]
    with x hx hx'
  rw [tailIntegral_congr hX hx, hx']

/-- **The outward sine operator on tail series**: `T_β` acts as multiplication by `σ_β`. -/
theorem HasTailSeries.outwardSine (hf : ThetaTypeTail f) {g : ℝ → ℂ} {a : PowerSeries ℂ}
    (hg : StronglyMeasurable g) (h : HasTailSeries f g a) (β : ℂ) :
    HasTailSeries f (RHTower.outwardSine β g) (sineSymbol β * a) := by
  have hT := h.tailSmall.outwardSine hf hg β
  have hTm := stronglyMeasurable_outwardSine hg β
  intro P
  induction P using Nat.strong_induction_on with
  | _ P ih =>
  by_cases hP : P < 2
  · exact (hT.mono (by omega) hf.eventually_nonneg).congr (Eventually.of_forall fun x => by
      rw [tailSeries_eq_zero (fun m hm => coeff_sineSymbol_mul_of_lt β a (by omega)), sub_zero])
  · obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 2 := ⟨P - 2, by omega⟩
    have hD := ih Q (by omega)
    have hs := stronglyMeasurable_tailSeries hf (sineSymbol β * a) Q
    have hDm : StronglyMeasurable fun x => RHTower.outwardSine β g x - tailSeries f (sineSymbol β * a) Q x :=
      hTm.sub hs
    have hID := hD.tailIntegral hf hDm
    have hIDm := stronglyMeasurable_tailIntegral hDm
    have hIID := hID.tailIntegral hf hIDm
    have hg2 := h.iterate_tailIntegral hf hg 2 (Q + 2)
    have hsym : PowerSeries.C (β ^ 2) * (PowerSeries.X ^ 2 * a) -
        PowerSeries.C (β ^ 2) * (PowerSeries.X * (PowerSeries.X * (sineSymbol β * a))) -
          sineSymbol β * a = 0 := by
      have := sineSymbol_mul β
      linear_combination (-a) * this
    refine ((hg2.const_smul (β ^ 2)).sub (hIID.const_smul (β ^ 2))).congr ?_
    have hTs := tailSmall_tailSeries hf (sineSymbol β * a) Q
    have hIT := hT.tailIntegral hf hTm
    have hITm := stronglyMeasurable_tailIntegral hTm
    have hIs := hTs.tailIntegral hf hs
    have hIsm := stronglyMeasurable_tailIntegral hs
    obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (tailIntegral_sub_eventually hf hTm hs hT hTs)
    filter_upwards [h.tailSmall.outwardSine_resolvent hf hg β,
      tailIntegral_sub_eventually hf hITm hIsm hIT hIs,
      tailIntegral_tailIntegral_tailSeries hf (sineSymbol β * a) Q, eventually_ge_atTop X₁]
      with x hres hsub2 hss hxX
    have hsub1 := tailIntegral_congr (g := RHTower.tailIntegral fun y =>
      RHTower.outwardSine β g y - tailSeries f (sineSymbol β * a) Q y)
      (g' := fun y => RHTower.tailIntegral (RHTower.outwardSine β g) y -
        RHTower.tailIntegral (tailSeries f (sineSymbol β * a) Q) y) hX₁ hxX
    have hzero := congrArg (fun φ => tailSeries f φ (Q + 2) x) hsym
    simp only [tailSeries_sub, tailSeries_C_mul] at hzero
    rw [tailSeries_eq_zero (a := 0) (fun m _ => by simp)] at hzero
    simp only [smul_eq_mul]
    rw [show (RHTower.tailIntegral^[2] g) = RHTower.tailIntegral (RHTower.tailIntegral g) from rfl,
      hsub1, hsub2, hss, hres]
    linear_combination -hzero

/-! ## Symbols of list divisions and partial-fraction combinations -/

/-- The symbol `∏_{β ∈ L} σ_β` of the list division `T_L`. -/
def listSymbol (L : List ℂ) : PowerSeries ℂ := (L.map sineSymbol).prod

theorem hasTailSeries_halfListDivision (hf : ThetaTypeTail f) (L : List ℂ) :
    HasTailSeries f (halfListDivision L fun y => (f y : ℂ)) (listSymbol L) := by
  induction L with
  | nil => simpa [listSymbol, halfListDivision] using hasTailSeries_base hf
  | cons β L ih =>
    simp only [listSymbol, List.map_cons, List.prod_cons]
    exact ih.outwardSine hf (ThetaTypeTail.stronglyMeasurable_halfListDivision L
      (Complex.continuous_ofReal.comp hf.continuous).stronglyMeasurable) β

/-- The symbol of the partial-fraction combination `listComb L e`. -/
def combSymbol : List ℂ → Polynomial ℂ → PowerSeries ℂ
  | [], e => PowerSeries.C (e.coeff 0)
  | β :: L, e => PowerSeries.C (e.eval (β ^ 2)) * listSymbol (β :: L) -
      PowerSeries.C (β ^ 2) * combSymbol L (e /ₘ (Polynomial.X - Polynomial.C (β ^ 2)))

/-- **Tail series of partial-fraction combinations**:
`listComb L e ∼ Σ_m (combSymbol L e)_m I^m f`. -/
theorem hasTailSeries_listComb (hf : ThetaTypeTail f) (L : List ℂ) (e : Polynomial ℂ) :
    HasTailSeries f (listComb (fun L' => halfListDivision L' fun y => (f y : ℂ)) L e)
      (combSymbol L e) := by
  induction L generalizing e with
  | nil =>
    have := (hasTailSeries_base hf).const_mul (e.coeff 0)
    simpa [listComb_nil, combSymbol, halfListDivision] using this
  | cons β L ih =>
    exact ((hasTailSeries_halfListDivision hf (β :: L)).const_mul (e.eval (β ^ 2))).sub
      ((ih (e /ₘ (Polynomial.X - Polynomial.C (β ^ 2)))).const_mul (β ^ 2))

end Series

/-! ## The closed form of the symbols -/

section Symbols

/-- The even reversal `Σ_{i≤n} (−1)^i e_i X^{2(n−i)}`, i.e. `w^{2n} e(−1/w²)`. -/
def evenRev {R : Type*} [CommRing R] (n : ℕ) (e : Polynomial R) : Polynomial R :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (e.coeff i * (-1) ^ i) * Polynomial.X ^ (2 * (n - i))

theorem eval_evenRev {n : ℕ} {e : Polynomial ℂ} (he : e.natDegree ≤ n) {w : ℂ} (hw : w ≠ 0) :
    (evenRev n e).eval w = w ^ (2 * n) * e.eval (-1 / w ^ 2) := by
  rw [evenRev, Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (n := n + 1) (by omega),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have h1 : w ^ (2 * n) = w ^ (2 * (n - i)) * (w ^ 2) ^ i := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have h2 : (w ^ 2) ^ i ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hw)
  rw [h1, div_pow]
  field_simp

theorem evenRev_succ {n : ℕ} {e : Polynomial ℂ} (he : e.natDegree ≤ n + 1) (c : ℂ) :
    evenRev (n + 1) e = Polynomial.C (e.eval c) * Polynomial.X ^ (2 * (n + 1)) -
      (1 + Polynomial.C c * Polynomial.X ^ 2) * evenRev n (e /ₘ (Polynomial.X - Polynomial.C c)) := by
  have hq := natDegree_divByMonic_X_sub_C_le he c
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.infinite_univ.sdiff (Set.finite_singleton 0)).mono
    fun w hw => ?_)
  have hw0 : w ≠ 0 := hw.2
  simp only [mem_setOf_eq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one]
  rw [eval_evenRev he hw0, eval_evenRev hq hw0]
  conv_lhs => rw [eq_C_add_X_sub_C_mul_divByMonic e c]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X]
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
  field_simp
  ring

/-- The denominator `Q_L = ∏_{β ∈ L} (1 + β²X²)`. -/
def symbolDen (L : List ℂ) : PowerSeries ℂ :=
  (L.map fun β => 1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2).prod

theorem listSymbol_mul_symbolDen (L : List ℂ) :
    listSymbol L * symbolDen L =
      PowerSeries.C ((L.map fun β => β ^ 2).prod) * PowerSeries.X ^ (2 * L.length) := by
  induction L with
  | nil => simp [listSymbol, symbolDen]
  | cons β L ih =>
    simp only [listSymbol, symbolDen, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
    have h := sineSymbol_mul β
    rw [show 2 * (L.length + 1) = 2 + 2 * L.length by ring, pow_add, map_mul]
    linear_combination (PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2) * ih +
      ((L.map sineSymbol).prod * (L.map fun β => 1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2).prod) * h

/-- **Closed form of the combination symbol**:
`combSymbol L e · ∏(1 + β²X²) = ∏β² · X^{2|L|} e(−1/X²)`, i.e. the symbol is the expansion of
`e(−1/w²)/P_L(−1/w²)` at `w = 0`. -/
theorem combSymbol_mul_symbolDen (L : List ℂ) {e : Polynomial ℂ} (he : e.natDegree ≤ L.length) :
    combSymbol L e * symbolDen L =
      PowerSeries.C ((L.map fun β => β ^ 2).prod) * (evenRev L.length e : PowerSeries ℂ) := by
  induction L generalizing e with
  | nil =>
    have he0 : e.natDegree = 0 := by simpa using he
    simp [combSymbol, symbolDen, evenRev]
  | cons β L ih =>
    have hq := natDegree_divByMonic_X_sub_C_le (n := L.length) (by simpa using he) (β ^ 2)
    have h1 := ih hq
    have h2 := listSymbol_mul_symbolDen L
    have h3 := sineSymbol_mul β
    have h4 := congrArg (fun p : Polynomial ℂ => (p : PowerSeries ℂ))
      (evenRev_succ (n := L.length) (by simpa using he) (β ^ 2))
    simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X] at h4
    simp only [combSymbol, listSymbol, symbolDen, List.map_cons, List.prod_cons,
      List.length_cons] at h1 h2 ⊢
    rw [h4, map_mul, show 2 * (L.length + 1) = 2 + 2 * L.length by ring, pow_add]
    linear_combination (PowerSeries.C (Polynomial.eval (β ^ 2) e) * PowerSeries.C (β ^ 2) *
        PowerSeries.X ^ 2) * h2 -
      (PowerSeries.C (β ^ 2) * (1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2)) * h1 +
      (PowerSeries.C (Polynomial.eval (β ^ 2) e) * (L.map sineSymbol).prod *
        (L.map fun β => 1 + PowerSeries.C (β ^ 2) * PowerSeries.X ^ 2).prod) * h3

end Symbols


end

end RHTower
