import Mathlib

open Complex MeasureTheory
open scoped BigOperators

/-!
# Arbitrary-genus primary factors and canonical products

For every finite genus `g`, this file constructs the Weierstrass primary factor

`E_g(z) = (1 - z) exp(∑_{m=1}^g z^m / m)`

and proves the uniform estimate

`‖E_g(z) - 1‖ ≤ exp(g) ‖z‖^(g+1)` for `‖z‖ ≤ 1`.

The estimate yields locally uniform convergence, and hence entireness, of arbitrarily indexed
canonical products whenever the `(g+1)`-power of the factor weights is summable.  No enumeration
or countability hypothesis is required.
-/

namespace HTGeometry

noncomputable def primaryExponent (g : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range g, z ^ (k + 1) / (k + 1 : ℂ)

noncomputable def primaryFactor (g : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (primaryExponent g z)

theorem primaryExponent_hasDerivAt (g : ℕ) (z : ℂ) :
    HasDerivAt (primaryExponent g) (∑ k ∈ Finset.range g, z ^ k) z := by
  change HasDerivAt
    (fun w : ℂ => ∑ k ∈ Finset.range g, w ^ (k + 1) / (k + 1 : ℂ))
    (∑ k ∈ Finset.range g, z ^ k) z
  have h : HasDerivAt
      (fun w : ℂ => ∑ k ∈ Finset.range g, w ^ (k + 1) / (k + 1 : ℂ))
      (∑ k ∈ Finset.range g, (k + 1 : ℂ) * z ^ k / (k + 1 : ℂ)) z :=
    .fun_sum fun k _ => by
      simpa only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one,
        Nat.cast_add, Nat.cast_one] using
        ((hasDerivAt_id z).pow (k + 1)).div_const (k + 1 : ℂ)
  convert h using 1
  congr with k
  field_simp

theorem geom_identity (g : ℕ) (z : ℂ) :
    (1 - z) * (∑ k ∈ Finset.range g, z ^ k) - 1 = -z ^ g := by
  have h := geom_sum_mul z g
  calc
    (1 - z) * (∑ k ∈ Finset.range g, z ^ k) - 1 =
        -((∑ k ∈ Finset.range g, z ^ k) * (z - 1)) - 1 := by ring
    _ = -(z ^ g - 1) - 1 := by rw [h]
    _ = -z ^ g := by ring

theorem primaryFactor_hasDerivAt (g : ℕ) (z : ℂ) :
    HasDerivAt (primaryFactor g)
      (-z ^ g * Complex.exp (primaryExponent g z)) z := by
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have hexp := (primaryExponent_hasDerivAt g z).cexp
  change HasDerivAt
    (fun w : ℂ => (1 - w) * Complex.exp (primaryExponent g w)) _ z
  apply (hsub.mul hexp).congr_deriv
  have hg := geom_identity g z
  calc
    -1 * Complex.exp (primaryExponent g z) +
        (1 - z) *
          (Complex.exp (primaryExponent g z) *
            ∑ k ∈ Finset.range g, z ^ k) =
        ((1 - z) * (∑ k ∈ Finset.range g, z ^ k) - 1) *
          Complex.exp (primaryExponent g z) := by ring
    _ = -(z ^ g) * Complex.exp (primaryExponent g z) := by rw [hg]

@[simp] theorem primaryExponent_zero (z : ℂ) :
    primaryExponent 0 z = 0 := by
  simp [primaryExponent]

theorem primaryExponent_succ (g : ℕ) (z : ℂ) :
    primaryExponent (g + 1) z =
      primaryExponent g z + z ^ (g + 1) / (g + 1 : ℂ) := by
  simp [primaryExponent, Finset.sum_range_succ]

theorem primaryExponent_re_le (g : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (primaryExponent g z).re ≤ g := by
  induction g with
  | zero => simp
  | succ g ih =>
      rw [primaryExponent_succ]
      simp only [Complex.add_re, Nat.cast_add, Nat.cast_one]
      have hterm :
          (z ^ (g + 1) / (g + 1 : ℂ)).re ≤ 1 := by
        calc
          (z ^ (g + 1) / (g + 1 : ℂ)).re ≤
              ‖z ^ (g + 1) / (g + 1 : ℂ)‖ :=
            Complex.re_le_norm _
          _ = ‖z‖ ^ (g + 1) / ((g : ℝ) + 1) := by
            rw [norm_div, norm_pow]
            rw [show (g : ℂ) + 1 = (((g : ℝ) + 1 : ℝ) : ℂ) by norm_num]
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by positivity)]
          _ ≤ 1 := by
            have hp : ‖z‖ ^ (g + 1) ≤ 1 :=
              pow_le_one₀ (norm_nonneg z) hz
            have hd : (1 : ℝ) ≤ (g : ℝ) + 1 := by
              have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
              linarith
            apply (div_le_one (by positivity)).2
            exact hp.trans hd
      linarith

@[simp] theorem primaryFactor_zero (g : ℕ) :
    primaryFactor g 0 = 1 := by
  simp [primaryFactor, primaryExponent]

theorem primaryFactor_sub_one_norm_le (g : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖primaryFactor g z - 1‖ ≤ Real.exp g * ‖z‖ ^ (g + 1) := by
  set f' : ℝ → ℂ := fun t =>
    -(z ^ (g + 1)) * (t : ℂ) ^ g *
      Complex.exp (primaryExponent g ((t : ℂ) * z)) with hf'def
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => primaryFactor g ((s : ℂ) * z)) (f' t) t := by
    intro t _
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const z
    have hcomp := (primaryFactor_hasDerivAt g ((t : ℂ) * z)).comp t hline
    change HasDerivAt
      ((primaryFactor g) ∘ fun s : ℝ => (s : ℂ) * z) _ t
    apply hcomp.congr_deriv
    simp only [hf'def, mul_pow]
    ring
  have hcont : Continuous f' := by
    simp only [hf'def, primaryExponent]
    fun_prop
  have hint : IntervalIntegrable f' volume 0 1 := hcont.intervalIntegrable 0 1
  have hrep : primaryFactor g z - 1 = ∫ t in (0 : ℝ)..1, f' t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp [primaryFactor_zero]
  have hptwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖f' t‖ ≤ Real.exp g * ‖z‖ ^ (g + 1) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have htz : ‖(t : ℂ) * z‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact mul_le_one₀ ht1 (norm_nonneg z) hz
    have hpre : (primaryExponent g ((t : ℂ) * z)).re ≤ g :=
      primaryExponent_re_le g htz
    simp only [hf'def, norm_mul, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht0, Complex.norm_exp]
    have htpow : t ^ g ≤ 1 := pow_le_one₀ ht0 ht1
    have hexp :
        Real.exp (primaryExponent g ((t : ℂ) * z)).re ≤ Real.exp g :=
      Real.exp_le_exp.mpr hpre
    calc
      ‖z‖ ^ (g + 1) * t ^ g *
          Real.exp (primaryExponent g ((t : ℂ) * z)).re ≤
          ‖z‖ ^ (g + 1) * 1 * Real.exp g := by
            gcongr
      _ = Real.exp g * ‖z‖ ^ (g + 1) := by ring
  rw [hrep]
  calc
    ‖∫ t in (0 : ℝ)..1, f' t‖ ≤ ∫ t in (0 : ℝ)..1, ‖f' t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _t in (0 : ℝ)..1, Real.exp g * ‖z‖ ^ (g + 1) := by
      refine intervalIntegral.integral_mono_on (by norm_num) hint.norm
        (Continuous.intervalIntegrable (by fun_prop) 0 1) hptwise
    _ = Real.exp g * ‖z‖ ^ (g + 1) := by simp

open Filter Topology Metric

noncomputable def canonicalProduct {ι : Type*}
    (g : ℕ) (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, primaryFactor g (z / a i)

theorem canonicalProduct_hasProdLocallyUniformlyOn {ι : Type*}
    (g : ℕ) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (g + 1))) :
    HasProdLocallyUniformlyOn (fun i z => primaryFactor g (z / a i))
      (canonicalProduct g a) Set.univ := by
  have hball : ∀ S : ℝ, 0 < S →
      HasProdLocallyUniformlyOn (fun i z => primaryFactor g (z / a i))
        (canonicalProduct g a) (Metric.ball 0 S) := by
    intro S hSpos
    set f : ι → ℂ → ℂ := fun i z => primaryFactor g (z / a i) - 1 with hf
    have hu : Summable (fun i =>
        (Real.exp g * S ^ (g + 1)) * (1 / ‖a i‖ ^ (g + 1))) :=
      hsum.mul_left _
    have hev : ∀ᶠ i in cofinite, S ≤ ‖a i‖ := by
      have htend : Tendsto (fun i => 1 / ‖a i‖ ^ (g + 1)) cofinite (𝓝 0) :=
        hsum.tendsto_cofinite_zero
      have hlt : ∀ᶠ i in cofinite,
          1 / ‖a i‖ ^ (g + 1) < 1 / S ^ (g + 1) :=
        htend.eventually_lt_const (by positivity)
      filter_upwards [hlt] with i hi
      have haipos : 0 < ‖a i‖ :=
        (norm_nonneg _).lt_of_ne (Ne.symm (norm_ne_zero_iff.mpr (ha i)))
      have hpow : S ^ (g + 1) < ‖a i‖ ^ (g + 1) :=
        lt_of_one_div_lt_one_div (pow_pos haipos _) hi
      exact le_of_lt (lt_of_pow_lt_pow_left₀ (g + 1) (norm_nonneg _) hpow)
    have hbound : ∀ᶠ i in cofinite, ∀ z ∈ Metric.ball (0 : ℂ) S,
        ‖f i z‖ ≤
          (Real.exp g * S ^ (g + 1)) * (1 / ‖a i‖ ^ (g + 1)) := by
      filter_upwards [hev] with i hi z hz
      have hzS : ‖z‖ < S := mem_ball_zero_iff.mp hz
      have haipos : 0 < ‖a i‖ := lt_of_lt_of_le hSpos hi
      have hzlt : ‖z‖ < ‖a i‖ := lt_of_lt_of_le hzS hi
      have hdiv : ‖z / a i‖ = ‖z‖ / ‖a i‖ := norm_div z (a i)
      have hle1 : ‖z / a i‖ ≤ 1 := by
        rw [hdiv]
        exact le_of_lt ((div_lt_one haipos).mpr hzlt)
      calc
        ‖f i z‖ = ‖primaryFactor g (z / a i) - 1‖ := by simp only [hf]
        _ ≤ Real.exp g * ‖z / a i‖ ^ (g + 1) :=
          primaryFactor_sub_one_norm_le g hle1
        _ = Real.exp g * ‖z‖ ^ (g + 1) *
            (1 / ‖a i‖ ^ (g + 1)) := by
              rw [hdiv, div_pow, div_eq_mul_one_div]
              ring
        _ ≤ (Real.exp g * S ^ (g + 1)) *
            (1 / ‖a i‖ ^ (g + 1)) := by
              gcongr
    have hcts : ∀ i, ContinuousOn (f i) (Metric.ball (0 : ℂ) S) := by
      intro i
      have : Continuous (f i) := by
        simp only [hf, primaryFactor, primaryExponent]
        fun_prop
      exact this.continuousOn
    have hpl :=
      Summable.hasProdLocallyUniformlyOn_one_add isOpen_ball hu hbound hcts
    convert hpl using 1
    · ext i z
      simp only [hf]
      ring
    · funext z
      exact tprod_congr (fun i => by simp only [hf]; ring)
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hKcompact
  obtain ⟨S, hSpos, hKS⟩ : ∃ S : ℝ, 0 < S ∧ K ⊆ Metric.ball (0 : ℂ) S :=
    hKcompact.isBounded.subset_ball_lt 0 0
  exact ((hball S hSpos).mono hKS).hasProdUniformlyOn_of_isCompact hKcompact

theorem canonicalProduct_analytic {ι : Type*}
    (g : ℕ) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (g + 1))) :
    AnalyticOnNhd ℂ (canonicalProduct g a) Set.univ := by
  have hpl := canonicalProduct_hasProdLocallyUniformlyOn g a ha hsum
  have hdiff : ∀ᶠ s : Finset ι in atTop,
      DifferentiableOn ℂ
        (fun z => ∏ i ∈ s, primaryFactor g (z / a i)) Set.univ := by
    exact Eventually.of_forall fun s => (Differentiable.fun_finsetProd fun i _ => by
      simp only [primaryFactor, primaryExponent]
      fun_prop).differentiableOn
  exact (show TendstoLocallyUniformlyOn
      (fun s : Finset ι => fun z => ∏ i ∈ s, primaryFactor g (z / a i))
      (canonicalProduct g a) atTop Set.univ from hpl).differentiableOn
        hdiff isOpen_univ |>.analyticOnNhd isOpen_univ

/-- At every fixed point, the centered primary factors form an absolutely summable series. -/
theorem canonicalProduct_sub_one_norm_summable {ι : Type*}
    (g : ℕ) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (g + 1))) (z : ℂ) :
    Summable (fun i => ‖primaryFactor g (z / a i) - 1‖) := by
  let S : ℝ := ‖z‖ + 1
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hu : Summable (fun i =>
      (Real.exp g * S ^ (g + 1)) * (1 / ‖a i‖ ^ (g + 1))) :=
    hsum.mul_left _
  have hev : ∀ᶠ i in cofinite, S ≤ ‖a i‖ := by
    have htend : Tendsto (fun i => 1 / ‖a i‖ ^ (g + 1)) cofinite (𝓝 0) :=
      hsum.tendsto_cofinite_zero
    have hlt : ∀ᶠ i in cofinite,
        1 / ‖a i‖ ^ (g + 1) < 1 / S ^ (g + 1) :=
      htend.eventually_lt_const (by positivity)
    filter_upwards [hlt] with i hi
    have haipos : 0 < ‖a i‖ :=
      (norm_nonneg _).lt_of_ne (Ne.symm (norm_ne_zero_iff.mpr (ha i)))
    have hpow : S ^ (g + 1) < ‖a i‖ ^ (g + 1) :=
      lt_of_one_div_lt_one_div (pow_pos haipos _) hi
    exact le_of_lt (lt_of_pow_lt_pow_left₀ (g + 1) (norm_nonneg _) hpow)
  refine hu.of_norm_bounded_eventually ?_
  filter_upwards [hev] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hzS : ‖z‖ < S := by
    dsimp [S]
    linarith
  have haipos : 0 < ‖a i‖ := lt_of_lt_of_le hSpos hi
  have hzlt : ‖z‖ < ‖a i‖ := lt_of_lt_of_le hzS hi
  have hdiv : ‖z / a i‖ = ‖z‖ / ‖a i‖ := norm_div z (a i)
  have hle1 : ‖z / a i‖ ≤ 1 := by
    rw [hdiv]
    exact le_of_lt ((div_lt_one haipos).mpr hzlt)
  calc
    ‖primaryFactor g (z / a i) - 1‖ ≤
        Real.exp g * ‖z / a i‖ ^ (g + 1) :=
      primaryFactor_sub_one_norm_le g hle1
    _ = Real.exp g * ‖z‖ ^ (g + 1) *
        (1 / ‖a i‖ ^ (g + 1)) := by
          rw [hdiv, div_pow, div_eq_mul_one_div]
          ring
    _ ≤ (Real.exp g * S ^ (g + 1)) *
        (1 / ‖a i‖ ^ (g + 1)) := by
          gcongr

noncomputable def canonicalWeightProduct {ι : Type*}
    (g : ℕ) (q : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, primaryFactor g (z * q i)

theorem canonicalWeightProduct_hasProdLocallyUniformlyOn {ι : Type*}
    (g : ℕ) (q : ι → ℂ) (hq : ∀ i, q i ≠ 0)
    (hsum : Summable (fun i => ‖q i‖ ^ (g + 1))) :
    HasProdLocallyUniformlyOn (fun i z => primaryFactor g (z * q i))
      (canonicalWeightProduct g q) Set.univ := by
  let a : ι → ℂ := fun i => (q i)⁻¹
  have ha : ∀ i, a i ≠ 0 := fun i => inv_ne_zero (hq i)
  have haSum : Summable (fun i => 1 / ‖a i‖ ^ (g + 1)) := by
    convert hsum using 1
    funext i
    simp only [a, norm_inv, inv_pow]
    field_simp
  have h := canonicalProduct_hasProdLocallyUniformlyOn g a ha haSum
  convert h using 1
  · ext i z
    simp [a, div_eq_mul_inv]
  · funext z
    simp [canonicalProduct, canonicalWeightProduct, a, div_eq_mul_inv]

/-- Absolute convergence of the centered weighted factors at every point. -/
theorem canonicalWeightProduct_sub_one_norm_summable {ι : Type*}
    (g : ℕ) (q : ι → ℂ) (hq : ∀ i, q i ≠ 0)
    (hsum : Summable (fun i => ‖q i‖ ^ (g + 1))) (z : ℂ) :
    Summable (fun i => ‖primaryFactor g (z * q i) - 1‖) := by
  let a : ι → ℂ := fun i => (q i)⁻¹
  have ha : ∀ i, a i ≠ 0 := fun i => inv_ne_zero (hq i)
  have haSum : Summable (fun i => 1 / ‖a i‖ ^ (g + 1)) := by
    convert hsum using 1
    funext i
    simp only [a, norm_inv, inv_pow]
    field_simp
  simpa [a, div_eq_mul_inv] using
    canonicalProduct_sub_one_norm_summable g a ha haSum z

theorem canonicalWeightProduct_analytic {ι : Type*}
    (g : ℕ) (q : ι → ℂ) (hq : ∀ i, q i ≠ 0)
    (hsum : Summable (fun i => ‖q i‖ ^ (g + 1))) :
    AnalyticOnNhd ℂ (canonicalWeightProduct g q) Set.univ := by
  let a : ι → ℂ := fun i => (q i)⁻¹
  have ha : ∀ i, a i ≠ 0 := fun i => inv_ne_zero (hq i)
  have haSum : Summable (fun i => 1 / ‖a i‖ ^ (g + 1)) := by
    convert hsum using 1
    funext i
    simp only [a, norm_inv, inv_pow]
    field_simp
  have heq : canonicalWeightProduct g q = canonicalProduct g a := by
    funext z
    apply tprod_congr
    intro i
    simp [a, div_eq_mul_inv]
  rw [heq]
  exact canonicalProduct_analytic g a ha haSum

end HTGeometry
