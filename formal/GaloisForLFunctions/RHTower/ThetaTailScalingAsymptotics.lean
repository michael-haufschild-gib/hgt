import GaloisForLFunctions.RHTower.ThetaSeedHalfLineDivision
import GaloisForLFunctions.RHTower.ThetaRenewalProbabilityPhase
import GaloisForLFunctions.RHTower.ThetaSourceTailRatioCalculus

/-!
# Laplace asymptotics at the theta tail

A continuous `f` has a *theta tail* if `f(x+t) ≤ C₀ e^{(B − 2π e^{2x}) t} f(x)` for large `x` and
`f(x + τ e^{-2x}) / f(x) → e^{-2πτ}`.  The literal seed `h` and source `k` have theta tails
(`k/h → 1` by the first-atom approximation).

* Weighted tail integrals: `∫₀^∞ t^m e^{ct} f(x+t) dt ≤ K e^{-2(m+1)x} f(x)`.
* Laplace asymptotics: if `|K(t)| ≤ A t^m e^{ct}` and `K(t)/t^m → a` as `t → 0⁺`, then
  `e^{2(m+1)x} ∫₀^∞ K(t) f(x+t) dt / f(x) → a m!/(2π)^{m+1}` (substitution `t = τ e^{-2x}` and
  dominated convergence).
* One division step raises the tail order by one: `e^{4jx} g/f → a` implies
  `e^{4(j+1)x} T_β g/f → a β²/(2π)²`; hence `e^{4|L|x} T_L f/f → ∏β²/(2π)^{2|L|}`, and the
  partial-fraction combination realizing `e` of degree `n ≤ |L|` has
  `e^{4dx} u/f → (−1)^d e_n ∏(−β²)/(2π)^{2d}`, `d = |L| − n`.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Functions with the theta double-exponential tail -/

/-- A continuous function, positive near `+∞`, with the theta tail: for `x ≥ X₀`, `t ≥ 0`,
`f(x+t) ≤ C₀ e^{(B − 2π e^{2x}) t} f(x)`, and the scaling law
`f(x + τ e^{-2x}) / f(x) → e^{-2πτ}` for every `τ ≥ 0`. -/
structure ThetaTypeTail (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  shift : ∃ C₀ B X₀ : ℝ, 0 ≤ B ∧ 0 ≤ X₀ ∧ ∀ x, X₀ ≤ x → 0 < f x ∧ ∀ t, 0 ≤ t →
    f (x + t) ≤ C₀ * Real.exp ((B - 2 * Real.pi * Real.exp (2 * x)) * t) * f x
  scaling : ∀ τ, 0 ≤ τ → Tendsto (fun x => f (x + τ * Real.exp (-(2 * x))) / f x) atTop
    (𝓝 (Real.exp (-(2 * Real.pi * τ))))

theorem norm_csin_mul_ofReal_le_mul_exp (β : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.sin (β * t)‖ ≤ ‖β‖ * t * Real.exp (|β.im| * t) := by
  have h := norm_csin_le_norm_mul_exp (β * t)
  rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_add, abs_mul, abs_of_nonneg ht] at h

theorem tendsto_csin_mul_div (β : ℂ) :
    Tendsto (fun t : ℝ => Complex.sin (β * t) / (t : ℂ)) (𝓝[>] 0) (𝓝 β) := by
  have hd : HasDerivAt (fun t : ℝ => Complex.sin (β * t)) (β * Complex.cos (β * (0 : ℝ))) 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).const_mul β).csin.comp_ofReal
    simpa using this
  have h := hd.tendsto_slope_zero
  simp only [zero_add, Complex.ofReal_zero, mul_zero, Complex.sin_zero, sub_zero,
    Complex.cos_zero, mul_one] at h
  refine (h.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)).congr fun t => ?_
  rw [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

/-- The zero numerator gives the zero combination. -/
theorem listComb_zero (D : List ℂ → ℝ → ℂ) (L : List ℂ) : listComb D L 0 = fun _ => 0 := by
  induction L with
  | nil => funext x; simp [listComb_nil]
  | cons β L ih => funext x; simp [listComb_cons, Polynomial.zero_divByMonic, ih]

/-- `∏(−β²) = (−1)^{|L|} ∏ β²`. -/
theorem prod_map_neg_sq (L : List ℂ) :
    (L.map fun β => -β ^ 2).prod = (-1) ^ L.length * (L.map fun β => β ^ 2).prod := by
  induction L with
  | nil => simp
  | cons β L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    ring

namespace ThetaTypeTail

variable {f : ℝ → ℝ}

theorem eventually_pos (hf : ThetaTypeTail f) : ∀ᶠ x in atTop, 0 < f x := by
  obtain ⟨C₀, B, X₀, -, -, h⟩ := hf.shift
  filter_upwards [eventually_ge_atTop X₀] with x hx using (h x hx).1

/-- **Weighted tail integrals.**  `∫₀^∞ t^m e^{ct} f(x+t) dt ≤ K e^{-2(m+1)x} f(x)` for large `x`. -/
theorem exists_integral_le (hf : ThetaTypeTail f) (m : ℕ) (c : ℝ) :
    ∃ K X : ℝ, ∀ x, X ≤ x →
      IntegrableOn (fun t => t ^ m * Real.exp (c * t) * f (x + t)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (c * t) * f (x + t) ≤
        K * Real.exp (-(2 * (m + 1) * x)) * f x := by
  obtain ⟨C₀, B, X₀, hB, hX₀, h⟩ := hf.shift
  have hπ := Real.pi_pos
  refine ⟨max C₀ 0 * m.factorial / Real.pi ^ (m + 1), max X₀ ((B + |c|) / (2 * Real.pi)),
    fun x hx => ?_⟩
  have hxX₀ : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := hX₀.trans hxX₀
  obtain ⟨hfx, hsh⟩ := h x hxX₀
  set a := 2 * Real.pi * Real.exp (2 * x) - B - c
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have ha : Real.pi * Real.exp (2 * x) ≤ a := by
    have h1 : (B + |c|) / (2 * Real.pi) ≤ x := (le_max_right _ _).trans hx
    rw [div_le_iff₀ (by positivity)] at h1
    have := le_abs_self c
    simp only [a]; nlinarith
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hbound : ∀ t, 0 < t → t ^ m * Real.exp (c * t) * f (x + t) ≤
      max C₀ 0 * f x * (t ^ m * Real.exp (-(a * t))) := by
    intro t ht
    have h2 := hsh t ht.le
    calc t ^ m * Real.exp (c * t) * f (x + t) ≤ t ^ m * Real.exp (c * t) *
          (max C₀ 0 * Real.exp ((B - 2 * Real.pi * Real.exp (2 * x)) * t) * f x) :=
          mul_le_mul_of_nonneg_left (h2.trans (by gcongr; exact le_max_left _ _))
            (by positivity)
      _ = max C₀ 0 * f x * (t ^ m * Real.exp (-(a * t))) := by
          rw [show -(a * t) = c * t + (B - 2 * Real.pi * Real.exp (2 * x)) * t by simp only [a]; ring,
            Real.exp_add]
          ring
  have hmeas : AEStronglyMeasurable (fun t => t ^ m * Real.exp (c * t) * f (x + t))
      (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous fun t : ℝ => t ^ m * Real.exp (c * t)).mul
      (hf.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hnn : ∀ t, 0 < t → 0 ≤ t ^ m * Real.exp (c * t) * f (x + t) := fun t ht =>
    mul_nonneg (mul_nonneg (pow_nonneg ht.le m) (Real.exp_pos _).le)
      (h (x + t) (by linarith)).1.le
  have hint : IntegrableOn (fun t => t ^ m * Real.exp (c * t) * f (x + t)) (Ioi 0) := by
    refine ((integrableOn_natPow_mul_exp_neg_mul_Ioi m hapos).const_mul (max C₀ 0 * f x)).mono'
      hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    rw [Real.norm_of_nonneg (hnn t ht')]
    exact hbound t ht'
  refine ⟨hint, ?_⟩
  calc ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (c * t) * f (x + t)
      ≤ ∫ t in Ioi (0 : ℝ), max C₀ 0 * f x * (t ^ m * Real.exp (-(a * t))) :=
        setIntegral_mono_on hint ((integrableOn_natPow_mul_exp_neg_mul_Ioi m hapos).const_mul _)
          measurableSet_Ioi fun t ht => hbound t ht
    _ = max C₀ 0 * f x * (m.factorial / a ^ (m + 1)) := by
        rw [integral_const_mul, integral_natPow_mul_exp_neg_mul_Ioi m hapos]
    _ ≤ max C₀ 0 * f x * (m.factorial / (Real.pi * Real.exp (2 * x)) ^ (m + 1)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
          (by positivity) (pow_le_pow_left₀ (by positivity) ha _))
          (mul_nonneg (le_max_right _ _) hfx.le)
    _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul, show -(2 * ((m : ℝ) + 1) * x) =
          -(((m + 1 : ℕ) : ℝ) * (2 * x)) by push_cast; ring, Real.exp_neg]
        field_simp

theorem tendsto_mul_exp_neg_two_nhdsWithin {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun x : ℝ => τ * Real.exp (-(2 * x))) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall fun x => mul_pos hτ (Real.exp_pos _))
  have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul τ
  simpa [Function.comp] using this

/-- **Laplace asymptotics at the theta tail.**  If `‖K t‖ ≤ A t^m e^{ct}` for `t > 0` and
`K(t)/t^m → a` as `t → 0⁺`, then `e^{2(m+1)x} ∫₀^∞ K(t) f(x+t) dt / f(x) → a m!/(2π)^{m+1}`: the
substitution `t = τ e^{-2x}` and the scaling law reduce the integral to `∫ a τ^m e^{-2πτ} dτ`. -/
theorem tendsto_integral_kernel (hf : ThetaTypeTail f) {K : ℝ → ℂ} (hKm : StronglyMeasurable K)
    (m : ℕ) {A c : ℝ} (hK : ∀ t, 0 < t → ‖K t‖ ≤ A * t ^ m * Real.exp (c * t)) {a : ℂ}
    (hK0 : Tendsto (fun t => K t / (t : ℂ) ^ m) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun x => ((Real.exp (2 * (m + 1) * x) : ℝ) : ℂ) *
      (∫ t in Ioi (0 : ℝ), K t * (f (x + t) : ℂ)) / (f x : ℂ)) atTop
      (𝓝 (a * m.factorial / (2 * Real.pi) ^ (m + 1))) := by
  obtain ⟨C₀, B, X₀, hB, hX₀, h⟩ := hf.shift
  have hπ := Real.pi_pos
  set F : ℝ → ℝ → ℂ := fun x τ => ((Real.exp (2 * x) ^ m : ℝ) : ℂ) *
    K (τ * Real.exp (-(2 * x))) * ((f (x + τ * Real.exp (-(2 * x))) / f x : ℝ) : ℂ)
  -- the substitution `t = τ e^{-2x}`
  have hsub : ∀ x, X₀ ≤ x → ((Real.exp (2 * (m + 1) * x) : ℝ) : ℂ) *
      (∫ t in Ioi (0 : ℝ), K t * (f (x + t) : ℂ)) / (f x : ℂ) = ∫ τ in Ioi (0 : ℝ), F x τ := by
    intro x hx
    have hfx := (h x hx).1
    set b := Real.exp (-(2 * x)) with hb
    have hb0 : 0 < b := Real.exp_pos _
    have hcv := integral_comp_mul_right_Ioi (fun t => K t * (f (x + t) : ℂ)) 0 hb0
    rw [zero_mul] at hcv
    have hcv' : ∫ t in Ioi (0 : ℝ), K t * (f (x + t) : ℂ) =
        b • ∫ τ in Ioi (0 : ℝ), K (τ * b) * (f (x + τ * b) : ℂ) := by
      rw [hcv, smul_smul, mul_inv_cancel₀ hb0.ne', one_smul]
    have hy : Real.exp (2 * (m + 1) * x) * b = Real.exp (2 * x) ^ m := by
      rw [hb, ← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring
    have hF : ∀ τ, F x τ = ((Real.exp (2 * x) ^ m / f x : ℝ) : ℂ) *
        (K (τ * b) * (f (x + τ * b) : ℂ)) := fun τ => by
      simp only [F, ← hb]; push_cast; field_simp
    rw [hcv', Complex.real_smul, integral_congr_ae (Eventually.of_forall hF), integral_const_mul,
      ← hy]
    push_cast
    ring
  -- the dominating function
  set y₁ := max 1 ((|c| + B) / Real.pi)
  have hev : ∀ᶠ x in atTop, X₀ ≤ x ∧ y₁ ≤ Real.exp (2 * x) := by
    have := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    filter_upwards [eventually_ge_atTop X₀, this.eventually_ge_atTop y₁] with x hx hy
    exact ⟨hx, hy⟩
  set bound : ℝ → ℝ := fun τ => max A 0 * max C₀ 0 * (τ ^ m * Real.exp (-(Real.pi * τ)))
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    (integrableOn_natPow_mul_exp_neg_mul_Ioi m hπ).const_mul _
  have hmeas : ∀ᶠ x in atTop, AEStronglyMeasurable (F x) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun x => by
      refine (aestronglyMeasurable_const.mul ?_).mul ?_
      · exact (hKm.comp_measurable (measurable_id.mul_const _)).aestronglyMeasurable
      · exact (Complex.continuous_ofReal.comp ((hf.continuous.comp
          (continuous_const.add (continuous_id.mul continuous_const))).div_const _)).aestronglyMeasurable
  have hbd : ∀ᶠ x in atTop, ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))), ‖F x τ‖ ≤ bound τ := by
    filter_upwards [hev] with x ⟨hx, hy⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hτ' : 0 < τ := hτ
    obtain ⟨hfx, hsh⟩ := h x hx
    simp only [F, norm_mul, Complex.norm_real]
    set b := Real.exp (-(2 * x))
    set y := Real.exp (2 * x)
    have hyb : y * b = 1 := by simp only [y, b]; rw [← Real.exp_add]; simp
    have hy0 : 0 < y := Real.exp_pos _
    have hb0 : 0 < b := Real.exp_pos _
    have hτb : 0 < τ * b := mul_pos hτ' hb0
    have hratio : f (x + τ * b) / f x ≤ max C₀ 0 * Real.exp (B * (τ * b) - 2 * Real.pi * τ) := by
      rw [div_le_iff₀ hfx]
      refine (hsh _ hτb.le).trans ?_
      have : (B - 2 * Real.pi * y) * (τ * b) = B * (τ * b) - 2 * Real.pi * τ := by
        have : y * (τ * b) = τ := by rw [mul_left_comm, hyb, mul_one]
        linear_combination (-(2 * Real.pi)) * this
      rw [this]
      gcongr; exact le_max_left _ _
    have hpos : 0 ≤ f (x + τ * b) / f x := div_nonneg (h (x + τ * b) (by linarith)).1.le hfx.le
    have hKb := hK (τ * b) hτb
    have hexp : (c + B) * (τ * b) ≤ Real.pi * τ := by
      have h1 : (|c| + B) / Real.pi ≤ y := (le_max_right _ _).trans hy
      rw [div_le_iff₀ hπ] at h1
      have h2 : (c + B) * (τ * b) ≤ (|c| + B) * (τ * b) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hτb.le
      have h3 : (|c| + B) * (τ * b) ≤ y * Real.pi * (τ * b) :=
        mul_le_mul_of_nonneg_right (by linarith) hτb.le
      have h4 : y * Real.pi * (τ * b) = Real.pi * τ := by
        rw [show y * Real.pi * (τ * b) = Real.pi * τ * (y * b) by ring, hyb, mul_one]
      linarith
    have key : y ^ m * (τ * b) ^ m = τ ^ m := by
      rw [mul_pow, mul_left_comm, ← mul_pow, hyb, one_pow, mul_one]
    rw [Real.norm_of_nonneg (pow_nonneg hy0.le m), Real.norm_of_nonneg hpos]
    calc y ^ m * ‖K (τ * b)‖ * (f (x + τ * b) / f x)
        ≤ y ^ m * (max A 0 * (τ * b) ^ m * Real.exp (c * (τ * b))) *
            (max C₀ 0 * Real.exp (B * (τ * b) - 2 * Real.pi * τ)) := by
          gcongr
          exact hKb.trans (by gcongr; exact le_max_left _ _)
      _ = max A 0 * max C₀ 0 * (y ^ m * (τ * b) ^ m) *
            (Real.exp (c * (τ * b)) * Real.exp (B * (τ * b) - 2 * Real.pi * τ)) := by ring
      _ = max A 0 * max C₀ 0 * (τ ^ m * Real.exp ((c + B) * (τ * b) - 2 * Real.pi * τ)) := by
          rw [key, ← Real.exp_add, show c * (τ * b) + (B * (τ * b) - 2 * Real.pi * τ) =
            (c + B) * (τ * b) - 2 * Real.pi * τ by ring]
          ring
      _ ≤ bound τ := by
          simp only [bound]
          gcongr
          linarith
  have hpt : ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))), Tendsto (fun x => F x τ) atTop
      (𝓝 (a * (τ : ℂ) ^ m * ((Real.exp (-(2 * Real.pi * τ)) : ℝ) : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hτ' : 0 < τ := hτ
    have h1 := hK0.comp (tendsto_mul_exp_neg_two_nhdsWithin hτ')
    have h2 := Complex.continuous_ofReal.continuousAt.tendsto.comp (hf.scaling τ hτ'.le)
    have h3 := (h1.const_mul ((τ : ℂ) ^ m)).mul h2
    have h4 : Tendsto (fun x => F x τ) atTop (𝓝 ((τ : ℂ) ^ m * a *
        ((Real.exp (-(2 * Real.pi * τ)) : ℝ) : ℂ))) := by
      have alg : ∀ (T Y B' Kv R : ℂ), T ≠ 0 → Y * B' = 1 →
          T ^ m * (Kv / (T * B') ^ m) * R = Y ^ m * Kv * R := by
        intro T Y B' Kv R hT hYB
        have hB' : B' ≠ 0 := right_ne_zero_of_mul_eq_one hYB
        obtain rfl : Y = B'⁻¹ := eq_inv_of_mul_eq_one_left hYB
        rw [mul_pow, inv_pow]
        field_simp
      refine h3.congr fun x => ?_
      simp only [Function.comp, F]
      have hyb : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by rw [← Real.exp_add]; simp
      have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ'.ne'
      have hyb' : (Real.exp (2 * x) : ℂ) * (Real.exp (-(2 * x)) : ℂ) = 1 := by exact_mod_cast hyb
      rw [Complex.ofReal_mul, Complex.ofReal_pow]
      exact alg _ _ _ _ _ hτ0 hyb'
    convert h4 using 2
    ring
  have hlim := tendsto_integral_filter_of_dominated_convergence bound hmeas hbd hbound_int hpt
  have hval : ∫ τ in Ioi (0 : ℝ), a * (τ : ℂ) ^ m * ((Real.exp (-(2 * Real.pi * τ)) : ℝ) : ℂ) =
      a * m.factorial / (2 * Real.pi) ^ (m + 1) := by
    have h := integral_natPow_mul_exp_neg_mul_Ioi m (by positivity : (0 : ℝ) < 2 * Real.pi)
    simp_rw [mul_assoc a]
    rw [integral_const_mul]
    have h' : ∫ τ in Ioi (0 : ℝ), ((τ : ℂ) ^ m * ((Real.exp (-(2 * Real.pi * τ)) : ℝ) : ℂ)) =
        ((∫ τ in Ioi (0 : ℝ), τ ^ m * Real.exp (-(2 * Real.pi * τ)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall fun τ => by push_cast; ring_nf)
    rw [h', h]
    push_cast
    ring
  rw [hval] at hlim
  exact hlim.congr' (by
    filter_upwards [eventually_ge_atTop X₀] with x hx
    exact (hsub x hx).symm)

/-- **One division step at the tail.**  If `e^{4jx} g(x) / f(x) → a`, then
`e^{4(j+1)x} (T_β g)(x) / f(x) → a β²/(2π)²`. -/
theorem tendsto_outwardSine (hf : ThetaTypeTail f) {g : ℝ → ℂ} (hg : StronglyMeasurable g)
    {j : ℕ} {a : ℂ}
    (hga : Tendsto (fun x => ((Real.exp (4 * j * x) : ℝ) : ℂ) * g x / (f x : ℂ)) atTop (𝓝 a))
    (β : ℂ) :
    Tendsto (fun x => ((Real.exp (4 * (j + 1) * x) : ℝ) : ℂ) * outwardSine β g x / (f x : ℂ))
      atTop (𝓝 (a * β ^ 2 / (2 * Real.pi) ^ 2)) := by
  obtain ⟨C₀, B, X₀, hB, hX₀, h⟩ := hf.shift
  have hfc := hf.continuous
  set E : ℝ → ℝ := fun z => Real.exp (-(4 * j * z))
  set K : ℝ → ℂ := fun t => β * Complex.sin (β * t) * ((E t : ℝ) : ℂ)
  have hKc : Continuous K := by simp only [K, E]; fun_prop
  have hE1 : ∀ z, 0 ≤ z → E z ≤ 1 := fun z hz =>
    Real.exp_le_one_iff.2 (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hKb : ∀ t, 0 < t → ‖K t‖ ≤ ‖β‖ ^ 2 * t ^ 1 * Real.exp (|β.im| * t) := by
    intro t ht
    have hEt : ‖E t‖ = E t := Real.norm_of_nonneg (Real.exp_pos _).le
    rw [show K t = β * Complex.sin (β * t) * ((E t : ℝ) : ℂ) from rfl, norm_mul, norm_mul,
      Complex.norm_real, hEt, pow_one]
    calc ‖β‖ * ‖Complex.sin (β * t)‖ * E t ≤ ‖β‖ * (‖β‖ * t * Real.exp (|β.im| * t)) * 1 := by
          gcongr
          · exact norm_csin_mul_ofReal_le_mul_exp β ht.le
          · exact hE1 t ht.le
      _ = ‖β‖ ^ 2 * t * Real.exp (|β.im| * t) := by ring
  have hK0 : Tendsto (fun t => K t / (t : ℂ) ^ 1) (𝓝[>] 0) (𝓝 (β ^ 2)) := by
    have hE : Tendsto (fun t : ℝ => ((E t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      have : Continuous fun t : ℝ => ((E t : ℝ) : ℂ) := by simp only [E]; fun_prop
      have h0 := this.tendsto 0
      simp only [E, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := ((tendsto_csin_mul_div β).const_mul β).mul hE
    rw [mul_one, ← sq] at this
    refine this.congr fun t => ?_
    simp only [K, pow_one]
    ring
  have hmain : Tendsto (fun x => ((Real.exp (4 * x) : ℝ) : ℂ) *
      (∫ t in Ioi (0 : ℝ), K t * (f (x + t) : ℂ)) / (f x : ℂ)) atTop
      (𝓝 (β ^ 2 / (2 * Real.pi) ^ 2)) := by
    have := hf.tendsto_integral_kernel hKc.stronglyMeasurable 1 hKb hK0
    convert this using 4
    · push_cast; ring_nf
    · norm_num
  -- the remainder
  obtain ⟨K₁, X₁, hK₁⟩ := hf.exists_integral_le 1 |β.im|
  set K₁' := max K₁ 0
  set r : ℝ → ℂ := fun z => g z - a * ((E z : ℝ) : ℂ) * (f z : ℂ)
  have hrm : StronglyMeasurable r := hg.sub ((stronglyMeasurable_const.mul
    ((Complex.continuous_ofReal.comp (by simp only [E]; fun_prop :
      Continuous E)).stronglyMeasurable)).mul
      (Complex.continuous_ofReal.comp hfc).stronglyMeasurable)
  have hr : ∀ ε > 0, ∀ᶠ z in atTop, ‖r z‖ ≤ ε * E z * f z := by
    intro ε hε
    filter_upwards [hga.eventually (Metric.ball_mem_nhds a hε), hf.eventually_pos] with z hz hfz
    rw [dist_eq_norm] at hz
    have hE0 : 0 < E z := Real.exp_pos _
    have heq : r z = ((E z * f z : ℝ) : ℂ) *
        (((Real.exp (4 * j * z) : ℝ) : ℂ) * g z / (f z : ℂ) - a) := by
      have hEe : E z * Real.exp (4 * j * z) = 1 := by
        simp only [E]; rw [← Real.exp_add]; simp
      have hEe' : ((E z : ℝ) : ℂ) * ((Real.exp (4 * j * z) : ℝ) : ℂ) = 1 := by exact_mod_cast hEe
      have hf0 : (f z : ℂ) ≠ 0 := by exact_mod_cast hfz.ne'
      have h1 : ((E z * f z : ℝ) : ℂ) * (((Real.exp (4 * j * z) : ℝ) : ℂ) * g z / (f z : ℂ) - a) =
          ((E z : ℝ) : ℂ) * ((Real.exp (4 * j * z) : ℝ) : ℂ) * g z -
            a * ((E z : ℝ) : ℂ) * (f z : ℂ) := by
        push_cast; field_simp
      rw [h1, hEe', one_mul]
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_pos hE0 hfz).le]
    nlinarith [mul_pos hE0 hfz]
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.1 (hr 1 one_pos)
  set X₄ := max (max X₀ X₁) (max Z₁ 0)
  have hX₄ : ∀ x, X₄ ≤ x → X₀ ≤ x ∧ X₁ ≤ x ∧ Z₁ ≤ x ∧ 0 ≤ x := fun x hx =>
    ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hx),
      (le_max_right _ _).trans ((le_max_left _ _).trans hx),
      (le_max_left _ _).trans ((le_max_right _ _).trans hx),
      (le_max_right _ _).trans ((le_max_right _ _).trans hx)⟩
  have hEadd : ∀ x t, E (x + t) = E x * E t := fun x t => by
    simp only [E]; rw [← Real.exp_add]; ring_nf
  have hEx : ∀ x, Real.exp (4 * (j + 1) * x) * E x = Real.exp (4 * x) := fun x => by
    simp only [E]; rw [← Real.exp_add]; ring_nf
  have hsinb : ∀ t : ℝ, 0 < t → ‖Complex.sin (β * t)‖ ≤ ‖β‖ * (t ^ 1 * Real.exp (|β.im| * t)) :=
    fun t ht => by rw [pow_one, ← mul_assoc]; exact norm_csin_mul_ofReal_le_mul_exp β ht.le
  have hfpos : ∀ x, X₀ ≤ x → ∀ t, 0 ≤ t → 0 < f (x + t) := fun x hx t ht =>
    (h (x + t) (by linarith)).1
  have hint1 : ∀ x, X₄ ≤ x → IntegrableOn (fun t => K t * (f (x + t) : ℂ)) (Ioi 0) := by
    intro x hx
    obtain ⟨hx0, hx1, -, -⟩ := hX₄ x hx
    refine ((hK₁ x hx1).1.const_mul (‖β‖ ^ 2)).mono'
      (hKc.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (hfc.comp (continuous_const.add continuous_id))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hfpos x hx0 t ht'.le).le]
    calc ‖K t‖ * f (x + t) ≤ ‖β‖ ^ 2 * t ^ 1 * Real.exp (|β.im| * t) * f (x + t) :=
          mul_le_mul_of_nonneg_right (hKb t ht') (hfpos x hx0 t ht'.le).le
      _ = _ := by ring
  have hbnd : ∀ ε, ∀ x, X₄ ≤ x → (∀ z, x ≤ z → ‖r z‖ ≤ ε * E z * f z) → 0 ≤ ε →
      IntegrableOn (fun t : ℝ => Complex.sin (β * t) * r (x + t)) (Ioi 0) ∧
      ‖∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * r (x + t)‖ ≤
        ε * ‖β‖ * E x * (K₁' * Real.exp (-(4 * x)) * f x) := by
    intro ε x hx hrx hε
    obtain ⟨hx0, hx1, -, hx00⟩ := hX₄ x hx
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.sin (β * t) * r (x + t))
        (volume.restrict (Ioi 0)) :=
      ((by fun_prop : Continuous fun t : ℝ => Complex.sin (β * t)).aestronglyMeasurable.mul
        (hrm.comp_measurable (measurable_const.add measurable_id)).aestronglyMeasurable)
    have hpt : ∀ t : ℝ, 0 < t → ‖Complex.sin (β * t) * r (x + t)‖ ≤
        ε * ‖β‖ * E x * (t ^ 1 * Real.exp (|β.im| * t) * f (x + t)) := by
      intro t ht
      rw [norm_mul]
      have h1 := hrx (x + t) (by linarith)
      rw [hEadd] at h1
      have hEt := hE1 t ht.le
      have hfxt := (hfpos x hx0 t ht.le).le
      calc ‖Complex.sin (β * t)‖ * ‖r (x + t)‖ ≤ (‖β‖ * (t ^ 1 * Real.exp (|β.im| * t))) *
            (ε * (E x * E t) * f (x + t)) := mul_le_mul (hsinb t ht) h1 (norm_nonneg _)
              (by positivity)
        _ ≤ (‖β‖ * (t ^ 1 * Real.exp (|β.im| * t))) * (ε * (E x * 1) * f (x + t)) := by
            gcongr
        _ = _ := by ring
    have hI : IntegrableOn (fun t : ℝ => Complex.sin (β * t) * r (x + t)) (Ioi 0) :=
      ((hK₁ x hx1).1.const_mul (ε * ‖β‖ * E x)).mono' hmeas (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hpt t ht)
    refine ⟨hI, ?_⟩
    calc ‖∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * r (x + t)‖
        ≤ ∫ t in Ioi (0 : ℝ), ε * ‖β‖ * E x * (t ^ 1 * Real.exp (|β.im| * t) * f (x + t)) :=
          norm_integral_le_of_norm_le ((hK₁ x hx1).1.const_mul _) (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hpt t ht)
      _ = ε * ‖β‖ * E x * ∫ t in Ioi (0 : ℝ), t ^ 1 * Real.exp (|β.im| * t) * f (x + t) :=
          integral_const_mul _ _
      _ ≤ ε * ‖β‖ * E x * (K₁' * Real.exp (-(4 * x)) * f x) := by
          have h2 := (hK₁ x hx1).2
          have e4 : -(2 * (((1 : ℕ) : ℝ) + 1) * x) = -(4 * x) := by push_cast; ring
          rw [e4] at h2
          refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
          gcongr
          · exact (h x hx0).1.le
          · exact le_max_left _ _
  -- the decomposition
  have hdec : ∀ x, X₄ ≤ x → ((Real.exp (4 * (j + 1) * x) : ℝ) : ℂ) * outwardSine β g x /
      (f x : ℂ) = a * (((Real.exp (4 * x) : ℝ) : ℂ) *
        (∫ t in Ioi (0 : ℝ), K t * (f (x + t) : ℂ)) / (f x : ℂ)) +
      ((Real.exp (4 * (j + 1) * x) : ℝ) : ℂ) *
        (β * ∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * r (x + t)) / (f x : ℂ) := by
    intro x hx
    obtain ⟨hx0, -, hxZ, -⟩ := hX₄ x hx
    have hri := (hbnd 1 x hx (fun z hz => hZ₁ z (hxZ.trans hz)) zero_le_one).1
    have hpt : ∀ t : ℝ, β * (Complex.sin (β * t) * g (x + t)) =
        a * ((E x : ℝ) : ℂ) * (K t * (f (x + t) : ℂ)) + β * (Complex.sin (β * t) * r (x + t)) := by
      intro t
      have hg' : g (x + t) = r (x + t) + a * ((E (x + t) : ℝ) : ℂ) * (f (x + t) : ℂ) := by
        simp only [r]; ring
      rw [hg', hEadd]
      simp only [K]
      push_cast
      ring
    have hout : outwardSine β g x = a * ((E x : ℝ) : ℂ) * (∫ t in Ioi (0 : ℝ), K t * (f (x + t) : ℂ)) +
        β * ∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * r (x + t) := by
      rw [outwardSine, ← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi
        (fun t _ => hpt t), integral_add ((hint1 x hx).const_mul _) (hri.const_mul _),
        integral_const_mul, integral_const_mul]
    have hEx' : ((Real.exp (4 * (j + 1) * x) : ℝ) : ℂ) * ((E x : ℝ) : ℂ) =
        ((Real.exp (4 * x) : ℝ) : ℂ) := by exact_mod_cast hEx x
    rw [hout]
    have hf0 : (f x : ℂ) ≠ 0 := by exact_mod_cast (h x hx0).1.ne'
    field_simp
    linear_combination a * (∫ t in Ioi (0 : ℝ), K t * (f (x + t) : ℂ)) * hEx'
  -- the remainder is negligible
  have hlimE : Tendsto (fun x => ((Real.exp (4 * (j + 1) * x) : ℝ) : ℂ) *
      (β * ∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * r (x + t)) / (f x : ℂ)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun δ hδ => ?_
    set ε := δ / (2 * (‖β‖ * ‖β‖ * K₁' + 1))
    have hK₁'0 : 0 ≤ K₁' := le_max_right _ _
    have hε : 0 < ε := div_pos hδ (by positivity)
    obtain ⟨Zε, hZε⟩ := eventually_atTop.1 (hr ε hε)
    filter_upwards [eventually_ge_atTop (max X₄ Zε)] with x hx
    have hx4 : X₄ ≤ x := (le_max_left _ _).trans hx
    obtain ⟨hx0, -, -, -⟩ := hX₄ x hx4
    have hfx := (h x hx0).1
    have hb := (hbnd ε x hx4 (fun z hz => hZε z ((le_max_right _ _).trans (hx.trans hz)))
      hε.le).2
    rw [dist_zero_right, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hfx.le, div_lt_iff₀ hfx]
    have hEx4 := hEx x
    calc Real.exp (4 * (j + 1) * x) * (‖β‖ * ‖∫ t in Ioi (0 : ℝ), Complex.sin (β * t) * r (x + t)‖)
        ≤ Real.exp (4 * (j + 1) * x) * (‖β‖ * (ε * ‖β‖ * E x * (K₁' * Real.exp (-(4 * x)) * f x))) := by
          gcongr
      _ = ε * (‖β‖ * ‖β‖ * K₁') * f x * ((Real.exp (4 * (j + 1) * x) * E x) *
            Real.exp (-(4 * x))) := by ring
      _ = ε * (‖β‖ * ‖β‖ * K₁') * f x := by
          rw [hEx4, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ < δ * f x := by
          refine mul_lt_mul_of_pos_right ?_ hfx
          have : ε * (‖β‖ * ‖β‖ * K₁' + 1) = δ / 2 := by
            simp only [ε]; field_simp
          nlinarith [mul_nonneg (mul_nonneg (norm_nonneg β) (norm_nonneg β)) hK₁'0]
  have hsum := (hmain.const_mul a).add hlimE
  rw [add_zero] at hsum
  refine (hsum.congr' ?_).trans_eq (by rw [mul_div_assoc])
  filter_upwards [eventually_ge_atTop X₄] with x hx
  exact (hdec x hx).symm

/-- Higher tail order is negligible at lower order. -/
theorem tendsto_of_lt_order {g : ℝ → ℂ} {j j' : ℕ} {a : ℂ}
    (hga : Tendsto (fun x => ((Real.exp (4 * j * x) : ℝ) : ℂ) * g x / (f x : ℂ)) atTop (𝓝 a))
    (hjj : j' < j) :
    Tendsto (fun x => ((Real.exp (4 * j' * x) : ℝ) : ℂ) * g x / (f x : ℂ)) atTop (𝓝 0) := by
  have hpos : (0 : ℝ) < 4 * ((j : ℝ) - j') := by
    have : (j' : ℝ) < j := by exact_mod_cast hjj
    linarith
  have h1 : Tendsto (fun x : ℝ => Real.exp (-(4 * ((j : ℝ) - j') * x))) atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hpos)).congr
      fun x => by simp only [Function.comp, id]
  have hdec : Tendsto (fun x : ℝ => ((Real.exp (-(4 * ((j : ℝ) - j') * x)) : ℝ) : ℂ)) atTop
      (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at this
    exact this
  have := hdec.mul hga
  rw [zero_mul] at this
  refine this.congr fun x => ?_
  rw [← mul_div_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  congr 1
  ring

theorem stronglyMeasurable_halfListDivision (L : List ℂ) {g : ℝ → ℂ} (hg : StronglyMeasurable g) :
    StronglyMeasurable (halfListDivision L g) := by
  induction L with
  | nil => exact hg
  | cons β L ih => exact stronglyMeasurable_outwardSine ih β

/-- **Tail law of iterated divisions**: `e^{4jx} (T_{β₁} ⋯ T_{β_j} f)(x)/f(x) → ∏β²/(2π)^{2j}`. -/
theorem tendsto_halfListDivision (hf : ThetaTypeTail f) (L : List ℂ) :
    Tendsto (fun x => ((Real.exp (4 * L.length * x) : ℝ) : ℂ) *
      halfListDivision L (fun y => (f y : ℂ)) x / (f x : ℂ)) atTop
      (𝓝 ((L.map fun β => β ^ 2).prod / (2 * Real.pi) ^ (2 * L.length))) := by
  induction L with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero,
      Complex.ofReal_one, one_mul, List.map_nil, List.prod_nil, pow_zero, div_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hf.eventually_pos] with x hx
    have : (f x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact (div_self this).symm
  | cons β L ih =>
    have h := hf.tendsto_outwardSine (stronglyMeasurable_halfListDivision L
      (Complex.continuous_ofReal.comp hf.continuous).stronglyMeasurable) ih β
    have hval : ((β :: L).map fun β => β ^ 2).prod / (2 * (Real.pi : ℂ)) ^ (2 * (β :: L).length) =
        (L.map fun β => β ^ 2).prod / (2 * (Real.pi : ℂ)) ^ (2 * L.length) * β ^ 2 /
          (2 * (Real.pi : ℂ)) ^ 2 := by
      have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
      rw [List.map_cons, List.prod_cons, List.length_cons, mul_add, mul_one, pow_add]
      field_simp
    rw [hval]
    refine h.congr fun x => ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, halfListDivision]
    rfl

/-- **Tail law of partial-fraction combinations.**  For `e ≠ 0` of degree `n ≤ |L|` and
`d = |L| − n`, `e^{4dx} (listComb L e)(x)/f(x) → (−1)^d e_n ∏(−β²)/(2π)^{2d}`. -/
theorem tendsto_listComb (hf : ThetaTypeTail f) (L : List ℂ) (e : Polynomial ℂ) (he0 : e ≠ 0)
    (hdeg : e.natDegree ≤ L.length) :
    Tendsto (fun x => ((Real.exp (4 * ((L.length - e.natDegree : ℕ) : ℝ) * x) : ℝ) : ℂ) *
      listComb (fun L' => halfListDivision L' (fun y => (f y : ℂ))) L e x / (f x : ℂ)) atTop
      (𝓝 ((-1) ^ (L.length - e.natDegree) * e.leadingCoeff * (L.map fun β => -β ^ 2).prod /
        (2 * Real.pi) ^ (2 * (L.length - e.natDegree)))) := by
  induction L generalizing e with
  | nil =>
    have hn : e.natDegree = 0 := by simpa using hdeg
    simp only [List.length_nil, hn, Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul,
      Real.exp_zero, Complex.ofReal_one, one_mul, pow_zero, List.map_nil, List.prod_nil, mul_one,
      div_one, listComb_nil, halfListDivision]
    rw [Polynomial.leadingCoeff, hn]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hf.eventually_pos] with x hx
    have : (f x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    field_simp
  | cons β L ih =>
    rw [listComb_cons]
    set a := β ^ 2
    set e₁ := e /ₘ (Polynomial.X - Polynomial.C a)
    set G := halfListDivision (β :: L) (fun y => (f y : ℂ))
    have hG := tendsto_halfListDivision hf (β :: L)
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    by_cases hn : e.natDegree = 0
    · -- constant `e`
      have he₁ : e₁ = 0 := by
        rw [Polynomial.divByMonic_eq_zero_iff (Polynomial.monic_X_sub_C a),
          Polynomial.degree_X_sub_C, Polynomial.degree_eq_natDegree he0, hn]
        exact_mod_cast Nat.zero_lt_one
      have heC : e = Polynomial.C (e.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
      have hev : e.eval a = e.leadingCoeff := by
        rw [heC, Polynomial.eval_C, Polynomial.leadingCoeff_C]
      simp only [he₁, listComb_zero, mul_zero, sub_zero, hn, Nat.sub_zero]
      have hval : (-1) ^ (β :: L).length * e.leadingCoeff * ((β :: L).map fun β => -β ^ 2).prod /
          (2 * (Real.pi : ℂ)) ^ (2 * (β :: L).length) = e.eval a *
            (((β :: L).map fun β => β ^ 2).prod / (2 * (Real.pi : ℂ)) ^ (2 * (β :: L).length)) := by
        have h1 : ((-1 : ℂ) ^ (β :: L).length * (-1) ^ (β :: L).length) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
        rw [hev, prod_map_neg_sq]
        calc (-1) ^ (β :: L).length * e.leadingCoeff * ((-1) ^ (β :: L).length *
              ((β :: L).map fun β => β ^ 2).prod) / (2 * (Real.pi : ℂ)) ^ (2 * (β :: L).length)
            = e.leadingCoeff * ((-1 : ℂ) ^ (β :: L).length * (-1) ^ (β :: L).length) *
              ((β :: L).map fun β => β ^ 2).prod / (2 * (Real.pi : ℂ)) ^ (2 * (β :: L).length) := by
              ring
          _ = _ := by rw [h1]; ring
      rw [hval]
      exact (hG.const_mul (e.eval a)).congr fun x => by ring
    · -- `deg e ≥ 1`
      have hmon := Polynomial.monic_X_sub_C a
      have hdeg1 : (Polynomial.X - Polynomial.C a).degree ≤ e.degree := by
        rw [Polynomial.degree_X_sub_C, Polynomial.degree_eq_natDegree he0]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      have he₁0 : e₁ ≠ 0 := by
        rw [Ne, Polynomial.divByMonic_eq_zero_iff hmon, not_lt]; exact hdeg1
      have hn₁ : e₁.natDegree = e.natDegree - 1 := by
        rw [Polynomial.natDegree_divByMonic _ hmon, Polynomial.natDegree_X_sub_C]
      have hlc : e₁.leadingCoeff = e.leadingCoeff :=
        Polynomial.leadingCoeff_divByMonic_of_monic hmon hdeg1
      have hdeg₁ : e₁.natDegree ≤ L.length := by
        rw [hn₁]; simp only [List.length_cons] at hdeg; omega
      have hIH := ih e₁ he₁0 hdeg₁
      have hd : L.length - e₁.natDegree = (β :: L).length - e.natDegree := by
        rw [hn₁, List.length_cons]; omega
      rw [hd, hlc] at hIH
      have hGo := tendsto_of_lt_order hG (j' := (β :: L).length - e.natDegree) (by omega)
      have hsum := (hGo.const_mul (e.eval a)).sub (hIH.const_mul a)
      rw [mul_zero, zero_sub] at hsum
      have hval : (-1) ^ ((β :: L).length - e.natDegree) * e.leadingCoeff *
          ((β :: L).map fun β => -β ^ 2).prod / (2 * (Real.pi : ℂ)) ^
            (2 * ((β :: L).length - e.natDegree)) =
          -(a * ((-1) ^ ((β :: L).length - e.natDegree) * e.leadingCoeff *
            (L.map fun β => -β ^ 2).prod / (2 * (Real.pi : ℂ)) ^
              (2 * ((β :: L).length - e.natDegree)))) := by
        simp only [List.map_cons, List.prod_cons, a]
        ring
      rw [hval]
      exact hsum.congr fun x => by ring

end ThetaTypeTail

/-! ## The literal seed and source have theta tails -/

theorem tendsto_exp_mul_exp_sub_one (τ : ℝ) :
    Tendsto (fun x => Real.exp (2 * x) * (Real.exp (2 * (τ * Real.exp (-(2 * x)))) - 1)) atTop
      (𝓝 (2 * τ)) := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · simp
  have hu : Tendsto (fun x : ℝ => 2 * (τ * Real.exp (-(2 * x)))) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun x => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact mul_ne_zero two_ne_zero (mul_ne_zero hτ (Real.exp_pos _).ne'))
    have := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul τ).const_mul 2
    simpa [Function.comp] using this
  have hs := (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hu
  simp only [zero_add, Real.exp_zero, smul_eq_mul] at hs
  have := hs.const_mul (2 * τ)
  rw [mul_one] at this
  refine this.congr fun x => ?_
  simp only [Function.comp]
  have hne : 2 * (τ * Real.exp (-(2 * x))) ≠ 0 :=
    mul_ne_zero two_ne_zero (mul_ne_zero hτ (Real.exp_pos _).ne')
  have hyb : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  linear_combination (1 - Real.exp (2 * τ * Real.exp (-(2 * x)))) * hyb

/-- The literal seed `h` has the theta tail. -/
theorem thetaTypeTail_seed : ThetaTypeTail thetaCuspLogSeed := by
  refine ⟨continuous_thetaCuspLogSeed, ⟨2 * Real.pi / (2 * Real.pi - 3), 9 / 2, 0, by norm_num,
    le_rfl, fun x hx => ⟨thetaCuspLogSeed_pos hx, fun t ht => ?_⟩⟩, fun τ hτ => ?_⟩
  · refine (thetaCuspLogSeed_shift_le hx ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
        (div_pos (by positivity) (by linarith [Real.pi_gt_three])).le) (thetaCuspLogSeed_pos hx).le)
    have hq : 2 * t ≤ Real.exp (2 * t) - 1 := by linarith [Real.add_one_le_exp (2 * t)]
    have := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ Real.pi * Real.exp (2 * x))
    nlinarith
  · -- explicit ratio
    have hπ := Real.pi_gt_three
    set s : ℝ → ℝ := fun x => τ * Real.exp (-(2 * x))
    have hs0 : Tendsto s atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul τ
      simpa [s, Function.comp] using this
    have hexps : ∀ c : ℝ, Tendsto (fun x => Real.exp (c * s x)) atTop (𝓝 1) := fun c => by
      have h := hs0.const_mul c
      rw [mul_zero] at h
      have := (Real.continuous_exp.tendsto 0).comp h
      rw [Real.exp_zero] at this
      exact this
    have hF1 : Tendsto (fun x => Real.exp (5 / 2 * s x)) atTop (𝓝 1) := hexps (5 / 2)
    have hy0 : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).congr fun x => by
          simp only [Function.comp, id]
    have hF2 : Tendsto (fun x => (2 * Real.pi * Real.exp (2 * s x) - 3 * Real.exp (-(2 * x))) /
        (2 * Real.pi - 3 * Real.exp (-(2 * x)))) atTop (𝓝 1) := by
      have hN : Tendsto (fun x => 2 * Real.pi * Real.exp (2 * s x) - 3 * Real.exp (-(2 * x)))
          atTop (𝓝 (2 * Real.pi)) := by
        have := ((hexps 2).const_mul (2 * Real.pi)).sub (hy0.const_mul 3)
        simpa using this
      have hD : Tendsto (fun x => 2 * Real.pi - 3 * Real.exp (-(2 * x))) atTop
          (𝓝 (2 * Real.pi)) := by
        have := tendsto_const_nhds (x := 2 * Real.pi) |>.sub (hy0.const_mul 3)
        simpa using this
      have := hN.div hD (by positivity)
      rwa [div_self (by positivity)] at this
    have hF3 : Tendsto (fun x => Real.exp (-(Real.pi * (Real.exp (2 * x) *
        (Real.exp (2 * s x) - 1))))) atTop (𝓝 (Real.exp (-(2 * Real.pi * τ)))) := by
      have := (Real.continuous_exp.tendsto _).comp
        ((tendsto_exp_mul_exp_sub_one τ).const_mul Real.pi).neg
      refine this.congr' (Eventually.of_forall fun x => by simp [s, Function.comp]) |>.trans_eq ?_
      ring_nf
    have := (hF1.mul hF2).mul hF3
    rw [one_mul, one_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hx1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    have hden : 0 < 2 * Real.pi - 3 * Real.exp (-(2 * x)) := by
      have : Real.exp (-(2 * x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      nlinarith
    have hyb : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by rw [← Real.exp_add]; simp
    rw [thetaCuspLogSeed_eq, thetaCuspLogSeed_eq]
    have e1 : Real.exp (5 * (x + s x) / 2) = Real.exp (5 * x / 2) * Real.exp (5 / 2 * s x) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (2 * (x + s x)) = Real.exp (2 * x) * Real.exp (2 * s x) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (-(Real.pi * (Real.exp (2 * x) * Real.exp (2 * s x)))) =
        Real.exp (-(Real.pi * Real.exp (2 * x))) *
          Real.exp (-(Real.pi * (Real.exp (2 * x) * (Real.exp (2 * s x) - 1)))) := by
      rw [← Real.exp_add (-(Real.pi * Real.exp (2 * x)))]; congr 1; ring
    rw [e1, e2, e3]
    have hpos : 0 < 2 * Real.pi * Real.exp (2 * x) - 3 := by nlinarith
    have hratio : (2 * Real.pi * (Real.exp (2 * x) * Real.exp (2 * s x)) - 3) /
        (2 * Real.pi * Real.exp (2 * x) - 3) =
        (2 * Real.pi * Real.exp (2 * s x) - 3 * Real.exp (-(2 * x))) /
          (2 * Real.pi - 3 * Real.exp (-(2 * x))) := by
      rw [div_eq_div_iff hpos.ne' hden.ne']
      linear_combination (6 * Real.pi - 6 * Real.pi * Real.exp (2 * s x)) * hyb
    rw [← hratio]
    have hA := Real.exp_pos (5 * x / 2)
    have hB := Real.exp_pos (-(Real.pi * Real.exp (2 * x)))
    field_simp

theorem thetaCuspSourceTerm_one (x : ℝ) : thetaCuspSourceTerm x 1 = thetaCuspLogSeed x := by
  have h := rpow_neg_half_mul_thetaCuspLogSeed 1 x
  simpa using h.symm

theorem thetaCuspLogSeed_le_thetaCuspFullSource {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogSeed x ≤ thetaCuspFullSource x := by
  rw [← thetaCuspSourceTerm_one]
  exact (summable_thetaCuspSourceTerm x).le_tsum 1 fun n _ => thetaCuspSourceTerm_nonneg hx n

/-- The source is asymptotic to its first atom: `k/h → 1`. -/
theorem tendsto_thetaCuspFullSource_div_seed :
    Tendsto (fun x => thetaCuspFullSource x / thetaCuspLogSeed x) atTop (𝓝 1) := by
  have h := ThetaTailNegligible.tendsto (thetaSourceError_negligible 0)
  simp only [iteratedDeriv_zero] at h
  have := h.const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [thetaCuspSourceTerm_one]
  have := (thetaCuspLogSeed_pos hx).ne'
  field_simp
  ring

/-- The literal source `k` has the theta tail. -/
theorem thetaTypeTail_source : ThetaTypeTail thetaCuspFullSource := by
  obtain ⟨C₀, B, X₀, hB, hX₀, hsh⟩ := thetaTypeTail_seed.shift
  have hk2 : ∀ᶠ x in atTop, thetaCuspFullSource x ≤ 2 * thetaCuspLogSeed x := by
    filter_upwards [tendsto_thetaCuspFullSource_div_seed.eventually (gt_mem_nhds (by norm_num :
      (1 : ℝ) < 2)), eventually_ge_atTop (0 : ℝ)] with x hx hx0
    rw [div_lt_iff₀ (thetaCuspLogSeed_pos hx0)] at hx
    exact hx.le
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hk2
  refine ⟨contDiff_thetaCuspFullSource.continuous, ⟨2 * C₀, B, max X₀ (max X₁ 0), hB,
    le_max_of_le_left hX₀, fun x hx => ⟨thetaCuspFullSource_pos x, fun t ht => ?_⟩⟩, fun τ hτ => ?_⟩
  · have hxX₀ : X₀ ≤ x := (le_max_left _ _).trans hx
    have hxX₁ : X₁ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
    have hx0 : 0 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
    have h1 := hX₁ (x + t) (by linarith)
    have h2 := (hsh x hxX₀).2 t ht
    have h3 := thetaCuspLogSeed_le_thetaCuspFullSource hx0
    have hC₀ : 0 ≤ C₀ := by
      have := (hsh x hxX₀).2 0 le_rfl
      simp only [add_zero, mul_zero, Real.exp_zero, mul_one] at this
      have hh := (hsh x hxX₀).1
      nlinarith
    calc thetaCuspFullSource (x + t) ≤ 2 * thetaCuspLogSeed (x + t) := h1
      _ ≤ 2 * (C₀ * Real.exp ((B - 2 * Real.pi * Real.exp (2 * x)) * t) * thetaCuspLogSeed x) := by
          linarith
      _ ≤ 2 * (C₀ * Real.exp ((B - 2 * Real.pi * Real.exp (2 * x)) * t) * thetaCuspFullSource x) := by
          gcongr
      _ = _ := by ring
  · set s : ℝ → ℝ := fun x => x + τ * Real.exp (-(2 * x))
    have hs : Tendsto s atTop atTop := tendsto_atTop_mono (fun x => by
      simp only [s, id]; nlinarith [mul_nonneg hτ (Real.exp_pos (-(2 * x))).le]) tendsto_id
    have h1 := tendsto_thetaCuspFullSource_div_seed.comp hs
    have h2 := thetaTypeTail_seed.scaling τ hτ
    have h3 := tendsto_thetaCuspFullSource_div_seed.inv₀ one_ne_zero
    rw [inv_one] at h3
    have := (h1.mul h2).mul h3
    rw [one_mul, mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hsx : 0 ≤ x + τ * Real.exp (-(2 * x)) := by
      nlinarith [mul_nonneg hτ (Real.exp_pos (-(2 * x))).le]
    have h4 := (thetaCuspLogSeed_pos hx).ne'
    have h5 : thetaCuspLogSeed (x + τ * Real.exp (-(2 * x))) ≠ 0 := (thetaCuspLogSeed_pos hsx).ne'
    have h6 := (thetaCuspFullSource_pos x).ne'
    simp only [Function.comp, s]
    field_simp
    exact mul_div_cancel_right₀ _ (by rw [mul_comm x 2]; exact h5)

/-- **Tail law of reflected list divisions**: `e^{4|L|x} G_L(x)/k(x) → ∏β²/(2π)^{2|L|}`. -/
theorem tendsto_thetaListDivision (L : List ℂ) :
    Tendsto (fun x => ((Real.exp (4 * L.length * x) : ℝ) : ℂ) * thetaListDivision L x /
      (thetaCuspFullSource x : ℂ)) atTop
      (𝓝 ((L.map fun β => β ^ 2).prod / (2 * Real.pi) ^ (2 * L.length))) := by
  refine (thetaTypeTail_source.tendsto_halfListDivision L).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [thetaListDivision_eq_halfListDivision L x hx]
  rfl

/-- **Tail law of seed divisions**: `e^{4|L|x} (T_L h)(x)/h(x) → ∏β²/(2π)^{2|L|}`. -/
theorem tendsto_seedListDivision (L : List ℂ) :
    Tendsto (fun x => ((Real.exp (4 * L.length * x) : ℝ) : ℂ) * seedListDivision L x /
      (thetaCuspLogSeed x : ℂ)) atTop
      (𝓝 ((L.map fun β => β ^ 2).prod / (2 * Real.pi) ^ (2 * L.length))) :=
  thetaTypeTail_seed.tendsto_halfListDivision L

theorem listComb_congr {D D' : List ℂ → ℝ → ℂ} (hD : ∀ L x, 0 ≤ x → D L x = D' L x)
    (L : List ℂ) (e : Polynomial ℂ) {x : ℝ} (hx : 0 ≤ x) : listComb D L e x = listComb D' L e x := by
  induction L generalizing e with
  | nil => simp only [listComb_nil, hD [] x hx]
  | cons β L ih => simp only [listComb_cons, hD (β :: L) x hx, ih]

end

end RHTower
