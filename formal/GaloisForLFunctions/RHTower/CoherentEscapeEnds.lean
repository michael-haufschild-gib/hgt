import GaloisForLFunctions.RHTower.CoherentKernelChart

/-!
# The two escaping ends of the coherent chart

`prime-valuation-dyadic-fermion-normal-cone-law`, equation `(13i)` and the three-face rigging.

The coherent norm `‖F_u‖² = 2 Φ(u)` diverges at both ends of the normal coordinate, but at very
different rates:

* `u → +∞`:  `Φ(u) ≥ (e^{u/2} − 1)²/4`, an exponential of an exponential in the drift;
* `u → −∞`:  `Φ(−V) ≥ ½(1 − e^{−1})² log V`, only logarithmic — the half-normal end.

Cauchy–Schwarz for the prime-scale Gram form then gives `‖F_u − F_v‖ ≥ ‖F_u‖ − ‖F_v‖`, so for every
fixed `v` the coherent kernel `K(u,v)` escapes weakly to zero at both ends.

The positive end is genuinely different from the negative one: pairing `F_V` with the single test
profile `f(t) = t` already grows like `e^V/V`, so `F_V` has no limit in the distributional dual.
-/

open Filter Topology Set intervalIntegral MeasureTheory

namespace RHTower

noncomputable section

theorem divProfile_coherentProfile_nonneg (u v : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ divProfile (coherentProfile u v) t := by
  rw [divProfile]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (by rw [coherentProfile]; positivity) ht

theorem intervalIntegrable_divProfile_coherentProfile_sub {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (u v : ℝ) :
    IntervalIntegrable (divProfile (coherentProfile u v)) volume a b := by
  refine (intervalIntegrable_divProfile_coherentProfile u v).mono_set ?_
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.uIcc_of_le hab]
  exact Set.Icc_subset_Icc ha hb

/-- **The half-normal end diverges logarithmically.** -/
theorem coherentExponent_neg_ge {V : ℝ} (hV : 1 ≤ V) :
    (1 - Real.exp (-1)) ^ (2 : ℕ) / 2 * Real.log V ≤ coherentExponent (-V) 0 := by
  have hV0 : (0 : ℝ) < V := by linarith
  have hVinv : (0 : ℝ) < 1 / V := by positivity
  have hVinv1 : 1 / V ≤ 1 := by rw [div_le_one hV0]; linarith
  -- the integrand dominates `(1 - e^{-1})²/t` on `[1/V, 1]`
  have hdom : ∀ t ∈ Set.Icc (1 / V) 1,
      (1 - Real.exp (-1)) ^ (2 : ℕ) * (1 / t) ≤ divProfile (coherentProfile (-V) 0) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hVinv ht.1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hVt : V * t ≥ 1 := by
      have h := ht.1
      rw [div_le_iff₀ hV0] at h
      linarith
    have hexp : Real.exp (-V * t) ≤ Real.exp (-1) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hpos : 0 ≤ Real.exp (-V * t) := Real.exp_nonneg _
    have hsq : (1 - Real.exp (-1)) ^ (2 : ℕ) ≤ (Real.exp (-V * t) - Real.exp (0 * t)) ^ (2 : ℕ) := by
      rw [show (0 : ℝ) * t = 0 by ring, Real.exp_zero]
      have h1 : Real.exp (-V * t) - 1 ≤ Real.exp (-1) - 1 := by linarith
      have h2 : Real.exp (-1) - 1 < 0 := by
        have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
        linarith
      nlinarith [hpos]
    rw [divProfile, if_neg htne, coherentProfile]
    rw [show (1 - Real.exp (-1)) ^ (2 : ℕ) * (1 / t) = (1 - Real.exp (-1)) ^ (2 : ℕ) / t by ring]
    gcongr
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 - Real.exp (-1)) ^ (2 : ℕ) * (1 / t))
      volume (1 / V) 1 := by
    refine IntervalIntegrable.const_mul ?_ _
    refine intervalIntegral.intervalIntegrable_one_div (fun x hx => ?_) ?_
    · rw [Set.uIcc_of_le hVinv1] at hx
      exact ne_of_gt (lt_of_lt_of_le hVinv hx.1)
    · exact continuous_id.continuousOn
  have hint2 := intervalIntegrable_divProfile_coherentProfile_sub hVinv.le hVinv1
    (le_refl (1 : ℝ)) (-V) 0
  have hcmp : (∫ t in (1 / V)..1, (1 - Real.exp (-1)) ^ (2 : ℕ) * (1 / t))
      ≤ ∫ t in (1 / V)..1, divProfile (coherentProfile (-V) 0) t := by
    exact intervalIntegral.integral_mono_on hVinv1 hint1 hint2 (fun t ht => hdom t ht)
  have hlogval : (∫ t in (1 / V)..1, (1 - Real.exp (-1)) ^ (2 : ℕ) * (1 / t))
      = (1 - Real.exp (-1)) ^ (2 : ℕ) * Real.log V := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hVinv zero_lt_one,
      one_div_one_div]
  have hsplit : (∫ t in (0 : ℝ)..1, divProfile (coherentProfile (-V) 0) t)
      = (∫ t in (0 : ℝ)..(1 / V), divProfile (coherentProfile (-V) 0) t)
        + ∫ t in (1 / V)..1, divProfile (coherentProfile (-V) 0) t := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ hint2).symm
    exact intervalIntegrable_divProfile_coherentProfile_sub (le_refl (0:ℝ)) hVinv.le hVinv1 (-V) 0
  have hhead : 0 ≤ ∫ t in (0 : ℝ)..(1 / V), divProfile (coherentProfile (-V) 0) t :=
    intervalIntegral.integral_nonneg hVinv.le
      (fun t ht => divProfile_coherentProfile_nonneg _ _ ht.1)
  rw [coherentExponent, hsplit]
  rw [hlogval] at hcmp
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [le_div_iff₀ h2]
  nlinarith [hcmp, hhead]

/-- **The positive end diverges like an exponential of an exponential.** -/
theorem coherentExponent_pos_ge {u : ℝ} (hu : 0 ≤ u) :
    (Real.exp (u / 2) - 1) ^ (2 : ℕ) / 4 ≤ coherentExponent u 0 := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  have hdom : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      (Real.exp (u / 2) - 1) ^ (2 : ℕ) ≤ divProfile (coherentProfile u 0) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hexp : Real.exp (u / 2) ≤ Real.exp (u * t) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [ht.1, hu]
    have h1 : (0 : ℝ) ≤ Real.exp (u / 2) - 1 := by
      have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ u / 2)
      linarith
    have hsq : (Real.exp (u / 2) - 1) ^ (2 : ℕ) ≤ (Real.exp (u * t) - Real.exp (0 * t)) ^ (2 : ℕ) := by
      rw [show (0 : ℝ) * t = 0 by ring, Real.exp_zero]
      nlinarith
    rw [divProfile, if_neg htne, coherentProfile]
    rw [le_div_iff₀ ht0]
    nlinarith [hsq, ht.2, ht0, sq_nonneg (Real.exp (u * t) - 1)]
  have hint1 : IntervalIntegrable (fun _ : ℝ => (Real.exp (u / 2) - 1) ^ (2 : ℕ))
      volume (1 / 2) 1 := intervalIntegrable_const
  have hint2 := intervalIntegrable_divProfile_coherentProfile_sub hhalf hhalf1
    (le_refl (1 : ℝ)) u 0
  have hcmp : (∫ _t in (1 / 2 : ℝ)..1, (Real.exp (u / 2) - 1) ^ (2 : ℕ))
      ≤ ∫ t in (1 / 2 : ℝ)..1, divProfile (coherentProfile u 0) t :=
    intervalIntegral.integral_mono_on hhalf1 hint1 hint2 (fun t ht => hdom t ht)
  rw [intervalIntegral.integral_const] at hcmp
  have hsplit : (∫ t in (0 : ℝ)..1, divProfile (coherentProfile u 0) t)
      = (∫ t in (0 : ℝ)..(1 / 2 : ℝ), divProfile (coherentProfile u 0) t)
        + ∫ t in (1 / 2 : ℝ)..1, divProfile (coherentProfile u 0) t := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ hint2).symm
    exact intervalIntegrable_divProfile_coherentProfile_sub (le_refl (0:ℝ)) hhalf hhalf1 u 0
  have hhead : 0 ≤ ∫ t in (0 : ℝ)..(1 / 2 : ℝ), divProfile (coherentProfile u 0) t :=
    intervalIntegral.integral_nonneg hhalf
      (fun t ht => divProfile_coherentProfile_nonneg _ _ ht.1)
  rw [coherentExponent, hsplit, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  simp only [smul_eq_mul] at hcmp
  nlinarith [hcmp, hhead]

/-! ## Escape of the coherent kernel -/

theorem tendsto_coherentExponent_atTop :
    Tendsto (fun u : ℝ => coherentExponent u 0) atTop atTop := by
  refine tendsto_atTop_mono' atTop
    (f₁ := fun u : ℝ => (Real.exp (u / 2) - 1) ^ (2 : ℕ) / 4) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact coherentExponent_pos_ge hu
  · have hexp : Tendsto (fun u : ℝ => Real.exp (u / 2)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
    refine Filter.Tendsto.atTop_div_const (by norm_num) ?_
    have hsub : Tendsto (fun u : ℝ => Real.exp (u / 2) - 1) atTop atTop := by
      have h := hexp.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
      simpa [sub_eq_add_neg] using h
    refine tendsto_atTop_mono' atTop (f₁ := fun u : ℝ => Real.exp (u / 2) - 1) ?_ hsub
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
    have h1 : (1 : ℝ) ≤ Real.exp (u / 2) - 1 := by
      have he : Real.exp (1 : ℝ) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by linarith)
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      linarith
    nlinarith

theorem tendsto_coherentExponent_atBot :
    Tendsto (fun u : ℝ => coherentExponent u 0) atBot atTop := by
  have hcomp : Tendsto (fun V : ℝ => coherentExponent (-V) 0) atTop atTop := by
    refine tendsto_atTop_mono' atTop
      (f₁ := fun V : ℝ => (1 - Real.exp (-1)) ^ (2 : ℕ) / 2 * Real.log V) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with V hV
      exact coherentExponent_neg_ge hV
    · have hc : (0 : ℝ) < (1 - Real.exp (-1)) ^ (2 : ℕ) / 2 := by
        have h1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        have h2 : (0 : ℝ) < 1 - Real.exp (-1) := by linarith
        positivity
      exact Real.tendsto_log_atTop.const_mul_atTop hc
  have hneg : Tendsto (fun u : ℝ => -u) atBot atTop := tendsto_neg_atBot_atTop
  have := hcomp.comp hneg
  simpa [Function.comp_def] using this

theorem coherentExponent_nonneg (u v : ℝ) : 0 ≤ coherentExponent u v := by
  rw [coherentExponent]
  refine div_nonneg (intervalIntegral.integral_nonneg (by norm_num) ?_) (by norm_num)
  intro t ht
  exact divProfile_coherentProfile_nonneg u v ht.1

/-- **Cauchy–Schwarz for the prime-scale Gram form.** -/
theorem primeScaleInner_cauchy (u v : ℝ) :
    primeScaleInner u v ^ (2 : ℕ) ≤ primeScaleInner u u * primeScaleInner v v := by
  have hquad : ∀ x : ℝ, 0 ≤ primeScaleInner u u * (x * x) + 2 * primeScaleInner u v * x
      + primeScaleInner v v := by
    intro x
    have h := primeScaleInner_quadForm_nonneg ![u, v] ![x, 1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hsym : primeScaleInner v u = primeScaleInner u v := primeScaleInner_comm v u
    rw [hsym] at h
    nlinarith [h]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- The coherent exponent against a fixed reference diverges wherever the diagonal one does. -/
theorem tendsto_coherentExponent_of_tendsto {l : Filter ℝ} (v : ℝ)
    (hdiag : Tendsto (fun u : ℝ => coherentExponent u 0) l atTop) :
    Tendsto (fun u : ℝ => coherentExponent u v) l atTop := by
  have hkey : ∀ u : ℝ, (Real.sqrt (2 * coherentExponent u 0)
      - Real.sqrt (2 * coherentExponent v 0)) ^ (2 : ℕ) / 2 ≤ coherentExponent u v := by
    intro u
    have hA : primeScaleInner u u = 2 * coherentExponent u 0 := primeScaleInner_self u
    have hC : primeScaleInner v v = 2 * coherentExponent v 0 := primeScaleInner_self v
    have hcs := primeScaleInner_cauchy u v
    rw [hA, hC] at hcs
    have hA0 : 0 ≤ 2 * coherentExponent u 0 := by
      have := coherentExponent_nonneg u 0; linarith
    have hC0 : 0 ≤ 2 * coherentExponent v 0 := by
      have := coherentExponent_nonneg v 0; linarith
    have hsa : Real.sqrt (2 * coherentExponent u 0) ^ (2 : ℕ) = 2 * coherentExponent u 0 :=
      Real.sq_sqrt hA0
    have hsc : Real.sqrt (2 * coherentExponent v 0) ^ (2 : ℕ) = 2 * coherentExponent v 0 :=
      Real.sq_sqrt hC0
    have hbound : primeScaleInner u v
        ≤ Real.sqrt (2 * coherentExponent u 0) * Real.sqrt (2 * coherentExponent v 0) := by
      have h1 : primeScaleInner u v ≤ |primeScaleInner u v| := le_abs_self _
      have h2 : |primeScaleInner u v| = Real.sqrt (primeScaleInner u v ^ (2 : ℕ)) :=
        (Real.sqrt_sq_eq_abs _).symm
      have h3 : Real.sqrt (primeScaleInner u v ^ (2 : ℕ))
          ≤ Real.sqrt ((2 * coherentExponent u 0) * (2 * coherentExponent v 0)) :=
        Real.sqrt_le_sqrt hcs
      rw [Real.sqrt_mul hA0] at h3
      rw [h2] at h1
      linarith
    have hpol := primeScaleInner_eq u v
    have hexpand : (Real.sqrt (2 * coherentExponent u 0)
        - Real.sqrt (2 * coherentExponent v 0)) ^ (2 : ℕ)
        = 2 * coherentExponent u 0 - 2 * (Real.sqrt (2 * coherentExponent u 0)
          * Real.sqrt (2 * coherentExponent v 0)) + 2 * coherentExponent v 0 := by
      rw [sub_sq, hsa, hsc]
      ring
    rw [hexpand]
    linarith
  refine tendsto_atTop_mono' l
    (f₁ := fun u : ℝ => (Real.sqrt (2 * coherentExponent u 0)
      - Real.sqrt (2 * coherentExponent v 0)) ^ (2 : ℕ) / 2) ?_ ?_
  · exact Filter.Eventually.of_forall hkey
  · refine Filter.Tendsto.atTop_div_const (by norm_num) ?_
    have hsq : Tendsto (fun u : ℝ => Real.sqrt (2 * coherentExponent u 0)) l atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact hdiag.const_mul_atTop (by norm_num)
    have hsub : Tendsto (fun u : ℝ => Real.sqrt (2 * coherentExponent u 0)
        - Real.sqrt (2 * coherentExponent v 0)) l atTop := by
      have h := hsq.atTop_add
        (tendsto_const_nhds (x := -Real.sqrt (2 * coherentExponent v 0)))
      simpa [sub_eq_add_neg] using h
    refine tendsto_atTop_mono' l
      (f₁ := fun u : ℝ => Real.sqrt (2 * coherentExponent u 0)
        - Real.sqrt (2 * coherentExponent v 0)) ?_ hsub
    filter_upwards [hsub.eventually_ge_atTop 1] with u hu
    nlinarith

/-- **`(13i)`: the coherent kernel escapes weakly to zero at both ends.** -/
theorem tendsto_coherentKernel_atTop (v : ℝ) :
    Tendsto (fun u : ℝ => coherentKernel u v) atTop (nhds 0) := by
  have hdiv := tendsto_coherentExponent_of_tendsto v tendsto_coherentExponent_atTop
  have hneg : Tendsto (fun u : ℝ => -coherentExponent u v) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hdiv
  have := Real.tendsto_exp_atBot.comp hneg
  simpa [Function.comp_def, coherentKernel] using this

theorem tendsto_coherentKernel_atBot (v : ℝ) :
    Tendsto (fun u : ℝ => coherentKernel u v) atBot (nhds 0) := by
  have hdiv := tendsto_coherentExponent_of_tendsto v tendsto_coherentExponent_atBot
  have hneg : Tendsto (fun u : ℝ => -coherentExponent u v) atBot atBot :=
    tendsto_neg_atTop_atBot.comp hdiv
  have := Real.tendsto_exp_atBot.comp hneg
  simpa [Function.comp_def, coherentKernel] using this

theorem coherentExponent_comm (u v : ℝ) : coherentExponent u v = coherentExponent v u := by
  rw [coherentExponent, coherentExponent]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [divProfile, divProfile, coherentProfile, coherentProfile]
  split_ifs with ht
  · rfl
  · rw [show (Real.exp (u * t) - Real.exp (v * t)) ^ (2 : ℕ)
      = (Real.exp (v * t) - Real.exp (u * t)) ^ (2 : ℕ) by ring]

/-! ## The reflection-doubled chart `(13g)`–`(13h)` -/

/-- The reflection-doubled coherent kernel: the kernel of `F̃_u = F_u ⊕ F_{-u}` in `𝔥 ⊕ 𝔥`. -/
def bicoherentKernel (u v : ℝ) : ℝ := coherentKernel u v * coherentKernel (-u) (-v)

/-- **`(13h)`: reflection is the unitary swapping the two summands.** -/
theorem bicoherentKernel_reflection (u v : ℝ) :
    bicoherentKernel (-u) (-v) = bicoherentKernel u v := by
  rw [bicoherentKernel, bicoherentKernel, neg_neg, neg_neg]
  ring

theorem coherentKernel_posSemidef {n : ℕ} (u : Fin n → ℝ) :
    (Matrix.of fun i j => coherentKernel (u i) (u j)).PosSemidef := by
  refine posSemidef_of_quadForm (fun i j => ?_) (fun c => ?_)
  · simp only [Matrix.of_apply]
    rw [coherentKernel, coherentKernel, coherentExponent_comm]
  · simpa [Matrix.of_apply] using coherentKernel_quadForm_nonneg u c

/-- **`(13g)`: the reflection-doubled kernel is again a positive Gram kernel.** -/
theorem bicoherentKernel_quadForm_nonneg {n : ℕ} (u c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * bicoherentKernel (u i) (u j) * c j := by
  have h1 := coherentKernel_posSemidef u
  have h2 := coherentKernel_posSemidef (fun i => -u i)
  have hh := h1.hadamard h2
  have heq : (Matrix.of fun i j => coherentKernel (u i) (u j)).hadamard
      (Matrix.of fun i j => coherentKernel (-u i) (-u j))
      = Matrix.of fun i j => bicoherentKernel (u i) (u j) := by
    ext i j
    simp [Matrix.hadamard, bicoherentKernel]
  rw [heq] at hh
  simpa [Matrix.of_apply] using quadForm_of_posSemidef hh c

/-! ## The rapid end has no distributional limit -/

theorem divProfile_rapidPairing (V : ℝ) :
    divProfile (fun s => (Real.exp (V * s) - 1) * s) = fun t => Real.exp (V * t) - 1 := by
  funext t
  rw [divProfile]
  split_ifs with ht
  · rw [ht]
    simp
  · rw [mul_div_assoc, div_self ht, mul_one]

/-- **The positive end escapes rapidly.**  Pairing `F_V` with the single test profile `f(t) = t`
already grows like `e^V/V`, so `F_V` has no limit in the distributional dual. -/
theorem tendsto_rapidPairing_atTop :
    Tendsto (fun V : ℝ => ∫ t in (0 : ℝ)..1,
        divProfile (fun s => (Real.exp (V * s) - 1) * s) t) atTop atTop := by
  have hval : ∀ V : ℝ, (∫ t in (0 : ℝ)..1, divProfile (fun s => (Real.exp (V * s) - 1) * s) t)
      = ∫ t in (0 : ℝ)..1, (Real.exp (V * t) - 1) := by
    intro V
    rw [divProfile_rapidPairing]
  refine tendsto_atTop_mono' atTop
    (f₁ := fun V : ℝ => (Real.exp (V / 2) - 1) / 2) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
    rw [hval]
    have hcont : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (V * t) - 1) volume a b :=
      fun a b => (Continuous.intervalIntegrable
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const) a b)
    have hsplit : (∫ t in (0 : ℝ)..1, (Real.exp (V * t) - 1))
        = (∫ t in (0 : ℝ)..(1 / 2 : ℝ), (Real.exp (V * t) - 1))
          + ∫ t in (1 / 2 : ℝ)..1, (Real.exp (V * t) - 1) :=
      (intervalIntegral.integral_add_adjacent_intervals (hcont 0 (1/2)) (hcont (1/2) 1)).symm
    have hhead : 0 ≤ ∫ t in (0 : ℝ)..(1 / 2 : ℝ), (Real.exp (V * t) - 1) := by
      refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
      have := Real.one_le_exp (by nlinarith [ht.1] : (0:ℝ) ≤ V * t)
      linarith
    have htail : (Real.exp (V / 2) - 1) / 2 ≤ ∫ t in (1 / 2 : ℝ)..1, (Real.exp (V * t) - 1) := by
      have hmono : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
          Real.exp (V / 2) - 1 ≤ Real.exp (V * t) - 1 := by
        intro t ht
        have : Real.exp (V / 2) ≤ Real.exp (V * t) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith [ht.1]
        linarith
      have hcmp := intervalIntegral.integral_mono_on (by norm_num : (1/2:ℝ) ≤ 1)
        (intervalIntegrable_const (c := Real.exp (V / 2) - 1)) (hcont (1/2) 1) hmono
      rw [intervalIntegral.integral_const] at hcmp
      simp only [smul_eq_mul] at hcmp
      linarith
    rw [hsplit]
    linarith
  · refine Filter.Tendsto.atTop_div_const (by norm_num) ?_
    have hexp : Tendsto (fun V : ℝ => Real.exp (V / 2)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
    have h := hexp.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
    simpa [sub_eq_add_neg] using h

end

end RHTower
