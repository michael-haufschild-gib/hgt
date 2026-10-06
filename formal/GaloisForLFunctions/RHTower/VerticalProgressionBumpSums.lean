import GaloisForLFunctions.RHTower.VerticalProgressionFirstMomentExpansion

/-!
# Bump sums and the mollified coefficients at a fixed integer

**Bump sums** `L_T(u) = Σ_ℓ φ(ℓ/T) e(ℓu)` for a smooth `φ` supported in `[1, 2]`:
* `‖L_T(u)‖ ≤ (T + 1) Φ₀` (`norm_bumpSum_le`);
* if `u` is at distance `≥ δ > 0` from `ℤ`, `‖L_T(u)‖ ≤ (k + 2) Φ_k T / (4Tδ)^k`
  (`norm_bumpSum_le_osc`), from the lattice summation by parts;
* `L_T(j)/T → ∫ φ` for `j ∈ ℤ` (Riemann sums) and `L_T(u)/T → 0` for `u ∉ ℤ`
  (`tendsto_bumpSum_div_int`, `tendsto_bumpSum_div_of_not_int`).

**Mollified coefficients.** If `N → ∞` and `X → ∞` then `a(1) = b_N(1) V(1/X) → 1`
(`tendsto_mollCoeff_one`), and for every fixed `n ≥ 2`, `a(n) → 0` (`tendsto_mollCoeff_of_two_le`):
once `N ≥ n`,

`a(n) = Σ_{h | n} μ(h)(1 − log h/log N) V(n/(hX)) = Λ(n)/log N + Σ_{h | n} b_N(h)(V(n/(hX)) − 1)`,

because `Σ_{h | n} μ(h) = 0` and `Σ_{h | n} μ(h) log h = −Λ(n)`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.VerticalAP

noncomputable section

/-! ## Bump sums -/

theorem support_bump_subset {φ : ℝ → ℂ} (hsupp : Function.support φ ⊆ Icc 1 2) {T : ℝ}
    (hT : 0 < T) : Function.support (fun x => φ (x / T)) ⊆ Icc T (2 * T) := by
  have := support_cutoff_subset hsupp hT (fun _ => (1 : ℂ))
  simpa using this

theorem norm_bumpSum_le {φ : ℝ → ℂ} (hsupp : Function.support φ ⊆ Icc 1 2) {Φ₀ : ℝ}
    (hΦ₀ : ∀ y, ‖φ y‖ ≤ Φ₀) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    ‖bumpSum φ T u‖ ≤ (T + 1) * Φ₀ := by
  have h := norm_latticeSum_le_of_bound (h := fun x => φ (x / T)) (by linarith : T ≤ 2 * T)
    (support_bump_subset hsupp hT) (fun x => hΦ₀ _) u
  unfold bumpSum
  simpa [show 2 * T - T + 1 = T + 1 by ring] using h

theorem norm_iteratedDeriv_bump_le {φ : ℝ → ℂ} {k : ℕ} (hφ : ContDiff ℝ k φ) {Φk : ℝ}
    (hΦk : ∀ y, ‖iteratedDeriv k φ y‖ ≤ Φk) {T : ℝ} (hT : 0 < T) (y : ℝ) :
    ‖iteratedDeriv k (fun x => φ (x / T)) y‖ ≤ Φk / T ^ k := by
  have hfun : (fun x => φ (x / T)) = fun x => φ (T⁻¹ * x) := by
    funext x; rw [div_eq_inv_mul]
  rw [hfun, iteratedDeriv_comp_const_smul hφ T⁻¹, norm_smul, norm_pow, norm_inv, Real.norm_eq_abs,
    abs_of_pos hT, inv_pow, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hΦk _) (by positivity)

/-- **Oscillation bound for bump sums.** -/
theorem norm_bumpSum_le_osc {φ : ℝ → ℂ} {k : ℕ} (hφ : ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {Φk : ℝ} (hΦk : ∀ y, ‖iteratedDeriv k φ y‖ ≤ Φk)
    {T : ℝ} (hT : 1 ≤ T) {u δ : ℝ} (hδ : 0 < δ) (hu : ∀ j : ℤ, δ ≤ |u - j|) :
    ‖bumpSum φ T u‖ ≤ (k + 2) * Φk * T / (4 * T * δ) ^ k := by
  have hT0 : 0 < T := by linarith
  have hΦ0 : 0 ≤ Φk := (norm_nonneg _).trans (hΦk 0)
  have hcd : ContDiff ℝ k (fun x => φ (x / T)) := hφ.comp (contDiff_id.div_const T)
  have h := norm_latticeSum_le (by linarith : T ≤ 2 * T) hcd (support_bump_subset hsupp hT0)
    (norm_iteratedDeriv_bump_le hφ hΦk hT0) hδ hu
  unfold bumpSum
  refine h.trans ?_
  have e : (4 * T * δ) ^ k = T ^ k * (4 * δ) ^ k := by
    rw [show 4 * T * δ = T * (4 * δ) by ring, mul_pow]
  have e2 : (2 * T - T + k + 1) * (Φk / T ^ k) / (4 * δ) ^ k =
      ((2 * T - T + k + 1) * Φk) / (T ^ k * (4 * δ) ^ k) := by field_simp
  rw [e, e2]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hk : 2 * T - T + k + 1 ≤ (k + 2) * T := by nlinarith
  nlinarith

theorem bumpSum_int (φ : ℝ → ℂ) (T : ℝ) (j : ℤ) : bumpSum φ T j = ∑' ℓ : ℤ, φ (ℓ / T) := by
  unfold bumpSum latticeSum
  refine tsum_congr fun ℓ => ?_
  rw [show (ℓ : ℝ) * (j : ℝ) = ((ℓ * j : ℤ) : ℝ) by push_cast; ring, unitExp_int, mul_one]

/-- **Riemann sums.** `‖Σ_ℓ φ(ℓ/T) − T ∫ φ‖ ≤ (T + 4) Φ₁ / T`. -/
theorem norm_tsum_bump_sub_le {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {Φ₁ : ℝ} (hΦ₁ : ∀ y, ‖deriv φ y‖ ≤ Φ₁) {T : ℝ}
    (hT : 0 < T) :
    ‖(∑' ℓ : ℤ, φ (ℓ / T)) - (T : ℂ) * ∫ x, φ x‖ ≤ (T + 4) * (Φ₁ / T) := by
  have hdiff : Differentiable ℝ (fun x => φ (x / T)) :=
    (hφ.differentiable one_ne_zero).comp (differentiable_id.div_const T)
  have hderiv : ∀ x, ‖deriv (fun x => φ (x / T)) x‖ ≤ Φ₁ / T := by
    intro x
    have h := norm_iteratedDeriv_bump_le (k := 1) hφ (by simpa using hΦ₁) hT x
    simpa using h
  have h := norm_tsum_sub_integral_le (by linarith : T ≤ 2 * T) hdiff (support_bump_subset hsupp hT)
    hderiv
  have hint : (∫ x, φ (x / T)) = (T : ℂ) * ∫ x, φ x := by
    rw [Measure.integral_comp_div, abs_of_pos hT, Complex.real_smul]
  rw [hint] at h
  refine h.trans (le_of_eq ?_)
  ring

theorem tendsto_bumpSum_div_int {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {Φ₁ : ℝ} (hΦ₁ : ∀ y, ‖deriv φ y‖ ≤ Φ₁) (j : ℤ) :
    Tendsto (fun T : ℝ => bumpSum φ T j / T) atTop (𝓝 (∫ x, φ x)) := by
  have hΦ0 : 0 ≤ Φ₁ := (norm_nonneg _).trans (hΦ₁ 0)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ T : ℝ in atTop, ‖bumpSum φ T j / T - ∫ x, φ x‖ ≤ 5 * Φ₁ / T := by
    filter_upwards [eventually_ge_atTop 4] with T hT
    have hT0 : 0 < T := by linarith
    have h := norm_tsum_bump_sub_le hφ hsupp hΦ₁ hT0
    rw [← bumpSum_int] at h
    have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    have heq : bumpSum φ T j / T - ∫ x, φ x = (bumpSum φ T j - T * ∫ x, φ x) / T := by
      field_simp
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0, div_le_div_iff₀ hT0 hT0]
    calc ‖bumpSum φ T j - T * ∫ x, φ x‖ * T ≤ (T + 4) * (Φ₁ / T) * T :=
          mul_le_mul_of_nonneg_right h hT0.le
      _ = (T + 4) * Φ₁ := by field_simp
      _ ≤ 5 * Φ₁ * T := by nlinarith
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  exact tendsto_const_nhds.div_atTop tendsto_id

theorem tendsto_bumpSum_div_of_not_int {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) {Φ₂ : ℝ} (hΦ₂ : ∀ y, ‖iteratedDeriv 2 φ y‖ ≤ Φ₂)
    {u : ℝ} (hu : ∀ j : ℤ, u ≠ j) :
    Tendsto (fun T : ℝ => bumpSum φ T u / T) atTop (𝓝 0) := by
  set δ : ℝ := |u - round u| with hδ
  have hδpos : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr (hu _))
  have hδle : ∀ j : ℤ, δ ≤ |u - j| := fun j => round_le u j
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ T : ℝ in atTop, ‖bumpSum φ T u / T‖ ≤ (4 * Φ₂ / (4 * δ) ^ 2) / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : 0 < T := by linarith
    have h := norm_bumpSum_le_osc (k := 2) hφ hsupp hΦ₂ hT hδpos hδle
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0,
      div_le_div_iff₀ hT0 hT0]
    have hΦ0 : 0 ≤ Φ₂ := (norm_nonneg _).trans (hΦ₂ 0)
    calc ‖bumpSum φ T u‖ * T ≤ ((2 : ℕ) + 2) * Φ₂ * T / (4 * T * δ) ^ 2 * T :=
          mul_le_mul_of_nonneg_right h hT0.le
      _ = 4 * Φ₂ / (4 * δ) ^ 2 := by push_cast; field_simp; ring
      _ ≤ 4 * Φ₂ / (4 * δ) ^ 2 * T := le_mul_of_one_le_right (by positivity) hT
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  exact tendsto_const_nhds.div_atTop tendsto_id

/-! ## The mollified coefficients at a fixed integer -/

theorem tendsto_smoothAFECutoff_inv_atTop {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f atTop atTop) :
    Tendsto (fun T => smoothAFECutoff (c / f T)) atTop (𝓝 1) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1 / 4) (by norm_num)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun T => K * (c / f T) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T => c / f T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hf
    have h2 := (Real.continuousAt_rpow_const 0 (1 / 4) (Or.inr (by norm_num))).tendsto.comp h1
    simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using h2.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hf.eventually_gt_atTop 0] with T hT
  exact hKb (div_pos hc hT)

theorem linearMollifierCoeff_one {N : ℕ} (hN : 2 ≤ N) : Sieve.linearMollifierCoeff N 1 = 1 := by
  unfold Sieve.linearMollifierCoeff
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  simp [hlog]

/-- `a(1) = b_N(1) V(1/X) → 1`. -/
theorem tendsto_mollCoeff_one {Nm : ℝ → ℕ} {X : ℝ → ℝ} (hN : Tendsto Nm atTop atTop)
    (hX : Tendsto X atTop atTop) :
    Tendsto (fun T => mollCoeff (Nm T) (X T) 1) atTop (𝓝 1) := by
  have hV := tendsto_smoothAFECutoff_inv_atTop (c := 1) one_pos hX
  refine hV.congr' ?_
  filter_upwards [hN.eventually_ge_atTop 2] with T hT
  unfold mollCoeff
  rw [Finset.sum_eq_single 1]
  · simp [linearMollifierCoeff_one hT]
  · intro h hh h1
    have : ¬ h ∣ 1 := fun hd => h1 (Nat.dvd_one.mp hd)
    simp [this]
  · intro h; exfalso; exact h (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)

/-- The mollified coefficient at a fixed `n` once `N ≥ n`. -/
theorem mollCoeff_eq_divisors {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (X : ℝ) :
    mollCoeff N X n = ∑ h ∈ n.divisors,
      (Sieve.linearMollifierCoeff N h : ℂ) * smoothAFECutoff (((n / h : ℕ) : ℝ) / X) := by
  unfold mollCoeff
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext h
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, _⟩, hd⟩; exact ⟨hd, by omega⟩
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hnN⟩, hd⟩

/-- **For fixed `n ≥ 2`, `a(n) → 0`.** -/
theorem tendsto_mollCoeff_of_two_le {Nm : ℝ → ℕ} {X : ℝ → ℝ} (hN : Tendsto Nm atTop atTop)
    (hX : Tendsto X atTop atTop) {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun T => mollCoeff (Nm T) (X T) n) atTop (𝓝 0) := by
  have hlogN : Tendsto (fun T => Real.log (Nm T)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  -- the main part `Λ(n)/log N`
  have h1 : Tendsto (fun T => ((ArithmeticFunction.vonMangoldt n / Real.log (Nm T) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have h0 := (tendsto_const_nhds (x := ArithmeticFunction.vonMangoldt n)).div_atTop hlogN
    have h1 := (Complex.continuous_ofReal.tendsto 0).comp h0
    rw [Complex.ofReal_zero] at h1
    exact h1
  -- the cutoff part `Σ_{h | n} b_N(h)(V(n/(hX)) − 1)`
  have h2 : Tendsto (fun T => ∑ h ∈ n.divisors, (Sieve.linearMollifierCoeff (Nm T) h : ℂ) *
      (smoothAFECutoff (((n / h : ℕ) : ℝ) / X T) - 1)) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑ h ∈ n.divisors, (0 : ℂ) by simp]
    refine tendsto_finsetSum _ fun h hh => ?_
    have hpos : 0 < n / h := Nat.div_pos (Nat.divisor_le hh) (Nat.pos_of_mem_divisors hh)
    have hV := tendsto_smoothAFECutoff_inv_atTop (c := ((n / h : ℕ) : ℝ)) (by exact_mod_cast hpos) hX
    have hV0 : Tendsto (fun T => smoothAFECutoff (((n / h : ℕ) : ℝ) / X T) - 1) atTop (𝓝 0) := by
      simpa using hV.sub_const 1
    rw [tendsto_zero_iff_norm_tendsto_zero] at hV0 ⊢
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hV0
    filter_upwards [hN.eventually_ge_atTop n] with T hT
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := abs_linearMollifierCoeff_le_one (N := Nm T) (h := h)
      (Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hh, (Nat.divisor_le hh).trans hT⟩)
    calc |Sieve.linearMollifierCoeff (Nm T) h| *
          ‖smoothAFECutoff (((n / h : ℕ) : ℝ) / X T) - 1‖
        ≤ 1 * ‖smoothAFECutoff (((n / h : ℕ) : ℝ) / X T) - 1‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := one_mul _
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hN.eventually_ge_atTop n] with T hT
  have hNT : 2 ≤ Nm T := hn.trans hT
  have hlog : Real.log (Nm T) ≠ 0 := (Real.log_pos (by exact_mod_cast hNT)).ne'
  rw [mollCoeff_eq_divisors (by omega) hT]
  -- `Σ_{h | n} b_N(h) = Λ(n)/log N`
  have hb : ∑ h ∈ n.divisors, (Sieve.linearMollifierCoeff (Nm T) h : ℂ) =
      ((ArithmeticFunction.vonMangoldt n / Real.log (Nm T) : ℝ) : ℂ) := by
    have hμ : ∑ h ∈ n.divisors, ((ArithmeticFunction.moebius h : ℤ) : ℝ) = 0 := by
      have := congrArg (fun f : ArithmeticFunction ℤ => f n)
        ArithmeticFunction.moebius_mul_coe_zeta
      simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
        if_neg (by omega : n ≠ 1)] at this
      exact_mod_cast this
    have hΛ := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
    simp only [ArithmeticFunction.log_apply] at hΛ
    have hreal : ∑ h ∈ n.divisors, Sieve.linearMollifierCoeff (Nm T) h =
        ArithmeticFunction.vonMangoldt n / Real.log (Nm T) := by
      unfold Sieve.linearMollifierCoeff
      rw [← Finset.sum_div]
      congr 1
      have hsplit : ∀ h ∈ n.divisors, ((ArithmeticFunction.moebius h : ℤ) : ℝ) *
          Real.log ((Nm T : ℝ) / h) = ((ArithmeticFunction.moebius h : ℤ) : ℝ) * Real.log (Nm T) -
          ((ArithmeticFunction.moebius h : ℤ) : ℝ) * Real.log h := by
        intro h hh
        have hh0 : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_mem_divisors hh
        rw [Real.log_div (by positivity) hh0.ne']
        ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ, zero_mul,
        zero_sub, hΛ]
      ring
    rw [← hreal]
    push_cast
    rfl
  rw [← hb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  ring

end

end RHTower.VerticalAP
