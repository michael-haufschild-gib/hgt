import GaloisForLFunctions.RHTower.CramerZeroSumMeanSquare

/-!
# Cramér's sharp mean-square bound for the Chebyshev error

Under RH there is `C ≥ 0` such that
`∫_X^{2X} (ψ(x) - x)² dx ≤ C X²` for every `X ≥ 1`.

The genus-kernel explicit formula evaluates a multiplicative short-window average.
Its zero coefficients satisfy `|cρ(r)| ≤ 2/|Im ρ|` uniformly for `1 < r ≤ 2`, so
`CramerZeroSumMeanSquare` supplies one mean-square bound independent of the smoothing
width. The trivial-zero correction is uniformly bounded. Right continuity of `ψ`
and the logarithmic-mean squeeze identify the limit as `r ↓ 1`; dominated convergence
passes the bound to the literal prime error. The compact range `1 ≤ X < 2` is included.

No pointwise unsmoothed zero expansion or extra analytic bound is assumed.
-/

open Complex Finset MeasureTheory Set Filter Topology

namespace RHTower
noncomputable section

private def cramerWindowCoeff (r : ℝ) (q : XiZeroCopy) : ℂ :=
  lagWindowZeroTerm (q.1 : ℂ) 1 r

private theorem cramerWindowCoeff_bound {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (q : XiZeroCopy) : ‖cramerWindowCoeff r q‖ ≤ 2 / |zeroOrdinate q| := by
  have hr0 : 0 < r := by linarith
  have hw : 0 < 1 - 1 / r := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hr
  have hwC : ((1 - 1 / r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hρ1 : (q.1 : ℂ) - 1 ≠ 0 := by
    intro h
    exact xiZeroCopy_one_sub_ne_zero q (by linear_combination -h)
  have h0 : (0 : ℝ) ∉ uIcc 1 r := by
    rw [uIcc_of_le hr.le]
    norm_num
  have hI := integral_cpow (a := 1) (b := r) (r := (q.1 : ℂ) - 2)
    (Or.inr ⟨by intro h; exact hρ1 (by linear_combination h), h0⟩)
  rw [show (q.1 : ℂ) - 2 + 1 = (q.1 : ℂ) - 1 by ring] at hI
  have hrep : (q.1 : ℂ) * cramerWindowCoeff r q =
      -(∫ t in (1 : ℝ)..r, (t : ℂ) ^ ((q.1 : ℂ) - 2)) / ((1 - 1 / r : ℝ) : ℂ) := by
    rw [hI, cramerWindowCoeff, lagWindowZeroTerm]
    norm_num
    have hρ0 := xiZeroCopy_ne_zero q
    have hρ1' := xiZeroCopy_one_sub_ne_zero q
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => 2 * t ^ (-2 : ℤ)) volume 1 r :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul 2
  have hnorm : ‖∫ t in (1 : ℝ)..r, (t : ℂ) ^ ((q.1 : ℂ) - 2)‖ ≤
      2 * (1 - 1 / r) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le hr.le
      (f := fun t : ℝ => (t : ℂ) ^ ((q.1 : ℂ) - 2))
      (ae_of_all _ (fun t ht => ?_)) hint
    · simpa only [intervalIntegral.integral_const_mul,
        integral_zpow_neg_two (by norm_num : (0 : ℝ) < 1) hr.le, one_div_one] using h
    · have ht0 : 0 < t := by linarith [ht.1]
      have ht1 : 1 ≤ t := ht.1.le
      have hpow : t ^ (q.1 : ℂ).re ≤ 2 := by
        calc
          _ ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (xiZeroCopy_re_lt_one q).le
          _ = t := Real.rpow_one t
          _ ≤ 2 := ht.2.trans hr2
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re]
      change t ^ ((q.1 : ℂ).re - 2) ≤ 2 * t ^ (-2 : ℤ)
      rw [show (q.1 : ℂ).re - 2 = (q.1 : ℂ).re + (-2 : ℤ) by norm_num; ring,
        Real.rpow_add ht0, Real.rpow_intCast]
      exact mul_le_mul_of_nonneg_right hpow (zpow_nonneg ht0.le _)
  have hprod : ‖(q.1 : ℂ)‖ * ‖cramerWindowCoeff r q‖ ≤ 2 := by
    rw [← norm_mul, hrep, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr hnorm
  have hγ : 0 < |zeroOrdinate q| := by linarith [four_lt_abs_zeroOrdinate q]
  rw [le_div_iff₀ hγ]
  have him := Complex.abs_im_le_norm (q.1 : ℂ)
  change |zeroOrdinate q| ≤ ‖(q.1 : ℂ)‖ at him
  nlinarith [mul_le_mul_of_nonneg_right him (norm_nonneg (cramerWindowCoeff r q))]

private theorem cramerWindowCoeff_scale {r x : ℝ} (hr : 1 < r) (hx : 0 < x)
    (q : XiZeroCopy) :
    lagWindowZeroTerm (q.1 : ℂ) x (r * x) =
      cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ) := by
  have hr0 : 0 < r := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rw [cramerWindowCoeff, lagWindowZeroTerm, lagWindowZeroTerm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr0.le hx.le,
    Complex.cpow_sub _ _ hxC, Complex.cpow_one]
  norm_num
  field_simp

private theorem cramer_trivial_series_div {a : ℝ} (ha : 1 ≤ a) :
    HasSum (fun k : ℕ => (1 / a) ^ (2 * (k + 1) + 1) /
      (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) (trivialZeroSeriesReal a / a) := by
  have h := (summable_trivialZeroSeriesReal_term ha).hasSum.div_const a
  apply h.congr
  intro F
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  rw [pow_succ, one_div_pow, one_div]
  ring

private theorem cramer_trivial_window_bound {a b : ℝ} (ha : 2 ≤ a) (hab : a < b) :
    0 ≤ (trivialZeroSeriesReal a / a - trivialZeroSeriesReal b / b) / (1 / a - 1 / b) ∧
    (trivialZeroSeriesReal a / a - trivialZeroSeriesReal b / b) / (1 / a - 1 / b) ≤ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  let u := 1 / a
  let v := 1 / b
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hvu : v < u := one_div_lt_one_div_of_lt ha0 hab
  have hu2 : u ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) ha
  have hw : 0 < u - v := sub_pos.mpr hvu
  have hsa := cramer_trivial_series_div (show 1 ≤ a by linarith)
  have hsb := cramer_trivial_series_div (show 1 ≤ b by linarith)
  have hterm (k : ℕ) :
      u ^ (2 * (k + 1) + 1) / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) -
        v ^ (2 * (k + 1) + 1) / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) ≤
          (u - v) * (1 / 4 : ℝ) ^ k := by
    have hd : 0 < 2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
    have hp := abs_pow_sub_pow_le (a := u) (b := v) (n := 2 * (k + 1) + 1)
    rw [abs_of_pos hu, abs_of_pos hv, max_eq_left hvu.le, abs_of_pos hw,
      Nat.add_sub_cancel] at hp
    have hpow : u ^ (2 * (k + 1)) ≤ (1 / 4 : ℝ) ^ k := by
      rw [pow_mul]
      calc
        _ ≤ (1 / 4 : ℝ) ^ (k + 1) :=
          pow_le_pow_left₀ (sq_nonneg u) (by nlinarith) _
        _ ≤ _ := by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm : ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤
        2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by push_cast; nlinarith
    calc
      _ = (u ^ (2 * (k + 1) + 1) - v ^ (2 * (k + 1) + 1)) /
          (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) := by ring
      _ ≤ |u ^ (2 * (k + 1) + 1) - v ^ (2 * (k + 1) + 1)| /
          (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) :=
        div_le_div_of_nonneg_right (le_abs_self _) hd.le
      _ ≤ ((u - v) * ((2 * (k + 1) + 1 : ℕ) : ℝ) * u ^ (2 * (k + 1))) /
          (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) :=
        div_le_div_of_nonneg_right hp hd.le
      _ ≤ (u - v) * u ^ (2 * (k + 1)) := by
        rw [div_le_iff₀ hd]
        calc
          _ = ((u - v) * u ^ (2 * (k + 1))) * ((2 * (k + 1) + 1 : ℕ) : ℝ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hw.le
  have hgeom := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (u - v)
  have hbound : trivialZeroSeriesReal a / a - trivialZeroSeriesReal b / b ≤ 2 * (u - v) := by
    rw [← (hsa.sub hsb).tsum_eq]
    calc
      _ ≤ ∑' k : ℕ, (u - v) * (1 / 4 : ℝ) ^ k :=
        (hsa.sub hsb).summable.tsum_le_tsum hterm hgeom
      _ = (u - v) * (1 - (1 / 4 : ℝ))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ ≤ _ := by norm_num; linarith
  constructor
  · apply div_nonneg
    · exact sub_nonneg.mpr (trivialZeroSeriesReal_div_anti (by linarith) hab.le)
    · exact hw.le
  · exact (div_le_iff₀ hw).mpr hbound

private def cramerPrimeWindowError (r x : ℝ) : ℝ :=
  chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) -
    Real.log ((r * x) / x) / (1 / x - 1 / (r * x))

private theorem cramer_window_bounds {r x : ℝ} (hr : 1 < r) (hx : 0 < x) :
    Chebyshev.psi x ≤ chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) ∧
    chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) ≤ Chebyshev.psi (r * x) ∧
    x ≤ Real.log ((r * x) / x) / (1 / x - 1 / (r * x)) ∧
    Real.log ((r * x) / x) / (1 / x - 1 / (r * x)) ≤ r * x := by
  have hxr : x < r * x := by nlinarith
  have hw : 0 < 1 / x - 1 / (r * x) :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hx hxr)
  obtain ⟨h₁,h₂⟩ := chebyshevLagWindow_bounds hx hxr.le
  obtain ⟨h₃,h₄⟩ := log_div_le_mul_inv_sub hx hxr.le
  exact ⟨(le_div_iff₀ hw).mpr h₁, (div_le_iff₀ hw).mpr h₂,
    (le_div_iff₀ hw).mpr h₃, (div_le_iff₀ hw).mpr h₄⟩

private theorem cramerWindowError_measurable (r : ℝ) : Measurable (cramerPrimeWindowError r) := by
  have hL : Measurable lagPsiSum := by
    change Measurable ((fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)) ∘ (Nat.floor : ℝ → ℕ))
    exact measurable_from_nat.comp Nat.measurable_floor
  have hψ : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  unfold cramerPrimeWindowError chebyshevLagWindow
  fun_prop

private theorem cramerWindowError_bound {r X x : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (hX : 0 < X) (hx : x ∈ Set.Icc X (2 * X)) :
    |cramerPrimeWindowError r x| ≤ Chebyshev.psi (4 * X) + 4 * X := by
  have hx0 := hX.trans_le hx.1
  obtain ⟨h₁,h₂,h₃,h₄⟩ := cramer_window_bounds hr hx0
  have hrx : r * x ≤ 4 * X := by
    nlinarith [mul_le_mul_of_nonneg_right hr2 hx0.le, hx.2]
  have hψ := Chebyshev.psi_mono hrx
  have hJ0 : 0 ≤ chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)) :=
    (Chebyshev.psi_nonneg x).trans h₁
  have hL0 : 0 ≤ Real.log ((r * x) / x) / (1 / x - 1 / (r * x)) := hx0.le.trans h₃
  unfold cramerPrimeWindowError
  calc
    _ ≤ |chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x))| +
        |Real.log ((r * x) / x) / (1 / x - 1 / (r * x))| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg hJ0, abs_of_nonneg hL0]; linarith

private theorem cramer_psi_right_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun r : ℝ => Chebyshev.psi (r * x)) (𝓝[>] 1) (𝓝 (Chebyshev.psi x)) := by
  have ht : Tendsto (fun r : ℝ => r * x) (𝓝[>] 1) (𝓝 x) := by
    simpa using ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1)).mul_const x).mono_left
      nhdsWithin_le_nhds
  have hf : ∀ᶠ r : ℝ in 𝓝[>] 1, ⌊r * x⌋₊ = ⌊x⌋₊ := by
    filter_upwards [ht.eventually (gt_mem_nhds (Nat.lt_floor_add_one x)), self_mem_nhdsWithin]
      with r hr hrlow
    have hrx : x ≤ r * x := by
      simpa using mul_le_mul_of_nonneg_right (show 1 ≤ r from hrlow.le) hx.le
    apply (Nat.floor_eq_iff (hx.le.trans hrx)).mpr
    exact ⟨(Nat.floor_le hx.le).trans hrx, hr⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [hf] with r hr
  rw [Chebyshev.psi_eq_psi_coe_floor (r * x), hr, ← Chebyshev.psi_eq_psi_coe_floor x]

private theorem cramerWindowError_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun r => cramerPrimeWindowError r x) (𝓝[>] 1) (𝓝 (Chebyshev.psi x - x)) := by
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] 1, 1 < r := self_mem_nhdsWithin
  have hJ : Tendsto (fun r => chebyshevLagWindow x (r * x) / (1 / x - 1 / (r * x)))
      (𝓝[>] 1) (𝓝 (Chebyshev.psi x)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (cramer_psi_right_limit hx)
    · exact hbounds.mono (fun r hr => (cramer_window_bounds hr hx).1)
    · exact hbounds.mono (fun r hr => (cramer_window_bounds hr hx).2.1)
  have ht : Tendsto (fun r : ℝ => r * x) (𝓝[>] 1) (𝓝 x) := by
    simpa using ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1)).mul_const x).mono_left
      nhdsWithin_le_nhds
  have hL : Tendsto (fun r => Real.log ((r * x) / x) / (1 / x - 1 / (r * x)))
      (𝓝[>] 1) (𝓝 x) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    · exact hbounds.mono (fun r hr => (cramer_window_bounds hr hx).2.2.1)
    · exact hbounds.mono (fun r hr => (cramer_window_bounds hr hx).2.2.2)
  exact hJ.sub hL

private theorem cramer_zero_continuous {X : ℝ} (hX : 1 ≤ X) (c : XiZeroCopy → ℂ)
    (hc : Summable (fun q => ‖c q‖)) :
    ContinuousOn (fun x : ℝ => ∑' q : XiZeroCopy, c q * (x : ℂ) ^ (q.1 : ℂ))
      (Set.uIcc X (2 * X)) := by
  have hXX : X ≤ 2 * X := by linarith
  have hx1 : ∀ x ∈ Set.uIcc X (2 * X), 1 ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hXX] at hx
    exact hX.trans hx.1
  apply continuousOn_tsum (u := fun q => (2 * X) * ‖c q‖)
  · intro q
    apply continuousOn_const.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (by linarith [hx1 x hx]))
  · exact hc.mul_left _
  · intro q x hx
    have hx0 : 0 < x := by linarith [hx1 x hx]
    have hp := Real.rpow_le_rpow_of_exponent_le (hx1 x hx) (xiZeroCopy_re_lt_one q).le
    rw [Real.rpow_one] at hp
    rw [Set.uIcc_of_le hXX] at hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    nlinarith [norm_nonneg (c q), hx.2]

private theorem cramer_window_zero_energy (hRH : RiemannHypothesis) {r X : ℝ}
    (hr : 1 < r) (hr2 : r ≤ 2) (hX : 1 ≤ X) :
    ∫ x in X..2 * X, ‖∑' q : XiZeroCopy,
      cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 ≤
        32 * cramerZeroEnergyConstant * X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hs : Summable (fun q : XiZeroCopy => ‖cramerWindowCoeff r q‖) :=
    summable_norm_lagWindowZeroTerm (by norm_num : (1 : ℝ) ≤ 1) hr
  have hcont : ContinuousOn (fun x : ℝ =>
      ‖∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2)
      (Set.uIcc X (2 * X)) :=
    (cramer_zero_continuous hX (cramerWindowCoeff r) hs).norm.pow 2
  have hwcont := hcont.div (continuousOn_id.pow 3) (fun x hx => by
    rw [Set.uIcc_of_le hXX] at hx
    exact pow_ne_zero _ (hX0.trans_le hx.1).ne')
  have hweight := cramer_summable_zero_energy hRH hX (by norm_num : (0 : ℝ) ≤ 2)
    (cramerWindowCoeff r) (cramerWindowCoeff_bound hr hr2) hs
  calc
    _ ≤ ∫ x in X..2 * X, (2 * X) ^ 3 *
        (‖∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) := by
      apply intervalIntegral.integral_mono_on hXX hcont.intervalIntegrable
        (hwcont.const_mul _).intervalIntegrable
      intro x hx
      have hx0 : 0 < x := hX0.trans_le hx.1
      have hn : 0 ≤ ‖∑' q : XiZeroCopy,
          cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 := by positivity
      calc
        _ = x ^ 3 * (‖∑' q : XiZeroCopy,
            cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0.le hx.2 3) hn
    _ = (2 * X) ^ 3 * (∫ x in X..2 * X,
        ‖∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (2 * X) ^ 3 * (cramerZeroEnergyConstant * 2 ^ 2 / X) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by field_simp; ring

private theorem cramer_window_error_sq_le {r x : ℝ} (hr : 1 < r) (hx : 2 ≤ x) :
    cramerPrimeWindowError r x ^ 2 ≤
      2 * ‖∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 +
        2 * (|Real.log (2 * Real.pi)| + 2) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hxr : x < r * x := by nlinarith
  let Z := ∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)
  let T := (trivialZeroSeriesReal x / x - trivialZeroSeriesReal (r * x) / (r * x)) /
    (1 / x - 1 / (r * x))
  have hT := cramer_trivial_window_bound hx hxr
  have hform := chebyshevLagWindow_div_eq (by linarith : 1 < x) hxr
  have hsum : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (r * x)) = Z :=
    tsum_congr (fun q => cramerWindowCoeff_scale hr hx0 q)
  rw [hsum] at hform
  have hE : cramerPrimeWindowError r x = Z.re + (T - Real.log (2 * Real.pi)) := by
    unfold cramerPrimeWindowError
    rw [hform]
    dsimp [T]
    ring
  have hz : Z.re ^ 2 ≤ ‖Z‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg Z.re) (Complex.abs_re_le_norm Z) 2
  have hb : |T - Real.log (2 * Real.pi)| ≤ |Real.log (2 * Real.pi)| + 2 := by
    have h := abs_sub T (Real.log (2 * Real.pi))
    rw [abs_of_nonneg hT.1] at h
    linarith [hT.2]
  have hb2 := pow_le_pow_left₀ (abs_nonneg (T - Real.log (2 * Real.pi))) hb 2
  rw [sq_abs] at hb2
  rw [hE]
  change (Z.re + (T - Real.log (2 * Real.pi))) ^ 2 ≤ 2 * ‖Z‖ ^ 2 + _
  nlinarith [sq_nonneg (Z.re - (T - Real.log (2 * Real.pi)))]

private theorem cramer_intervalIntegrable_sq {f : ℝ → ℝ} {X C : ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.uIoc X (2 * X), |f x| ≤ C) :
    IntervalIntegrable (fun x => f x ^ 2) volume X (2 * X) := by
  apply (intervalIntegrable_const (c := C ^ 2)).mono_fun'
    (hf.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) (hbound x hx) 2

private def cramerPrimeEnergyConstant : ℝ :=
  64 * cramerZeroEnergyConstant + 2 * (|Real.log (2 * Real.pi)| + 2) ^ 2

private theorem cramerPrimeEnergyConstant_nonneg : 0 ≤ cramerPrimeEnergyConstant := by
  unfold cramerPrimeEnergyConstant
  have := cramerZeroEnergyConstant_nonneg
  positivity

private theorem cramer_window_energy (hRH : RiemannHypothesis) {r X : ℝ}
    (hr : 1 < r) (hr2 : r ≤ 2) (hX : 2 ≤ X) :
    ∫ x in X..2 * X, cramerPrimeWindowError r x ^ 2 ≤ cramerPrimeEnergyConstant * X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hi : IntervalIntegrable (fun x => cramerPrimeWindowError r x ^ 2) volume X (2 * X) :=
    cramer_intervalIntegrable_sq (cramerWindowError_measurable r) (fun x hx =>
      cramerWindowError_bound hr hr2 hX0 (by
        rw [Set.uIoc_of_le hXX] at hx
        exact ⟨hx.1.le,hx.2⟩))
  have hs : Summable (fun q : XiZeroCopy => ‖cramerWindowCoeff r q‖) :=
    summable_norm_lagWindowZeroTerm (by norm_num : (1 : ℝ) ≤ 1) hr
  have hz : ContinuousOn (fun x : ℝ =>
      ‖∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2)
      (Set.uIcc X (2 * X)) :=
    (cramer_zero_continuous (by linarith : 1 ≤ X) (cramerWindowCoeff r) hs).norm.pow 2
  have hbound := cramer_window_zero_energy hRH hr hr2 (by linarith : 1 ≤ X)
  calc
    _ ≤ ∫ x in X..2 * X,
        2 * ‖∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 +
          2 * (|Real.log (2 * Real.pi)| + 2) ^ 2 :=
      intervalIntegral.integral_mono_on hXX hi
        ((hz.const_mul 2).add continuousOn_const).intervalIntegrable
        (fun x hx => cramer_window_error_sq_le hr (hX.trans hx.1))
    _ = 2 * (∫ x in X..2 * X,
        ‖∑' q : XiZeroCopy, cramerWindowCoeff r q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2) +
          2 * (|Real.log (2 * Real.pi)| + 2) ^ 2 * X := by
      rw [intervalIntegral.integral_add (hz.const_mul 2).intervalIntegrable intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ cramerPrimeEnergyConstant * X ^ 2 := by
      unfold cramerPrimeEnergyConstant
      have hXX2 : X ≤ X ^ 2 := by nlinarith
      have hnonneg := sq_nonneg (|Real.log (2 * Real.pi)| + 2)
      nlinarith [mul_le_mul_of_nonneg_left hXX2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg)]

private theorem cramer_chebyshev_energy_large (hRH : RiemannHypothesis) {X : ℝ} (hX : 2 ≤ X) :
    ∫ x in X..2 * X, (Chebyshev.psi x - x) ^ 2 ≤ cramerPrimeEnergyConstant * X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hrange : ∀ᶠ r : ℝ in 𝓝[>] 1, r ∈ Set.Ioo 1 2 := Ioo_mem_nhdsGT (by norm_num)
  have ht : Tendsto (fun r => ∫ x in X..2 * X, cramerPrimeWindowError r x ^ 2) (𝓝[>] 1)
      (𝓝 (∫ x in X..2 * X, (Chebyshev.psi x - x) ^ 2)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => (Chebyshev.psi (4 * X) + 4 * X) ^ 2)
    · exact Eventually.of_forall (fun r =>
        ((cramerWindowError_measurable r).pow_const 2).aestronglyMeasurable)
    · filter_upwards [hrange] with r hr
      apply ae_of_all
      intro x hx
      rw [Set.uIoc_of_le hXX] at hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (cramerPrimeWindowError r x))
        (cramerWindowError_bound hr.1 hr.2.le hX0 ⟨hx.1.le,hx.2⟩) 2
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro x hx
      rw [Set.uIoc_of_le hXX] at hx
      exact (cramerWindowError_tendsto (hX0.trans hx.1)).pow 2
  exact le_of_tendsto ht (hrange.mono (fun r hr => cramer_window_energy hRH hr.1 hr.2.le hX))

/-- Cramér's sharp conditional dyadic mean-square bound for the literal Chebyshev error. -/
theorem dyadic_chebyshev_mean_square_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ∫ x in X..2 * X, (Chebyshev.psi x - x) ^ 2 ≤ C * X ^ 2 := by
  let B := Chebyshev.psi 4 + 4
  refine ⟨cramerPrimeEnergyConstant + B ^ 2, add_nonneg cramerPrimeEnergyConstant_nonneg (sq_nonneg _),
    fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  by_cases hX2 : 2 ≤ X
  · exact (cramer_chebyshev_energy_large hRH hX2).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _))
  · have hb (x : ℝ) (hx : x ∈ Set.Icc X (2 * X)) : |Chebyshev.psi x - x| ≤ B := by
      have hx0 : 0 ≤ x := (hX0.trans_le hx.1).le
      have hx4 : x ≤ 4 := by linarith [hx.2]
      have hψ := Chebyshev.psi_mono hx4
      have h := abs_sub (Chebyshev.psi x) x
      rw [abs_of_nonneg (Chebyshev.psi_nonneg x), abs_of_nonneg hx0] at h
      dsimp [B]
      linarith
    have hi : IntervalIntegrable (fun x => (Chebyshev.psi x - x) ^ 2) volume X (2 * X) :=
      cramer_intervalIntegrable_sq (Chebyshev.psi_mono.measurable.sub measurable_id) (fun x hx =>
        hb x (by rw [Set.uIoc_of_le hXX] at hx; exact ⟨hx.1.le,hx.2⟩))
    calc
      _ ≤ ∫ _ in X..2 * X, B ^ 2 := intervalIntegral.integral_mono_on hXX hi
        intervalIntegrable_const (fun x hx => by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Chebyshev.psi x - x)) (hb x hx) 2)
      _ = B ^ 2 * X := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ (cramerPrimeEnergyConstant + B ^ 2) * X ^ 2 := by
        have hXX2 : X ≤ X ^ 2 := by nlinarith
        have hB2 := sq_nonneg B
        nlinarith [mul_le_mul_of_nonneg_left hXX2 hB2,
          mul_nonneg cramerPrimeEnergyConstant_nonneg (sq_nonneg X)]

end
end RHTower
