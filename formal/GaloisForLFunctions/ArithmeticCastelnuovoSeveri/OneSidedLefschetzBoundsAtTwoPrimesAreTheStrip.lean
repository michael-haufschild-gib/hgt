import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OffLineZerosAreLefschetzRatios
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# One-sided Lefschetz bounds at two primes are the zero-free strip

Over `𝔽_q` one-sided Lefschetz bounds force purity except at a real outer eigenvalue: `Re(W β^m)`
keeps one sign only when `β > 0`. Over `ℤ` a test seeing an off-line zero `ρ` alone among the deep
zeros has Lefschetz sequence `c_m = W(T_{p^m} g, g) ~ W b^m`, `b = p^{ρ−½}`
(`OffLineZerosAreLefschetzRatios`).

* **A rotating phase rises** (`not_eventually_re_mul_pow_le`, `frequently_lt_re_mul_pow`). If
  `|ω| = 1`, `ω² ≠ 1` and `W ≠ 0`, then `Re(W ω^m) > |W|/8` for infinitely many `m`: the Cesàro
  means of `s_m = Re(W ω^m)` tend to `0` and those of `s_m² = |W|²/2 + Re(W² ω^{2m})/2` to `|W|²/2`,
  while `s_m ≤ |W|/8` forces `s_m² ≤ |W|²/4 − |W| s_m`.
* **One-sided growth** (`exists_lt_re_of_tendsto_div_pow`). Hence if `c_m/b^m → W ≠ 0` and
  `b ∉ ℝ`, `Re c_m > C R^m` for some `m`, for every `C` and `R < |b|`.
* **Two primes** (`exists_prime_frobEig_phase_sq_ne`). The phase of `p^{ρ−½}` is `e^{i Im ρ log p}`,
  real iff `Im ρ log p ∈ πℤ`; at two distinct primes this forces `Im ρ = 0`, because
  `log q/log p` is irrational, and `ζ` has no real zeros in the strip.
* **For `ζ`** (`zeta_width_le_iff_oneSided`, `zeta_riemannHypothesis_iff_oneSided_upper`,
  `zeta_riemannHypothesis_iff_oneSided_lower`). For distinct primes `p, q`, a sign `ε = ±1` and
  `θ ≥ 0`, the zero width is at most `θ` iff every test has `ε Re c_m^{(p)} = O(p^{θm})` and
  `ε Re c_m^{(q)} = O(q^{θm})`. RH holds iff every test satisfies the upper one-sided Weil
  inequalities `Re W(T_{p^m} g, g) ≤ W(g, g)` at `p` and `q`, and iff it satisfies the lower ones.

A one-sided bound, the shape positivity can deliver, is therefore as strong as a two-sided one
once two primes are used; one prime alone leaves the zeros with `Im ρ log p ∈ πℤ`.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  zetaZeroWidth abs_re_sub_half_le_zetaZeroWidth)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. A rotating phase rises -/

/-- The real part of `z` times a Cesàro mean is the mean of the real parts. -/
theorem re_mul_cesaro (z w : ℂ) (N : ℕ) :
    (z * cesaro N w).re = (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N, (z * w ^ m).re := by
  rw [cesaro, ← mul_assoc, mul_comm z, mul_assoc, Finset.mul_sum, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]

/-- **A rotating phase cannot stay low.** If `|ω| = 1`, `ω² ≠ 1` and `W ≠ 0`, then `Re(W ω^m)` is
not eventually at most `|W|/8`. -/
theorem not_eventually_re_mul_pow_le {W ω : ℂ} (hW : W ≠ 0) (hω : ‖ω‖ = 1) (hω2 : ω ^ 2 ≠ 1) :
    ¬ ∀ᶠ m : ℕ in atTop, (W * ω ^ m).re ≤ ‖W‖ / 8 := by
  intro h
  obtain ⟨M, hM⟩ := eventually_atTop.mp h
  have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hW
  -- shift by `M`
  set W' := W * ω ^ M with hW'
  have hnorm : ∀ m : ℕ, ‖W' * ω ^ m‖ = ‖W‖ := fun m => by
    rw [hW', norm_mul, norm_mul, norm_pow, norm_pow, hω, one_pow, one_pow, mul_one, mul_one]
  have hs : ∀ m : ℕ, (W' * ω ^ m).re ≤ ‖W‖ / 8 := fun m => by
    have e : W' * ω ^ m = W * ω ^ (m + M) := by rw [hW', mul_assoc, ← pow_add, add_comm M m]
    rw [e]
    exact hM _ (by omega)
  -- `s_m² ≤ 2|W|η − |W| s_m` for `s_m ≤ η = |W|/8`
  have hpt : ∀ m : ℕ, (W' * ω ^ m).re ^ 2 ≤
      2 * ‖W‖ * (‖W‖ / 8) - ‖W‖ * (W' * ω ^ m).re := fun m => by
    have habs : |(W' * ω ^ m).re| ≤ ‖W‖ := (Complex.abs_re_le_norm _).trans_eq (hnorm m)
    have hsη := hs m
    have hη0 : 0 ≤ ‖W‖ / 8 := by positivity
    rcases le_or_gt 0 (W' * ω ^ m).re with h0 | h0
    · nlinarith [mul_le_mul_of_nonneg_left hsη h0,
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans habs) hη0,
        mul_le_mul_of_nonneg_left hsη (norm_nonneg W)]
    · have h1 : -(W' * ω ^ m).re ≤ ‖W‖ := (neg_le_abs _).trans habs
      nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ -(W' * ω ^ m).re by linarith),
        mul_nonneg (norm_nonneg W) hη0]
  -- `s_m² = |W|²/2 + Re(W'² ω^{2m})/2`
  have hsq : ∀ m : ℕ, (W' * ω ^ m).re ^ 2 = ‖W‖ ^ 2 / 2 + (W' ^ 2 * (ω ^ 2) ^ m).re / 2 :=
    fun m => by
      have h1 : ∀ z : ℂ, z.re ^ 2 = (‖z‖ ^ 2 + (z ^ 2).re) / 2 := fun z => by
        rw [Complex.sq_norm, Complex.normSq_apply, pow_two z, Complex.mul_re]
        ring
      have h2 : (W' * ω ^ m) ^ 2 = W' ^ 2 * (ω ^ 2) ^ m := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2]
      rw [h1, h2, hnorm, add_div]
  -- the Cesàro means
  have hω1 : ω ≠ 1 := fun h1 => hω2 (by rw [h1, one_pow])
  have hA : Tendsto (fun N : ℕ => (W' * cesaro N ω).re) atTop (𝓝 0) := by
    have h := (tendsto_cesaro (le_of_eq hω)).const_mul W'
    rw [if_neg hω1, mul_zero] at h
    have h' := (Complex.continuous_re.tendsto _).comp h
    rwa [Complex.zero_re] at h'
  have hB : Tendsto (fun N : ℕ => (W' ^ 2 * cesaro N (ω ^ 2)).re) atTop (𝓝 0) := by
    have hn : ‖ω ^ 2‖ ≤ 1 := by rw [norm_pow, hω, one_pow]
    have h := (tendsto_cesaro hn).const_mul (W' ^ 2)
    rw [if_neg hω2, mul_zero] at h
    have h' := (Complex.continuous_re.tendsto _).comp h
    rwa [Complex.zero_re] at h'
  have havg : ∀ N : ℕ, 1 ≤ N → ‖W‖ ^ 2 / 2 + (W' ^ 2 * cesaro N (ω ^ 2)).re / 2 ≤
      2 * ‖W‖ * (‖W‖ / 8) - ‖W‖ * (W' * cesaro N ω).re := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hN' : (N : ℝ) ≠ 0 := hNpos.ne'
    rw [re_mul_cesaro, re_mul_cesaro]
    set S1 := ∑ m ∈ Finset.range N, (W' * ω ^ m).re
    set S2 := ∑ m ∈ Finset.range N, (W' ^ 2 * (ω ^ 2) ^ m).re
    have hL : ∑ m ∈ Finset.range N, (W' * ω ^ m).re ^ 2 = N * (‖W‖ ^ 2 / 2) + S2 / 2 := by
      rw [Finset.sum_congr rfl fun m _ => hsq m, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, Finset.sum_div]
    have hR : ∑ m ∈ Finset.range N, (2 * ‖W‖ * (‖W‖ / 8) - ‖W‖ * (W' * ω ^ m).re) =
        N * (2 * ‖W‖ * (‖W‖ / 8)) - ‖W‖ * S1 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.mul_sum]
    have hsum := Finset.sum_le_sum fun m (_ : m ∈ Finset.range N) => hpt m
    rw [hL, hR] at hsum
    have key := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
    have e1 : (N : ℝ)⁻¹ * (N * (‖W‖ ^ 2 / 2) + S2 / 2) = ‖W‖ ^ 2 / 2 + (N : ℝ)⁻¹ * S2 / 2 := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hN', one_mul]
      ring
    have e2 : (N : ℝ)⁻¹ * (N * (2 * ‖W‖ * (‖W‖ / 8)) - ‖W‖ * S1) =
        2 * ‖W‖ * (‖W‖ / 8) - ‖W‖ * ((N : ℝ)⁻¹ * S1) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hN', one_mul]
      ring
    rw [e1, e2] at key
    exact key
  have hlim := le_of_tendsto_of_tendsto (tendsto_const_nhds.add (hB.div_const 2))
    (tendsto_const_nhds.sub (hA.const_mul ‖W‖)) (eventually_atTop.mpr ⟨1, havg⟩)
  simp only [zero_div, add_zero, mul_zero, sub_zero] at hlim
  nlinarith

/-- **A rotating phase rises.** If `u_m → W ≠ 0`, `|ω| = 1` and `ω² ≠ 1`, then
`Re(u_m ω^m) > |W|/16` for infinitely many `m`. -/
theorem frequently_lt_re_mul_pow {u : ℕ → ℂ} {W ω : ℂ} (hu : Tendsto u atTop (𝓝 W))
    (hW : W ≠ 0) (hω : ‖ω‖ = 1) (hω2 : ω ^ 2 ≠ 1) :
    ∃ᶠ m in atTop, ‖W‖ / 16 < (u m * ω ^ m).re := by
  intro hnot
  apply not_eventually_re_mul_pow_le hW hω hω2
  have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hW
  have hclose : ∀ᶠ m in atTop, ‖u m - W‖ < ‖W‖ / 16 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hu).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hnot, hclose] with m h1 h2
  push Not at h1
  have h3 := Complex.re_le_norm ((W - u m) * ω ^ m)
  rw [norm_mul, norm_pow, hω, one_pow, mul_one, norm_sub_rev, sub_mul, Complex.sub_re] at h3
  linarith

/-- **One-sided growth.** If `c_m/b^m → W ≠ 0` and `b` is not real (`(b/|b|)² ≠ 1`), then for every
`C` and `0 ≤ R < |b|` some `m` has `Re c_m > C R^m`. -/
theorem exists_lt_re_of_tendsto_div_pow {c : ℕ → ℂ} {b W : ℂ} (hb0 : b ≠ 0)
    (hc : Tendsto (fun m => c m / b ^ m) atTop (𝓝 W)) (hW : W ≠ 0)
    (hb2 : (b / (‖b‖ : ℂ)) ^ 2 ≠ 1) {R : ℝ} (hR : 0 ≤ R) (hRb : R < ‖b‖) (C : ℝ) :
    ∃ m : ℕ, C * R ^ m < (c m).re := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hbc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hbn.ne'
  have hω : ‖b / (‖b‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hbn.le, div_self hbn.ne']
  have hfreq := frequently_lt_re_mul_pow hc hW hω hb2
  have hWpos : 0 < ‖W‖ / 16 := by have := norm_pos_iff.mpr hW; positivity
  have ht : Tendsto (fun m : ℕ => C * (R / ‖b‖) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hbn.le)
      ((div_lt_one hbn).mpr hRb)).const_mul C
  have hev : ∀ᶠ m : ℕ in atTop, C * R ^ m < ‖b‖ ^ m * (‖W‖ / 16) :=
    (ht.eventually (gt_mem_nhds hWpos)).mono fun m hm => by
      rw [div_pow, mul_div_assoc', div_lt_iff₀ (pow_pos hbn m)] at hm
      linarith
  obtain ⟨m, h1, h2⟩ := (hfreq.and_eventually hev).exists
  refine ⟨m, h2.trans ?_⟩
  have e : c m / b ^ m * (b / (‖b‖ : ℂ)) ^ m = ((‖b‖ ^ m)⁻¹ : ℝ) * c m := by
    rw [div_pow]
    push_cast
    field_simp
  rw [e, Complex.re_ofReal_mul] at h1
  have hbm : 0 < ‖b‖ ^ m := pow_pos hbn m
  calc ‖b‖ ^ m * (‖W‖ / 16) < ‖b‖ ^ m * ((‖b‖ ^ m)⁻¹ * (c m).re) :=
        mul_lt_mul_of_pos_left h1 hbm
    _ = (c m).re := by rw [← mul_assoc, mul_inv_cancel₀ hbm.ne', one_mul]

/-! ### 2. Two primes -/

/-- The phase of `e^{ℓ(ρ − ½)}` is `e^{iℓ Im ρ}`. -/
theorem frobEig_div_norm (ℓ : ℝ) (ρ : ℂ) :
    frobEig ℓ ρ / (‖frobEig ℓ ρ‖ : ℂ) = cexp ((ℓ * ρ.im : ℝ) * I) := by
  have e : (ℓ : ℂ) * (ρ - 1 / 2) = ((ℓ * (ρ.re - 1 / 2) : ℝ) : ℂ) + ((ℓ * ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [norm_frobEig, frobEig, e, Complex.exp_add, ← Complex.ofReal_exp,
    mul_div_cancel_left₀ _ (by exact_mod_cast (Real.exp_pos _).ne')]

/-- `(e^{ix})² = 1` only for `x ∈ πℤ`. -/
theorem exists_int_of_cexp_sq_eq_one {x : ℝ} (h : cexp ((x : ℂ) * I) ^ 2 = 1) :
    ∃ n : ℤ, x = n * Real.pi := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp [Complex.mul_im] at this
  linarith

/-- **Two primes do not both fold a non-real point onto the real axis.** If `Im ρ ≠ 0` and
`p ≠ q`, then `p^{ρ−½}` or `q^{ρ−½}` is not real. -/
theorem exists_prime_frobEig_phase_sq_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ρ : ℂ} (him : ρ.im ≠ 0) :
    (frobEig (Real.log p) ρ / (‖frobEig (Real.log p) ρ‖ : ℂ)) ^ 2 ≠ 1 ∨
      (frobEig (Real.log q) ρ / (‖frobEig (Real.log q) ρ‖ : ℂ)) ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨hp1, hq1⟩ := h
  rw [frobEig_div_norm] at hp1 hq1
  obtain ⟨a, ha⟩ := exists_int_of_cexp_sq_eq_one hp1
  obtain ⟨b, hb⟩ := exists_int_of_cexp_sq_eq_one hq1
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have ha0 : (a : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact hlp.ne' h
    · exact him h
  apply RHTower.irrational_log_ratio hp hq hpq
  refine ⟨(b : ℚ) / a, ?_⟩
  push_cast
  rw [div_eq_div_iff ha0 hlp.ne']
  apply mul_right_cancel₀ him
  linear_combination (b : ℝ) * ha - (a : ℝ) * hb

/-! ### 3. `ζ` -/

/-- A zero beyond depth `θ ≥ 0` gives a right zero beyond depth `θ`. -/
theorem exists_rightZero_of_lt_zetaZeroWidth {θ : ℝ} (hθ : 0 ≤ θ) (h : θ < zetaZeroWidth) :
    ∃ ρ ∈ rightZeros zetaZeroConfig, θ < ρ.re - 1 / 2 := by
  have hne : ((fun ρ : ℂ => |ρ.re - 1 / 2|) '' zetaZeroConfig.carrier).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    have h0 : zetaZeroWidth = 0 := by
      rw [show zetaZeroWidth = sSup ((fun ρ : ℂ => |ρ.re - 1 / 2|) '' zetaZeroConfig.carrier)
        from rfl, he, Real.sSup_empty]
    linarith
  obtain ⟨_, ⟨ρ, hρ, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne h
  replace hlt : θ < |ρ.re - 1 / 2| := hlt
  rcases lt_or_ge (1 / 2) ρ.re with hr | hr
  · exact ⟨ρ, ⟨hρ, hr⟩, by rwa [abs_of_pos (by linarith)] at hlt⟩
  · rw [abs_of_nonpos (by linarith)] at hlt
    exact ⟨reflect ρ, ⟨zetaZeroConfig.reflect_mem ρ hρ, by rw [re_reflect]; linarith⟩,
      by rw [re_reflect]; linarith⟩

/-- **One-sided Lefschetz bounds at two primes are the zero-free strip.** For distinct primes
`p, q`, a sign `ε = ±1` and `θ ≥ 0`, the zero width of `ζ` is at most `θ` iff every test satisfies
the one-sided bounds `ε Re W(T_{p^m} g, g) = O(p^{θm})` and `ε Re W(T_{q^m} g, g) = O(q^{θm})`. -/
theorem zeta_width_le_iff_oneSided {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {θ : ℝ} (hθ : 0 ≤ θ) :
    zetaZeroWidth ≤ θ ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∃ C, ∀ m : ℕ, ε * (towerMoment zetaZeroConfig g (Real.log p) m).re ≤
        C * ((p : ℝ) ^ θ) ^ m) ∧
      (∃ C, ∀ m : ℕ, ε * (towerMoment zetaZeroConfig g (Real.log q) m).re ≤
        C * ((q : ℝ) ^ θ) ^ m) := by
  have hεabs : ∀ x : ℝ, ε * x ≤ ‖(x : ℂ)‖ := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases hε with rfl | rfl
    · rw [one_mul]; exact le_abs_self x
    · rw [neg_one_mul]; exact neg_le_abs x
  constructor
  · intro hw g hg hgc
    have bound : ∀ r : ℕ, r.Prime → ∃ C, ∀ m : ℕ,
        ε * (towerMoment zetaZeroConfig g (Real.log r) m).re ≤ C * ((r : ℝ) ^ θ) ^ m := by
      intro r hr
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.one_lt.le
      have hR : 1 ≤ (r : ℝ) ^ θ := Real.one_le_rpow hr1 hθ
      have hdom := (zeta_forall_norm_frobEig_le_iff hr hR).mpr
        (Real.rpow_le_rpow_of_exponent_le hr1 hw)
      obtain ⟨C, hC⟩ := exists_norm_towerMoment_le _ temperedConfig_zetaZeroConfig hg hgc
        (Real.log_pos (by exact_mod_cast hr.one_lt)) hR hdom
      refine ⟨C, fun m => (hεabs _).trans ((?_ : ‖((towerMoment zetaZeroConfig g
        (Real.log r) m).re : ℂ)‖ ≤ _).trans (hC m))⟩
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    exact ⟨bound p hp, bound q hq⟩
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨ρ, hρ, hdeep⟩ := exists_rightZero_of_lt_zetaZeroWidth hθ hlt
    obtain ⟨g, hg, hgc, hlaw⟩ := deepSparse_exists_test_lefschetz_ratio _
      temperedConfig_zetaZeroConfig deepSparse_zeta hρ
    obtain ⟨hCp, hCq⟩ := h g hg hgc
    have hε0 : (ε : ℂ) ≠ 0 := by
      rcases hε with rfl | rfl <;> norm_num
    have key : ∀ r : ℕ, r.Prime →
        (frobEig (Real.log r) ρ / (‖frobEig (Real.log r) ρ‖ : ℂ)) ^ 2 ≠ 1 →
        (∃ C, ∀ m : ℕ, ε * (towerMoment zetaZeroConfig g (Real.log r) m).re ≤
          C * ((r : ℝ) ^ θ) ^ m) → False := by
      rintro r hr hphase ⟨C, hC⟩
      have hℓ : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
      obtain ⟨hW, hu, -, -⟩ := hlaw _ hℓ
      have hu' : Tendsto (fun m : ℕ => (ε : ℂ) * towerMoment zetaZeroConfig g (Real.log r) m /
          frobEig (Real.log r) ρ ^ m) atTop
          (𝓝 ((ε : ℂ) * frobWeight zetaZeroConfig g (Real.log r) (frobEig (Real.log r) ρ))) := by
        simpa only [mul_div_assoc] using hu.const_mul (ε : ℂ)
      have hRb : (r : ℝ) ^ θ < ‖frobEig (Real.log r) ρ‖ := by
        rw [norm_frobEig, Real.rpow_def_of_pos (by exact_mod_cast hr.pos), Real.exp_lt_exp]
        exact mul_lt_mul_of_pos_left hdeep hℓ
      obtain ⟨m, hm⟩ := exists_lt_re_of_tendsto_div_pow (frobEig_ne_zero _ _) hu'
        (mul_ne_zero hε0 hW) hphase (Real.rpow_nonneg (Nat.cast_nonneg _) θ) hRb C
      rw [Complex.re_ofReal_mul] at hm
      exact absurd (hC m) (not_le.mpr hm)
    rcases exists_prime_frobEig_phase_sq_ne hp hq hpq (zetaZeroConfig_im_ne_zero' ρ hρ.1) with
      h1 | h1
    · exact key p hp h1 hCp
    · exact key q hq h1 hCq

/-- RH from the one-sided bounds with constant `W(g, g)`. -/
theorem zeta_riemannHypothesis_of_oneSided {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ m : ℕ,
      ε * (towerMoment zetaZeroConfig g (Real.log p) m).re ≤
          (towerMoment zetaZeroConfig g (Real.log p) 0).re ∧
        ε * (towerMoment zetaZeroConfig g (Real.log q) m).re ≤
          (towerMoment zetaZeroConfig g (Real.log q) 0).re) :
    RiemannHypothesis := by
  have hw : zetaZeroWidth ≤ 0 := (zeta_width_le_iff_oneSided hp hq hpq hε le_rfl).mpr
    fun g hg hgc =>
      ⟨⟨(towerMoment zetaZeroConfig g (Real.log p) 0).re, fun m => by
        rw [Real.rpow_zero, one_pow, mul_one]; exact (h g hg hgc m).1⟩,
       ⟨(towerMoment zetaZeroConfig g (Real.log q) 0).re, fun m => by
        rw [Real.rpow_zero, one_pow, mul_one]; exact (h g hg hgc m).2⟩⟩
  rw [← rightZeros_zeta_eq_empty_iff]
  refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => ?_
  have := (le_abs_self _).trans (abs_re_sub_half_le_zetaZeroWidth hρ.1)
  linarith [hρ.2]

/-- Under RH every test satisfies both one-sided Weil inequalities at every prime. -/
theorem abs_re_towerMoment_le_of_riemannHypothesis (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (m : ℕ) :
    |(towerMoment zetaZeroConfig g ℓ m).re| ≤ (towerMoment zetaZeroConfig g ℓ 0).re :=
  (Complex.abs_re_le_norm _).trans (norm_towerMoment_le_of_rightZeros_eq_empty _
    temperedConfig_zetaZeroConfig hg hgc ℓ (rightZeros_zeta_eq_empty_iff.mpr hRH) m)

/-- **The upper one-sided Weil inequalities at two primes decide RH.** For distinct primes `p, q`:
RH holds iff every test satisfies `Re W(T_{p^m} g, g) ≤ W(g, g)` and `Re W(T_{q^m} g, g) ≤ W(g, g)`
for all `m`. -/
theorem zeta_riemannHypothesis_iff_oneSided_upper {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ m : ℕ,
      (towerMoment zetaZeroConfig g (Real.log p) m).re ≤
          (towerMoment zetaZeroConfig g (Real.log p) 0).re ∧
        (towerMoment zetaZeroConfig g (Real.log q) m).re ≤
          (towerMoment zetaZeroConfig g (Real.log q) 0).re := by
  refine ⟨fun hRH g hg hgc m => ⟨(le_abs_self _).trans
      (abs_re_towerMoment_le_of_riemannHypothesis hRH hg hgc _ m), (le_abs_self _).trans
      (abs_re_towerMoment_le_of_riemannHypothesis hRH hg hgc _ m)⟩, fun h => ?_⟩
  exact zeta_riemannHypothesis_of_oneSided hp hq hpq (Or.inl rfl) fun g hg hgc m => by
    simpa only [one_mul] using h g hg hgc m

/-- **The lower one-sided Weil inequalities at two primes decide RH.** For distinct primes `p, q`:
RH holds iff every test satisfies `−Re W(T_{p^m} g, g) ≤ W(g, g)` and
`−Re W(T_{q^m} g, g) ≤ W(g, g)` for all `m`. -/
theorem zeta_riemannHypothesis_iff_oneSided_lower {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ m : ℕ,
      -(towerMoment zetaZeroConfig g (Real.log p) m).re ≤
          (towerMoment zetaZeroConfig g (Real.log p) 0).re ∧
        -(towerMoment zetaZeroConfig g (Real.log q) m).re ≤
          (towerMoment zetaZeroConfig g (Real.log q) 0).re := by
  refine ⟨fun hRH g hg hgc m => ⟨(neg_le_abs _).trans
      (abs_re_towerMoment_le_of_riemannHypothesis hRH hg hgc _ m), (neg_le_abs _).trans
      (abs_re_towerMoment_le_of_riemannHypothesis hRH hg hgc _ m)⟩, fun h => ?_⟩
  exact zeta_riemannHypothesis_of_oneSided hp hq hpq (Or.inr rfl) fun g hg hgc m => by
    simpa only [neg_one_mul] using h g hg hgc m

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
