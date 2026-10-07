import GaloisForLFunctions.RHTower.ZetaTwistedFirstMomentUniform

/-!
# Sign rigidity of absolutely convergent critical Dirichlet series against `ζ`

Let `F(s) = Σ_{n ≥ 2} f(n) n^{-s}` with the log moment `Σ |f(n)| n^{-1/2} (1 + log n) < ∞`
(`LogMomentSummable`; implied by `Σ |f(n)| n^{-1/2+δ} < ∞` for some `δ > 0`). If
`Re(F(1/2+iy) · conj ζ(1/2+iy)) ≤ 0` for all `y ≥ 8`, then `f(n) = 0` for every `n ≥ 1`
(`eq_zero_of_re_mul_conj_zeta_nonpos`). This extends the Dirichlet-polynomial case
(`critDirPoly_eq_zero_of_re_mul_conj_zeta_nonpos`) to infinite series.

The proof follows the polynomial case. By strong induction on `a`, take the Cesàro mean of
`F · conj ζ` against the nonnegative weight `|M_D(y)(1 + c a^{-iy})|²`, with `M_D` the Möbius polynomial
of `D = K!` and `c = f(a)`. Two new inputs handle the infinite series.

* **General Möbius collapse** (`zetaMobiusLimit_log_sub_eq`). For all `u, w ≥ 1`, the limit weight of
  the frequency `log u − log w` is `(u/w)^{-1/2}` if `w ∣ u` and `u/w` is coprime to `D`, and `0`
  otherwise. Frequencies with a prime factor above `K` therefore survive, but only through `n > K`.
  This gives `|L_K − f(a)² a^{-1/2}| ≤ (1 + c² + |c|√a) Σ_{n > K} |f(n)|/n`
  (`norm_tsum_weightLimit_sub_le`); the third-term divisor is unique by `eq_of_coprime_div`.
* **Exchange of limit and sum.** For all `n, T`, the Cesàro means are dominated by
  `C |f(n)| n^{-1/2} √(1 + log(nQ))`, which comes from the uniform twisted first moment
  `exists_norm_integral_zeta_twist_le`. This majorant is summable under the log moment.

Letting `K → ∞` gives `f(a)² a^{-1/2} ≤ 0`. The case `F(1) < 0` needs no separate argument: the
weight `M_D` removes the diagonal, so `F(1)` never enters the limit.
-/

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Interval

noncomputable section

namespace RHTower.ZetaUniformMoment

open RHTower

/-! ## The Möbius collapse for arbitrary integers -/

/-- **Möbius collapse.** For `D ≠ 0` and `u, w ≥ 1`, the Cesàro limit of `ζ · M_D` at the frequency
`log u − log w` is `(u/w)^{-1/2}` if `w ∣ u` and `u/w` is coprime to `D`, and `0` otherwise. -/
theorem zetaMobiusLimit_log_sub_eq {D u w : ℕ} (hD : D ≠ 0) (hu : 1 ≤ u) (hw : 1 ≤ w) :
    zetaMobiusLimit D (Real.log u - Real.log w) =
      if w ∣ u ∧ Nat.Coprime D (u / w) then ((((u / w : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      else 0 := by
  unfold zetaMobiusLimit
  have hterm : ∀ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
      ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        zetaFreqWeight (Real.log u - Real.log w - Real.log d)) =
      if w * d ∣ u then ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
        ((((u / w : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0 := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hwd : 1 ≤ w * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlog : Real.log u - Real.log w - Real.log d = Real.log u - Real.log (w * d : ℕ) := by
      push_cast
      rw [Real.log_mul (by exact_mod_cast (by omega : w ≠ 0))
        (by exact_mod_cast (by omega : d ≠ 0))]
      ring
    rw [hlog, zetaFreqWeight_log_sub hu hwd]
    split_ifs with hdiv
    · obtain ⟨m, hm⟩ := hdiv
      have hq : u / w = d * m := by
        rw [hm, mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
      have hq2 : u / (w * d) = m := by rw [hm, Nat.mul_div_cancel_left _ (by positivity)]
      rw [hq, hq2]
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hmpos : (0 : ℝ) < m := by
        have : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at hm; omega
          · exact h
        exact_mod_cast this
      push_cast
      rw [Real.mul_rpow hdpos.le hmpos.le]
      push_cast
      ring
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  by_cases hwu : w ∣ u
  · obtain ⟨q, hq⟩ := hwu
    have hfilter : D.divisors.filter (fun d => w * d ∣ u) = (Nat.gcd D q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, hq]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨Nat.dvd_gcd h1 (Nat.dvd_of_mul_dvd_mul_left (by omega) h2),
          Nat.gcd_ne_zero_left hD⟩
      · rintro ⟨h1, _⟩
        exact ⟨⟨(Nat.dvd_gcd_iff.mp h1).1, hD⟩, Nat.mul_dvd_mul_left w (Nat.dvd_gcd_iff.mp h1).2⟩
    rw [hfilter, hq, Nat.mul_div_cancel_left _ (by omega), ← Finset.sum_mul]
    have hmob : ∑ d ∈ (Nat.gcd D q).divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) =
        if Nat.gcd D q = 1 then 1 else 0 := by
      have h := congrArg (fun f : ArithmeticFunction ℤ => f (Nat.gcd D q))
        ArithmeticFunction.moebius_mul_coe_zeta
      simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
      have h2 : ((∑ i ∈ (Nat.gcd D q).divisors, (ArithmeticFunction.moebius i : ℤ) : ℤ) : ℂ) =
          (((if Nat.gcd D q = 1 then 1 else 0 : ℤ)) : ℂ) := by rw [h]
      push_cast at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun d _ => ?_
      push_cast
      rfl
    rw [hmob]
    by_cases hg : Nat.gcd D q = 1
    · rw [if_pos hg, if_pos ⟨Dvd.intro q rfl, hg⟩, one_mul]
    · rw [if_neg hg, zero_mul, if_neg (fun h => hg h.2)]
  · rw [if_neg (fun h => hwu h.1)]
    apply Finset.sum_eq_zero
    intro d hd
    exact absurd (Dvd.dvd.trans (Dvd.intro d rfl) (Finset.mem_filter.mp hd).2) hwu

/-! ## The critical-line series -/

theorem critDirPoly_singleton (f : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    critDirPoly {n} f y = (f n : ℂ) *
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-((Real.log n : ℝ) : ℂ) * y * I)) := by
  simp [critDirPoly]

theorem LSeries_term_line (f : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    LSeries.term (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) n = critDirPoly {n} f y := by
  rw [critDirPoly_singleton]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn.ne']
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hpow : (n : ℂ) ^ ((1 / 2 : ℂ) + y * I) =
        (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * cexp ((Real.log n : ℂ) * y * I) := by
      rw [Complex.cpow_add _ _ hn0, Complex.cpow_def_of_ne_zero hn0 (y * I)]
      congr 1
      · rw [Complex.ofReal_cpow hnr]; push_cast; ring_nf
      · congr 1
        rw [show (Complex.log (n : ℂ)) = (Real.log n : ℂ) by
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnr] ]
        ring
    have hA : (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hnpos _).ne'
    rw [hpow, Real.rpow_neg hnr, Complex.ofReal_inv,
      show -((Real.log n : ℝ) : ℂ) * y * I = -((Real.log n : ℂ) * y * I) by ring, Complex.exp_neg]
    field_simp

theorem LSeries_line_eq_tsum (f : ℕ → ℝ) (y : ℝ) :
    LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) = ∑' n, critDirPoly {n} f y := by
  unfold LSeries
  congr 1
  funext n
  exact LSeries_term_line f n y

theorem norm_critDirPoly_singleton (f : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    ‖critDirPoly {n} f y‖ = |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [critDirPoly_singleton, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    show -((Real.log n : ℝ) : ℂ) * y * I = ((-(Real.log n) * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-! ## Summability -/

/-- The log moment `Σ |f(n)| n^{-1/2} (1 + log n) < ∞`. -/
def LogMomentSummable (f : ℕ → ℝ) : Prop :=
  Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log n)

theorem one_le_one_add_log_nat (n : ℕ) : 1 ≤ 1 + Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.log_nonneg this]

theorem sqrt_one_add_log_le {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (1 + Real.log (n * Q)) ≤ (1 + Real.log Q) * (1 + Real.log n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  rw [Real.log_mul (by positivity) (by positivity)]
  have hx : 1 ≤ 1 + (Real.log n + Real.log Q) := by linarith
  have hsq : Real.sqrt (1 + (Real.log n + Real.log Q)) ≤ 1 + (Real.log n + Real.log Q) := by
    have h0 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (Real.log n + Real.log Q) by linarith)
    nlinarith [Real.sqrt_nonneg (1 + (Real.log n + Real.log Q)), Real.one_le_sqrt.mpr hx]
  nlinarith [mul_nonneg hlogn hlogQ]

/-- The majorant `|f(n)| n^{-1/2} √(1 + log(nQ))` is summable under the log moment. -/
theorem summable_majorant {f : ℕ → ℝ} {Q : ℝ} (hQ : 1 ≤ Q) (hlog : LogMomentSummable f) :
    Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 + Real.log (n * Q)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hlog.mul_left (1 + Real.log Q))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 + Real.log (n * Q))
        ≤ |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((1 + Real.log Q) * (1 + Real.log n)) := by
          gcongr; exact sqrt_one_add_log_le hQ hn
      _ = (1 + Real.log Q) * (|f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log n)) := by ring

theorem summable_abs_mul_rpow {f : ℕ → ℝ} (hlog : LogMomentSummable f) :
    Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => le_mul_of_one_le_right (by positivity) (one_le_one_add_log_nat n)) hlog

theorem summable_abs_div {f : ℕ → ℝ} (hlog : LogMomentSummable f) :
    Summable fun n : ℕ => |f n| / n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_abs_mul_rpow hlog)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have h : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hnpos.le, one_div]
      exact inv_anti₀ (Real.rpow_pos_of_pos hnpos _)
        (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (show (1 / 2 : ℝ) ≤ 1 by norm_num))
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- Absolute convergence past `½` implies the log moment. -/
theorem logMomentSummable_of_lSeriesSummable {f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) : LogMomentSummable f := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity)
    (le_trans zero_le_one (one_le_one_add_log_nat n))) (fun n => ?_) (hf.norm.mul_left (1 + 1 / δ))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.ofReal_re]
    have hlog : Real.log n ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div hnpos.le hδ
    have hnδ : (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow hn1 hδ.le
    have h1 : 1 + Real.log n ≤ (1 + 1 / δ) * (n : ℝ) ^ δ := by
      rw [add_mul, one_mul, one_div, inv_mul_eq_div]; linarith
    have hsplit : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ δ = 1 / (n : ℝ) ^ (1 / 2 - δ) := by
      rw [← Real.rpow_add hnpos, eq_div_iff (Real.rpow_pos_of_pos hnpos _).ne', ← Real.rpow_add hnpos,
        show -(1 / 2 : ℝ) + δ + (1 / 2 - δ) = 0 by ring, Real.rpow_zero]
    calc |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + Real.log n)
        ≤ |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((1 + 1 / δ) * (n : ℝ) ^ δ) := by gcongr
      _ = (1 + 1 / δ) * (|f n| * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ δ)) := by ring
      _ = (1 + 1 / δ) * (|f n| / (n : ℝ) ^ (1 / 2 - δ)) := by rw [hsplit]; ring

/-! ## The weighted integrand -/

/-- `f(n) n^{-1/2} μ(d) d^{-1/2}`. -/
def coeffβ (f : ℕ → ℝ) (n d : ℕ) : ℝ :=
  f n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ))

/-- The `n`-th term of `ζ M_D conj(F M_D) |1 + c e^{-i La y}|²`. -/
def weightTerm (f : ℕ → ℝ) (D : ℕ) (c La : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  ∑ d ∈ D.divisors, (coeffβ f n d : ℂ) *
    ((1 + (c : ℂ) ^ 2) * zetaMobiusTerm D (Real.log n + Real.log d) y +
      (c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d + La) y +
      (c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d - La) y)

/-- The Cesàro limit of `weightTerm`. -/
def weightLimit (f : ℕ → ℝ) (D : ℕ) (c La : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ D.divisors, (coeffβ f n d : ℂ) *
    ((1 + (c : ℂ) ^ 2) * zetaMobiusLimit D (Real.log n + Real.log d) +
      (c : ℂ) * zetaMobiusLimit D (Real.log n + Real.log d + La) +
      (c : ℂ) * zetaMobiusLimit D (Real.log n + Real.log d - La))

theorem coeffβ_zero_left (f : ℕ → ℝ) (d : ℕ) : coeffβ f 0 d = 0 := by
  simp [coeffβ]

theorem abs_coeffβ_le (f : ℕ → ℝ) (n d : ℕ) :
    |coeffβ f n d| ≤ |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold coeffβ
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  have h0 : 0 ≤ |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have h1 : 0 ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  calc |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * |(ArithmeticFunction.moebius d : ℝ)| *
        (d : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * 1 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring

theorem weightTerm_zero_left (f : ℕ → ℝ) (D : ℕ) (c La y : ℝ) : weightTerm f D c La 0 y = 0 := by
  simp [weightTerm, coeffβ_zero_left]

theorem weightLimit_zero_left (f : ℕ → ℝ) (D : ℕ) (c La : ℝ) : weightLimit f D c La 0 = 0 := by
  simp [weightLimit, coeffβ_zero_left]

/-- **The pointwise identity** for one term. -/
theorem weightTerm_eq (f : ℕ → ℝ) (D : ℕ) (c La : ℝ) (n : ℕ) (y : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + y * I) * mobiusPoly D y *
        starRingEnd ℂ (critDirPoly {n} f y * mobiusPoly D y) *
        ((1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I)) *
          starRingEnd ℂ (1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I))) =
      weightTerm f D c La n y := by
  rw [conj_critDirPoly_mul_mobiusPoly, conj_one_add_mul_cexp, Finset.sum_singleton]
  unfold weightTerm coeffβ
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [zetaMobiusTerm]
  rw [show (((Real.log n + Real.log d + La : ℝ)) : ℂ) * y * I =
      ((Real.log n + Real.log d : ℝ) : ℂ) * y * I + (La : ℂ) * y * I by push_cast; ring,
    show (((Real.log n + Real.log d - La : ℝ)) : ℂ) * y * I =
      ((Real.log n + Real.log d : ℝ) : ℂ) * y * I + (-((La : ℝ) : ℂ) * y * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_add]
  push_cast
  ring

/-- **The pointwise identity**: the weighted integrand is the sum of the terms. -/
theorem integrand_eq_tsum (f : ℕ → ℝ) (D : ℕ) (c La y : ℝ) :
    starRingEnd ℂ (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
        starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))) *
      ((‖mobiusPoly D y * (1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I))‖ ^ 2 : ℝ) : ℂ) =
      ∑' n, weightTerm f D c La n y := by
  set Z := riemannZeta ((1 / 2 : ℂ) + y * I)
  set M := mobiusPoly D y
  set R := (1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I))
  set F := LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I)
  have hnorm : ((‖M * R‖ ^ 2 : ℝ) : ℂ) = (M * R) * starRingEnd ℂ (M * R) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnorm]
  have hre : starRingEnd ℂ (F * starRingEnd ℂ Z) * ((M * R) * starRingEnd ℂ (M * R)) =
      Z * M * starRingEnd ℂ (F * M) * (R * starRingEnd ℂ R) := by
    simp only [map_mul, Complex.conj_conj]; ring
  rw [hre]
  have hF : F * M = ∑' n, critDirPoly {n} f y * M := by
    rw [show F = ∑' n, critDirPoly {n} f y from LSeries_line_eq_tsum f y, tsum_mul_right]
  rw [hF, Complex.conj_tsum, ← tsum_mul_left, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [← weightTerm_eq f D c La n y]

/-! ## Bounds -/

/-- `Σ_{d ∣ D} d^{-1/2}`. -/
def divSum (D : ℕ) : ℝ := ∑ d ∈ D.divisors, (d : ℝ) ^ (-(1 / 2 : ℝ))

theorem divSum_nonneg (D : ℕ) : 0 ≤ divSum D :=
  Finset.sum_nonneg fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _

theorem norm_mobiusPoly_le (D : ℕ) (y : ℝ) : ‖mobiusPoly D y‖ ≤ divSum D := by
  unfold mobiusPoly divSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
    show -((Real.log d : ℝ) : ℂ) * y * I = ((-(Real.log d) * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  have h1 : 0 ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  nlinarith

theorem norm_zetaMobiusTerm_le (D : ℕ) (κ y : ℝ) :
    ‖zetaMobiusTerm D κ y‖ ≤ divSum D * ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖ := by
  rw [zetaMobiusTerm, norm_mul, norm_mul,
    show ((κ : ℂ) * y * I) = ((κ * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_mobiusPoly_le D y) (norm_nonneg _)

/-- `‖weightTerm n y‖ ≤ |f(n)| n^{-1/2} K |ζ(1/2+iy)|`. -/
theorem norm_weightTerm_le (f : ℕ → ℝ) (D : ℕ) (c La : ℝ) (n : ℕ) (y : ℝ) :
    ‖weightTerm f D c La n y‖ ≤ |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      (divSum D ^ 2 * (1 + c ^ 2 + 2 * |c|) * ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖) := by
  set z := ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖
  have hz : 0 ≤ z := norm_nonneg _
  have hS := divSum_nonneg D
  have hterm : ∀ κ : ℝ, ‖zetaMobiusTerm D κ y‖ ≤ divSum D * z := fun κ => norm_zetaMobiusTerm_le D κ y
  have hinner : ∀ d : ℕ, ‖(1 + (c : ℂ) ^ 2) * zetaMobiusTerm D (Real.log n + Real.log d) y +
      (c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d + La) y +
      (c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d - La) y‖ ≤
      (1 + c ^ 2 + 2 * |c|) * (divSum D * z) := by
    intro d
    have hc2 : ‖(1 + (c : ℂ) ^ 2)‖ = 1 + c ^ 2 := by
      rw [show (1 + (c : ℂ) ^ 2) = ((1 + c ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hc : ‖(c : ℂ)‖ = |c| := by rw [Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ ‖(1 + (c : ℂ) ^ 2) * zetaMobiusTerm D (Real.log n + Real.log d) y‖ +
          ‖(c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d + La) y‖ +
          ‖(c : ℂ) * zetaMobiusTerm D (Real.log n + Real.log d - La) y‖ := norm_add₃_le
      _ ≤ (1 + c ^ 2) * (divSum D * z) + |c| * (divSum D * z) + |c| * (divSum D * z) := by
          rw [norm_mul, norm_mul, norm_mul, hc2, hc]
          gcongr <;> exact hterm _
      _ = (1 + c ^ 2 + 2 * |c|) * (divSum D * z) := by ring
  unfold weightTerm
  calc ‖∑ d ∈ D.divisors, (coeffβ f n d : ℂ) * _‖
      ≤ ∑ d ∈ D.divisors, |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((1 + c ^ 2 + 2 * |c|) * (divSum D * z)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (abs_coeffβ_le f n d) (hinner d) (norm_nonneg _) (by positivity)
    _ = |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (divSum D ^ 2 * (1 + c ^ 2 + 2 * |c|) * z) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        unfold divSum
        ring

theorem continuous_weightTerm (f : ℕ → ℝ) (D : ℕ) (c La : ℝ) (n : ℕ) :
    Continuous (weightTerm f D c La n) := by
  unfold weightTerm
  exact continuous_finsetSum _ fun d _ => continuous_const.mul
    (((continuous_const.mul (continuous_zetaMobiusTerm D _)).add
      (continuous_const.mul (continuous_zetaMobiusTerm D _))).add
      (continuous_const.mul (continuous_zetaMobiusTerm D _)))

/-- The integral of the weighted integrand is the sum of the termwise integrals. -/
theorem hasSum_integral_weightTerm {f : ℕ → ℝ} (hs : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)))
    (D : ℕ) (c La T : ℝ) :
    HasSum (fun n => ∫ y in (8 : ℝ)..T, weightTerm f D c La n y)
      (∫ y in (8 : ℝ)..T, starRingEnd ℂ (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
        starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))) *
        ((‖mobiusPoly D y * (1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I))‖ ^ 2 : ℝ) : ℂ)) := by
  set K := divSum D ^ 2 * (1 + c ^ 2 + 2 * |c|)
  have hfun : (fun y : ℝ => starRingEnd ℂ (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
        starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))) *
        ((‖mobiusPoly D y * (1 + (c : ℂ) * cexp (-((La : ℝ) : ℂ) * y * I))‖ ^ 2 : ℝ) : ℂ)) =
      fun y => ∑' n, weightTerm f D c La n y := funext fun y => integrand_eq_tsum f D c La y
  rw [hfun]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n y => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (K * ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖))
    (fun n => (continuous_weightTerm f D c La n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun y _ => norm_weightTerm_le f D c La n y)
    (Eventually.of_forall fun y _ => hs.mul_right _) ?_
    (Eventually.of_forall fun y _ => ?_)
  · have : (fun y : ℝ => ∑' n : ℕ, |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        (K * ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖)) =
        fun y : ℝ => (∑' n : ℕ, |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) *
          (K * ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖) := funext fun y => tsum_mul_right
    rw [this]
    exact (continuous_const.mul (continuous_const.mul continuous_norm_zeta_line)).intervalIntegrable _ _
  · refine Summable.hasSum ?_
    exact Summable.of_norm_bounded (hs.mul_right (K * ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖))
      (fun n => norm_weightTerm_le f D c La n y)

/-- The Cesàro mean of one term converges. -/
theorem tendsto_mean_weightTerm (f : ℕ → ℝ) (D : ℕ) (c La : ℝ) (n : ℕ) :
    Tendsto (fun T : ℝ => (∫ y in (8 : ℝ)..T, weightTerm f D c La n y) / T) atTop
      (𝓝 (weightLimit f D c La n)) := by
  have hcont : ∀ κ : ℝ, Continuous (zetaMobiusTerm D κ) := continuous_zetaMobiusTerm D
  have hint : ∀ T : ℝ, (∫ y in (8 : ℝ)..T, weightTerm f D c La n y) / T =
      ∑ d ∈ D.divisors, (coeffβ f n d : ℂ) *
        ((1 + (c : ℂ) ^ 2) * ((∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d) y) / T) +
          (c : ℂ) * ((∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d + La) y) / T) +
          (c : ℂ) * ((∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d - La) y) / T)) := by
    intro T
    unfold weightTerm
    rw [intervalIntegral.integral_finsetSum, Finset.sum_div]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_three_combo (hcont _) (hcont _) (hcont _)]
      ring
    · intro d _
      exact (continuous_const.mul (((continuous_const.mul (hcont _)).add
        (continuous_const.mul (hcont _))).add (continuous_const.mul (hcont _)))).intervalIntegrable _ _
  simp_rw [hint]
  unfold weightLimit
  refine tendsto_finsetSum _ fun d _ => ?_
  refine Tendsto.const_mul _ ?_
  exact (((tendsto_zeta_mobiusPoly_moment D _).const_mul _).add
    ((tendsto_zeta_mobiusPoly_moment D _).const_mul _)).add
    ((tendsto_zeta_mobiusPoly_moment D _).const_mul _)

/-- The twisted first moment of `ζ · M_D` at `log p − log q`, uniformly in `p, q`. -/
theorem norm_integral_zetaMobiusTerm_le {C : ℝ} (hC : 0 ≤ C)
    (hmom : ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → ∀ T : ℝ, 8 ≤ T →
      ‖∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((Real.log p - Real.log q : ℝ) : ℂ) * y * I)‖ ≤
        C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q)))
    (D : ℕ) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {T : ℝ} (hT : 8 ≤ T) :
    ‖∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log p - Real.log q) y‖ ≤
      divSum D * (C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q * D))) := by
  have hpt : ∀ y : ℝ, zetaMobiusTerm D (Real.log p - Real.log q) y =
      ∑ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
        ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((Real.log p - Real.log (q * d : ℕ) : ℝ) : ℂ) * y * I))) := by
    intro y
    rw [zetaMobiusTerm, mobiusPoly, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hlog : Real.log p - Real.log (q * d : ℕ) = (Real.log p - Real.log q) - Real.log d := by
      push_cast
      rw [Real.log_mul (by exact_mod_cast (by omega : q ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0))]
      ring
    rw [hlog, show ((((Real.log p - Real.log q) - Real.log d : ℝ)) : ℂ) * y * I =
      ((Real.log p - Real.log q : ℝ) : ℂ) * y * I + (-((Real.log d : ℝ) : ℂ) * y * I) by push_cast; ring,
      Complex.exp_add]
    ring
  simp_rw [hpt]
  have hint : ∀ d ∈ D.divisors, IntervalIntegrable (fun y : ℝ =>
      ((ArithmeticFunction.moebius d : ℝ) : ℂ) * ((((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((Real.log p - Real.log (q * d : ℕ) : ℝ) : ℂ) * y * I)))) volume 8 T := fun d _ =>
    (continuous_const.mul (continuous_const.mul
      (continuous_riemannZeta_criticalLine.mul (by fun_prop)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint]
  unfold divSum
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hdD : d ≤ D := Nat.divisor_le hd
  have hqd : 1 ≤ q * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  have hm := hmom p (q * d) hp hqd T hT
  have hle : Real.sqrt (1 + Real.log ((p : ℝ) * ((q * d : ℕ) : ℝ))) ≤
      Real.sqrt (1 + Real.log ((p : ℝ) * q * D)) := by
    apply Real.sqrt_le_sqrt
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hdD' : (d : ℝ) ≤ D := by exact_mod_cast hdD
    have : Real.log ((p : ℝ) * ((q * d : ℕ) : ℝ)) ≤ Real.log ((p : ℝ) * q * D) := by
      apply Real.log_le_log (by positivity)
      push_cast
      rw [← mul_assoc]
      gcongr
    linarith
  have hd0 : 0 ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hrhs : 0 ≤ C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q * D)) := by
    have : (0 : ℝ) ≤ T := by linarith
    positivity
  calc |(ArithmeticFunction.moebius d : ℝ)| * ((d : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((Real.log p - Real.log (q * d : ℕ) : ℝ) : ℂ) * y * I)‖)
      ≤ 1 * ((d : ℝ) ^ (-(1 / 2 : ℝ)) * (C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q * D)))) := by
        gcongr
        refine hm.trans ?_
        exact mul_le_mul_of_nonneg_left hle (mul_nonneg hC (by linarith))
    _ = (d : ℝ) ^ (-(1 / 2 : ℝ)) * (C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q * D))) := one_mul _

/-- The same bound, monotone in the integer `p q`. -/
theorem norm_integral_zetaMobiusTerm_le_of_le {C : ℝ} (hC : 0 ≤ C)
    (hmom : ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → ∀ T : ℝ, 8 ≤ T →
      ‖∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((Real.log p - Real.log q : ℝ) : ℂ) * y * I)‖ ≤
        C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q)))
    {D : ℕ} (hD : 1 ≤ D) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {X : ℝ} (hX : (p : ℝ) * q * D ≤ X)
    {T : ℝ} (hT : 8 ≤ T) :
    ‖∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log p - Real.log q) y‖ ≤
      divSum D * (C * T * Real.sqrt (1 + Real.log X)) := by
  refine (norm_integral_zetaMobiusTerm_le hC hmom D hp hq hT).trans ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hpos : (0 : ℝ) < (p : ℝ) * q * D := by positivity
  have hlog : Real.log ((p : ℝ) * q * D) ≤ Real.log X := Real.log_le_log hpos hX
  have hsq : Real.sqrt (1 + Real.log ((p : ℝ) * q * D)) ≤ Real.sqrt (1 + Real.log X) :=
    Real.sqrt_le_sqrt (by linarith)
  have h0 : 0 ≤ C * T := mul_nonneg hC (by linarith)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq h0) (divSum_nonneg D)

theorem log_add_log (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Real.log n + Real.log d = Real.log (n * d : ℕ) - Real.log (1 : ℕ) := by
  push_cast
  rw [Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0)),
    Real.log_one]
  ring

theorem log_add_log_add_log (n d a : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (ha : 1 ≤ a) :
    Real.log n + Real.log d + Real.log a = Real.log (n * d * a : ℕ) - Real.log (1 : ℕ) := by
  push_cast
  rw [Real.log_mul (by positivity) (by exact_mod_cast (by omega : a ≠ 0)),
    Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0)),
    Real.log_one]
  ring

theorem log_add_log_sub_log (n d a : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Real.log n + Real.log d - Real.log a = Real.log (n * d : ℕ) - Real.log a := by
  push_cast
  rw [Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : d ≠ 0))]

/-- **Uniform bound for the Cesàro means**, `n ≥ 0`, `T ≥ 8`. -/
theorem norm_mean_weightTerm_le {C : ℝ} (hC : 0 ≤ C)
    (hmom : ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → ∀ T : ℝ, 8 ≤ T →
      ‖∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((Real.log p - Real.log q : ℝ) : ℂ) * y * I)‖ ≤
        C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q)))
    (f : ℕ → ℝ) {D a : ℕ} (hD : 1 ≤ D) (ha : 1 ≤ a) (c : ℝ) (n : ℕ) {T : ℝ} (hT : 8 ≤ T) :
    ‖(∫ y in (8 : ℝ)..T, weightTerm f D c (Real.log a) n y) / T‖ ≤
      |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (divSum D ^ 2 * (1 + c ^ 2 + 2 * |c|) * C *
        Real.sqrt (1 + Real.log (n * ((D : ℝ) * D * a * a)))) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hS := divSum_nonneg D
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [weightTerm_zero_left, intervalIntegral.integral_zero, zero_div, norm_zero]
    simp
  have hn1 : 1 ≤ n := hn
  set X : ℝ := n * ((D : ℝ) * D * a * a) with hX
  set B : ℝ := divSum D * (C * T * Real.sqrt (1 + Real.log X)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ C * T := mul_nonneg hC hTpos.le
    positivity
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hbound : ∀ d ∈ D.divisors, ∀ κ ∈ ({Real.log n + Real.log d, Real.log n + Real.log d + Real.log a,
      Real.log n + Real.log d - Real.log a} : Set ℝ),
      ‖∫ y in (8 : ℝ)..T, zetaMobiusTerm D κ y‖ ≤ B := by
    intro d hd κ hκ
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdD : (d : ℝ) ≤ D := by exact_mod_cast Nat.divisor_le hd
    have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    rcases hκ with rfl | rfl | rfl
    · rw [log_add_log n d hn1 hd1]
      refine norm_integral_zetaMobiusTerm_le_of_le hC hmom hD (Nat.one_le_iff_ne_zero.mpr (by positivity))
        le_rfl ?_ hT
      rw [hX]; push_cast
      calc (n : ℝ) * d * 1 * D ≤ n * D * 1 * D := by gcongr
        _ ≤ n * ((D : ℝ) * D * a * a) := by
          have : (1 : ℝ) ≤ a * a := one_le_mul_of_one_le_of_one_le ha1 ha1
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n * D * D) (by linarith : (0 : ℝ) ≤ a * a - 1)]
    · rw [log_add_log_add_log n d a hn1 hd1 ha]
      refine norm_integral_zetaMobiusTerm_le_of_le hC hmom hD (Nat.one_le_iff_ne_zero.mpr (by positivity))
        le_rfl ?_ hT
      rw [hX]; push_cast
      calc (n : ℝ) * d * a * 1 * D ≤ n * D * a * 1 * D := by gcongr
        _ ≤ n * ((D : ℝ) * D * a * a) := by
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n * D * D * a) (by linarith : (0 : ℝ) ≤ a - 1)]
    · rw [log_add_log_sub_log n d a hn1 hd1]
      refine norm_integral_zetaMobiusTerm_le_of_le hC hmom hD (Nat.one_le_iff_ne_zero.mpr (by positivity))
        ha ?_ hT
      rw [hX]; push_cast
      calc (n : ℝ) * d * a * D ≤ n * D * a * D := by gcongr
        _ ≤ n * ((D : ℝ) * D * a * a) := by
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n * D * D * a) (by linarith : (0 : ℝ) ≤ a - 1)]
  have hcont : ∀ κ : ℝ, Continuous (zetaMobiusTerm D κ) := continuous_zetaMobiusTerm D
  have hint : (∫ y in (8 : ℝ)..T, weightTerm f D c (Real.log a) n y) =
      ∑ d ∈ D.divisors, (coeffβ f n d : ℂ) *
        ((1 + (c : ℂ) ^ 2) * (∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d) y) +
          (c : ℂ) * (∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d + Real.log a) y) +
          (c : ℂ) * (∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d - Real.log a) y)) := by
    unfold weightTerm
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_three_combo (hcont _) (hcont _) (hcont _)]
    · intro d _
      exact (continuous_const.mul (((continuous_const.mul (hcont _)).add
        (continuous_const.mul (hcont _))).add (continuous_const.mul (hcont _)))).intervalIntegrable _ _
  rw [hint, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos, div_le_iff₀ hTpos]
  have hc2 : ‖(1 + (c : ℂ) ^ 2)‖ = 1 + c ^ 2 := by
    rw [show (1 + (c : ℂ) ^ 2) = ((1 + c ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : ‖(c : ℂ)‖ = |c| := by rw [Complex.norm_real, Real.norm_eq_abs]
  calc ‖∑ d ∈ D.divisors, (coeffβ f n d : ℂ) * _‖
      ≤ ∑ d ∈ D.divisors, |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((1 + c ^ 2 + 2 * |c|) * B) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul (abs_coeffβ_le f n d) ?_ (norm_nonneg _) (by positivity)
        calc _ ≤ ‖(1 + (c : ℂ) ^ 2) * (∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d) y)‖ +
              ‖(c : ℂ) * (∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d + Real.log a) y)‖ +
              ‖(c : ℂ) * (∫ y in (8 : ℝ)..T, zetaMobiusTerm D (Real.log n + Real.log d - Real.log a) y)‖ :=
              norm_add₃_le
          _ ≤ (1 + c ^ 2) * B + |c| * B + |c| * B := by
              rw [norm_mul, norm_mul, norm_mul, hc2, hc]
              gcongr
              · exact hbound d hd _ (by simp)
              · exact hbound d hd _ (by simp)
              · exact hbound d hd _ (by simp)
          _ = (1 + c ^ 2 + 2 * |c|) * B := by ring
    _ = |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (divSum D ^ 2 * (1 + c ^ 2 + 2 * |c|) * C *
          Real.sqrt (1 + Real.log X)) * T := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hB]
        unfold divSum
        ring

/-! ## Convergence of the weighted mean -/

/-- **The Cesàro mean of the weighted integrand** converges to `Σ_n weightLimit n`. -/
theorem tendsto_mean_integrand {f : ℕ → ℝ} (hlog : LogMomentSummable f) {D a : ℕ} (hD : 1 ≤ D)
    (ha : 1 ≤ a) (c : ℝ) :
    Tendsto (fun T : ℝ => (∫ y in (8 : ℝ)..T,
        starRingEnd ℂ (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
          starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))) *
        ((‖mobiusPoly D y * (1 + (c : ℂ) * cexp (-((Real.log a : ℝ) : ℂ) * y * I))‖ ^ 2 : ℝ) : ℂ)) / T)
      atTop (𝓝 (∑' n, weightLimit f D c (Real.log a) n)) := by
  obtain ⟨C, hC, hmom⟩ := exists_norm_integral_zeta_twist_le
  have hs := summable_abs_mul_rpow hlog
  set Q : ℝ := (D : ℝ) * D * a * a with hQ
  have hQ1 : 1 ≤ Q := by
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have h1 : (1 : ℝ) ≤ D * D := one_le_mul_of_one_le_of_one_le hD1 hD1
    have h2 : (1 : ℝ) ≤ D * D * a := one_le_mul_of_one_le_of_one_le h1 ha1
    exact one_le_mul_of_one_le_of_one_le h2 ha1
  set K' := divSum D ^ 2 * (1 + c ^ 2 + 2 * |c|) * C
  have hsum : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      (K' * Real.sqrt (1 + Real.log (n * Q))) := by
    refine ((summable_majorant hQ1 hlog).mul_left K').congr fun n => ?_
    ring
  have hrw : ∀ T : ℝ, (∫ y in (8 : ℝ)..T,
        starRingEnd ℂ (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
          starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))) *
        ((‖mobiusPoly D y * (1 + (c : ℂ) * cexp (-((Real.log a : ℝ) : ℂ) * y * I))‖ ^ 2 : ℝ) : ℂ)) / T =
      ∑' n, (∫ y in (8 : ℝ)..T, weightTerm f D c (Real.log a) n y) / T := by
    intro T
    rw [(hasSum_integral_weightTerm hs D c (Real.log a) T).tsum_eq.symm, tsum_div_const]
  simp_rw [hrw]
  refine tendsto_tsum_of_dominated_convergence hsum (fun n => tendsto_mean_weightTerm f D c _ n) ?_
  filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT n
  refine (norm_mean_weightTerm_le hC hmom f hD ha c n hT).trans (le_of_eq ?_)
  ring

/-! ## Evaluation of the limit -/

theorem not_coprime_of_dvd {D d : ℕ} (hdD : d ∣ D) (hd : 2 ≤ d) {m : ℕ} (hdm : d ∣ m) :
    ¬ Nat.Coprime D m := by
  intro h
  have h1 : d ∣ Nat.gcd D m := Nat.dvd_gcd hdD hdm
  rw [Nat.Coprime.gcd_eq_one h] at h1
  have := Nat.dvd_one.mp h1
  omega

theorem eq_one_of_coprime_of_dvd {D d : ℕ} (hdD : d ∣ D) (h : Nat.Coprime D d) : d = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h) hdD

/-- At most one divisor `d ∣ D` has `a ∣ nd` and `nd/a` coprime to `D`. -/
theorem eq_of_coprime_div {D a n d₁ d₂ : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a) (hd₁ : d₁ ∣ D) (hd₂ : d₂ ∣ D)
    (hd₁0 : 1 ≤ d₁)
    (h₁ : a ∣ n * d₁ ∧ Nat.Coprime D (n * d₁ / a)) (h₂ : a ∣ n * d₂ ∧ Nat.Coprime D (n * d₂ / a)) :
    d₁ = d₂ := by
  obtain ⟨g₁, hg₁⟩ := h₁.1
  obtain ⟨g₂, hg₂⟩ := h₂.1
  have hq₁ : n * d₁ / a = g₁ := by rw [hg₁, Nat.mul_div_cancel_left _ (by omega)]
  have hq₂ : n * d₂ / a = g₂ := by rw [hg₂, Nat.mul_div_cancel_left _ (by omega)]
  have hc₁ : Nat.Coprime D g₁ := hq₁ ▸ h₁.2
  have hc₂ : Nat.Coprime D g₂ := hq₂ ▸ h₂.2
  have hcross : g₁ * d₂ = g₂ * d₁ := by
    have : a * (g₁ * d₂) = a * (g₂ * d₁) := by
      calc a * (g₁ * d₂) = (a * g₁) * d₂ := by ring
        _ = n * d₁ * d₂ := by rw [← hg₁]
        _ = n * d₂ * d₁ := by ring
        _ = (a * g₂) * d₁ := by rw [hg₂]
        _ = a * (g₂ * d₁) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hcop₁ : Nat.Coprime g₁ d₁ := (Nat.Coprime.coprime_dvd_left hd₁ hc₁).symm
  have hcop₂ : Nat.Coprime g₂ d₂ := (Nat.Coprime.coprime_dvd_left hd₂ hc₂).symm
  have h12 : g₁ ∣ g₂ := hcop₁.dvd_of_dvd_mul_right ⟨d₂, hcross.symm⟩
  have h21 : g₂ ∣ g₁ := hcop₂.dvd_of_dvd_mul_right ⟨d₁, hcross⟩
  have heq : g₁ = g₂ := Nat.dvd_antisymm h12 h21
  have hg₁0 : g₁ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hg₁
    have : n * d₁ ≠ 0 := by positivity
    exact this hg₁
  rw [heq] at hcross
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (heq ▸ hg₁0)) hcross).symm

/-- `n^{-1/2} d^{-1/2} (nd/a)^{-1/2} ≤ √a / n` when `a ∣ nd`. -/
theorem rpow_mul_rpow_mul_rpow_le {n d a : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (ha : 1 ≤ a) (hdiv : a ∣ n * d) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ)) * (((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      Real.sqrt a / n := by
  obtain ⟨g, hg⟩ := hdiv
  have hq : n * d / a = g := by rw [hg, Nat.mul_div_cancel_left _ (by omega)]
  rw [hq]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hgpos : (0 : ℝ) < g := by
    have : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h | h
      · subst h; simp at hg; omega
      · exact h
    exact_mod_cast this
  have hag : (a : ℝ) * g = n * d := by exact_mod_cast hg.symm
  have e : ∀ x : ℝ, 0 < x → x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
    intro x hx
    rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [e _ hnpos, e _ hdpos, e _ hgpos, div_mul_div_comm, div_mul_div_comm, one_mul, one_mul,
    ← Real.sqrt_mul hnpos.le, ← Real.sqrt_mul (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hnpos, one_mul]
  have hprod : Real.sqrt a * Real.sqrt ((n : ℝ) * d * g) = (n : ℝ) * d := by
    rw [← Real.sqrt_mul hapos.le, show (a : ℝ) * (n * d * g) = (n * d) ^ 2 by
      rw [show (a : ℝ) * (n * d * g) = (a * g) * (n * d) by ring, hag]; ring,
      Real.sqrt_sq (by positivity)]
  rw [hprod]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [mul_le_mul_of_nonneg_left hd1 hnpos.le]

theorem zetaMobiusLimit_first {D n d : ℕ} (hD : D ≠ 0) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    zetaMobiusLimit D (Real.log n + Real.log d) =
      if Nat.Coprime D (n * d) then ((((n * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0 := by
  rw [log_add_log n d hn hd, zetaMobiusLimit_log_sub_eq hD
    (Nat.one_le_iff_ne_zero.mpr (by positivity)) le_rfl]
  simp [Nat.div_one]

theorem zetaMobiusLimit_second {D n d a : ℕ} (hD : D ≠ 0) (hn : 1 ≤ n) (hd : 1 ≤ d) (ha2 : 2 ≤ a)
    (haD : a ∣ D) : zetaMobiusLimit D (Real.log n + Real.log d + Real.log a) = 0 := by
  rw [log_add_log_add_log n d a hn hd (by omega), zetaMobiusLimit_log_sub_eq hD
    (Nat.one_le_iff_ne_zero.mpr (by positivity)) le_rfl, if_neg]
  rintro ⟨_, h⟩
  rw [Nat.div_one] at h
  exact not_coprime_of_dvd haD ha2 (dvd_mul_left a (n * d)) h

theorem zetaMobiusLimit_third {D n d a : ℕ} (hD : D ≠ 0) (hn : 1 ≤ n) (hd : 1 ≤ d) (ha : 1 ≤ a) :
    zetaMobiusLimit D (Real.log n + Real.log d - Real.log a) =
      if a ∣ n * d ∧ Nat.Coprime D (n * d / a) then ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      else 0 := by
  rw [log_add_log_sub_log n d a hn hd, zetaMobiusLimit_log_sub_eq hD
    (Nat.one_le_iff_ne_zero.mpr (by positivity)) ha]

/-- `weightLimit` with the three collapsed frequencies. -/
theorem weightLimit_eq {f : ℕ → ℝ} {D a n : ℕ} (hD : D ≠ 0) (hn : 1 ≤ n) (ha2 : 2 ≤ a) (haD : a ∣ D)
    (c : ℝ) :
    weightLimit f D c (Real.log a) n =
      (∑ d ∈ D.divisors, (coeffβ f n d : ℂ) * ((1 + (c : ℂ) ^ 2) *
        (if Nat.Coprime D (n * d) then ((((n * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0))) +
      ∑ d ∈ D.divisors, (coeffβ f n d : ℂ) * ((c : ℂ) *
        (if a ∣ n * d ∧ Nat.Coprime D (n * d / a) then
          ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)) := by
  unfold weightLimit
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  rw [zetaMobiusLimit_first hD hn hd1, zetaMobiusLimit_second hD hn hd1 ha2 haD,
    zetaMobiusLimit_third hD hn hd1 (by omega)]
  ring

/-- **The coefficient `f(a)`**: at `n = a` the limit is `c f(a) a^{-1/2}`. -/
theorem weightLimit_self {f : ℕ → ℝ} {D a : ℕ} (hD : D ≠ 0) (ha2 : 2 ≤ a) (haD : a ∣ D) (c : ℝ) :
    weightLimit f D c (Real.log a) a = ((c * (f a * (a : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
  rw [weightLimit_eq hD (by omega) ha2 haD]
  have h1 : ∑ d ∈ D.divisors, (coeffβ f a d : ℂ) * ((1 + (c : ℂ) ^ 2) *
      (if Nat.Coprime D (a * d) then ((((a * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg (not_coprime_of_dvd haD ha2 (dvd_mul_right a d))]
    ring
  rw [h1, zero_add, Finset.sum_eq_single 1]
  · have hc : Nat.Coprime D (a * 1 / a) := by
      rw [mul_one, Nat.div_self (by omega)]; exact Nat.coprime_one_right D
    rw [if_pos ⟨dvd_mul_right a 1, hc⟩, show a * 1 / a = 1 by rw [mul_one, Nat.div_self (by omega)] ]
    unfold coeffβ
    simp
    ring
  · intro d hd hd1
    rw [if_neg]
    · ring
    rintro ⟨_, h⟩
    rw [Nat.mul_div_cancel_left _ (by omega)] at h
    exact hd1 (eq_one_of_coprime_of_dvd (Nat.dvd_of_mem_divisors hd) h)
  · intro h; exact absurd (Nat.one_mem_divisors.mpr hD) h

/-- **The middle range**: for `a < n ≤ K` the limit vanishes. -/
theorem weightLimit_eq_zero_of_le {f : ℕ → ℝ} {K a n : ℕ} (ha2 : 2 ≤ a) (haK : a ≤ K) (han : a < n)
    (hnK : n ≤ K) (c : ℝ) : weightLimit f (Nat.factorial K) c (Real.log a) n = 0 := by
  have hD : Nat.factorial K ≠ 0 := Nat.factorial_ne_zero K
  have haD : a ∣ Nat.factorial K := Nat.dvd_factorial (by omega) haK
  have hnD : n ∣ Nat.factorial K := Nat.dvd_factorial (by omega) hnK
  rw [weightLimit_eq hD (by omega) ha2 haD]
  have h1 : ∀ d ∈ (Nat.factorial K).divisors, (coeffβ f n d : ℂ) * ((1 + (c : ℂ) ^ 2) *
      (if Nat.Coprime (Nat.factorial K) (n * d) then
        ((((n * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)) = 0 := by
    intro d _
    rw [if_neg (not_coprime_of_dvd hnD (by omega) (dvd_mul_right n d))]
    ring
  have h3 : ∀ d ∈ (Nat.factorial K).divisors, (coeffβ f n d : ℂ) * ((c : ℂ) *
      (if a ∣ n * d ∧ Nat.Coprime (Nat.factorial K) (n * d / a) then
        ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)) = 0 := by
    intro d hd
    rw [if_neg]
    · ring
    rintro ⟨⟨g, hg⟩, hcop⟩
    have hq : n * d / a = g := by rw [hg, Nat.mul_div_cancel_left _ (by omega)]
    rw [hq] at hcop
    have hdD : d ∣ Nat.factorial K := Nat.dvd_of_mem_divisors hd
    have hgd : Nat.Coprime g d := (Nat.Coprime.coprime_dvd_left hdD hcop).symm
    have hgn : g ∣ n := hgd.dvd_of_dvd_mul_right ⟨a, by rw [hg]; ring⟩
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    rcases Nat.lt_or_ge g 2 with hg2 | hg2
    · interval_cases g
      · simp at hg; omega
      · have : n * d = a := by rw [hg, mul_one]
        have : n ≤ n * d := Nat.le_mul_of_pos_right n hd1
        omega
    · have hgK : g ≤ K := (Nat.le_of_dvd (by omega) hgn).trans hnK
      exact not_coprime_of_dvd (Nat.dvd_factorial (by omega) hgK) hg2 dvd_rfl hcop
  rw [Finset.sum_eq_zero h1, Finset.sum_eq_zero h3, add_zero]

/-- **The tail**: for `n > K`, `‖weightLimit n‖ ≤ (1 + c² + |c| √a) |f(n)| / n`. -/
theorem norm_weightLimit_le_of_lt {f : ℕ → ℝ} {K a n : ℕ} (ha2 : 2 ≤ a) (haK : a ≤ K) (hKn : K < n)
    (c : ℝ) :
    ‖weightLimit f (Nat.factorial K) c (Real.log a) n‖ ≤
      (1 + c ^ 2 + |c| * Real.sqrt a) * (|f n| / n) := by
  set D := Nat.factorial K with hDdef
  have hD : D ≠ 0 := Nat.factorial_ne_zero K
  have haD : a ∣ D := Nat.dvd_factorial (by omega) haK
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnn : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / n := by
    rw [← Real.rpow_add hnpos, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one,
      one_div]
  rw [weightLimit_eq hD hn1 ha2 haD]
  -- first sum
  have hfirst : ‖∑ d ∈ D.divisors, (coeffβ f n d : ℂ) * ((1 + (c : ℂ) ^ 2) *
      (if Nat.Coprime D (n * d) then ((((n * d : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0))‖ ≤
      (1 + c ^ 2) * (|f n| / n) := by
    rw [Finset.sum_eq_single 1]
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        show (1 + (c : ℂ) ^ 2) = ((1 + c ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + c ^ 2)]
      have hcoef : |coeffβ f n 1| ≤ |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have := abs_coeffβ_le f n 1
        simpa using this
      have hval : ‖(if Nat.Coprime D (n * 1) then ((((n * 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          else 0)‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        split_ifs
        · rw [Complex.norm_real, Real.norm_eq_abs, mul_one,
            abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
        · rw [norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc |coeffβ f n 1| * ((1 + c ^ 2) * ‖(if Nat.Coprime D (n * 1) then
              ((((n * 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)‖)
          ≤ (|f n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) * ((1 + c ^ 2) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
            gcongr
        _ = (1 + c ^ 2) * (|f n| * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)))) := by ring
        _ = (1 + c ^ 2) * (|f n| / n) := by rw [hnn]; ring
    · intro d hd hd1
      have hd2 : 2 ≤ d := by have := Nat.pos_of_mem_divisors hd; omega
      rw [if_neg (not_coprime_of_dvd (Nat.dvd_of_mem_divisors hd) hd2 (dvd_mul_left d n))]
      ring
    · intro h; exact absurd (Nat.one_mem_divisors.mpr hD) h
  -- third sum
  set S := D.divisors.filter (fun d => a ∣ n * d ∧ Nat.Coprime D (n * d / a)) with hS
  have hcard : S.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun d₁ h₁ d₂ h₂ => ?_
    rw [hS, Finset.mem_filter] at h₁ h₂
    exact eq_of_coprime_div hn1 (by omega) (Nat.dvd_of_mem_divisors h₁.1)
      (Nat.dvd_of_mem_divisors h₂.1) (Nat.pos_of_mem_divisors h₁.1) h₁.2 h₂.2
  have hthird : ‖∑ d ∈ D.divisors, (coeffβ f n d : ℂ) * ((c : ℂ) *
      (if a ∣ n * d ∧ Nat.Coprime D (n * d / a) then
        ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0))‖ ≤
      |c| * Real.sqrt a * (|f n| / n) := by
    have hrw : ∑ d ∈ D.divisors, (coeffβ f n d : ℂ) * ((c : ℂ) *
        (if a ∣ n * d ∧ Nat.Coprime D (n * d / a) then
          ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0)) =
        ∑ d ∈ S, (coeffβ f n d : ℂ) * ((c : ℂ) * ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> ring
    rw [hrw]
    have hterm : ∀ d ∈ S, ‖(coeffβ f n d : ℂ) * ((c : ℂ) *
        ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ ≤ |c| * Real.sqrt a * (|f n| / n) := by
      intro d hd
      rw [hS, Finset.mem_filter] at hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd.1
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      have hc := abs_coeffβ_le f n d
      have hr := rpow_mul_rpow_mul_rpow_le hn1 hd1 (by omega) hd.2.1
      have hA : 0 ≤ (((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      calc |coeffβ f n d| * (|c| * ((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
          ≤ (|f n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ))) *
              (|c| * ((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = |c| * |f n| * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ)) *
              ((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ |c| * |f n| * (Real.sqrt a / n) := by gcongr
        _ = |c| * Real.sqrt a * (|f n| / n) := by ring
    calc ‖∑ d ∈ S, (coeffβ f n d : ℂ) * ((c : ℂ) * ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖
        ≤ ∑ d ∈ S, ‖(coeffβ f n d : ℂ) * ((c : ℂ) *
            ((((n * d / a : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ S.card • (|c| * Real.sqrt a * (|f n| / n)) := Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ 1 • (|c| * Real.sqrt a * (|f n| / n)) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          gcongr
      _ = |c| * Real.sqrt a * (|f n| / n) := one_smul _ _
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (1 + c ^ 2) * (|f n| / n) + |c| * Real.sqrt a * (|f n| / n) := add_le_add hfirst hthird
    _ = (1 + c ^ 2 + |c| * Real.sqrt a) * (|f n| / n) := by ring

/-- `Σ_{n > K} |f(n)|/n`. -/
def tailSum (f : ℕ → ℝ) (K : ℕ) : ℝ := ∑' n, if K < n then |f n| / n else 0

theorem tendsto_tailSum {f : ℕ → ℝ} (hs : Summable fun n : ℕ => |f n| / n) :
    Tendsto (tailSum f) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := fun n : ℕ => |f n| / n)
    (f := fun (K n : ℕ) => if K < n then |f n| / n else 0) (g := fun _ => (0 : ℝ)) hs
    (fun n => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop n] with K hK
      rw [if_neg (by omega)]))
    (Eventually.of_forall fun K n => by
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [norm_zero]; positivity)
  show Tendsto (fun K : ℕ => ∑' n : ℕ, if K < n then |f n| / n else 0) atTop (𝓝 0)
  simpa using h

/-- **The limit, up to the tail**: `‖Σ_n weightLimit n − f(a)² a^{-1/2}‖ ≤ C · Σ_{n > K} |f(n)|/n`. -/
theorem norm_tsum_weightLimit_sub_le {f : ℕ → ℝ} (hlog : LogMomentSummable f) {K a : ℕ} (ha2 : 2 ≤ a)
    (haK : a ≤ K) (hih : ∀ m, 1 ≤ m → m < a → f m = 0) :
    ‖(∑' n, weightLimit f (Nat.factorial K) (f a) (Real.log a) n) -
        ((f a * (f a * (a : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)‖ ≤
      (1 + f a ^ 2 + |f a| * Real.sqrt a) * tailSum f K := by
  set c := f a
  set v : ℂ := ((c * (f a * (a : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)
  set C₀ := 1 + c ^ 2 + |c| * Real.sqrt a
  have hC₀ : 0 ≤ C₀ := by positivity
  set e : ℕ → ℂ := fun n => weightLimit f (Nat.factorial K) c (Real.log a) n - if n = a then v else 0
  set b : ℕ → ℝ := fun n => C₀ * (if K < n then |f n| / n else 0)
  have hbsum : Summable b := by
    refine Summable.mul_left C₀ ?_
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      (summable_abs_div hlog)
    split_ifs
    · exact le_rfl
    · positivity
  have heb : ∀ n, ‖e n‖ ≤ b n := by
    intro n
    simp only [e, b]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [weightLimit_zero_left, if_neg (by omega), sub_zero, norm_zero]
      split_ifs <;> positivity
    rcases lt_trichotomy n a with hna | rfl | hna
    · rw [if_neg (by omega)]
      have hfn : f n = 0 := hih n hn hna
      have : weightLimit f (Nat.factorial K) c (Real.log a) n = 0 := by
        unfold weightLimit
        refine Finset.sum_eq_zero fun d _ => ?_
        simp [coeffβ, hfn]
      rw [this, sub_zero, norm_zero]
      split_ifs <;> positivity
    · rw [if_pos rfl, weightLimit_self (Nat.factorial_ne_zero K) ha2
        (Nat.dvd_factorial (by omega) haK), sub_self, norm_zero]
      split_ifs <;> positivity
    · rw [if_neg (by omega), sub_zero]
      by_cases hnK : n ≤ K
      · rw [weightLimit_eq_zero_of_le ha2 haK hna hnK, norm_zero]
        split_ifs <;> positivity
      · push Not at hnK
        rw [if_pos hnK]
        exact norm_weightLimit_le_of_lt ha2 haK hnK c
  have hesum : Summable e := Summable.of_norm_bounded hbsum heb
  have hite : Summable fun n : ℕ => if n = a then v else 0 :=
    summable_of_ne_finset_zero (s := {a}) fun n hn => by
      rw [if_neg (by simpa using hn)]
  have hvt : (∑' n : ℕ, if n = a then v else 0) = v := by
    rw [tsum_eq_single a]
    · simp
    · intro n hn; simp [hn]
  have hsplit : (∑' n, weightLimit f (Nat.factorial K) c (Real.log a) n) =
      (∑' n, e n) + v := by
    rw [← hvt, ← Summable.tsum_add hesum hite]
    refine tsum_congr fun n => ?_
    simp only [e]
    ring
  rw [hsplit, add_sub_cancel_right]
  calc ‖∑' n, e n‖ ≤ ∑' n, ‖e n‖ := norm_tsum_le_tsum_norm (Summable.of_norm_bounded hbsum heb |>.norm)
    _ ≤ ∑' n, b n := Summable.tsum_le_tsum heb (Summable.of_norm_bounded hbsum heb |>.norm) hbsum
    _ = C₀ * tailSum f K := by rw [tsum_mul_left]; rfl

theorem continuous_LSeries_line {f : ℕ → ℝ} (hs : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) :
    Continuous fun y : ℝ => LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) := by
  have : (fun y : ℝ => LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I)) =
      fun y => ∑' n, critDirPoly {n} f y := funext fun y => LSeries_line_eq_tsum f y
  rw [this]
  refine continuous_tsum (fun n => ?_) hs (fun n y => (norm_critDirPoly_singleton f n y).le)
  rw [show critDirPoly {n} f = fun y : ℝ => (f n : ℂ) * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    cexp (-((Real.log n : ℝ) : ℂ) * y * I)) from funext fun y => critDirPoly_singleton f n y]
  fun_prop

/-- **Sign rigidity of critical Dirichlet series against `ζ`.**
Let `Σ |f(n)| n^{-1/2} (1 + log n) < ∞`, with `f(1) = 0`. If
`Re(F(1/2+iy) · conj ζ(1/2+iy)) ≤ 0` for all `y ≥ 8`, where `F` is the Dirichlet series of `f`,
then `f(n) = 0` for every `n ≥ 1`. -/
theorem eq_zero_of_re_mul_conj_zeta_nonpos {f : ℕ → ℝ} (hlog : LogMomentSummable f) (hf1 : f 1 = 0)
    (h : ∀ y : ℝ, 8 ≤ y → (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
      starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))).re ≤ 0) :
    ∀ n, 1 ≤ n → f n = 0 := by
  have hs := summable_abs_mul_rpow hlog
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have : a = 1 := by omega
    subst this; exact hf1
  have hih : ∀ m, 1 ≤ m → m < a → f m = 0 := fun m hm hma => ih m hma hm
  set c := f a with hc
  set v : ℝ := c * (f a * (a : ℝ) ^ (-(1 / 2 : ℝ))) with hv
  set C₀ := 1 + f a ^ 2 + |f a| * Real.sqrt a with hC₀
  have hre : ∀ K : ℕ, a ≤ K →
      (∑' n, weightLimit f (Nat.factorial K) c (Real.log a) n).re ≤ 0 := by
    intro K _
    have hD : 1 ≤ Nat.factorial K := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero K)
    have hlim := tendsto_mean_integrand hlog hD (by omega : 1 ≤ a) c
    set Φ : ℝ → ℂ := fun y => starRingEnd ℂ (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
        starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))) *
      ((‖mobiusPoly (Nat.factorial K) y *
        (1 + (c : ℂ) * cexp (-((Real.log a : ℝ) : ℂ) * y * I))‖ ^ 2 : ℝ) : ℂ) with hΦ
    have hcontΦ : Continuous Φ := by
      refine Continuous.mul ?_ (Complex.continuous_ofReal.comp ?_)
      · exact Complex.continuous_conj.comp ((continuous_LSeries_line hs).mul
          (Complex.continuous_conj.comp continuous_riemannZeta_criticalLine))
      · exact ((continuous_mobiusPoly _).mul (by fun_prop)).norm.pow 2
    have hsign : ∀ y : ℝ, 8 ≤ y → (Φ y).re ≤ 0 := by
      intro y hy
      simp only [hΦ]
      rw [Complex.re_mul_ofReal, Complex.conj_re]
      exact mul_nonpos_of_nonpos_of_nonneg (h y hy) (by positivity)
    have hnonpos : ∀ᶠ T : ℝ in atTop, ((∫ y in (8 : ℝ)..T, Φ y) / T).re ≤ 0 := by
      filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
      have hTpos : (0 : ℝ) < T := by linarith
      rw [Complex.div_ofReal_re]
      apply div_nonpos_of_nonpos_of_nonneg _ hTpos.le
      have hreint : (∫ y in (8 : ℝ)..T, Φ y).re = ∫ y in (8 : ℝ)..T, (Φ y).re :=
        (Complex.reCLM.intervalIntegral_comp_comm (hcontΦ.intervalIntegrable _ _)).symm
      rw [hreint]
      have := intervalIntegral.integral_nonneg (μ := volume) (a := (8 : ℝ)) (b := T)
        (f := fun y => -(Φ y).re) hT (fun y hy => by have := hsign y hy.1; linarith)
      rw [intervalIntegral.integral_neg] at this
      linarith
    exact le_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim) hnonpos
  have hvK : ∀ K : ℕ, a ≤ K → v ≤ C₀ * tailSum f K := by
    intro K hK
    have h1 := hre K hK
    have h2 := norm_tsum_weightLimit_sub_le hlog ha2 hK hih
    set L := ∑' n, weightLimit f (Nat.factorial K) c (Real.log a) n
    have h3 : v - L.re ≤ ‖L - (v : ℂ)‖ := by
      have : v - L.re = ((v : ℂ) - L).re := by simp
      rw [this, norm_sub_rev]
      exact Complex.re_le_norm _
    linarith
  have htail := tendsto_tailSum (summable_abs_div hlog)
  have hlim : Tendsto (fun K => C₀ * tailSum f K) atTop (𝓝 0) := by
    simpa using htail.const_mul C₀
  have hv0 : v ≤ 0 := ge_of_tendsto hlim ((eventually_ge_atTop a).mono hvK)
  have hpos : 0 < (a : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < a)) _
  have hcc : c * c ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < c * c * (a : ℝ) ^ (-(1 / 2 : ℝ)) := mul_pos hcon hpos
    have hv' : v = c * c * (a : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hv, hc]; ring
    linarith
  exact mul_self_eq_zero.mp (le_antisymm hcc (mul_self_nonneg c))

/-- **Sign rigidity against `ζ`, absolutely convergent case.** If `Σ |f(n)| n^{-1/2+δ} < ∞` for some
`δ > 0`, `f(1) = 0`, and `Re(F(1/2+iy) · conj ζ(1/2+iy)) ≤ 0` for all `y ≥ 8`, then `f(n) = 0` for
every `n ≥ 1`. -/
theorem eq_zero_of_re_mul_conj_zeta_nonpos_of_lSeriesSummable {f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (h : ∀ y : ℝ, 8 ≤ y → (LSeries (fun n => (f n : ℂ)) ((1 / 2 : ℂ) + y * I) *
      starRingEnd ℂ (riemannZeta ((1 / 2 : ℂ) + y * I))).re ≤ 0) :
    ∀ n, 1 ≤ n → f n = 0 :=
  eq_zero_of_re_mul_conj_zeta_nonpos (logMomentSummable_of_lSeriesSummable hδ hf) hf1 h

end RHTower.ZetaUniformMoment
