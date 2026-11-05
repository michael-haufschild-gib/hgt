import GaloisForLFunctions.ArithmeticProduction.TheInterpolationAtALargeHeight
import GaloisForLFunctions.RHTower.ZetaFiniteMeanSquare
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.OneSignedPerturbations

/-!
# The length–precision law

For `P_a(t) = Σ_{n ≤ N} a(n) n^{−½−it}` at height `T` and length `N = T^θ`: which weights `a` of size `εn^{−η}` does the second moment see?  The answer is exactly

  `η < ½ − 1/(2θ)`.

* **Sharp mean value** (`abs_integral_norm_sq_linePoly_sub_le`).  `∫_{T₁}^{T₂}|P_a|² = (T₂−T₁) Σ|a_n|²/n + O(Σ|a_n|²)`.
* **Blind side** (`power_bounded_second_moment_le`).  If `θ(1−2η) ≤ 1`, every `a` with `|a_n| ≤ εn^{−η}` has second moment `O(ε² T log T)`, uniformly in `a`.
* **Resonant side** (`resonance_beats_every_constant`).  If `θ(1−2η) > 1`, the resonant weight `εn^{−η+iγ}`, `γ ∈ [T, 2T]`, has second moment `≫ T log T` by any constant: its polynomial has
  size `εN^{½−η}` on a window of length `1/log N` around `γ`.
* **The threshold** (`length_precision_law`).  The two cases are exhaustive.  For `θ ≤ 1` every `η ≥ 0` is blind (`below_the_window_every_power_is_blind`), and for every
  `η < ½` some finite `θ` sees it, but square-root precision itself needs `θ → ∞`.
* **Moduli below the window** (`abs_integral_twist_sub_le`).  Up to `O(Σ|a_n|²)`, the second moment depends only on `|a_n|`, so it cannot detect a sign or a phase.

The weight `n^{−η+iγ}` is the term of the explicit formula of a zero `1 − η + iγ`.  So length `T^θ` reaches zeros at height `T` with `β > ½ + 1/(2θ)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower
open ArithmeticOfSquareRootPrecision

/-- `P_a(t) = Σ_{n ≤ N} a(n) n^{−½−it}`. -/
def linePoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  edPoly a (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)

theorem continuous_linePoly (a : ℕ → ℂ) (N : ℕ) : Continuous (linePoly a N) := by
  unfold linePoly
  exact (differentiable_edPoly a (fun n hn => (Finset.mem_Icc.mp hn).1)).continuous.comp (by fun_prop)

/-- The coefficients of `P_a` as a polynomial on `Fin N`. -/
private def lineCoeff (a : ℕ → ℂ) (N : ℕ) (n : Fin N) : ℂ :=
  a ((n : ℕ) + 1) * ((((n : ℕ) + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

private theorem linePoly_eq_dirPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    linePoly a N t = Sieve.dirPoly N (lineCoeff a N) (-t) := by
  classical
  unfold linePoly
  rw [edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1)]
  unfold cdpoly cdterm Sieve.dirPoly lineCoeff
  rw [← Sieve.image_succ_univ N, Finset.sum_image (Sieve.succ_injOn N)]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2
  push_cast
  ring

private theorem rpow_neg_half_sq (n : ℕ) : (((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ 2 = ((n : ℝ) + 1)⁻¹ := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num
  exact Real.rpow_neg_one _

private theorem sum_norm_sq_lineCoeff (a : ℕ → ℂ) (N : ℕ) :
    ∑ n : Fin N, ‖lineCoeff a N n‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / n := by
  classical
  rw [← Sieve.image_succ_univ N, Finset.sum_image (Sieve.succ_injOn N)]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold lineCoeff
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity), rpow_neg_half_sq]
  push_cast
  rw [div_eq_mul_inv]

private theorem sum_succ_mul_norm_sq_lineCoeff (a : ℕ → ℂ) (N : ℕ) :
    ∑ n : Fin N, (((n : ℕ) : ℝ) + 1) * ‖lineCoeff a N n‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  rw [← Sieve.image_succ_univ N, Finset.sum_image (Sieve.succ_injOn N)]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold lineCoeff
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity), rpow_neg_half_sq]
  have hne : ((n : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- **The sharp mean value theorem**, in the normalization of the critical line. -/
theorem abs_integral_norm_sq_linePoly_sub_le (a : ℕ → ℂ) (N : ℕ) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖linePoly a N t‖ ^ 2) - (T₂ - T₁) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / n| ≤
      208 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := Sieve.dirichlet_meanValue_sharp_window_neg N (lineCoeff a N) T₁ T₂
  rw [sum_norm_sq_lineCoeff, sum_succ_mul_norm_sq_lineCoeff] at h
  simpa only [linePoly_eq_dirPoly] using h

/-- **Below the window only the moduli are seen.** -/
theorem abs_integral_twist_sub_le (a χ : ℕ → ℂ) (N : ℕ) (T₁ T₂ : ℝ)
    (hχ : ∀ n ∈ Finset.Icc 1 N, ‖χ n‖ = 1) :
    |(∫ t in T₁..T₂, ‖linePoly (fun n => χ n * a n) N t‖ ^ 2) - ∫ t in T₁..T₂, ‖linePoly a N t‖ ^ 2| ≤
      416 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h1 := abs_integral_norm_sq_linePoly_sub_le (fun n => χ n * a n) N T₁ T₂
  have h2 := abs_integral_norm_sq_linePoly_sub_le a N T₁ T₂
  have hnorm : ∀ n ∈ Finset.Icc 1 N, ‖χ n * a n‖ = ‖a n‖ := by
    intro n hn
    rw [norm_mul, hχ n hn, one_mul]
  have hs1 : ∑ n ∈ Finset.Icc 1 N, ‖χ n * a n‖ ^ 2 / n = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / n :=
    Finset.sum_congr rfl fun n hn => by rw [hnorm n hn]
  have hs2 : ∑ n ∈ Finset.Icc 1 N, ‖χ n * a n‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_congr rfl fun n hn => by rw [hnorm n hn]
  rw [hs1, hs2] at h1
  obtain ⟨h3, h4⟩ := abs_le.mp h1
  obtain ⟨h5, h6⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- `Σ_{n ≤ N} 1/n ≤ 1 + log N`. -/
theorem sum_inv_Icc_le {N : ℕ} (hN : 1 ≤ N) : ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := sum_powerWeight_le_integral (η := 1) zero_le_one hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∫ t in (1 : ℝ)..N, t ^ (-(1 : ℝ)) = Real.log N := by
    simp_rw [Real.rpow_neg_one]
    rw [integral_inv_of_pos one_pos hN0, div_one]
  rw [hint] at h
  refine le_trans (le_of_eq ?_) h
  rw [show Finset.Icc 1 N = Finset.Ioc 0 N by ext; simp [Nat.succ_le_iff]]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold powerWeight
  rw [Real.rpow_neg_one]

/-- **The bound on a power-bounded class.** -/
theorem integral_linePoly_le_of_power_bound {a : ℕ → ℂ} {ε η T₁ T₂ : ℝ} {N : ℕ} (hε : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hη : η < 1 / 2) (hN : 1 ≤ N) (hT : T₁ ≤ T₂)
    (ha : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ ε * (n : ℝ) ^ (-η)) :
    (∫ t in T₁..T₂, ‖linePoly a N t‖ ^ 2) ≤
      ε ^ 2 * ((T₂ - T₁) * (1 + Real.log N) + 208 * (1 + (N : ℝ) ^ (1 - 2 * η) / (1 - 2 * η))) := by
  have h := (abs_le.mp (abs_integral_norm_sq_linePoly_sub_le a N T₁ T₂)).2
  have hsq : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ≤ ε ^ 2 * powerWeight (2 * η) n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2
    refine h1.trans (le_of_eq ?_)
    unfold powerWeight
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-η)), ← Real.rpow_mul hn0.le]
    congr 2
    push_cast
    ring
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext
    simp [Nat.succ_le_iff]
  have hS₂ : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ≤ ε ^ 2 * (1 + (N : ℝ) ^ (1 - 2 * η) / (1 - 2 * η)) := by
    have h1 := partialSum_powerWeight_le_rpow (η := 2 * η) (x := N) (by positivity) (by linarith)
      (by exact_mod_cast hN)
    have h2 : partialSum (powerWeight (2 * η)) (N : ℝ) = ∑ n ∈ Finset.Icc 1 N, powerWeight (2 * η) n := by
      unfold partialSum
      rw [Nat.floor_natCast, hIcc]
    rw [h2] at h1
    calc ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, ε ^ 2 * powerWeight (2 * η) n :=
          Finset.sum_le_sum hsq
      _ = ε ^ 2 * ∑ n ∈ Finset.Icc 1 N, powerWeight (2 * η) n := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hS₁ : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / n ≤ ε ^ 2 * (1 + Real.log N) := by
    calc ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / n ≤ ∑ n ∈ Finset.Icc 1 N, ε ^ 2 * ((n : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have h1 : powerWeight (2 * η) n ≤ 1 := by
            unfold powerWeight
            exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
          have h2 : ‖a n‖ ^ 2 ≤ ε ^ 2 :=
            (hsq n hn).trans (mul_le_of_le_one_right (by positivity) h1)
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ε ^ 2 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_Icc_le hN) (by positivity)
  have h3 := mul_le_mul_of_nonneg_left hS₁ (by linarith : 0 ≤ T₂ - T₁)
  have h4 := mul_le_mul_of_nonneg_left hS₂ (by norm_num : (0 : ℝ) ≤ 208)
  have hexp : ε ^ 2 * ((T₂ - T₁) * (1 + Real.log N) + 208 * (1 + (N : ℝ) ^ (1 - 2 * η) / (1 - 2 * η))) =
      (T₂ - T₁) * (ε ^ 2 * (1 + Real.log N)) +
        208 * (ε ^ 2 * (1 + (N : ℝ) ^ (1 - 2 * η) / (1 - 2 * η))) := by ring
  rw [hexp]
  linarith

/-- **The blind side of the law.**  If `θ(1−2η) ≤ 1`, the second moment of the whole class `|a_n| ≤ εn^{−η}` is `O(ε² T log T)`. -/
theorem power_bounded_second_moment_le {θ η : ℝ} (hθ : 0 < θ) (hη0 : 0 ≤ η) (hη : η < 1 / 2)
    (hexp : θ * (1 - 2 * η) ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (a : ℕ → ℂ) (ε : ℝ) (N : ℕ), 0 ≤ ε → 1 ≤ N → (N : ℝ) ≤ T ^ θ →
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ ε * (n : ℝ) ^ (-η)) →
      (∫ t in T..(2 * T), ‖linePoly a N t‖ ^ 2) ≤ C * ε ^ 2 * (T * Real.log T) := by
  have hη' : 0 < 1 - 2 * η := by linarith
  refine ⟨1 + θ + 208 * (1 + 1 / (1 - 2 * η)), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with
    T hT hℓ a ε N hε hN hNT ha
  have hT0 : 0 < T := by linarith
  have hb := integral_linePoly_le_of_power_bound (T₁ := T) (T₂ := 2 * T) hε hη0 hη hN (by linarith) ha
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log N ≤ θ * Real.log T := by
    have h1 := Real.log_le_log (by linarith) hNT
    rwa [Real.log_rpow hT0] at h1
  have hNpow : (N : ℝ) ^ (1 - 2 * η) ≤ T := by
    calc (N : ℝ) ^ (1 - 2 * η) ≤ (T ^ θ) ^ (1 - 2 * η) :=
          Real.rpow_le_rpow (by positivity) hNT hη'.le
      _ = T ^ (θ * (1 - 2 * η)) := by rw [← Real.rpow_mul hT0.le]
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT hexp
      _ = T := Real.rpow_one T
  refine hb.trans ?_
  rw [mul_right_comm, mul_comm (1 + θ + 208 * (1 + 1 / (1 - 2 * η))) (ε ^ 2), mul_assoc (ε ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set ℓ := Real.log T with hℓdef
  have hTℓ : T ≤ T * ℓ := le_mul_of_one_le_right hT0.le hℓ
  have h1 : (2 * T - T) * (1 + Real.log N) ≤ T * ℓ + θ * (T * ℓ) := by
    have h2 : 1 + Real.log N ≤ 1 + θ * ℓ := by linarith
    calc (2 * T - T) * (1 + Real.log N) ≤ (2 * T - T) * (1 + θ * ℓ) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = T + θ * (T * ℓ) := by ring
      _ ≤ _ := by linarith
  have h2 : (N : ℝ) ^ (1 - 2 * η) / (1 - 2 * η) ≤ T * ℓ * (1 / (1 - 2 * η)) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (hNpow.trans hTℓ) (by positivity)
  have h3 : (1 : ℝ) ≤ T * ℓ := by nlinarith
  have hfin : (1 + θ + 208 * (1 + 1 / (1 - 2 * η))) * (T * ℓ) =
      T * ℓ + θ * (T * ℓ) + 208 * (T * ℓ + T * ℓ * (1 / (1 - 2 * η))) := by ring
  rw [hfin]
  linarith

/-! ### The resonant side -/

/-- The resonant weight `εn^{−η+iγ}`: the term of the explicit formula of a zero `1 − η + iγ`, scaled by `ε`. -/
def resonantWeight (ε η γ : ℝ) (n : ℕ) : ℂ :=
  ((ε * (n : ℝ) ^ (-η) : ℝ) : ℂ) * Complex.exp (((γ * Real.log n : ℝ) : ℂ) * I)

/-- Near the ordinate `γ`, the resonant polynomial has no cancellation. -/
theorem le_norm_linePoly_resonant {ε η γ t : ℝ} {N : ℕ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hN : 1 ≤ N)
    (ht : |γ - t| * Real.log N ≤ 1 / 2) :
    ε / 2 * (N : ℝ) ^ (1 / 2 - η) ≤ ‖linePoly (resonantWeight ε η γ) N t‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine le_trans ?_ (Complex.re_le_norm _)
  unfold linePoly
  rw [edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1)]
  unfold cdpoly
  rw [Complex.re_sum]
  have hterm : ∀ n ∈ Finset.Icc 1 N, ε / 2 * (N : ℝ) ^ (-(1 / 2 + η)) ≤
      (cdterm (resonantWeight ε η γ) (1 / 2) t n).re := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn2
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hval : cdterm (resonantWeight ε η γ) (1 / 2) t n =
        ((ε * (n : ℝ) ^ (-(1 / 2 + η)) : ℝ) : ℂ) * Complex.exp ((((γ - t) * Real.log n : ℝ) : ℂ) * I) := by
      unfold cdterm resonantWeight
      have hp : (n : ℝ) ^ (-(1 / 2 + η)) = (n : ℝ) ^ (-η) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
      rw [hp]
      have he : Complex.exp (((γ - t) * Real.log n : ℝ) * I) =
          Complex.exp (((γ * Real.log n : ℝ) : ℂ) * I) * Complex.exp (((-Real.log n * t : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [he]
      push_cast
      ring
    rw [hval, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    set x := (γ - t) * Real.log n with hx
    have hxabs : |x| ≤ 1 / 2 := by
      rw [hx, abs_mul, abs_of_nonneg hlogn]
      exact (mul_le_mul_of_nonneg_left (Real.log_le_log hn0 hnN) (abs_nonneg _)).trans ht
    have hcos : 1 / 2 ≤ Real.cos x := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
      have h2 : x ^ 2 ≤ (1 / 2) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hxabs 2
      linarith
    have hpow : (N : ℝ) ^ (-(1 / 2 + η)) ≤ (n : ℝ) ^ (-(1 / 2 + η)) :=
      Real.rpow_le_rpow_of_nonpos hn0 hnN (by linarith)
    calc ε / 2 * (N : ℝ) ^ (-(1 / 2 + η)) ≤ ε / 2 * (n : ℝ) ^ (-(1 / 2 + η)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ε * (n : ℝ) ^ (-(1 / 2 + η)) * (1 / 2) := by ring
      _ ≤ ε * (n : ℝ) ^ (-(1 / 2 + η)) * Real.cos x :=
          mul_le_mul_of_nonneg_left hcos (by positivity)
  have hsum := Finset.card_nsmul_le_sum _ _ _ hterm
  rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  refine le_trans (le_of_eq ?_) hsum
  have hp : (N : ℝ) * (N : ℝ) ^ (-(1 / 2 + η)) = (N : ℝ) ^ (1 / 2 - η) := by
    nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc ε / 2 * (N : ℝ) ^ (1 / 2 - η) = ε / 2 * ((N : ℝ) * (N : ℝ) ^ (-(1 / 2 + η))) := by rw [hp]
    _ = _ := by ring

/-- **The second moment of a resonance.** -/
theorem resonant_second_moment_ge {ε η γ T₁ T₂ : ℝ} {N : ℕ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (hN : 2 ≤ N)
    (h1 : T₁ + 1 / (2 * Real.log N) ≤ γ) (h2 : γ + 1 / (2 * Real.log N) ≤ T₂) :
    ε ^ 2 * (N : ℝ) ^ (1 - 2 * η) / (4 * Real.log N) ≤
      ∫ t in T₁..T₂, ‖linePoly (resonantWeight ε η γ) N t‖ ^ 2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN1
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (2 * Real.log N) := ⟨_, rfl⟩
  rw [← hδ] at h1 h2
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hcont : Continuous fun t => ‖linePoly (resonantWeight ε η γ) N t‖ ^ 2 :=
    (continuous_linePoly _ N).norm.pow 2
  have hmono := intervalIntegral.integral_mono_interval (μ := volume)
    (f := fun t => ‖linePoly (resonantWeight ε η γ) N t‖ ^ 2) (a := γ - δ) (b := γ + δ)
    (c := T₁) (d := T₂) (by linarith) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun t => by
      show 0 ≤ _
      positivity) (hcont.intervalIntegrable _ _)
  refine le_trans ?_ hmono
  have hsq : ((N : ℝ) ^ (1 / 2 - η)) ^ 2 = (N : ℝ) ^ (1 - 2 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hconst : (∫ _t in (γ - δ)..(γ + δ), (ε / 2 * (N : ℝ) ^ (1 / 2 - η)) ^ 2) ≤
      ∫ t in (γ - δ)..(γ + δ), ‖linePoly (resonantWeight ε η γ) N t‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hcont.intervalIntegrable _ _) fun t ht => ?_
    have hdist : |γ - t| * Real.log N ≤ 1 / 2 := by
      have h3 : |γ - t| ≤ δ := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      calc |γ - t| * Real.log N ≤ δ * Real.log N := mul_le_mul_of_nonneg_right h3 hlog.le
        _ = 1 / 2 := by
          rw [hδ]
          field_simp
    exact pow_le_pow_left₀ (by positivity) (le_norm_linePoly_resonant hε hη (by omega) hdist) 2
  refine le_trans (le_of_eq ?_) hconst
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_pow, hsq, hδ]
  field_simp
  ring

/-- **The resonant side of the law.**  If `θ(1−2η) > 1`, the resonance at any ordinate in `[T, 2T]` exceeds `T log T` by any constant. -/
theorem resonance_beats_every_constant {θ η ε : ℝ} (hθ : 0 < θ) (hη0 : 0 ≤ η) (hε : 0 < ε)
    (hexp : 1 < θ * (1 - 2 * η)) (A : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ γ : ℝ, T + 1 ≤ γ → γ ≤ 2 * T - 1 →
      A * (T * Real.log T) ≤ ∫ t in T..(2 * T), ‖linePoly (resonantWeight ε η γ) ⌊T ^ θ⌋₊ t‖ ^ 2 := by
  have hη' : 0 < 1 - 2 * η := by
    by_contra h
    have h1 : θ * (1 - 2 * η) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ.le (not_lt.mp h)
    linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = θ * (1 - 2 * η) - 1 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε ^ 2 / (16 * θ * (|A| + 1)) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hpow : Tendsto (fun T : ℝ => T ^ θ) atTop atTop := tendsto_rpow_atTop hθ
  filter_upwards [eventually_log_pow_mul_exp_le 2 (c := κ) (ε := ε') hκ0 hε'0,
    hpow.eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hsm hT4 hT2 hℓ γ hγ1 hγ2
  set ℓ := Real.log T with hℓdef
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊T ^ θ⌋₊ := ⟨_, rfl⟩
  rw [← hN]
  have hN2 : 2 ≤ N := by
    rw [hN]
    exact Nat.le_floor (by norm_num; linarith)
  have hNle : (N : ℝ) ≤ T ^ θ := by
    rw [hN]
    exact Nat.floor_le (by positivity)
  have hNge : T ^ θ / 2 ≤ (N : ℝ) := by
    have h1 := Nat.lt_floor_add_one (T ^ θ)
    rw [← hN] at h1
    linarith
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlogN0 : 0 < Real.log N := Real.log_pos hN1
  have hlogN : Real.log N ≤ θ * ℓ := by
    have h1 := Real.log_le_log (by linarith) hNle
    rwa [Real.log_rpow hT0] at h1
  have hlogN2 : 1 / 2 ≤ Real.log N := by
    have h1 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
    have h2 := Real.log_two_gt_d9
    linarith
  have hδ : 1 / (2 * Real.log N) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hres := resonant_second_moment_ge (ε := ε) (η := η) (γ := γ) (T₁ := T) (T₂ := 2 * T) hε.le hη0 hN2
    (by linarith) (by linarith)
  refine le_trans ?_ hres
  -- the size of the resonance
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = T ^ κ := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; positivity
  have hTe : Real.exp (-(κ * ℓ)) = X⁻¹ := by
    rw [hX, Real.rpow_def_of_pos hT0, Real.exp_neg, mul_comm]
  rw [hTe] at hsm
  have hℓ2 : ℓ ^ 2 ≤ ε' * X := by
    rw [← div_eq_mul_inv, div_le_iff₀ hX0] at hsm
    exact hsm
  have hNpow : X * T / 2 ≤ (N : ℝ) ^ (1 - 2 * η) := by
    have h1 : (T ^ θ / 2) ^ (1 - 2 * η) ≤ (N : ℝ) ^ (1 - 2 * η) :=
      Real.rpow_le_rpow (by positivity) hNge hη'.le
    refine le_trans ?_ h1
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hT0.le]
    have h2 : T ^ (θ * (1 - 2 * η)) = X * T := by
      rw [hX, ← Real.rpow_add_one hT0.ne', hκ]
      congr 1
      ring
    rw [h2]
    have h3 : (2 : ℝ) ^ (1 - 2 * η) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - 2 * η) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h3
  -- comparison
  have hA : A * (T * ℓ) ≤ (|A| + 1) * (T * ℓ) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) (by positivity)
  refine hA.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have hden : (|A| + 1) * (T * ℓ) * (4 * Real.log N) ≤ (|A| + 1) * (T * ℓ) * (4 * (θ * ℓ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine hden.trans ?_
  have hnum := mul_le_mul_of_nonneg_left hNpow (by positivity : 0 ≤ ε ^ 2)
  refine le_trans ?_ hnum
  have h5 : (|A| + 1) * (T * ℓ) * (4 * (θ * ℓ)) = T * ((|A| + 1) * 4 * θ) * ℓ ^ 2 := by ring
  rw [h5]
  have h6 := mul_le_mul_of_nonneg_left hℓ2 (by positivity : 0 ≤ T * ((|A| + 1) * 4 * θ))
  refine h6.trans (le_of_eq ?_)
  rw [hε']
  field_simp
  ring

/-- **The length–precision law.**  The threshold of the second moment at length `T^θ` is `θ(1−2η) = 1`, that is, `η = ½ − 1/(2θ)`. -/
theorem length_precision_law {θ η ε : ℝ} (hθ : 0 < θ) (hη0 : 0 ≤ η) (hη : η < 1 / 2) (hε : 0 < ε) :
    (η < 1 / 2 - 1 / (2 * θ) → ∀ A : ℝ, ∀ᶠ T : ℝ in atTop, ∀ γ : ℝ, T + 1 ≤ γ → γ ≤ 2 * T - 1 →
      A * (T * Real.log T) ≤ ∫ t in T..(2 * T), ‖linePoly (resonantWeight ε η γ) ⌊T ^ θ⌋₊ t‖ ^ 2) ∧
    (1 / 2 - 1 / (2 * θ) ≤ η → ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (a : ℕ → ℂ) (N : ℕ), 1 ≤ N →
      (N : ℝ) ≤ T ^ θ → (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ ε * (n : ℝ) ^ (-η)) →
      (∫ t in T..(2 * T), ‖linePoly a N t‖ ^ 2) ≤ C * ε ^ 2 * (T * Real.log T)) := by
  have hkey : 1 / (2 * θ) * (2 * θ) = 1 := by
    field_simp
  constructor
  · intro h A
    refine resonance_beats_every_constant hθ hη0 hε ?_ A
    have h1 : 1 / (2 * θ) < 1 / 2 - η := by linarith
    have h2 := mul_lt_mul_of_pos_right h1 (by positivity : 0 < 2 * θ)
    rw [hkey] at h2
    linarith
  · intro h
    have h1 : 1 / 2 - η ≤ 1 / (2 * θ) := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 2 * θ)
    rw [hkey] at h2
    obtain ⟨C, hC, hev⟩ := power_bounded_second_moment_le hθ hη0 hη (by linarith)
    exact ⟨C, hC, hev.mono fun T hT a N hN hNT ha => hT a ε N hε.le hN hNT ha⟩

/-- **Below the window every power is blind.**  At `θ ≤ 1` no `η ≥ 0` is seen. -/
theorem below_the_window_every_power_is_blind {θ η : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hη0 : 0 ≤ η)
    (hη : η < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (a : ℕ → ℂ) (ε : ℝ) (N : ℕ), 0 ≤ ε → 1 ≤ N → (N : ℝ) ≤ T ^ θ →
      (∀ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ ε * (n : ℝ) ^ (-η)) →
      (∫ t in T..(2 * T), ‖linePoly a N t‖ ^ 2) ≤ C * ε ^ 2 * (T * Real.log T) := by
  refine power_bounded_second_moment_le hθ hη0 hη ?_
  have h1 : 1 - 2 * η ≤ 1 := by linarith
  have h2 : 0 ≤ 1 - 2 * η := by linarith
  calc θ * (1 - 2 * η) ≤ 1 * 1 := mul_le_mul hθ1 h1 h2 zero_le_one
    _ = 1 := one_mul 1

end GaloisForLFunctions.ArithmeticProduction
