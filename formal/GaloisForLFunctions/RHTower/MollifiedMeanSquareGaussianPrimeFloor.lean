import GaloisForLFunctions.RHTower.ZetaGaussianTwistedMoment
import GaloisForLFunctions.RHTower.MollifiedMeanSquareUnmollifiedPrimeFloor

/-!
# Unmollified primes put a floor under every mollified mean square of length `T^θ`, `θ < 1`

Let `Ψ(s) = Σ_{d ≤ y} b_d d^{-s}` with `b_1 = 1`, `|b_d| ≤ 1`, and `c_n = Σ_{d ≤ y, d ∣ n} b_d`.
Every prime `p > y` has `c_p = 1`. The sharp-cutoff argument
(`exists_eventually_integral_normSq_zetaMollified_rightShift_ge`) pays `√T` per twist and so
only reaches `y ≤ T^{1/100}`. Here the twisted first moment is taken against Gaussian windows
`w_τ(t) = exp(−2(t−τ)²/H²)` (`norm_integral_twistedZeta_gauss_sub_diag_le`), whose errors are
Gaussian-small, and the windows are averaged over `τ` by Fubini. With `Q = Σ_{n ≤ M} c_n n^{-s}`:

* `∫ |Q(σ+it)|² w_τ ≤ √(πH²/2) (D + (Σ|c_n| n^{-σ})² e^{−H²/(8M²)})`, `D = Σ_{n ≤ M} |c_n|² n^{-2σ}`
  (`integral_normSq_edPoly_gauss_le`);
* `∫_{τ−R}^{τ+R} |ζΨ|² w_τ ≥ √(πH²/2) (D − 3ε)` (`gaussFloor_window`);
* `∫_T^{2T} |ζΨ|² ≥ (T − 2R)(D − 3ε)` (`integral_ge_of_gaussian_windows`).

With `y ≤ T^θ`, `M ≈ T^{θ+δ/4}`, `H = T^{θ+δ/2}`, `R = T^{θ+3δ/4}`, `δ = 1 − θ`, the primes in
`(y, M]` give `D ≥ 1 + (δ/8) e^{−2a}` on `Re s = 1/2 + a/log T`, and for every `a > 0`, `θ < 1`, all
large `T`, uniformly over all such mollifiers,

`∫_T^{2T} |ζΨ(1/2 + a/log T + it)|² dt ≥ (1 + (1−θ) e^{−2a}/16) T`
(`exists_eventually_integral_normSq_zetaMollified_rightShift_ge_of_lt_one`).
-/

noncomputable section

open Complex MeasureTheory Set Filter

namespace RHTower

/-! ## The Gaussian mean value of a Dirichlet polynomial -/

theorem gaussFourier_zero_shift (H ω τ t : ℝ) :
    gaussFourier H 0 ω τ t =
      Complex.exp (I * ((t * ω : ℝ) : ℂ)) * ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ) := by
  unfold gaussFourier
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  have hI : I ^ 2 = -1 := Complex.I_sq
  push_cast
  linear_combination (2 / (H : ℂ) ^ 2 * ((t : ℂ) - τ) ^ 2) * hI

theorem conj_natCast_cpow_line (σ t : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) =
      ((n : ℝ) : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 2 * (σ : ℂ)) := by
  have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj ((n : ℝ) : ℂ) (-((σ : ℂ) + (t : ℂ) * I)) harg
  rw [Complex.conj_ofReal] at h
  rw [← h]
  congr 1
  apply Complex.ext <;> simp
  ring

theorem normSq_edPoly_gauss_eq (c : ℕ → ℂ) (M : ℕ) (σ τ H t : ℝ) :
    (((‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ)) : ℂ) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, c m * (starRingEnd ℂ) (c n) *
        (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
          gaussFourier H 0 (Real.log n - Real.log m) τ t := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hQ : ((‖edPoly c (Finset.Icc 1 M) s‖ ^ 2 : ℝ) : ℂ) =
      edPoly c (Finset.Icc 1 M) s * (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) s) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Complex.ofReal_mul, hQ]
  unfold edPoly
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hexp : ((m : ℝ) : ℂ) ^ (-s) * ((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ)) =
      (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (I * ((t * (Real.log n - Real.log m) : ℝ) : ℂ)) := by
    rw [ofReal_natCast_cpow_eq_exp hm1, ofReal_natCast_cpow_eq_exp hn1, Real.rpow_def_of_pos hm0,
      Real.rpow_def_of_pos hn0, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hs]
    push_cast
    ring
  rw [gaussFourier_zero_shift]
  calc c m * ((m : ℝ) : ℂ) ^ (-s) * (starRingEnd ℂ) (c n * ((n : ℝ) : ℂ) ^ (-s)) *
        ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ)
      = c m * (starRingEnd ℂ) (c n) *
          (((m : ℝ) : ℂ) ^ (-s) * ((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ))) *
            ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ) := by
        rw [map_mul, hs, conj_natCast_cpow_line]; ring
    _ = _ := by rw [hexp]; ring

/-- **Gaussian mean value theorem.** -/
theorem integral_normSq_edPoly_gauss_le (c : ℕ → ℂ) {M : ℕ} (hM : 1 ≤ M) (σ τ : ℝ) {H : ℝ}
    (hH : 0 < H) :
    ∫ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) ≤
      Real.sqrt (Real.pi * H ^ 2 / 2) * (∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) +
        (∑ n ∈ Finset.Icc 1 M, ‖c n‖ * (n : ℝ) ^ (-σ)) ^ 2 *
          Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2)))) := by
  classical
  set K : ℝ := Real.sqrt (Real.pi * H ^ 2 / 2) with hK
  set E : ℝ := Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2))) with hE
  set a : ℕ → ℝ := fun n => ‖c n‖ * (n : ℝ) ^ (-σ) with ha
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have ha0 : ∀ n, 0 ≤ a n := fun n => by simp only [ha]; positivity
  have hint : ∀ m n : ℕ, Integrable (fun t : ℝ => c m * (starRingEnd ℂ) (c n) *
      (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        gaussFourier H 0 (Real.log n - Real.log m) τ t) :=
    fun m n => (integrable_gaussFourier hH _ _ _).const_mul _
  have hval : ((∫ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, c m * (starRingEnd ℂ) (c n) *
        (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
          ∫ t : ℝ, gaussFourier H 0 (Real.log n - Real.log m) τ t := by
    rw [← integral_complex_ofReal]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun t => normSq_edPoly_gauss_eq c M σ τ H t)]
    rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => hint m n]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum _ fun n _ => hint m n]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact integral_const_mul _ _
  have hnonneg : 0 ≤ ∫ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
      Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) := integral_nonneg fun t => by positivity
  have hpair : ∀ m ∈ Finset.Icc 1 M, ∀ n ∈ Finset.Icc 1 M,
      ‖c m * (starRingEnd ℂ) (c n) * (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
          ∫ t : ℝ, gaussFourier H 0 (Real.log n - Real.log m) τ t‖ ≤
        K * ((if m = n then a m * a n else 0) + E * (a m * a n)) := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), norm_integral_gaussFourier hH]
    have hsimp : 2 / H ^ 2 * (0 : ℝ) ^ 2 - (Real.log n - Real.log m + 4 * 0 / H ^ 2) ^ 2 *
        H ^ 2 / 8 = -((Real.log n - Real.log m) ^ 2 * H ^ 2 / 8) := by ring
    rw [hsimp]
    have hprod : ‖c m‖ * ‖c n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) = a m * a n := by
      simp only [ha]; ring
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, sub_self]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div,
        neg_zero, Real.exp_zero, mul_one]
      rw [hprod]
      have : 0 ≤ E * (a m * a m) := mul_nonneg hE0 (mul_nonneg (ha0 m) (ha0 m))
      nlinarith [mul_nonneg (ha0 m) (ha0 m)]
    · rw [if_neg hmn, zero_add]
      have hsp := HTGeometry.inv_max_le_abs_log_sub_log_nat
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1 (Ne.symm hmn)
      have hmax : max (n : ℝ) (m : ℝ) ≤ M := max_le (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
        (by exact_mod_cast (Finset.mem_Icc.mp hm).2)
      have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
      have hω : 1 / (M : ℝ) ≤ |Real.log n - Real.log m| :=
        le_trans (one_div_le_one_div_of_le (lt_max_of_lt_left hn0) hmax) hsp
      have hω2 : (1 / (M : ℝ)) ^ 2 ≤ (Real.log n - Real.log m) ^ 2 := by
        rw [← sq_abs (Real.log n - Real.log m)]
        exact pow_le_pow_left₀ (by positivity) hω 2
      have hexp : Real.exp (-((Real.log n - Real.log m) ^ 2 * H ^ 2 / 8)) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        have : H ^ 2 / (8 * (M : ℝ) ^ 2) = (1 / (M : ℝ)) ^ 2 * H ^ 2 / 8 := by field_simp
        rw [this, neg_le_neg_iff]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hω2 (by positivity))
          (by norm_num)
      calc ‖c m‖ * ‖c n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) *
            (K * Real.exp (-((Real.log n - Real.log m) ^ 2 * H ^ 2 / 8)))
          = K * (a m * a n) * Real.exp (-((Real.log n - Real.log m) ^ 2 * H ^ 2 / 8)) := by
            rw [hprod]; ring
        _ ≤ K * (a m * a n) * E :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg hK0 (mul_nonneg (ha0 m) (ha0 n)))
        _ = K * (E * (a m * a n)) := by ring
  have hdiag : ∀ m ∈ Finset.Icc 1 M,
      ∑ n ∈ Finset.Icc 1 M, K * ((if m = n then a m * a n else 0) + E * (a m * a n)) =
        K * (‖c m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)) + K * E * (a m * ∑ n ∈ Finset.Icc 1 M, a n) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hm]
    congr 1
    · simp only [ha]
      have : (m : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) = (m : ℝ) ^ (-2 * σ) := by
        rw [← Real.rpow_add hm0]; congr 1; ring
      rw [← this]; ring
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
  calc ∫ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2)
      = ‖((∫ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, c m * (starRingEnd ℂ) (c n) *
          (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
            ∫ t : ℝ, gaussFourier H 0 (Real.log n - Real.log m) τ t‖ := by rw [hval]
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          K * ((if m = n then a m * a n else 0) + E * (a m * a n)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => hpair m hm n hn))
    _ = K * (∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) +
          (∑ n ∈ Finset.Icc 1 M, a n) ^ 2 * E) := by
        rw [Finset.sum_congr rfl hdiag, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.sum_mul, sq]
        ring

/-! ## One window -/

/-- **The windowed pairing.** `∫_{τ−R}^{τ+R} ζΨ · conj(Q) · w_τ` is `√(πH²/2) D` up to
Gaussian-small errors. -/
theorem norm_window_pairing_sub_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) {y M : ℕ}
    (hM : 1 ≤ M) {b : ℕ → ℂ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) {T H R τ : ℝ} (hT : 4 ≤ T)
    (hH : 0 < H) (hHM : 24 * (M : ℝ) ≤ H ^ 2) (hR : 0 ≤ R) (hτ1 : T ≤ τ - R)
    (hτ2 : τ + R ≤ 2 * T) :
    ‖(∫ t in (τ - R)..(τ + R), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (edPoly (mollifiedZetaCoeff b y) (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) *
          ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ)) -
        ((Real.sqrt (Real.pi * H ^ 2 / 2) *
          ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) : ℝ) : ℂ)‖ ≤
      (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) +
        2 * M * gaussTwistError H R M) := by
  classical
  set c : ℕ → ℂ := mollifiedZetaCoeff b y with hc
  set K : ℝ := Real.sqrt (Real.pi * H ^ 2 / 2) with hK
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) with hDdef
  set W : ℝ → ℂ := fun t => ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ) with hW
  have hs : ∀ n ∈ Finset.Icc 1 M, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hsy : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hWc : Continuous W := by simp only [hW]; fun_prop
  have hcont : ∀ d ∈ Finset.Icc 1 y, ∀ n ∈ Finset.Icc 1 M,
      Continuous (fun t : ℝ => b d * (starRingEnd ℂ) (c n) *
        (twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t)) := by
    intro d hd n hn
    refine continuous_const.mul ((continuous_iff_continuousAt.mpr fun t => ?_).mul hWc)
    exact ContinuousAt.comp (g := twistedZeta σ d n) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_twistedZeta σ (hsy d hd) (hs n hn) (hline t)).continuousAt (by fun_prop)
  have hcorr : (∫ t in (τ - R)..(τ + R), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) * W t) =
      ∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) *
        ∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t := by
    have hpt : ∀ t : ℝ, riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) * W t =
        ∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) *
          (twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t) := by
      intro t
      rw [zeta_mul_edPoly_mul_conj_eq_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    simp only [hpt]
    rw [intervalIntegral.integral_finsetSum (f := fun d t => ∑ n ∈ Finset.Icc 1 M,
      b d * (starRingEnd ℂ) (c n) * (twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t))
      fun d hd => (continuous_finsetSum _ fun n hn => hcont d hd n hn).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun n t =>
      b d * (starRingEnd ℂ) (c n) * (twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t))
      fun n hn => (hcont d hd n hn).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  set diag : ℕ → ℕ → ℂ := fun d n =>
    if d ∣ n then (((n : ℝ) ^ (-2 * σ) * K : ℝ) : ℂ) else 0 with hdiagdef
  have hmain : ∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M,
      b d * (starRingEnd ℂ) (c n) * diag d n = ((K * D : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    have hn : ∀ n ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 y, b d * (starRingEnd ℂ) (c n) * diag d n =
        (((‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) * K : ℝ) : ℂ) := by
      intro n _
      have h1 : ∑ d ∈ Finset.Icc 1 y, b d * (starRingEnd ℂ) (c n) * diag d n =
          (starRingEnd ℂ) (c n) * (((n : ℝ) ^ (-2 * σ) * K : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), b d := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [hdiagdef]
        split_ifs <;> ring
      rw [h1]
      have h2 : ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), b d = c n := rfl
      rw [h2, mul_comm ((starRingEnd ℂ) (c n)), mul_assoc, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [Finset.sum_congr rfl hn, ← Complex.ofReal_sum, hDdef, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hterm : ∀ d ∈ Finset.Icc 1 y, ∀ n ∈ Finset.Icc 1 M,
      ‖b d * (starRingEnd ℂ) (c n) *
          (∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t) -
        b d * (starRingEnd ℂ) (c n) * diag d n‖ ≤
      y * (27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) + 2 * M * gaussTwistError H R M) := by
    intro d hd n hn
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hHn : 24 * (n : ℝ) ≤ H ^ 2 := by linarith
    have h1 := norm_integral_twistedZeta_gauss_sub_diag_le hσ (by linarith) (hsy d hd) (hs n hn)
      hT hH hHn hR hτ1 hτ2
    have hdiag_eq : diag d n = (if d ∣ n then (((n : ℝ) ^ (-2 * σ) *
        Real.sqrt (Real.pi * H ^ 2 / 2) : ℝ) : ℂ) else 0) := rfl
    rw [← hdiag_eq] at h1
    have hgte : gaussTwistError H R n ≤ gaussTwistError H R M := by
      unfold gaussTwistError
      have : Real.exp (1 - H ^ 2 / (128 * (n : ℝ) ^ 2)) ≤ Real.exp (1 - H ^ 2 / (128 * (M : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have : H ^ 2 / (128 * (M : ℝ) ^ 2) ≤ H ^ 2 / (128 * (n : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by nlinarith)
        linarith
      have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg (Real.pi * H ^ 2 / 2))
      linarith
    have h2 : 27 * Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) + 2 * n * gaussTwistError H R n ≤
        27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) + 2 * M * gaussTwistError H R M := by
      have hg0 : 0 ≤ gaussTwistError H R n := by unfold gaussTwistError; positivity
      have hs0 : 0 ≤ Real.sqrt T * Real.exp (1 - R ^ 2 / H ^ 2) := by positivity
      have hA : 27 * Real.sqrt T * n * Real.exp (1 - R ^ 2 / H ^ 2) ≤
          27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) := by nlinarith
      have hB : 2 * n * gaussTwistError H R n ≤ 2 * M * gaussTwistError H R M := by
        have := mul_le_mul hnM hgte hg0 (by linarith)
        linarith
      linarith
    rw [← mul_sub, norm_mul, norm_mul, Complex.norm_conj]
    calc ‖b d‖ * ‖c n‖ * ‖(∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t) -
          diag d n‖ ≤ 1 * y * (27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) +
            2 * M * gaussTwistError H R M) := by
          gcongr
          · exact hb d hd
          · exact norm_mollifiedZetaCoeff_le hb n
          · exact h1.trans h2
      _ = _ := by ring
  have herr : ‖(∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) *
        ∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t) -
        ((K * D : ℝ) : ℂ)‖ ≤
      (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) +
        2 * M * gaussTwistError H R M) := by
    rw [← hmain, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ Finset.Icc 1 y, ‖(∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) *
          ∫ t in (τ - R)..(τ + R), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) * W t) -
          ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) * diag d n‖
        ≤ ∑ _d ∈ Finset.Icc 1 y, ∑ _n ∈ Finset.Icc 1 M, (y : ℝ) *
            (27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) + 2 * M * gaussTwistError H R M) := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [← Finset.sum_sub_distrib]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => hterm d hd n hn)
      _ = _ := by simp; ring
  rw [hcorr]
  exact herr

/-- The closing algebra of one window: from `K(D−ε) ≤ P ≤ √(K(D+ε)X)` get `X ≥ K(D−3ε)`. -/
theorem gaussFloor_window_algebra {K D ε P X : ℝ} (hK : 0 < K) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hP : K * (D - ε) ≤ P) (hPX : P ≤ Real.sqrt (K * (D + ε) * X))
    (hX : 0 ≤ X) : K * (D - 3 * ε) ≤ X := by
  have hDε : 0 ≤ D - ε := by linarith
  have h0 : 0 ≤ K * (D - ε) := mul_nonneg hK.le hDε
  have hsq : (K * (D - ε)) ^ 2 ≤ K * (D + ε) * X :=
    (Real.le_sqrt h0 (by positivity)).mp (hP.trans hPX)
  have h1 : K * (D - ε) ^ 2 ≤ (D + ε) * X := by
    have : K * (K * (D - ε) ^ 2) ≤ K * ((D + ε) * X) := by nlinarith
    exact le_of_mul_le_mul_left this hK
  have h2 : (D - 3 * ε) * (D + ε) ≤ (D - ε) ^ 2 := by nlinarith
  have h3 : K * (D - 3 * ε) * (D + ε) ≤ X * (D + ε) := by nlinarith
  exact le_of_mul_le_mul_right h3 (by linarith)

/-- **One Gaussian window.** If the pairing and mean-value errors are at most `ε ≤ 1/2`
(relative to the window mass) and `D ≥ 1`, then `∫_{τ−R}^{τ+R} |ζΨ|² w_τ ≥ √(πH²/2)(D − 3ε)`. -/
theorem gaussFloor_window {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) {y M : ℕ} (hM : 1 ≤ M)
    {b : ℕ → ℂ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) {T H R τ ε : ℝ} (hT : 4 ≤ T) (hH : 0 < H)
    (hHM : 24 * (M : ℝ) ≤ H ^ 2) (hR : 0 ≤ R) (hτ1 : T ≤ τ - R) (hτ2 : τ + R ≤ 2 * T)
    (hD1 : 1 ≤ ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hE1 : (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) +
      2 * M * gaussTwistError H R M) ≤ Real.sqrt (Real.pi * H ^ 2 / 2) * ε)
    (hE2 : (∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ * (n : ℝ) ^ (-σ)) ^ 2 *
      Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2))) ≤ ε) :
    Real.sqrt (Real.pi * H ^ 2 / 2) *
        ((∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) - 3 * ε) ≤
      ∫ t in (τ - R)..(τ + R), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) := by
  set c : ℕ → ℂ := mollifiedZetaCoeff b y with hc
  set K : ℝ := Real.sqrt (Real.pi * H ^ 2 / 2) with hK
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) with hDdef
  set w : ℝ → ℝ := fun t => Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) with hw
  have hK0 : 0 < K := Real.sqrt_pos.mpr (by positivity)
  have hs : ∀ n ∈ Finset.Icc 1 M, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hsy : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hZc : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta (hline t)).continuousAt (by fun_prop)).mul
      (((differentiable_edPoly b hsy).continuous.comp (by fun_prop)).continuousAt)
  have hQc : Continuous fun t : ℝ => edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I) :=
    (differentiable_edPoly c hs).continuous.comp (by fun_prop)
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hw0 : ∀ t, 0 ≤ w t := fun t => (Real.exp_pos _).le
  have hsqw : ∀ t, Real.sqrt (w t) ^ 2 = w t := fun t => Real.sq_sqrt (hw0 t)
  set f : ℝ → ℂ := fun t => edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I) *
    ((Real.sqrt (w t) : ℝ) : ℂ) with hf
  set g : ℝ → ℂ := fun t => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
    edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) * ((Real.sqrt (w t) : ℝ) : ℂ) with hg
  have hfc : Continuous f := hQc.mul (Complex.continuous_ofReal.comp (hwc.sqrt))
  have hgc : Continuous g := hZc.mul (Complex.continuous_ofReal.comp (hwc.sqrt))
  have hnf : ∀ t, ‖f t‖ ^ 2 = ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
    intro t
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsqw]
  have hng : ∀ t, ‖g t‖ ^ 2 = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
    intro t
    simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsqw]
  -- the mean value on the window
  have hMVT := integral_normSq_edPoly_gauss_le c hM σ τ hH
  have hfS : ∫ t in (τ - R)..(τ + R), ‖f t‖ ^ 2 ≤ K * (D + ε) := by
    simp only [hnf]
    have hint : Integrable fun t : ℝ => ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
      have hb2 : Integrable w := by
        simp only [hw]
        exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 / H ^ 2)).comp_sub_right τ
      obtain ⟨C, hC⟩ : ∃ C, ∀ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C := by
        refine ⟨(∑ n ∈ Finset.Icc 1 M, ‖c n‖ * (n : ℝ) ^ (-σ)) ^ 2, fun t => ?_⟩
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        unfold edPoly
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        rw [norm_mul, norm_ofReal_natCast_cpow (hs n hn)]
        simp
      refine (hb2.const_mul C).mono' ((hQc.norm.pow 2).mul hwc).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hw0 t))]
      exact mul_le_mul_of_nonneg_right (hC t) (hw0 t)
    calc ∫ t in (τ - R)..(τ + R), ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t
        ≤ ∫ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => by
            have := hw0 t; positivity)
      _ ≤ K * (D + (∑ n ∈ Finset.Icc 1 M, ‖c n‖ * (n : ℝ) ^ (-σ)) ^ 2 *
            Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2)))) := hMVT
      _ ≤ K * (D + ε) := by gcongr
  -- Cauchy–Schwarz
  have hSA : 0 < K * (D + ε) := by
    have : 0 < D + ε := by linarith
    positivity
  have hcs := GaloisForLFunctions.HTGeometry.integral_norm_mul_le_sqrt_of_bound
    (A := τ - R) (B := τ + R) (by linarith) hfc hgc hSA hfS
  have hgS : ∫ t in (τ - R)..(τ + R), ‖g t‖ ^ 2 =
      ∫ t in (τ - R)..(τ + R), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
    simp only [hng]
  rw [hgS] at hcs
  -- the pairing
  have hpair := norm_window_pairing_sub_le hσ hσ1 hM hb hT hH hHM hR hτ1 hτ2
  rw [← hc, ← hDdef] at hpair
  have hP : K * (D - ε) ≤ ∫ t in (τ - R)..(τ + R), ‖f t‖ * ‖g t‖ := by
    have h1 : ‖((K * D : ℝ) : ℂ)‖ - K * ε ≤
        ‖∫ t in (τ - R)..(τ + R), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) *
          ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ)‖ := by
      have := norm_sub_norm_le ((K * D : ℝ) : ℂ) (∫ t in (τ - R)..(τ + R),
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) * edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) *
          ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ))
      rw [norm_sub_rev] at this
      linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have h2 : K * (D - ε) = K * D - K * ε := by ring
    rw [h2]
    refine h1.trans ?_
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hf, hg, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.abs_exp]
    have hwt : Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) = Real.sqrt (w t) * Real.sqrt (w t) :=
      (Real.mul_self_sqrt (hw0 t)).symm
    rw [hwt]
    ring
  have hX0 : 0 ≤ ∫ t in (τ - R)..(τ + R), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => by have := hw0 t; positivity
  exact gaussFloor_window_algebra hK0 hD1 hε0 hε hP hcs hX0

/-! ## Averaging the windows -/

/-- **Fubini over the window centres.** If every Gaussian window centred in `[T+R, 2T−R]` carries
`√(πH²/2) A` of the mass of `Z`, then `∫_T^{2T} Z ≥ (T − 2R) A`. -/
theorem integral_ge_of_gaussian_windows {Z : ℝ → ℝ} (hZ : Continuous Z) (hZ0 : ∀ t, 0 ≤ Z t)
    {T R H A : ℝ} (hH : 0 < H) (hTR : T + R ≤ 2 * T - R) (hR : 0 ≤ R)
    (hwin : ∀ τ ∈ Icc (T + R) (2 * T - R), Real.sqrt (Real.pi * H ^ 2 / 2) * A ≤
      ∫ t in T..(2 * T), Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2)) :
    (T - 2 * R) * A ≤ ∫ t in T..(2 * T), Z t := by
  set K : ℝ := Real.sqrt (Real.pi * H ^ 2 / 2) with hK
  have hK0 : 0 < K := Real.sqrt_pos.mpr (by positivity)
  set F : ℝ → ℝ → ℝ := fun τ t => Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) with hF
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF]
    exact (hZ.comp continuous_snd).mul (by fun_prop)
  have hT : T ≤ 2 * T := by linarith
  -- integrate the window bound over the centres
  have hinner_c : Continuous fun τ => ∫ t in T..(2 * T), F τ t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc T (2 * T)
  have h1 : (2 * T - R - (T + R)) * (K * A) ≤ ∫ τ in (T + R)..(2 * T - R), ∫ t in T..(2 * T), F τ t := by
    have := intervalIntegral.integral_mono_on (μ := volume) hTR intervalIntegrable_const
      (hinner_c.intervalIntegrable _ _) fun τ hτ => hwin τ hτ
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  -- swap
  have hswap : (∫ τ in (T + R)..(2 * T - R), ∫ t in T..(2 * T), F τ t) =
      ∫ t in T..(2 * T), ∫ τ in (T + R)..(2 * T - R), F τ t := by
    apply intervalIntegral_intervalIntegral_swap
    refine (hFc.continuousOn.integrableOn_compact (μ := volume)
      ((isCompact_uIcc (a := T + R) (b := 2 * T - R)).prod
        (isCompact_uIcc (a := T) (b := 2 * T)))).mono_set ?_
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  -- the inner Gaussian mass
  have hmass : ∀ t, ∫ τ in (T + R)..(2 * T - R), Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) ≤ K := by
    intro t
    have hint : Integrable fun τ : ℝ => Real.exp (-(2 / H ^ 2) * (τ - t) ^ 2) :=
      (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 / H ^ 2)).comp_sub_right t
    have heq : (fun τ : ℝ => Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2)) =
        fun τ : ℝ => Real.exp (-(2 / H ^ 2) * (τ - t) ^ 2) := by
      funext τ; congr 2; ring
    rw [heq, intervalIntegral.integral_of_le hTR]
    refine (setIntegral_le_integral hint (Filter.Eventually.of_forall fun τ => (Real.exp_pos _).le)).trans
      (le_of_eq ?_)
    rw [integral_sub_right_eq_self (fun τ => Real.exp (-(2 / H ^ 2) * τ ^ 2)) t, integral_gaussian,
      hK]
    congr 1
    field_simp
  have h2 : (∫ t in T..(2 * T), ∫ τ in (T + R)..(2 * T - R), F τ t) ≤ ∫ t in T..(2 * T), Z t * K := by
    have hc1 : Continuous fun t => ∫ τ in (T + R)..(2 * T - R), F τ t := by
      have : Continuous (Function.uncurry fun t τ => F τ t) := by
        simp only [hF]
        exact (hZ.comp continuous_fst).mul (by fun_prop)
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
    refine intervalIntegral.integral_mono_on hT (hc1.intervalIntegrable _ _)
      ((hZ.mul continuous_const).intervalIntegrable _ _) fun t _ => ?_
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hmass t) (hZ0 t)
  have h3 : (∫ t in T..(2 * T), Z t * K) = K * ∫ t in T..(2 * T), Z t := by
    rw [intervalIntegral.integral_mul_const, mul_comm]
  have htot : K * ((T - 2 * R) * A) ≤ K * ∫ t in T..(2 * T), Z t := by
    have : (2 * T - R - (T + R)) * (K * A) = K * ((T - 2 * R) * A) := by ring
    rw [← this]
    linarith [h1, h2, h3, hswap]
  exact le_of_mul_le_mul_left htot hK0

/-! ## Asymptotics -/

theorem eventually_exp_mul_exp_neg_exp_le {k C δ ε : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ L in atTop, Real.exp (k * L) * Real.exp (-(C * Real.exp (δ * L))) ≤ ε := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / δ) C hC
  have h2 : Tendsto (fun L : ℝ => Real.exp (δ * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hδ)
  have h3 := (h1.comp h2).eventually (Iic_mem_nhds hε)
  filter_upwards [h3] with L hL
  simp only [Function.comp] at hL
  have hpow : Real.exp (δ * L) ^ (k / δ) = Real.exp (k * L) := by
    rw [← Real.exp_mul]; congr 1; field_simp
  rw [hpow, neg_mul] at hL
  exact hL

end RHTower

namespace RHTower

/-- The unmollified primes in `(y, M]` give `D ≥ 1 + ((1−θ)/8) e^{−2a}` at `T = e^L`,
`σ = 1/2 + a/L`, `y ≤ e^{θL}`, `M ≈ e^{(θ + (1−θ)/4) L}`. -/
theorem gaussFloor_D_ge {b : ℕ → ℂ} {y M : ℕ} {L a θ : ℝ} (ha : 0 < a) (hθ1 : θ < 1)
    (hL0 : 0 < L)
    (hLK : 8 * (Real.log 2 + 2 * |mertensPrimeConst|) ≤ (1 - θ) * L)
    (hy : 1 ≤ y) (hb1 : b 1 = 1) (hyM : y ≤ M) (hM2 : 2 ≤ M)
    (hMle : (M : ℝ) ≤ Real.exp ((θ + (1 - θ) / 4) * L))
    (hMge : Real.exp ((θ + (1 - θ) / 4) * L) / 2 ≤ M)
    (hyle : (y : ℝ) ≤ Real.exp (θ * L)) :
    1 + (1 - θ) / 8 * Real.exp (-(2 * a)) ≤
      ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
  have hσ12 : 1 / 2 ≤ 1 / 2 + a / L := by have := div_pos ha hL0; linarith
  have hDge := sum_normSq_mollifiedZetaCoeff_ge (b := b) hy hyM hM2 hb1 hσ12
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hpowM : Real.exp (-(2 * a)) ≤ (M : ℝ) ^ (1 - 2 * (1 / 2 + a / L)) := by
    have h1 : Real.exp ((θ + (1 - θ) / 4) * L) ^ (1 - 2 * (1 / 2 + a / L)) ≤
        (M : ℝ) ^ (1 - 2 * (1 / 2 + a / L)) :=
      Real.rpow_le_rpow_of_nonpos hMpos hMle (by have := div_pos ha hL0; linarith)
    have h2 : Real.exp ((θ + (1 - θ) / 4) * L) ^ (1 - 2 * (1 / 2 + a / L)) =
        Real.exp (-(2 * a * (θ + (1 - θ) / 4))) := by
      rw [← Real.exp_mul]; congr 1; field_simp; ring
    have h3 : Real.exp (-(2 * a)) ≤ Real.exp (-(2 * a * (θ + (1 - θ) / 4))) := by
      apply Real.exp_le_exp.mpr
      have : θ + (1 - θ) / 4 ≤ 1 := by linarith
      nlinarith
    linarith
  have hlogMle : Real.log (M : ℝ) ≤ L := by
    have := Real.log_le_log hMpos hMle
    rw [Real.log_exp] at this
    nlinarith
  have hlogMge : (θ + (1 - θ) / 4) * L - Real.log 2 ≤ Real.log (M : ℝ) := by
    have := Real.log_le_log (by positivity) hMge
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
  have hlogy : Real.log (y : ℝ) ≤ θ * L := by
    have := Real.log_le_log hypos hyle
    rwa [Real.log_exp] at this
  have hlogM0 : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hratio : (1 - θ) / 8 ≤
      (Real.log M - Real.log y - 2 * mertensPrimeConst) / Real.log M := by
    rw [le_div_iff₀ hlogM0]
    have hK : mertensPrimeConst ≤ |mertensPrimeConst| := le_abs_self _
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (1 - θ) / 8 * Real.log M ≤ (1 - θ) / 8 * L :=
      mul_le_mul_of_nonneg_left hlogMle (by linarith)
    nlinarith
  have h := mul_le_mul hpowM hratio (by linarith) (Real.rpow_nonneg hMpos.le _)
  linarith

/-- The Gaussian-small errors at `T = e^L`, `H = e^{(θ+δ/2)L}`, `R = e^{(θ+3δ/4)L}`, `δ = 1−θ`. -/
theorem gaussFloor_error_bounds {θ L ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hL : 0 ≤ L)
    {y M : ℕ} (hy : 1 ≤ y) (hyle : (y : ℝ) ≤ Real.exp (θ * L)) (hM1 : 1 ≤ M)
    (hMle : (M : ℝ) ≤ Real.exp ((θ + (1 - θ) / 4) * L))
    (hsup : 99 * (Real.exp (5 * L) *
      Real.exp (-(1 / 128 * Real.exp ((1 - θ) / 2 * L)))) ≤ ε)
    {b : ℕ → ℂ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) {σ : ℝ} (hσ : 0 ≤ σ) :
    (y : ℝ) ^ 2 * M * (27 * Real.sqrt (Real.exp L) * M *
        Real.exp (1 - Real.exp ((θ + 3 * (1 - θ) / 4) * L) ^ 2 /
          Real.exp ((θ + (1 - θ) / 2) * L) ^ 2) +
        2 * M * gaussTwistError (Real.exp ((θ + (1 - θ) / 2) * L))
          (Real.exp ((θ + 3 * (1 - θ) / 4) * L)) M) ≤
      Real.sqrt (Real.pi * Real.exp ((θ + (1 - θ) / 2) * L) ^ 2 / 2) * ε ∧
    (∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ * (n : ℝ) ^ (-σ)) ^ 2 *
        Real.exp (-(Real.exp ((θ + (1 - θ) / 2) * L) ^ 2 / (8 * (M : ℝ) ^ 2))) ≤ ε := by
  set H : ℝ := Real.exp ((θ + (1 - θ) / 2) * L) with hH
  set R : ℝ := Real.exp ((θ + 3 * (1 - θ) / 4) * L) with hR
  set u : ℝ := Real.exp ((1 - θ) / 2 * L) with hu
  set ξ : ℝ := Real.exp (-(1 / 128 * u)) with hξ
  set K : ℝ := Real.sqrt (Real.pi * H ^ 2 / 2) with hK
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hξ0 : 0 ≤ ξ := (Real.exp_pos _).le
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hH1 : 1 ≤ H := Real.one_le_exp (mul_nonneg (by linarith) hL)
  have hH2 : H ^ 2 = Real.exp (2 * ((θ + (1 - θ) / 2) * L)) := by
    rw [hH, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hR2 : R ^ 2 = Real.exp (2 * ((θ + 3 * (1 - θ) / 4) * L)) := by
    rw [hR, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hM2 : (M : ℝ) ^ 2 ≤ Real.exp (2 * ((θ + (1 - θ) / 4) * L)) := by
    calc (M : ℝ) ^ 2 ≤ Real.exp ((θ + (1 - θ) / 4) * L) ^ 2 := pow_le_pow_left₀ hMpos.le hMle 2
      _ = _ := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  -- the two Gaussian ratios
  have hRH : R ^ 2 / H ^ 2 = u := by
    rw [hR2, hH2, ← Real.exp_sub, hu]; congr 1; ring
  have hHM : u / 128 ≤ H ^ 2 / (128 * (M : ℝ) ^ 2) := by
    have h1 : H ^ 2 / (128 * Real.exp (2 * ((θ + (1 - θ) / 4) * L))) ≤ H ^ 2 / (128 * (M : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h2 : H ^ 2 / (128 * Real.exp (2 * ((θ + (1 - θ) / 4) * L))) = u / 128 := by
      have hsplit : Real.exp (2 * ((θ + (1 - θ) / 2) * L)) =
          u * Real.exp (2 * ((θ + (1 - θ) / 4) * L)) := by
        rw [hu, ← Real.exp_add]; congr 1; ring
      rw [hH2, hsplit]
      field_simp
    linarith
  have hexpR : Real.exp (1 - R ^ 2 / H ^ 2) ≤ 3 * ξ := by
    rw [hRH, Real.exp_sub, hξ, div_eq_mul_inv, ← Real.exp_neg]
    refine mul_le_mul he3 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by norm_num)
  have hexpM : Real.exp (1 - H ^ 2 / (128 * (M : ℝ) ^ 2)) ≤ 3 * ξ := by
    have : Real.exp (1 - H ^ 2 / (128 * (M : ℝ) ^ 2)) ≤ Real.exp 1 * ξ := by
      rw [hξ, ← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    exact this.trans (mul_le_mul_of_nonneg_right he3 hξ0)
  have hexpM8 : Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2))) ≤ ξ := by
    rw [hξ]; apply Real.exp_le_exp.mpr
    have : H ^ 2 / (128 * (M : ℝ) ^ 2) ≤ H ^ 2 / (8 * (M : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by have := sq_nonneg (M : ℝ); linarith)
    linarith
  -- the window mass
  have hK1 : 1 ≤ K := by
    rw [hK, Real.le_sqrt (by norm_num) (by positivity)]
    have hH2' : 1 ≤ H ^ 2 := one_le_pow₀ hH1
    have := mul_le_mul (le_of_lt Real.pi_gt_three) hH2' (by norm_num) Real.pi_pos.le
    linarith
  have hsq2 : Real.sqrt (Real.pi * H ^ 2) ≤ 2 * K := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc Real.sqrt (Real.pi * H ^ 2) ≤ Real.sqrt (4 * (Real.pi * H ^ 2 / 2)) :=
          Real.sqrt_le_sqrt (by have : 0 ≤ Real.pi * H ^ 2 := by positivity
                                linarith)
      _ = 2 * K := by rw [Real.sqrt_mul (by norm_num), h4]
  have hgte : gaussTwistError H R M ≤ 9 * K * ξ := by
    unfold gaussTwistError
    rw [← hK]
    have h1 : K * Real.exp (1 - H ^ 2 / (128 * (M : ℝ) ^ 2)) ≤ K * (3 * ξ) :=
      mul_le_mul_of_nonneg_left hexpM (by linarith)
    have h2 : Real.exp (1 - R ^ 2 / H ^ 2) * Real.sqrt (Real.pi * H ^ 2) ≤ 3 * ξ * (2 * K) :=
      mul_le_mul hexpR hsq2 (Real.sqrt_nonneg _) (by positivity)
    calc K * Real.exp (1 - H ^ 2 / (128 * (M : ℝ) ^ 2)) + Real.exp (1 - R ^ 2 / H ^ 2) *
          Real.sqrt (Real.pi * H ^ 2) ≤ K * (3 * ξ) + 3 * ξ * (2 * K) := add_le_add h1 h2
      _ = 9 * K * ξ := by ring
  -- polynomial sizes
  have hsqT : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hsqT1 : 1 ≤ Real.sqrt (Real.exp L) := by rw [hsqT]; exact Real.one_le_exp (by linarith)
  have hy2 : (y : ℝ) ^ 2 ≤ Real.exp (2 * L) := by
    calc (y : ℝ) ^ 2 ≤ Real.exp (θ * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg y) hyle 2
      _ = Real.exp (2 * (θ * L)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (2 * L) := by
          have : θ * L ≤ L := mul_le_of_le_one_left hL hθ1.le
          exact Real.exp_le_exp.mpr (by linarith)
  have hM2' : (M : ℝ) ^ 2 ≤ Real.exp (2 * L) := by
    have h : 2 * ((θ + (1 - θ) / 4) * L) ≤ 2 * L := by
      have : (θ + (1 - θ) / 4) * L ≤ L := mul_le_of_le_one_left hL (by linarith)
      linarith
    exact hM2.trans (Real.exp_le_exp.mpr h)
  have hpoly : (y : ℝ) ^ 2 * (M : ℝ) ^ 2 * Real.sqrt (Real.exp L) ≤ Real.exp (5 * L) := by
    have h5 : Real.exp (5 * L) = Real.exp (2 * L) * Real.exp (2 * L) * Real.exp L := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hsT : Real.sqrt (Real.exp L) ≤ Real.exp L := by
      rw [hsqT]; exact Real.exp_le_exp.mpr (by linarith)
    rw [h5]
    gcongr
  constructor
  · have hinner : 27 * Real.sqrt (Real.exp L) * M * Real.exp (1 - R ^ 2 / H ^ 2) +
        2 * M * gaussTwistError H R M ≤ 99 * K * Real.sqrt (Real.exp L) * M * ξ := by
      have h1 : 27 * Real.sqrt (Real.exp L) * M * Real.exp (1 - R ^ 2 / H ^ 2) ≤
          81 * K * Real.sqrt (Real.exp L) * M * ξ := by
        have := mul_le_mul_of_nonneg_left hexpR
          (by positivity : (0 : ℝ) ≤ 27 * Real.sqrt (Real.exp L) * M)
        have h' : 27 * Real.sqrt (Real.exp L) * M * (3 * ξ) ≤ 81 * K * Real.sqrt (Real.exp L) * M * ξ := by
          have h0 : 0 ≤ Real.sqrt (Real.exp L) * M * ξ := by positivity
          have := mul_le_mul_of_nonneg_right hK1 h0
          linarith
        linarith
      have h2 : 2 * M * gaussTwistError H R M ≤ 18 * K * Real.sqrt (Real.exp L) * M * ξ := by
        have := mul_le_mul_of_nonneg_left hgte (by positivity : (0 : ℝ) ≤ 2 * M)
        have h' : 2 * (M : ℝ) * (9 * K * ξ) ≤ 18 * K * Real.sqrt (Real.exp L) * M * ξ := by
          have h0 : 0 ≤ K * M * ξ := by positivity
          have := mul_le_mul_of_nonneg_left hsqT1 h0
          linarith
        linarith
      linarith
    calc (y : ℝ) ^ 2 * M * (27 * Real.sqrt (Real.exp L) * M * Real.exp (1 - R ^ 2 / H ^ 2) +
          2 * M * gaussTwistError H R M)
        ≤ (y : ℝ) ^ 2 * M * (99 * K * Real.sqrt (Real.exp L) * M * ξ) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 99 * K * ((y : ℝ) ^ 2 * (M : ℝ) ^ 2 * Real.sqrt (Real.exp L)) * ξ := by ring
      _ ≤ 99 * K * Real.exp (5 * L) * ξ := by gcongr
      _ = K * (99 * (Real.exp (5 * L) * ξ)) := by ring
      _ ≤ K * ε := mul_le_mul_of_nonneg_left hsup (by linarith)
  · have hsum : ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ * (n : ℝ) ^ (-σ) ≤ M * y := by
      calc ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ * (n : ℝ) ^ (-σ)
          ≤ ∑ _n ∈ Finset.Icc 1 M, (y : ℝ) := Finset.sum_le_sum fun n hn => by
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
            have h1 : (n : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
            have h2 := norm_mollifiedZetaCoeff_le hb n
            exact (mul_le_of_le_one_right (norm_nonneg _) h1).trans h2
        _ = M * y := by simp
    have hsum0 : 0 ≤ ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ * (n : ℝ) ^ (-σ) :=
      Finset.sum_nonneg fun n _ => by positivity
    have hMy : ((M : ℝ) * y) ^ 2 ≤ Real.exp (5 * L) := by
      have h1 : ((M : ℝ) * y) ^ 2 = (y : ℝ) ^ 2 * (M : ℝ) ^ 2 * 1 := by ring
      rw [h1]
      exact le_trans (mul_le_mul_of_nonneg_left hsqT1 (by positivity)) hpoly
    calc (∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ * (n : ℝ) ^ (-σ)) ^ 2 *
          Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2)))
        ≤ ((M : ℝ) * y) ^ 2 * ξ :=
          mul_le_mul (pow_le_pow_left₀ hsum0 hsum 2) hexpM8 (Real.exp_pos _).le (by positivity)
      _ ≤ Real.exp (5 * L) * ξ := mul_le_mul_of_nonneg_right hMy hξ0
      _ ≤ 99 * (Real.exp (5 * L) * ξ) := by
          have : 0 ≤ Real.exp (5 * L) * ξ := by positivity
          linarith
      _ ≤ ε := hsup

/-- Scale facts at `T = e^L`: `M ≈ e^{(θ+δ/4)L}` exceeds `y` and `2`, `24M ≤ H²`, `32R ≤ cT`. -/
theorem gaussFloor_scale {θ c L : ℝ} (hθ0 : 0 < θ) (hc0 : 0 < c) (hL0 : 0 < L)
    (hδL8 : 8 ≤ (1 - θ) / 4 * L) (hδLc : 32 / c ≤ (1 - θ) / 4 * L) {y M : ℕ}
    (hyle : (y : ℝ) ≤ Real.exp (θ * L))
    (hMle : (M : ℝ) ≤ Real.exp ((θ + (1 - θ) / 4) * L))
    (hMgt : Real.exp ((θ + (1 - θ) / 4) * L) - 1 < M) :
    2 ≤ M ∧ y ≤ M ∧ Real.exp ((θ + (1 - θ) / 4) * L) / 2 ≤ M ∧
      24 * (M : ℝ) ≤ Real.exp ((θ + (1 - θ) / 2) * L) ^ 2 ∧
      32 * Real.exp ((θ + 3 * (1 - θ) / 4) * L) ≤ c * Real.exp L := by
  set q : ℝ := Real.exp ((1 - θ) / 4 * L) with hqdef
  have hθL : 1 ≤ Real.exp (θ * L) := Real.one_le_exp (by nlinarith)
  have hq : 9 ≤ q := by have := Real.add_one_le_exp ((1 - θ) / 4 * L); linarith
  have hqc : 32 / c ≤ q := by have := Real.add_one_le_exp ((1 - θ) / 4 * L); linarith
  have hμexp : Real.exp ((θ + (1 - θ) / 4) * L) = Real.exp (θ * L) * q := by
    rw [hqdef, ← Real.exp_add]; congr 1; ring
  have hμ9 : 9 * Real.exp (θ * L) ≤ Real.exp ((θ + (1 - θ) / 4) * L) := by
    rw [hμexp]; nlinarith
  have hM2r : (2 : ℝ) < M := by linarith
  refine ⟨by exact_mod_cast hM2r.le, ?_, by linarith, ?_, ?_⟩
  · have : (y : ℝ) < M := by linarith
    exact_mod_cast this.le
  · have h1 : Real.exp ((θ + (1 - θ) / 2) * L) ^ 2 =
        Real.exp ((θ + (1 - θ) / 4) * L) * (Real.exp (θ * L) * q ^ 3) := by
      rw [hqdef, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    have h3 : (729 : ℝ) ≤ q ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) hq 3
      norm_num at this; linarith
    have h2 : 27 ≤ Real.exp (θ * L) * q ^ 3 := by
      have := mul_le_mul hθL h3 (by norm_num) (by linarith)
      linarith
    rw [h1]
    have hE : 0 < Real.exp ((θ + (1 - θ) / 4) * L) := Real.exp_pos _
    calc 24 * (M : ℝ) ≤ 24 * Real.exp ((θ + (1 - θ) / 4) * L) := by linarith
      _ ≤ Real.exp ((θ + (1 - θ) / 4) * L) * 27 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hE.le
  · have hTR : Real.exp L = Real.exp ((θ + 3 * (1 - θ) / 4) * L) * q := by
      rw [hqdef, ← Real.exp_add]; congr 1; ring
    rw [hTR]
    have h1 := (div_le_iff₀ hc0).mp hqc
    have hR0 := Real.exp_pos ((θ + 3 * (1 - θ) / 4) * L)
    have := mul_le_mul_of_nonneg_left h1 hR0.le
    linarith

theorem continuous_normSq_zetaMollified_line {σ : ℝ} (hσ : σ ≠ 1) (b : ℕ → ℂ) (y : ℕ) :
    Continuous fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hsy : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    exact hσ this
  refine (continuous_iff_continuousAt.mpr fun t => ?_).norm.pow 2
  exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
    (differentiableAt_riemannZeta (hline t)).continuousAt (by fun_prop)).mul
    (((differentiable_edPoly b hsy).continuous.comp (by fun_prop)).continuousAt)

/-- **The Gaussian floor at one scale `T = e^L`.** -/
theorem gaussFloor_at_scale {a θ L : ℝ} (ha : 0 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hLa : 2 * a + 3 ≤ L) (hLK : 8 * (Real.log 2 + 2 * |mertensPrimeConst|) ≤ (1 - θ) * L)
    (hδL8 : 8 ≤ (1 - θ) / 4 * L)
    (hδLc : 32 / ((1 - θ) / 8 * Real.exp (-(2 * a))) ≤ (1 - θ) / 4 * L)
    (hsup : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ) / 2 * L)))) ≤
      (1 - θ) / 8 * Real.exp (-(2 * a)) / 12)
    {y : ℕ} (hy : 1 ≤ y) (hyle : (y : ℝ) ≤ Real.exp (θ * L)) {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) :
    (1 + (1 - θ) / 16 * Real.exp (-(2 * a))) * Real.exp L ≤
      ∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  set c : ℝ := (1 - θ) / 8 * Real.exp (-(2 * a)) with hc
  have hδ0 : 0 < 1 - θ := by linarith
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    have h1 : Real.exp (-(2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have : (1 - θ) / 8 * Real.exp (-(2 * a)) ≤ 1 / 8 * 1 :=
      mul_le_mul (by linarith) h1 (Real.exp_pos _).le (by norm_num)
    linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌊Real.exp ((θ + (1 - θ) / 4) * L)⌋₊ := ⟨_, rfl⟩
  have hMle : (M : ℝ) ≤ Real.exp ((θ + (1 - θ) / 4) * L) := by
    rw [hMdef]; exact Nat.floor_le (by positivity)
  have hMgt : Real.exp ((θ + (1 - θ) / 4) * L) - 1 < M := by
    rw [hMdef]; have := Nat.lt_floor_add_one (Real.exp ((θ + (1 - θ) / 4) * L)); linarith
  obtain ⟨hM2, hyM, hMge, hHM, h2R⟩ := gaussFloor_scale hθ0 hc0 hL0 hδL8 hδLc hyle hMle hMgt
  have hσ12 : 1 / 2 ≤ 1 / 2 + a / L := by have := div_pos ha hL0; linarith
  have hσ1 : 1 / 2 + a / L < 1 := by
    have : a / L < 1 / 2 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  have hD := gaussFloor_D_ge (b := b) ha hθ1 hL0 hLK hy hb1 hyM hM2 hMle hMge hyle
  rw [← hc] at hD
  obtain ⟨hE1, hE2⟩ := gaussFloor_error_bounds (σ := 1 / 2 + a / L) hθ0.le hθ1 hL0.le hy hyle
    (by omega : 1 ≤ M) hMle hsup hb (by linarith)
  set H : ℝ := Real.exp ((θ + (1 - θ) / 2) * L) with hH
  set R : ℝ := Real.exp ((θ + 3 * (1 - θ) / 4) * L) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hH0 : 0 < H := Real.exp_pos _
  have hT4 : 4 ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hRT : Real.exp L + R ≤ 2 * Real.exp L - R := by nlinarith
  have hZc := continuous_normSq_zetaMollified_line (σ := 1 / 2 + a / L) (by linarith) b y
  set Z : ℝ → ℝ := fun t => ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
    edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hZ
  have hZ0 : ∀ t, 0 ≤ Z t := fun t => by simp only [hZ]; positivity
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 *
    (n : ℝ) ^ (-2 * (1 / 2 + a / L)) with hDdef
  have hwin : ∀ τ ∈ Icc (Real.exp L + R) (2 * Real.exp L - R),
      Real.sqrt (Real.pi * H ^ 2 / 2) * (D - 3 * (c / 12)) ≤
        ∫ t in (Real.exp L)..(2 * Real.exp L), Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) := by
    intro τ hτ
    have hτ1 : Real.exp L ≤ τ - R := by linarith [hτ.1]
    have hτ2 : τ + R ≤ 2 * Real.exp L := by linarith [hτ.2]
    have h1 := gaussFloor_window hσ12 hσ1 (by omega : 1 ≤ M) hb hT4 hH0 hHM hR0.le hτ1 hτ2
      (by rw [← hDdef]; linarith) (by positivity) (by linarith) hE1 hE2
    refine h1.trans ?_
    have hcont : Continuous fun t => Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) :=
      hZc.mul (by fun_prop)
    exact intervalIntegral.integral_mono_interval hτ1 (by linarith) hτ2
      (Filter.Eventually.of_forall fun t => mul_nonneg (hZ0 t) (Real.exp_pos _).le)
      (hcont.intervalIntegrable _ _)
  have hfub := integral_ge_of_gaussian_windows hZc hZ0 hH0 hRT hR0.le hwin
  have hD3 : 1 + 3 * c / 4 ≤ D - 3 * (c / 12) := by linarith
  have hTR2 : 0 ≤ Real.exp L - 2 * R := by linarith
  have h1 : (Real.exp L - 2 * R) * (1 + 3 * c / 4) ≤ (Real.exp L - 2 * R) * (D - 3 * (c / 12)) :=
    mul_le_mul_of_nonneg_left hD3 hTR2
  have h2 : Real.exp L * (1 + c / 2) ≤ (Real.exp L - 2 * R) * (1 + 3 * c / 4) := by nlinarith
  calc (1 + (1 - θ) / 16 * Real.exp (-(2 * a))) * Real.exp L = Real.exp L * (1 + c / 2) := by
        rw [hc]; ring
    _ ≤ (Real.exp L - 2 * R) * (D - 3 * (c / 12)) := h2.trans h1
    _ ≤ ∫ t in (Real.exp L)..(2 * Real.exp L), Z t := hfub

/-- **The floor under every mollified mean square of length `T^θ`, `θ < 1`, right of the line.**
For every `a > 0` and `0 < θ < 1`, for all large `T`, every mollifier `Ψ = Σ_{d ≤ y} b_d d^{-s}`
with `y ≤ T^θ`, `b_1 = 1`, `|b_d| ≤ 1` satisfies
`∫_T^{2T} |ζΨ(1/2 + a/log T + it)|² dt ≥ (1 + (1−θ) e^{−2a}/16) T`. -/
theorem exists_eventually_integral_normSq_zetaMollified_rightShift_ge_of_lt_one {a θ : ℝ}
    (ha : 0 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ T in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ T ^ θ → ∀ b : ℕ → ℂ, b 1 = 1 →
      (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
      (1 + (1 - θ) / 16 * Real.exp (-(2 * a))) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  set c : ℝ := (1 - θ) / 8 * Real.exp (-(2 * a)) with hc
  have hδ0 : 0 < 1 - θ := by linarith
  have hc0 : 0 < c := by positivity
  have hsup := eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128) (δ := (1 - θ) / 2)
    (ε := c / 1200) (by norm_num) (by positivity) (by positivity)
  set L₀ : ℝ := max (max (2 * a + 3) (8 * (Real.log 2 + 2 * |mertensPrimeConst|) / (1 - θ)))
    (max (32 / (1 - θ)) (128 / (c * (1 - θ)))) with hL₀
  filter_upwards [Real.tendsto_log_atTop.eventually ((eventually_ge_atTop L₀).and hsup),
    eventually_gt_atTop 0] with T hTL hT0
  obtain ⟨hLL₀, hsupL⟩ := hTL
  intro y hy hyle b hb1 hb
  have hLa : 2 * a + 3 ≤ Real.log T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL₀
  have hLK' : 8 * (Real.log 2 + 2 * |mertensPrimeConst|) / (1 - θ) ≤ Real.log T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL₀
  have hL32 : 32 / (1 - θ) ≤ Real.log T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL₀
  have hLc : 128 / (c * (1 - θ)) ≤ Real.log T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL₀
  have hLK : 8 * (Real.log 2 + 2 * |mertensPrimeConst|) ≤ (1 - θ) * Real.log T := by
    rw [div_le_iff₀ hδ0] at hLK'; linarith
  have hδL8 : 8 ≤ (1 - θ) / 4 * Real.log T := by
    rw [div_le_iff₀ hδ0] at hL32; linarith
  have hδLc : 32 / c ≤ (1 - θ) / 4 * Real.log T := by
    rw [div_le_iff₀ (by positivity)] at hLc
    rw [div_le_iff₀ hc0]; nlinarith
  have hsup' : 99 * (Real.exp (5 * Real.log T) *
      Real.exp (-(1 / 128 * Real.exp ((1 - θ) / 2 * Real.log T)))) ≤ c / 12 := by
    linarith
  have hyle' : (y : ℝ) ≤ Real.exp (θ * Real.log T) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hT0]; exact hyle
  have key := gaussFloor_at_scale ha hθ0 hθ1 hLa hLK hδL8 hδLc hsup' hy hyle' hb1 hb
  rw [Real.exp_log hT0] at key
  exact key

end RHTower
