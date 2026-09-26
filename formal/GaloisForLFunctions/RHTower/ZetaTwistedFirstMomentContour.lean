import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound
import GaloisForLFunctions.HTGeometry.LogarithmicSpacing
import Mathlib.NumberTheory.ZetaValues

/-!
# The first moment of `ζ` twisted by a ratio of integers

For integers `d, n ≥ 1` and `1/2 ≤ σ < 2` let `g(s) = ζ(s) d^{-s} n^{s-2σ}`. On `Re s = σ` this is
`ζ(σ+it) · d^{-σ} n^{-σ} (n/d)^{it}`, the integrand of the first moment of `ζ` twisted by `n/d`.
Since `g` is holomorphic in `s`, the integral over `[T, 2T]` moves to `Re s = 2`, where `ζ` is its
Dirichlet series and only the diagonal `dm = n` survives:

`‖∫_T^{2T} g(σ+it) dt − [d ∣ n] n^{-2σ} T‖ ≤ 27√T n + 8n²`
(`norm_integral_twistedZeta_sub_diag_le`).

The horizontal edges cost `27√T n` through the square-root vertical bound for `ζ`; the off-diagonal
terms `m ≠ n/d` of the Dirichlet series cost `8n²` through the logarithmic spacing
`|log n − log(dm)| ≥ 1/max(n, dm)`.
-/

noncomputable section

open Complex MeasureTheory Set

namespace RHTower

/-- The twisted zeta integrand `ζ(s) d^{-s} n^{s-2σ}`. -/
def twistedZeta (σ : ℝ) (d n : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * ((d : ℝ) : ℂ) ^ (-s) * ((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ))

theorem ofReal_natCast_cpow_eq_exp {x : ℕ} (hx : 1 ≤ x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    exact_mod_cast this.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log (Nat.cast_nonneg x)]

theorem norm_ofReal_natCast_cpow {x : ℕ} (hx : 1 ≤ x) (w : ℂ) :
    ‖((x : ℝ) : ℂ) ^ w‖ = (x : ℝ) ^ w.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : 0 < x)) w

/-! ## The line `Re s = 2` -/

/-- The `m`-th Dirichlet term of `g(2 + it)`. -/
def twistedZetaTerm (σ : ℝ) (d n m : ℕ) (t : ℝ) : ℂ :=
  1 / (m : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) * ((d : ℝ) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I)) *
    ((n : ℝ) : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I - 2 * (σ : ℂ))

/-- Amplitude of the `m`-th term. -/
def twistedZetaAmp (σ : ℝ) (d n m : ℕ) : ℝ :=
  Real.exp ((2 - 2 * σ) * Real.log n - 2 * Real.log d - 2 * Real.log m)

/-- Frequency of the `m`-th term. -/
def twistedZetaFreq (d n m : ℕ) : ℝ := Real.log n - Real.log d - Real.log m

theorem twistedZetaTerm_eq {σ : ℝ} {d n m : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hm : 1 ≤ m) (t : ℝ) :
    twistedZetaTerm σ d n m t =
      (twistedZetaAmp σ d n m : ℂ) * Complex.exp (I * ((t * twistedZetaFreq d n m : ℝ) : ℂ)) := by
  unfold twistedZetaTerm twistedZetaAmp twistedZetaFreq
  have hm' : (m : ℂ) = ((m : ℝ) : ℂ) := by norm_cast
  rw [hm', ofReal_natCast_cpow_eq_exp hm, ofReal_natCast_cpow_eq_exp hd,
    ofReal_natCast_cpow_eq_exp hn, one_div, ← Complex.exp_neg, ← Complex.exp_add,
    ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem twistedZetaTerm_zero (σ : ℝ) (d n : ℕ) (t : ℝ) : twistedZetaTerm σ d n 0 t = 0 := by
  unfold twistedZetaTerm
  have hne : ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  simp [Complex.zero_cpow hne]

theorem hasSum_twistedZetaTerm (σ : ℝ) (d n : ℕ) (t : ℝ) :
    HasSum (fun m => twistedZetaTerm σ d n m t)
      (twistedZeta σ d n ((2 : ℂ) + (t : ℂ) * I)) := by
  have hre : 1 < ((2 : ℂ) + (t : ℂ) * I).re := by simp
  have hs := (Complex.summable_one_div_nat_cpow.mpr hre).hasSum
  rw [← zeta_eq_tsum_one_div_nat_cpow hre] at hs
  unfold twistedZeta
  exact (hs.mul_right _).mul_right _

theorem twistedZetaAmp_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {d n m : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : twistedZetaAmp σ d n m ≤ n / (m : ℝ) ^ 2 := by
  unfold twistedZetaAmp
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : (2 - 2 * σ) * Real.log n - 2 * Real.log d - 2 * Real.log m ≤
      Real.log n - 2 * Real.log m := by nlinarith
  calc Real.exp ((2 - 2 * σ) * Real.log n - 2 * Real.log d - 2 * Real.log m)
      ≤ Real.exp (Real.log n - 2 * Real.log m) := Real.exp_le_exp.mpr h1
    _ = n / (m : ℝ) ^ 2 := by
        rw [Real.exp_sub, Real.exp_log hn0, show 2 * Real.log (m : ℝ) = Real.log ((m : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem norm_twistedZetaTerm_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (m : ℕ) (t : ℝ) : ‖twistedZetaTerm σ d n m t‖ ≤ n * (1 / (m : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [twistedZetaTerm_zero, norm_zero]; simp
  · have hA0 : 0 ≤ twistedZetaAmp σ d n m := by unfold twistedZetaAmp; positivity
    have hexp : ‖Complex.exp (I * ((t * twistedZetaFreq d n m : ℝ) : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    rw [twistedZetaTerm_eq hd hn hm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hA0, hexp, mul_one]
    have := twistedZetaAmp_le hσ hd hn hm
    rw [mul_one_div]
    exact this

theorem integral_exp_I_mul (φ T : ℝ) (hφ : φ ≠ 0) :
    ‖∫ t in T..(2 * T), Complex.exp (I * ((t * φ : ℝ) : ℂ))‖ ≤ 2 / |φ| := by
  have hc : I * (φ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hφ)
  have heq : (fun t : ℝ => Complex.exp (I * ((t * φ : ℝ) : ℂ))) =
      fun t : ℝ => Complex.exp ((I * (φ : ℂ)) * (t : ℂ)) := by
    funext t; congr 1; push_cast; ring
  rw [heq, integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, div_le_div_iff_of_pos_right (abs_pos.mpr hφ)]
  refine (norm_sub_le _ _).trans ?_
  rw [show (I * (φ : ℂ)) * ((2 * T : ℝ) : ℂ) = (((2 * T * φ : ℝ) : ℂ)) * I by push_cast; ring,
    show (I * (φ : ℂ)) * ((T : ℝ) : ℂ) = (((T * φ : ℝ) : ℂ)) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- **The line `Re s = 2`:** only the diagonal `dm = n` survives. -/
theorem norm_integral_twistedZeta_two_sub_diag_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {d n : ℕ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (T : ℝ) :
    ‖(∫ t in T..(2 * T), twistedZeta σ d n ((2 : ℂ) + (t : ℂ) * I)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0)‖ ≤ 8 * (n : ℝ) ^ 2 := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- exchange of the Dirichlet series and the integral
  have hsum2 : Summable fun m : ℕ => (n : ℝ) * (1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  have hHas : HasSum (fun m => ∫ t in T..(2 * T), twistedZetaTerm σ d n m t)
      (∫ t in T..(2 * T), twistedZeta σ d n ((2 : ℂ) + (t : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => (n : ℝ) * (1 / (m : ℝ) ^ 2)) (fun m => ?_) (fun m => ?_) ?_ ?_ ?_
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · have h0 : twistedZetaTerm σ d n 0 = fun _ => 0 := funext (twistedZetaTerm_zero σ d n)
        rw [h0]; exact aestronglyMeasurable_const
      · have hc : Continuous fun t : ℝ => twistedZetaTerm σ d n m t := by
          have : (fun t : ℝ => twistedZetaTerm σ d n m t) = fun t : ℝ =>
              (twistedZetaAmp σ d n m : ℂ) * Complex.exp (I * ((t * twistedZetaFreq d n m : ℝ) : ℂ)) :=
            funext fun t => twistedZetaTerm_eq hd hn hm t
          rw [this]; fun_prop
        exact hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t _ => norm_twistedZetaTerm_le hσ hd hn m t
    · exact Filter.Eventually.of_forall fun t _ => hsum2
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ => hasSum_twistedZetaTerm σ d n t
  -- the diagonal
  set D : ℕ → ℂ := fun m => if d * m = n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0 with hD
  have hDsum : HasSum D (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0) := by
    by_cases hdn : d ∣ n
    · obtain ⟨k, hk⟩ := hdn
      rw [if_pos ⟨k, hk⟩]
      have hsingle : ∀ m ≠ k, D m = 0 := by
        intro m hm
        simp only [hD]
        rw [if_neg]
        intro h
        apply hm
        have hd0 : 0 < d := by omega
        exact Nat.eq_of_mul_eq_mul_left hd0 (h.trans hk)
      have := hasSum_single k hsingle
      simp only [hD, if_pos hk.symm] at this
      exact this
    · rw [if_neg hdn]
      have : D = fun _ => 0 := by
        funext m
        simp only [hD]
        rw [if_neg]
        intro h
        exact hdn ⟨m, h.symm⟩
      rw [this]
      exact hasSum_zero
  -- off-diagonal bound, term by term
  have hterm : ∀ m : ℕ, ‖(∫ t in T..(2 * T), twistedZetaTerm σ d n m t) - D m‖ ≤
      4 * (n : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hD0 : D 0 = 0 := by
        simp only [hD]; rw [if_neg]; omega
      simp only [twistedZetaTerm_zero, intervalIntegral.integral_zero, hD0, sub_zero, norm_zero]
      positivity
    · have hint : (∫ t in T..(2 * T), twistedZetaTerm σ d n m t) =
          (twistedZetaAmp σ d n m : ℂ) *
            ∫ t in T..(2 * T), Complex.exp (I * ((t * twistedZetaFreq d n m : ℝ) : ℂ)) := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun t _ => twistedZetaTerm_eq hd hn hm t
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have hA := twistedZetaAmp_le hσ hd hn hm
      have hA0 : 0 ≤ twistedZetaAmp σ d n m := (Real.exp_pos _).le
      by_cases hdiag : d * m = n
      · -- the diagonal term is exact
        have hφ : twistedZetaFreq d n m = 0 := by
          unfold twistedZetaFreq
          rw [← hdiag]
          push_cast
          rw [Real.log_mul (by exact_mod_cast (by omega : d ≠ 0))
            (by exact_mod_cast (by omega : m ≠ 0))]
          ring
        have hamp : twistedZetaAmp σ d n m = (n : ℝ) ^ (-2 * σ) := by
          unfold twistedZetaAmp
          rw [Real.rpow_def_of_pos hn0]
          congr 1
          have : Real.log (n : ℝ) = Real.log d + Real.log m := by
            rw [← hdiag]; push_cast
            exact Real.log_mul (by exact_mod_cast (by omega : d ≠ 0))
              (by exact_mod_cast (by omega : m ≠ 0))
          rw [this]; ring
        have hDm : D m = (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) := by
          simp only [hD]; rw [if_pos hdiag]
        have hone : (∫ t in T..(2 * T), Complex.exp (I * ((t * twistedZetaFreq d n m : ℝ) : ℂ))) =
            ((T : ℝ) : ℂ) := by
          have : ∀ t : ℝ, Complex.exp (I * ((t * twistedZetaFreq d n m : ℝ) : ℂ)) = 1 := by
            intro t; rw [hφ, mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
          simp only [this, intervalIntegral.integral_const]
          rw [Complex.real_smul, mul_one]
          push_cast; ring
        rw [hint, hone, hDm, hamp]
        push_cast
        rw [sub_self, norm_zero]
        positivity
      · -- off the diagonal
        have hD0 : D m = 0 := by simp only [hD]; rw [if_neg hdiag]
        rw [hD0, sub_zero, hint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
        have hdm : (0 : ℕ) < d * m := by positivity
        have hne : d * m ≠ n := hdiag
        have hφ : twistedZetaFreq d n m = Real.log n - Real.log ((d * m : ℕ) : ℝ) := by
          unfold twistedZetaFreq
          push_cast
          rw [Real.log_mul (by exact_mod_cast (by omega : d ≠ 0))
            (by exact_mod_cast (by omega : m ≠ 0))]
          ring
        have hφne : twistedZetaFreq d n m ≠ 0 := by
          rw [hφ]
          intro h
          have h' : Real.log (n : ℝ) = Real.log ((d * m : ℕ) : ℝ) := by linarith
          have := Real.log_injOn_pos (Set.mem_Ioi.mpr hn0)
            (Set.mem_Ioi.mpr (by exact_mod_cast hdm)) h'
          exact hne (by exact_mod_cast this.symm)
        have hexp := integral_exp_I_mul (twistedZetaFreq d n m) T hφne
        have hinv : 2 / |twistedZetaFreq d n m| ≤ 4 * n := by
          rw [div_le_iff₀ (abs_pos.mpr hφne)]
          rcases le_or_gt (2 * n) (d * m) with hbig | hsmall
          · -- `dm ≥ 2n`: the logarithms differ by at least `log 2`
            have hlog2 : (1 / 2 : ℝ) ≤ |twistedZetaFreq d n m| := by
              rw [hφ, abs_sub_comm, abs_of_nonneg]
              · have h1 : Real.log (2 * (n : ℝ)) ≤ Real.log ((d * m : ℕ) : ℝ) :=
                  Real.log_le_log (by positivity) (by exact_mod_cast hbig)
                rw [Real.log_mul (by norm_num) hn0.ne'] at h1
                have := Real.log_two_gt_d9
                linarith
              · have : Real.log (n : ℝ) ≤ Real.log ((d * m : ℕ) : ℝ) :=
                  Real.log_le_log hn0 (by exact_mod_cast (by omega : n ≤ d * m))
                linarith
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
            nlinarith
          · -- `dm < 2n`: logarithmic spacing
            have hsp := HTGeometry.inv_max_le_abs_log_sub_log_nat
              (by omega : 0 < n) hdm hne.symm
            rw [← hφ] at hsp
            have hmax : max (n : ℝ) ((d * m : ℕ) : ℝ) ≤ 2 * n := by
              apply max_le (by linarith)
              exact_mod_cast hsmall.le
            have : 1 / (2 * (n : ℝ)) ≤ |twistedZetaFreq d n m| :=
              le_trans (one_div_le_one_div_of_le (by positivity) hmax) hsp
            rw [div_le_iff₀ (by positivity)] at this
            nlinarith
        calc twistedZetaAmp σ d n m *
              ‖∫ t in T..(2 * T), Complex.exp (I * ((t * twistedZetaFreq d n m : ℝ) : ℂ))‖
            ≤ (n / (m : ℝ) ^ 2) * (4 * n) :=
              mul_le_mul hA (hexp.trans hinv) (norm_nonneg _) (by positivity)
          _ = 4 * (n : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) := by ring
  -- assemble
  have hdiff : HasSum (fun m => (∫ t in T..(2 * T), twistedZetaTerm σ d n m t) - D m)
      ((∫ t in T..(2 * T), twistedZeta σ d n ((2 : ℂ) + (t : ℂ) * I)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0)) := hHas.sub hDsum
  have hbound : Summable fun m : ℕ => 4 * (n : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  calc ‖(∫ t in T..(2 * T), twistedZeta σ d n ((2 : ℂ) + (t : ℂ) * I)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0)‖
      ≤ ∑' m : ℕ, 4 * (n : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) :=
        hdiff.norm_le_of_bounded hbound.hasSum hterm
    _ = 4 * (n : ℝ) ^ 2 * (Real.pi ^ 2 / 6) := by rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]
    _ ≤ 8 * (n : ℝ) ^ 2 := by
        have h1 := Real.pi_lt_d2
        have hπ := Real.pi_pos
        have hπ2 : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left hπ2 (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2)
        linarith

/-! ## The contour shift -/

theorem differentiableAt_twistedZeta (σ : ℝ) {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {s : ℂ}
    (hs : s ≠ 1) : DifferentiableAt ℂ (twistedZeta σ d n) s := by
  have hd0 : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < d).ne'
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < n).ne'
  unfold twistedZeta
  exact ((differentiableAt_riemannZeta hs).mul
    ((differentiableAt_id.neg).const_cpow (Or.inl hd0))).mul
    ((differentiableAt_id.sub_const _).const_cpow (Or.inl hn0))

/-- On a horizontal segment at height `Y ∈ [T, 2T]`, `T ≥ 4`, the integrand is at most `9√T n`. -/
theorem norm_twistedZeta_horizontal_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {d n : ℕ} (hd : 1 ≤ d)
    (hn : 1 ≤ n) {T Y x : ℝ} (hT : 4 ≤ T) (hY1 : T ≤ Y) (hY2 : Y ≤ 2 * T) (hx1 : σ ≤ x)
    (hx2 : x ≤ 2) :
    ‖twistedZeta σ d n ((x : ℂ) + (Y : ℂ) * I)‖ ≤ 9 * Real.sqrt T * n := by
  set s : ℂ := (x : ℂ) + (Y : ℂ) * I with hsdef
  have hre : s.re = x := by simp [hsdef]
  have him : s.im = Y := by simp [hsdef]
  have hsep : (1 : ℝ) ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, him, Complex.one_im, sub_zero, abs_of_pos (by linarith)] at this
    linarith
  have hζ := norm_riemannZeta_le_sqrt_norm_add_two_half (s := s) (by rw [hre]; linarith)
    one_pos hsep
  have hsn : ‖s‖ ≤ 2 + 2 * T := by
    have := norm_le_abs_re_add_abs_im s
    rw [hre, him, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
    linarith
  have hsqrt : Real.sqrt (‖s‖ + 2) ≤ Real.sqrt 3 * Real.sqrt T := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs3 : Real.sqrt 3 ≤ 7 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hζ' : ‖riemannZeta s‖ ≤ 9 * Real.sqrt T := by
    have hT0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    calc ‖riemannZeta s‖ ≤ (2 + 1 / 1 + 2) * Real.sqrt (‖s‖ + 2) := hζ
      _ ≤ 5 * (Real.sqrt 3 * Real.sqrt T) := by norm_num; linarith
      _ ≤ 9 * Real.sqrt T := by nlinarith
  have hdpow : ‖((d : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_ofReal_natCast_cpow hd, Complex.neg_re, hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
  have hnpow : ‖((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ))‖ ≤ n := by
    rw [norm_ofReal_natCast_cpow hn]
    have hre2 : (s - 2 * (σ : ℂ)).re = x - 2 * σ := by simp [hre]
    rw [hre2]
    calc (n : ℝ) ^ (x - 2 * σ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
      _ = n := Real.rpow_one _
  unfold twistedZeta
  rw [norm_mul, norm_mul]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ‖riemannZeta s‖ * ‖((d : ℝ) : ℂ) ^ (-s)‖ * ‖((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ))‖
      ≤ (9 * Real.sqrt T) * 1 * n := by gcongr
    _ = 9 * Real.sqrt T * n := by ring

/-- **The twisted first moment of `ζ`.** -/
theorem norm_integral_twistedZeta_sub_diag_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) {d n : ℕ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) {T : ℝ} (hT : 4 ≤ T) :
    ‖(∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0)‖ ≤
      27 * Real.sqrt T * n + 8 * (n : ℝ) ^ 2 := by
  set f := twistedZeta σ d n with hf
  set z : ℂ := (σ : ℂ) + (T : ℂ) * I with hz
  set w : ℂ := (2 : ℂ) + ((2 * T : ℝ) : ℂ) * I with hw
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = T := by simp [hz]
  have hwre : w.re = 2 := by simp [hw]
  have hwim : w.im = 2 * T := by simp [hw]
  have hdiff : DifferentiableOn ℂ f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro s hs
    have him := (Complex.mem_reProdIm.mp hs).2
    rw [hzim, hwim, Set.uIcc_of_le (by linarith)] at him
    have hs1 : s ≠ 1 := by
      intro h; rw [h, Complex.one_im] at him; linarith [him.1]
    exact (differentiableAt_twistedZeta σ hd hn hs1).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hdiff
  rw [hzre, hzim, hwre, hwim] at hrect
  -- horizontal edges
  have hhor : ∀ Y : ℝ, T ≤ Y → Y ≤ 2 * T →
      ‖∫ x in σ..2, f ((x : ℂ) + (Y : ℂ) * I)‖ ≤ 27 / 2 * Real.sqrt T * n := by
    intro Y hY1 hY2
    have hb : ∀ x ∈ Set.uIoc σ 2, ‖f ((x : ℂ) + (Y : ℂ) * I)‖ ≤ 9 * Real.sqrt T * n := by
      intro x hx
      rw [Set.uIoc_of_le hσ2] at hx
      exact norm_twistedZeta_horizontal_le hσ hd hn hT hY1 hY2 hx.1.le hx.2
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    rw [abs_of_nonneg (by linarith)]
    have h0 : 0 ≤ Real.sqrt T * n := by positivity
    nlinarith
  have hH1 := hhor T le_rfl (by linarith)
  have hH2 := hhor (2 * T) (by linarith) le_rfl
  have hvert : ‖(∫ t in T..(2 * T), f ((σ : ℂ) + (t : ℂ) * I)) -
      ∫ t in T..(2 * T), f ((2 : ℂ) + (t : ℂ) * I)‖ ≤ 27 * Real.sqrt T * n := by
    have hcast2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    rw [hcast2] at hrect
    have hkey : (∫ t in T..(2 * T), f ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in T..(2 * T), f ((2 : ℂ) + (t : ℂ) * I) =
        -I * ((∫ x in σ..2, f ((x : ℂ) + (T : ℂ) * I)) -
          ∫ x in σ..2, f ((x : ℂ) + ((2 * T : ℝ) : ℂ) * I)) := by
      have hI : I * I = -1 := Complex.I_mul_I
      simp only [smul_eq_mul] at hrect
      linear_combination I * hrect + ((∫ t in T..(2 * T), f ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in T..(2 * T), f ((2 : ℂ) + (t : ℂ) * I)) * hI
    rw [hkey, norm_mul, norm_neg, Complex.norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hright := norm_integral_twistedZeta_two_sub_diag_le hσ hd hn T
  calc ‖(∫ t in T..(2 * T), f ((σ : ℂ) + (t : ℂ) * I)) -
        (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0)‖
      = ‖((∫ t in T..(2 * T), f ((σ : ℂ) + (t : ℂ) * I)) -
          ∫ t in T..(2 * T), f ((2 : ℂ) + (t : ℂ) * I)) +
        ((∫ t in T..(2 * T), f ((2 : ℂ) + (t : ℂ) * I)) -
          (if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0))‖ := by
        congr 1; ring
    _ ≤ 27 * Real.sqrt T * n + 8 * (n : ℝ) ^ 2 := (norm_add_le _ _).trans (add_le_add hvert hright)

end RHTower
