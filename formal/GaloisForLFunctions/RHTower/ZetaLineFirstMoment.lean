import GaloisForLFunctions.RHTower.EMCarrier
import GaloisForLFunctions.RHTower.HardyZ

/-!
# The first moment of `ζ` on the critical line

Over a dyadic window the mean of `ζ` on the critical line is asymptotically the length of the
window: the constant term `n = 1` of the Euler–Maclaurin block contributes the full length, every
higher term oscillates, and both the explicit continuation term and the Euler–Maclaurin remainder
are negligible once the block length is taken slightly beyond the square of the height.

Combined with the Cauchy–Schwarz inequality this gives an unconditional lower bound of the exact
order of the window length for the second moment of `ζ` on the critical line.
-/

open Complex MeasureTheory

noncomputable section

namespace RHTower

/-! ## The oscillating Dirichlet terms -/

theorem cpow_neg_linePt_eq (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(linePt t))
      = (((n : ℝ) ^ (-(1/2) : ℝ) : ℝ) : ℂ) * Complex.exp (-(Real.log n : ℂ) * I * (t : ℂ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rw [linePt, Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log,
    Real.rpow_def_of_pos hnpos, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_cpow_neg_linePt (n : ℕ) (hn : 1 ≤ n) :
    Continuous fun t : ℝ => (n : ℂ) ^ (-(linePt t)) := by
  have : Continuous fun t : ℝ =>
      (((n : ℝ) ^ (-(1/2) : ℝ) : ℝ) : ℂ) * Complex.exp (-(Real.log n : ℂ) * I * (t : ℂ)) := by
    fun_prop
  exact this.congr fun t => (cpow_neg_linePt_eq n hn t).symm

theorem integral_cpow_neg_linePt (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) :
    ∫ t in a..b, (n : ℂ) ^ (-(linePt t))
      = (((n : ℝ) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ((Complex.exp (-(Real.log n : ℂ) * I * (b : ℂ))
            - Complex.exp (-(Real.log n : ℂ) * I * (a : ℂ)))
          / (-(Real.log n : ℂ) * I)) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hne : (-(Real.log n : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
    exact ne_of_gt hlog
  have hcongr : ∀ t : ℝ, (n : ℂ) ^ (-(linePt t))
      = (((n : ℝ) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        Complex.exp ((-(Real.log n : ℂ) * I) * (t : ℂ)) := by
    intro t
    rw [cpow_neg_linePt_eq n hn1 t]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
    (((n : ℝ) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
      Complex.exp ((-(Real.log n : ℂ) * I) * (t : ℂ))) (fun t _ => hcongr t)]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hne]

theorem norm_exp_neg_ofReal_mul_I_mul (L b : ℝ) :
    ‖Complex.exp (-(L : ℂ) * I * (b : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem norm_integral_cpow_neg_linePt_le (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) :
    ‖∫ t in a..b, (n : ℂ) ^ (-(linePt t))‖
      ≤ 2 * ((n : ℝ) ^ (-(1/2) : ℝ)) / Real.log n := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hpow : (0 : ℝ) < (n : ℝ) ^ (-(1/2) : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le two_pos hn
    positivity
  rw [integral_cpow_neg_linePt n hn a b, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpow]
  have hden : ‖(-(Real.log n : ℂ) * I)‖ = Real.log n := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlog]
  rw [hden]
  have hnum : ‖Complex.exp (-(Real.log n : ℂ) * I * (b : ℂ))
      - Complex.exp (-(Real.log n : ℂ) * I * (a : ℂ))‖ ≤ 2 := by
    calc ‖Complex.exp (-(Real.log n : ℂ) * I * (b : ℂ))
        - Complex.exp (-(Real.log n : ℂ) * I * (a : ℂ))‖
        ≤ ‖Complex.exp (-(Real.log n : ℂ) * I * (b : ℂ))‖
          + ‖Complex.exp (-(Real.log n : ℂ) * I * (a : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by
          rw [norm_exp_neg_ofReal_mul_I_mul, norm_exp_neg_ofReal_mul_I_mul]; norm_num
  calc (n : ℝ) ^ (-(1/2) : ℝ) *
        (‖Complex.exp (-(Real.log n : ℂ) * I * (b : ℂ))
          - Complex.exp (-(Real.log n : ℂ) * I * (a : ℂ))‖ / Real.log n)
      ≤ (n : ℝ) ^ (-(1/2) : ℝ) * (2 / Real.log n) := by gcongr
    _ = 2 * ((n : ℝ) ^ (-(1/2) : ℝ)) / Real.log n := by ring

/-! ## The Dirichlet block -/

theorem integral_dirichletPoly_line (N : ℕ) (a b : ℝ) :
    ∫ t in a..b, dirichletPoly N (linePt t)
      = ∑ n ∈ Finset.Icc 1 N, ∫ t in a..b, (n : ℂ) ^ (-(linePt t)) := by
  rw [show (fun t : ℝ => dirichletPoly N (linePt t))
      = fun t : ℝ => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(linePt t)) from rfl]
  refine intervalIntegral.integral_finsetSum fun n hn => ?_
  exact (continuous_cpow_neg_linePt n (Finset.mem_Icc.mp hn).1).intervalIntegrable a b

theorem integral_cpow_neg_linePt_one (a b : ℝ) :
    ∫ t in a..b, ((1 : ℕ) : ℂ) ^ (-(linePt t)) = ((b - a : ℝ) : ℂ) := by
  simp

/-! ## Elementary sum bounds -/

theorem rpow_neg_half_eq (n : ℕ) : (n : ℝ) ^ (-(1/2) : ℝ) = (Real.sqrt n)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.sqrt_eq_rpow]

theorem sum_rpow_neg_half_le (K : ℕ) :
    ∑ n ∈ Finset.Icc 1 K, ((n : ℝ) ^ (-(1/2) : ℝ)) ≤ 2 * Real.sqrt K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : (((K + 1 : ℕ) : ℝ) ^ (-(1/2) : ℝ))
          ≤ 2 * Real.sqrt ((K + 1 : ℕ)) - 2 * Real.sqrt K := by
        rw [rpow_neg_half_eq]
        have hK : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg _
        have hK1 : (0 : ℝ) < Real.sqrt ((K + 1 : ℕ)) := by
          refine Real.sqrt_pos.mpr ?_
          exact_mod_cast Nat.succ_pos K
        have hsq : Real.sqrt ((K + 1 : ℕ)) ^ 2 = ((K : ℝ) + 1) := by
          rw [Real.sq_sqrt (by positivity)]
          push_cast
          ring
        have hsqK : Real.sqrt (K : ℝ) ^ 2 = (K : ℝ) := Real.sq_sqrt (Nat.cast_nonneg K)
        rw [inv_le_iff_one_le_mul₀ hK1] at *
        nlinarith [hsq, hsqK, hK, hK1]
      have : (2 : ℝ) * Real.sqrt K + (((K + 1 : ℕ) : ℝ) ^ (-(1/2) : ℝ))
          ≤ 2 * Real.sqrt ((K + 1 : ℕ)) := by linarith
      linarith [ih]

/-! ## The oscillating part of the Dirichlet block -/

theorem norm_sum_integral_osc_le {N M : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) (a b : ℝ) :
    ‖∑ n ∈ Finset.Ioc 1 N, ∫ t in a..b, (n : ℂ) ^ (-(linePt t))‖
      ≤ 4 * Real.sqrt M / Real.log 2 + 4 * Real.sqrt N / Real.log M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  have hsplit : ∑ n ∈ Finset.Ioc 1 M, (∫ t in a..b, (n : ℂ) ^ (-(linePt t)))
      + ∑ n ∈ Finset.Ioc M N, (∫ t in a..b, (n : ℂ) ^ (-(linePt t)))
      = ∑ n ∈ Finset.Ioc 1 N, ∫ t in a..b, (n : ℂ) ^ (-(linePt t)) :=
    Finset.sum_Ioc_consecutive _ (by omega) hMN
  rw [← hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hlow : ‖∑ n ∈ Finset.Ioc 1 M, ∫ t in a..b, (n : ℂ) ^ (-(linePt t))‖
      ≤ 4 * Real.sqrt M / Real.log 2 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioc 1 M,
        ‖∫ t in a..b, (n : ℂ) ^ (-(linePt t))‖
          ≤ 2 * ((n : ℝ) ^ (-(1/2) : ℝ)) / Real.log 2 := by
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Ioc.mp hn).1
      have hlogn : Real.log 2 ≤ Real.log n := by
        refine Real.log_le_log (by norm_num) ?_
        exact_mod_cast hn2
      refine le_trans (norm_integral_cpow_neg_linePt_le n hn2 a b) ?_
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1/2) : ℝ) := by positivity
      gcongr
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have : ∑ n ∈ Finset.Ioc 1 M, 2 * ((n : ℝ) ^ (-(1/2) : ℝ)) / Real.log 2
        = (2 / Real.log 2) * ∑ n ∈ Finset.Ioc 1 M, ((n : ℝ) ^ (-(1/2) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    have hsub : ∑ n ∈ Finset.Ioc 1 M, ((n : ℝ) ^ (-(1/2) : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ (-(1/2) : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
      intro n hn
      have := Finset.mem_Ioc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
    have hbound := le_trans hsub (sum_rpow_neg_half_le M)
    have h2 : (0 : ℝ) < 2 / Real.log 2 := by positivity
    calc (2 / Real.log 2) * ∑ n ∈ Finset.Ioc 1 M, ((n : ℝ) ^ (-(1/2) : ℝ))
        ≤ (2 / Real.log 2) * (2 * Real.sqrt M) := by
          exact mul_le_mul_of_nonneg_left hbound h2.le
      _ = 4 * Real.sqrt M / Real.log 2 := by ring
  have hhigh : ‖∑ n ∈ Finset.Ioc M N, ∫ t in a..b, (n : ℂ) ^ (-(linePt t))‖
      ≤ 4 * Real.sqrt N / Real.log M := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioc M N,
        ‖∫ t in a..b, (n : ℂ) ^ (-(linePt t))‖
          ≤ 2 * ((n : ℝ) ^ (-(1/2) : ℝ)) / Real.log M := by
      intro n hn
      have hnM : M < n := (Finset.mem_Ioc.mp hn).1
      have hn2 : 2 ≤ n := by omega
      have hlogn : Real.log M ≤ Real.log n := by
        refine Real.log_le_log ?_ ?_
        · exact_mod_cast lt_of_lt_of_le two_pos hM
        · exact_mod_cast hnM.le
      refine le_trans (norm_integral_cpow_neg_linePt_le n hn2 a b) ?_
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1/2) : ℝ) := by positivity
      gcongr
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have heq : ∑ n ∈ Finset.Ioc M N, 2 * ((n : ℝ) ^ (-(1/2) : ℝ)) / Real.log M
        = (2 / Real.log M) * ∑ n ∈ Finset.Ioc M N, ((n : ℝ) ^ (-(1/2) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [heq]
    have hsub : ∑ n ∈ Finset.Ioc M N, ((n : ℝ) ^ (-(1/2) : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-(1/2) : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
      intro n hn
      have := Finset.mem_Ioc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
    have hbound := le_trans hsub (sum_rpow_neg_half_le N)
    have h2 : (0 : ℝ) < 2 / Real.log M := by positivity
    calc (2 / Real.log M) * ∑ n ∈ Finset.Ioc M N, ((n : ℝ) ^ (-(1/2) : ℝ))
        ≤ (2 / Real.log M) * (2 * Real.sqrt N) := mul_le_mul_of_nonneg_left hbound h2.le
      _ = 4 * Real.sqrt N / Real.log M := by ring
  linarith

/-! ## Basic estimates on the critical line -/

theorem continuous_linePt : Continuous linePt := by
  unfold linePt
  fun_prop

theorem norm_linePt_sub_one_ge (t : ℝ) : |t| ≤ ‖linePt t - 1‖ := by
  have h : linePt t - 1 = ((-(1/2) : ℝ) : ℂ) + (t : ℂ) * I := by
    rw [linePt]; push_cast; ring
  rw [h, Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have : Real.sqrt (t ^ 2) ≤ Real.sqrt ((-(1/2) + (t * 0 - 0 * 1)) * (-(1/2) + (t * 0 - 0 * 1))
      + (0 + (t * 1 + 0 * 0)) * (0 + (t * 1 + 0 * 0))) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [sq_nonneg t]
  calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ _ := this

theorem norm_linePt_le (t : ℝ) : ‖linePt t‖ ≤ 1/2 + |t| := by
  have h : linePt t = ((1/2 : ℝ) : ℂ) + (t : ℂ) * I := rfl
  rw [h]
  refine le_trans (norm_add_le _ _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem linePt_ne_one (t : ℝ) : linePt t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [linePt_re, Complex.one_re] at this
  norm_num at this

/-! ## The Euler–Maclaurin remainder -/

theorem continuous_emTail_line {N : ℕ} (hN : 1 ≤ N) :
    Continuous fun t : ℝ => emTail N (linePt t) := by
  have hdiff := differentiableOn_emTail (N := N) hN
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : linePt t ∈ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1}) :=
    ⟨linePt_re_pos t, linePt_ne_one t⟩
  have hat : ContinuousAt (emTail N) (linePt t) :=
    (hdiff.differentiableAt (isOpen_emStrip.mem_nhds hmem)).continuousAt
  exact hat.comp continuous_linePt.continuousAt

theorem norm_integral_linePt_mul_emTail_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in T..(2*T), linePt t * emTail N (linePt t)‖
      ≤ (1 + 4 * T) / Real.sqrt N * T := by
  have hbound : ∀ t ∈ Set.uIoc T (2*T), ‖linePt t * emTail N (linePt t)‖
      ≤ (1 + 4 * T) / Real.sqrt N := by
    intro t ht
    have htmem : t ∈ Set.Ioc T (2*T) := by
      rwa [Set.uIoc_of_le (by linarith)] at ht
    have habs : |t| ≤ 2 * T := by
      rw [abs_of_nonneg (le_trans hT htmem.1.le)]
      exact htmem.2
    have h1 : ‖linePt t‖ ≤ 1/2 + 2 * T := le_trans (norm_linePt_le t) (by linarith)
    have h2 : ‖emTail N (linePt t)‖ ≤ 2 / Real.sqrt N := by
      have := norm_emTail_le hN (linePt_re_pos t) (linePt_ne_one t)
      rw [linePt_re] at this
      rw [rpow_neg_half_eq] at this
      calc ‖emTail N (linePt t)‖ ≤ (Real.sqrt N)⁻¹ / (1/2 : ℝ) := by
            simpa using this
        _ = 2 / Real.sqrt N := by
            rw [div_div_eq_mul_div, inv_eq_one_div]
            ring
    have hnn : (0 : ℝ) ≤ 2 / Real.sqrt N := by positivity
    calc ‖linePt t * emTail N (linePt t)‖ = ‖linePt t‖ * ‖emTail N (linePt t)‖ := norm_mul _ _
      _ ≤ (1/2 + 2 * T) * (2 / Real.sqrt N) := by
          refine mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
      _ = (1 + 4 * T) / Real.sqrt N := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc ‖∫ t in T..(2*T), linePt t * emTail N (linePt t)‖
      ≤ (1 + 4 * T) / Real.sqrt N * |2 * T - T| := this
    _ = (1 + 4 * T) / Real.sqrt N * T := by rw [show 2 * T - T = T by ring, abs_of_nonneg hT]

/-! ## The explicit continuation term -/

theorem cpow_one_sub_linePt {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    (N : ℂ) ^ (1 - linePt t)
      = ((Real.sqrt N : ℝ) : ℂ) * Complex.exp (-(Real.log N : ℂ) * I * (t : ℂ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
  have hsqrt : Real.sqrt N = Real.exp (Real.log N * (1/2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
  rw [Complex.cpow_def_of_ne_zero hN0, ← Complex.natCast_log, hsqrt, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  rw [linePt]
  push_cast
  ring

theorem norm_cpow_one_sub_linePt {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖(N : ℂ) ^ (1 - linePt t)‖ = Real.sqrt N := by
  rw [cpow_one_sub_linePt hN, norm_mul, norm_exp_neg_ofReal_mul_I_mul, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem hasDerivAt_linePt_sub_one (t : ℝ) :
    HasDerivAt (fun u : ℝ => linePt u - 1) I t := by
  have hof : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have := (hof.mul_const I).const_add ((1/2 : ℝ) : ℂ)
  simpa [linePt] using this.sub_const 1

theorem hasDerivAt_emPole_line {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    HasDerivAt (fun u : ℝ => emPole N (linePt u))
      (-(Real.log N : ℂ) * I * emPole N (linePt t)
        - I * ((N : ℂ) ^ (1 - linePt t) / (linePt t - 1) ^ 2)) t := by
  have hvne : ∀ u : ℝ, linePt u - 1 ≠ 0 := fun u => sub_ne_zero.mpr (linePt_ne_one u)
  have hof : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hinner : HasDerivAt (fun u : ℝ => -(Real.log N : ℂ) * I * (u : ℂ))
      (-(Real.log N : ℂ) * I) t := by
    simpa using hof.const_mul (-(Real.log N : ℂ) * I)
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(Real.log N : ℂ) * I * (u : ℂ)))
      (Complex.exp (-(Real.log N : ℂ) * I * (t : ℂ)) * (-(Real.log N : ℂ) * I)) t :=
    hinner.cexp
  have hu : HasDerivAt (fun u : ℝ =>
      ((Real.sqrt N : ℝ) : ℂ) * Complex.exp (-(Real.log N : ℂ) * I * (u : ℂ)))
      (((Real.sqrt N : ℝ) : ℂ) *
        (Complex.exp (-(Real.log N : ℂ) * I * (t : ℂ)) * (-(Real.log N : ℂ) * I))) t :=
    hexp.const_mul _
  have hv := hasDerivAt_linePt_sub_one t
  have hdiv := hu.div hv (hvne t)
  have hfun : (fun u : ℝ => emPole N (linePt u))
      = fun u : ℝ =>
        ((Real.sqrt N : ℝ) : ℂ) * Complex.exp (-(Real.log N : ℂ) * I * (u : ℂ))
          / (linePt u - 1) := by
    funext u
    simp only [emPole]
    rw [cpow_one_sub_linePt hN u]
  rw [hfun]
  convert hdiv using 1
  simp only [emPole]
  rw [cpow_one_sub_linePt hN t]
  field_simp
  ring

theorem continuous_emPole_line {N : ℕ} (hN : 1 ≤ N) :
    Continuous fun t : ℝ => emPole N (linePt t) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_emPole_line hN t).continuousAt

theorem continuous_emPoleSq_line {N : ℕ} (hN : 1 ≤ N) :
    Continuous fun t : ℝ => (N : ℂ) ^ (1 - linePt t) / (linePt t - 1) ^ 2 := by
  have hnum : Continuous fun t : ℝ =>
      ((Real.sqrt N : ℝ) : ℂ) * Complex.exp (-(Real.log N : ℂ) * I * (t : ℂ)) := by
    fun_prop
  have hden : Continuous fun t : ℝ => (linePt t - 1) ^ 2 :=
    ((continuous_linePt.sub continuous_const).pow 2)
  have hne : ∀ t : ℝ, (linePt t - 1) ^ 2 ≠ 0 := fun t =>
    pow_ne_zero 2 (sub_ne_zero.mpr (linePt_ne_one t))
  have := hnum.div hden hne
  refine this.congr fun t => ?_
  simp only [Pi.div_apply]
  rw [cpow_one_sub_linePt hN t]

theorem norm_integral_emPole_line_le {N : ℕ} (hN : 2 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..(2*T), emPole N (linePt t)‖ ≤ 3 * Real.sqrt N / (Real.log N * T) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hsq : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  set P : ℝ → ℂ := fun t => emPole N (linePt t) with hP
  set Q : ℝ → ℂ := fun t => (N : ℂ) ^ (1 - linePt t) / (linePt t - 1) ^ 2 with hQ
  have hPc : Continuous P := continuous_emPole_line hN1
  have hQc : Continuous Q := continuous_emPoleSq_line hN1
  have hderiv : ∀ t ∈ Set.uIcc T (2*T),
      HasDerivAt P (-(Real.log N : ℂ) * I * P t - I * Q t) t :=
    fun t _ => hasDerivAt_emPole_line hN1 t
  have hint : IntervalIntegrable (fun t => -(Real.log N : ℂ) * I * P t - I * Q t)
      MeasureTheory.volume T (2*T) :=
    ((hPc.const_mul _).sub (hQc.const_mul _)).intervalIntegrable _ _
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsplit : (∫ t in T..(2*T), (-(Real.log N : ℂ) * I * P t - I * Q t))
      = -(Real.log N : ℂ) * I * (∫ t in T..(2*T), P t)
        - I * (∫ t in T..(2*T), Q t) := by
    rw [intervalIntegral.integral_sub ((hPc.const_mul _).intervalIntegrable _ _)
      ((hQc.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at hsub
  -- pointwise bounds
  have hPbound : ∀ t : ℝ, 0 < t → ‖P t‖ ≤ Real.sqrt N / t := by
    intro t ht
    have hden : t ≤ ‖linePt t - 1‖ := by
      have := norm_linePt_sub_one_ge t
      rwa [abs_of_pos ht] at this
    simp only [hP, emPole]
    rw [norm_div, norm_cpow_one_sub_linePt hN1]
    exact div_le_div_of_nonneg_left hsq ht hden
  have hQbound : ∀ t : ℝ, 0 < t → ‖Q t‖ ≤ Real.sqrt N / t ^ 2 := by
    intro t ht
    have hden : t ≤ ‖linePt t - 1‖ := by
      have := norm_linePt_sub_one_ge t
      rwa [abs_of_pos ht] at this
    rw [hQ, norm_div, norm_pow, norm_cpow_one_sub_linePt hN1]
    have h2 : t ^ 2 ≤ ‖linePt t - 1‖ ^ 2 := by
      exact pow_le_pow_left₀ ht.le hden 2
    exact div_le_div_of_nonneg_left hsq (by positivity) h2
  have hQint : ‖∫ t in T..(2*T), Q t‖ ≤ Real.sqrt N / T := by
    have hb : ∀ t ∈ Set.uIoc T (2*T), ‖Q t‖ ≤ Real.sqrt N / T ^ 2 := by
      intro t ht
      have htmem : t ∈ Set.Ioc T (2*T) := by
        rwa [Set.uIoc_of_le (by linarith)] at ht
      have htpos : 0 < t := lt_trans hTpos htmem.1
      refine le_trans (hQbound t htpos) ?_
      have : T ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hTpos.le htmem.1.le 2
      exact div_le_div_of_nonneg_left hsq (by positivity) this
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    calc ‖∫ t in T..(2*T), Q t‖ ≤ Real.sqrt N / T ^ 2 * |2 * T - T| := this
      _ = Real.sqrt N / T := by
          rw [show 2 * T - T = T by ring, abs_of_pos hTpos]
          field_simp
  have hPT : ‖P T‖ ≤ Real.sqrt N / T := hPbound T hTpos
  have hP2T : ‖P (2*T)‖ ≤ Real.sqrt N / T := by
    refine le_trans (hPbound (2*T) (by linarith)) ?_
    exact div_le_div_of_nonneg_left hsq hTpos (by linarith)
  -- conclude
  have hkey : Real.log N * ‖∫ t in T..(2*T), P t‖ ≤ 3 * (Real.sqrt N / T) := by
    have hnorm : ‖-(Real.log N : ℂ) * I * (∫ t in T..(2*T), P t)‖
        = Real.log N * ‖∫ t in T..(2*T), P t‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hlog]
    have hid : -(Real.log N : ℂ) * I * (∫ t in T..(2*T), P t)
        = (P (2*T) - P T) + I * (∫ t in T..(2*T), Q t) := by
      linear_combination hsub
    rw [← hnorm, hid]
    calc ‖(P (2*T) - P T) + I * (∫ t in T..(2*T), Q t)‖
        ≤ ‖P (2*T) - P T‖ + ‖I * (∫ t in T..(2*T), Q t)‖ := norm_add_le _ _
      _ ≤ (‖P (2*T)‖ + ‖P T‖) + ‖∫ t in T..(2*T), Q t‖ := by
          have h1 : ‖P (2*T) - P T‖ ≤ ‖P (2*T)‖ + ‖P T‖ := norm_sub_le _ _
          have h2 : ‖I * (∫ t in T..(2*T), Q t)‖ = ‖∫ t in T..(2*T), Q t‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
          linarith
      _ ≤ 3 * (Real.sqrt N / T) := by linarith
  rw [le_div_iff₀ (by positivity : (0:ℝ) < Real.log N * T)]
  have h := mul_le_mul_of_nonneg_right hkey hTpos.le
  have h2 : 3 * (Real.sqrt N / T) * T = 3 * Real.sqrt N := by field_simp
  rw [h2] at h
  calc ‖∫ t in T..(2*T), P t‖ * (Real.log N * T)
      = Real.log N * ‖∫ t in T..(2*T), P t‖ * T := by ring
    _ ≤ 3 * Real.sqrt N := h

end RHTower
