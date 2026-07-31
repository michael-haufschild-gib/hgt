import GaloisForLFunctions.RHTower.BoseCumulantJets
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# The Zipf half of the Bose-log cumulants

Under the Gamma/Zipf factorization `T = G/N` of the Bose-log law, the zeta factor of the Mellin
normalizer carries the arithmetic.  Its cumulants are the log-weighted von Mangoldt sums

`(-1)^r (d/da)^r log (zeta (a+1)) = sum_m Lambda m (log m)^(r-1) m^(-(a+1))`,

which are strictly positive at every order.  This is the probabilistic form of the all-order prime
sign alignment: the arithmetic side of every completed Xi jet is a cumulant sequence of the
zeta-distributed integer, hence positive term by term.

The order-one link `zeta'/zeta = - sum_m Lambda m m^(-s)` is the only arithmetic input; every
higher order is termwise differentiation of that Dirichlet series, with a uniform majorant on each
ray `(c, infinity)`, `c > 1`.

The mixture density closing the factorization is the same geometric expansion of the Bose kernel
that evaluates the Mellin coordinate.
-/

open Set Filter

namespace RHTower

noncomputable section

/-! ### The log-weighted von Mangoldt series -/

/-- The log-weighted real von Mangoldt Dirichlet series. -/
def vonMangoldtLogSeries (k : ℕ) (s : ℝ) : ℝ :=
  ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k * (m : ℝ) ^ (-s)

theorem vonMangoldtLogTerm_nonneg (k : ℕ) (s : ℝ) (m : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k * (m : ℝ) ^ (-s) := by
  have h1 : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (0:ℝ) ≤ Real.log m ^ k := pow_nonneg (Real.log_natCast_nonneg m) k
  have h3 : (0:ℝ) ≤ (m : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  positivity

theorem summable_vonMangoldtLogTerm {c : ℝ} (hc : 1 < c) (k : ℕ) :
    Summable (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k * (m : ℝ) ^ (-c)) := by
  set d : ℝ := (1 + c) / 2 with hd
  have hd1 : (1:ℝ) < d := by rw [hd]; linarith
  have hdc : d < c := by rw [hd]; linarith
  set δ : ℝ := (c - d) / (k + 1) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    apply div_pos (by linarith)
    positivity
  have hmaj : Summable (fun m : ℕ => (δ ^ k)⁻¹ *
      ((ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) ^ d)) :=
    (summable_vonMangoldt_div_rpow hd1).mul_left _
  refine Summable.of_nonneg_of_le (fun m => vonMangoldtLogTerm_nonneg k c m) (fun m => ?_) hmaj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm1 : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0:ℝ) < (m : ℝ) := by linarith
    have hlog : (0:ℝ) ≤ Real.log m := Real.log_natCast_nonneg m
    have hstep : Real.log m ^ k ≤ ((m : ℝ) ^ δ / δ) ^ k :=
      pow_le_pow_left₀ hlog (Real.log_le_rpow_div (le_of_lt hmpos) hδpos) k
    have hpowk : ((m : ℝ) ^ δ / δ) ^ k = (m : ℝ) ^ (δ * k) * (δ ^ k)⁻¹ := by
      rw [div_pow, ← Real.rpow_natCast ((m : ℝ) ^ δ) k, ← Real.rpow_mul (le_of_lt hmpos),
        div_eq_mul_inv]
    have hexp : δ * (k : ℝ) - c ≤ -d := by
      rw [hδ]
      have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hkey : (c - d) / ((k : ℝ) + 1) * (k : ℝ) ≤ c - d := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    have hrpow : (m : ℝ) ^ (δ * (k : ℝ) - c) ≤ (m : ℝ) ^ (-d) :=
      Real.rpow_le_rpow_of_exponent_le hm1 hexp
    have hsplit : (m : ℝ) ^ (δ * (k : ℝ)) * (m : ℝ) ^ (-c) = (m : ℝ) ^ (δ * (k : ℝ) - c) := by
      rw [← Real.rpow_add hmpos]
      ring_nf
    have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hmc : (0:ℝ) ≤ (m : ℝ) ^ (-c) := Real.rpow_nonneg (le_of_lt hmpos) _
    have hδk : (0:ℝ) < (δ ^ k)⁻¹ := by positivity
    calc
      (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k * (m : ℝ) ^ (-c)
          ≤ (ArithmeticFunction.vonMangoldt m : ℝ) * ((m : ℝ) ^ (δ * k) * (δ ^ k)⁻¹) *
            (m : ℝ) ^ (-c) := by
            rw [← hpowk]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hstep hΛ) hmc
      _ = (δ ^ k)⁻¹ * ((ArithmeticFunction.vonMangoldt m : ℝ) *
            ((m : ℝ) ^ (δ * (k : ℝ)) * (m : ℝ) ^ (-c))) := by
            ring
      _ ≤ (δ ^ k)⁻¹ * ((ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) ^ d) := by
            rw [hsplit]
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hδk)
            rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hmpos)]
            exact mul_le_mul_of_nonneg_left hrpow hΛ

/-! ### Termwise differentiation -/

theorem hasDerivAt_vonMangoldtLogTerm (k : ℕ) (m : ℕ) (s : ℝ) :
    HasDerivAt
      (fun y : ℝ => (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k * (m : ℝ) ^ (-y))
      (-((ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) * (m : ℝ) ^ (-s))) s := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, ArithmeticFunction.map_zero, zero_mul, Real.log_zero]
    simpa using hasDerivAt_const s (0 : ℝ)
  · have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hfun : (fun y : ℝ => (m : ℝ) ^ (-y))
        = fun y : ℝ => Real.exp (Real.log m * (-y)) := by
      funext y
      rw [Real.rpow_def_of_pos hmpos]
    have hlin : HasDerivAt (fun y : ℝ => Real.log m * (-y)) (-Real.log m) s := by
      have h := ((hasDerivAt_id s).neg).const_mul (Real.log (m : ℝ))
      rw [show Real.log (m : ℝ) * (-1 : ℝ) = -Real.log (m : ℝ) from by ring] at h
      exact h
    have hbase : HasDerivAt (fun y : ℝ => (m : ℝ) ^ (-y))
        (Real.exp (Real.log m * (-s)) * (-Real.log m)) s := by
      rw [hfun]
      exact hlin.exp
    have hres := hbase.const_mul
      ((ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k)
    have hval : (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k *
        (Real.exp (Real.log m * (-s)) * (-Real.log m))
        = -((ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) * (m : ℝ) ^ (-s)) := by
      rw [Real.rpow_def_of_pos hmpos]
      ring
    rw [← hval]
    exact hres

theorem hasDerivAt_vonMangoldtLogSeries {s : ℝ} (hs : 1 < s) (k : ℕ) :
    HasDerivAt (vonMangoldtLogSeries k) (-(vonMangoldtLogSeries (k + 1) s)) s := by
  set c : ℝ := (1 + s) / 2 with hcdef
  have hc1 : (1:ℝ) < c := by rw [hcdef]; linarith
  have hcs : c < s := by rw [hcdef]; linarith
  have hu : Summable (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) * (m : ℝ) ^ (-c)) :=
    summable_vonMangoldtLogTerm hc1 (k + 1)
  have hderiv : ∀ m : ℕ, ∀ y ∈ Ioi c,
      HasDerivAt
        (fun t : ℝ => (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k * (m : ℝ) ^ (-t))
        (-((ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) * (m : ℝ) ^ (-y))) y :=
    fun m y _ => hasDerivAt_vonMangoldtLogTerm k m y
  have hbound : ∀ m : ℕ, ∀ y ∈ Ioi c,
      ‖-((ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) * (m : ℝ) ^ (-y))‖ ≤
        (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) * (m : ℝ) ^ (-c) := by
    intro m y hy
    have hy' : c < y := hy
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (vonMangoldtLogTerm_nonneg (k + 1) y m)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm1 : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hcoef : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) := by
        have h1 : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) :=
          ArithmeticFunction.vonMangoldt_nonneg
        have h2 : (0:ℝ) ≤ Real.log m ^ (k + 1) :=
          pow_nonneg (Real.log_natCast_nonneg m) _
        positivity
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)) hcoef
  have hsum0 : Summable (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ k * (m : ℝ) ^ (-s)) :=
    summable_vonMangoldtLogTerm hs k
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hderiv hbound
    (Set.mem_Ioi.mpr hcs) hsum0 (Set.mem_Ioi.mpr hcs)
  have hvalue : -(vonMangoldtLogSeries (k + 1) s)
      = ∑' m : ℕ,
        -((ArithmeticFunction.vonMangoldt m : ℝ) * Real.log m ^ (k + 1) * (m : ℝ) ^ (-s)) := by
    rw [vonMangoldtLogSeries, ← tsum_neg]
  rw [hvalue]
  exact hmain

theorem iteratedDeriv_vonMangoldtLogSeries (j : ℕ) :
    ∀ {s : ℝ}, 1 < s →
      iteratedDeriv j (vonMangoldtLogSeries 0) s = (-1 : ℝ) ^ j * vonMangoldtLogSeries j s := by
  induction j with
  | zero =>
      intro s _
      simp [iteratedDeriv_zero]
  | succ j ih =>
      intro s hs
      have hEq : iteratedDeriv j (vonMangoldtLogSeries 0)
          =ᶠ[nhds s] (fun y : ℝ => (-1 : ℝ) ^ j * vonMangoldtLogSeries j y) := by
        filter_upwards [Ioi_mem_nhds hs] with y hy using ih hy
      rw [iteratedDeriv_succ, hEq.deriv_eq,
        ((hasDerivAt_vonMangoldtLogSeries hs j).const_mul ((-1 : ℝ) ^ j)).deriv]
      ring

/-! ### The order-one arithmetic link -/

theorem hasDerivAt_realZetaSeries {s : ℝ} (hs : 1 < s) :
    HasDerivAt realZetaSeries ((deriv riemannZeta ((s : ℝ) : ℂ)).re) s := by
  have hne : ((s : ℝ) : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    linarith
  have hz : HasDerivAt riemannZeta (deriv riemannZeta ((s : ℝ) : ℂ)) ((s : ℝ) : ℂ) :=
    (differentiableAt_riemannZeta hne).hasDerivAt
  have hreal := hz.comp_ofReal
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hreal
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with y hy
  rw [Function.comp_apply, Complex.reCLM_apply, ← ofReal_realZetaSeries (s := y) hy,
    Complex.ofReal_re]

theorem deriv_log_realZetaSeries {s : ℝ} (hs : 1 < s) :
    deriv (fun b : ℝ => Real.log (realZetaSeries b)) s = -vonMangoldtLogSeries 0 s := by
  have hZpos : 0 < realZetaSeries s := realZetaSeries_pos hs
  have hlog := (hasDerivAt_realZetaSeries hs).log (ne_of_gt hZpos)
  rw [hlog.deriv]
  have hre : (1:ℝ) < (((s : ℝ) : ℂ)).re := by simpa using hs
  have harith := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  rw [LSeries_vonMangoldt_ofReal s, ← ofReal_realZetaSeries (s := s) hs] at harith
  have hZne : (((realZetaSeries s : ℝ)) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hZpos
  have hmul : ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) *
      (((realZetaSeries s : ℝ)) : ℂ) = -deriv riemannZeta ((s : ℝ) : ℂ) := by
    rw [harith]
    field_simp
  have hreal : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s) *
      realZetaSeries s = -(deriv riemannZeta ((s : ℝ) : ℂ)).re := by
    have h := congrArg Complex.re hmul
    rwa [← Complex.ofReal_mul, Complex.ofReal_re, Complex.neg_re] at h
  have hV : vonMangoldtLogSeries 0 s =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s := by
    rw [vonMangoldtLogSeries]
    refine tsum_congr (fun n => ?_)
    rw [pow_zero, mul_one, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  rw [hV]
  field_simp
  linarith [hreal]

theorem iteratedDeriv_log_realZetaSeries {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 1 < s) :
    iteratedDeriv r (fun b : ℝ => Real.log (realZetaSeries b)) s
      = (-1 : ℝ) ^ r * vonMangoldtLogSeries (r - 1) s := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, r = j + 1 := ⟨r - 1, by omega⟩
  have hEq : deriv (fun b : ℝ => Real.log (realZetaSeries b))
      =ᶠ[nhds s] (fun y : ℝ => -vonMangoldtLogSeries 0 y) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy using deriv_log_realZetaSeries hy
  rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq j hEq]
  have hneg : (fun y : ℝ => -vonMangoldtLogSeries 0 y) = -(vonMangoldtLogSeries 0) := rfl
  rw [hneg, iteratedDeriv_neg, iteratedDeriv_vonMangoldtLogSeries j hs]
  simp only [Nat.add_sub_cancel]
  ring

/-! ### Positivity and the Zipf cumulant law -/

theorem vonMangoldtLogSeries_pos {k : ℕ} {s : ℝ} (hs : 1 < s) :
    0 < vonMangoldtLogSeries k s := by
  have hsum := summable_vonMangoldtLogTerm hs k
  have hΛ : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : Real.log ((2:ℕ) : ℝ) = Real.log 2 := by norm_num
  have hterm2 :
      0 < (ArithmeticFunction.vonMangoldt 2 : ℝ) * Real.log ((2:ℕ) : ℝ) ^ k *
        ((2:ℕ) : ℝ) ^ (-s) := by
    have hrp : (0:ℝ) < ((2:ℕ) : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
    have hk : (0:ℝ) < Real.log ((2:ℕ) : ℝ) ^ k := by
      rw [hcast]
      exact pow_pos hlog2 k
    rw [hΛ]
    positivity
  exact hsum.tsum_pos (fun m => vonMangoldtLogTerm_nonneg k s m) 2 hterm2

/-- **Equation (12).**  The Zipf cumulants of the Bose-log law are exactly the log-weighted
von Mangoldt sums. -/
theorem zipfCumulant_eq_vonMangoldtLogSeries {r : ℕ} (hr : 1 ≤ r) {a : ℝ} (ha : 0 < a) :
    (-1 : ℝ) ^ r * iteratedDeriv r (fun b : ℝ => Real.log (realZetaSeries (b + 1))) a
      = vonMangoldtLogSeries (r - 1) (a + 1) := by
  have hshift : iteratedDeriv r (fun b : ℝ => Real.log (realZetaSeries (b + 1))) a
      = iteratedDeriv r (fun b : ℝ => Real.log (realZetaSeries b)) (a + 1) := by
    rw [iteratedDeriv_comp_add_const r (fun b : ℝ => Real.log (realZetaSeries b)) 1]
  rw [hshift, iteratedDeriv_log_realZetaSeries hr (by linarith : (1:ℝ) < a + 1),
    ← mul_assoc, ← pow_add, show r + r = 2 * r from by ring, pow_mul]
  norm_num

/-- The all-order prime sign alignment as a probability law: every Zipf cumulant is strictly
positive. -/
theorem zipfCumulant_pos {r : ℕ} (hr : 1 ≤ r) {a : ℝ} (ha : 0 < a) :
    0 < (-1 : ℝ) ^ r * iteratedDeriv r (fun b : ℝ => Real.log (realZetaSeries (b + 1))) a := by
  rw [zipfCumulant_eq_vonMangoldtLogSeries hr ha]
  exact vonMangoldtLogSeries_pos (by linarith)

/-! ### The Gamma/Zipf mixture density -/

/-- **Equation (10).**  Mixing the scaled Gamma densities against the Zipf weights reproduces the
Bose density exactly: this is the density form of `T = G/N`. -/
theorem hasSum_gammaZipfMixture {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasSum (fun m : ℕ =>
      (((m : ℝ) + 1) ^ (-(a + 1)) / realZetaSeries (a + 1)) * ((m : ℝ) + 1) *
        ((((m : ℝ) + 1) * t) ^ a * Real.exp (-((m : ℝ) + 1) * t) / Real.Gamma (a + 1)))
      (t ^ a / ((Real.exp t - 1) * boseMellin a)) := by
  have hZ : 0 < realZetaSeries (a + 1) := realZetaSeries_pos (by linarith)
  have hG : 0 < Real.Gamma (a + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hker := (hasSum_boseKernel ht).mul_left
    (t ^ a / (realZetaSeries (a + 1) * Real.Gamma (a + 1)))
  have hfun : (fun m : ℕ =>
      (((m : ℝ) + 1) ^ (-(a + 1)) / realZetaSeries (a + 1)) * ((m : ℝ) + 1) *
        ((((m : ℝ) + 1) * t) ^ a * Real.exp (-((m : ℝ) + 1) * t) / Real.Gamma (a + 1)))
      = fun m : ℕ => t ^ a / (realZetaSeries (a + 1) * Real.Gamma (a + 1)) *
          Real.exp (-((m : ℝ) + 1) * t) := by
    funext m
    have hM : (0:ℝ) < (m : ℝ) + 1 := by positivity
    have hsplit : (((m : ℝ) + 1) * t) ^ a = ((m : ℝ) + 1) ^ a * t ^ a :=
      Real.mul_rpow (le_of_lt hM) (le_of_lt ht)
    have hcollect : ((m : ℝ) + 1) ^ (-(a + 1)) * ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ a = 1 := by
      have h1 : ((m : ℝ) + 1) ^ (-(a + 1)) * ((m : ℝ) + 1) ^ a
          = ((m : ℝ) + 1) ^ (-(a + 1) + a) := (Real.rpow_add hM _ _).symm
      calc ((m : ℝ) + 1) ^ (-(a + 1)) * ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ a
          = (((m : ℝ) + 1) ^ (-(a + 1)) * ((m : ℝ) + 1) ^ a) * ((m : ℝ) + 1) := by ring
        _ = ((m : ℝ) + 1) ^ (-(1 : ℝ)) * ((m : ℝ) + 1) := by
            rw [h1, show (-(a + 1) + a : ℝ) = -1 from by ring]
        _ = 1 := by
            rw [Real.rpow_neg (le_of_lt hM), Real.rpow_one]
            field_simp
    calc ((m : ℝ) + 1) ^ (-(a + 1)) / realZetaSeries (a + 1) * ((m : ℝ) + 1) *
          ((((m : ℝ) + 1) * t) ^ a * Real.exp (-((m : ℝ) + 1) * t) / Real.Gamma (a + 1))
        = (((m : ℝ) + 1) ^ (-(a + 1)) * ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ a) *
            (t ^ a / (realZetaSeries (a + 1) * Real.Gamma (a + 1)) *
              Real.exp (-((m : ℝ) + 1) * t)) := by
          rw [hsplit]; ring
      _ = t ^ a / (realZetaSeries (a + 1) * Real.Gamma (a + 1)) *
            Real.exp (-((m : ℝ) + 1) * t) := by rw [hcollect, one_mul]
  rw [hfun]
  have hexpne : Real.exp t - 1 ≠ 0 := by
    have h1 : (1:ℝ) < Real.exp t := by
      have := Real.add_one_lt_exp (x := t) (ne_of_gt ht)
      linarith
    linarith
  have hval : t ^ a / (realZetaSeries (a + 1) * Real.Gamma (a + 1)) * (Real.exp t - 1)⁻¹
      = t ^ a / ((Real.exp t - 1) * boseMellin a) := by
    rw [boseMellin_eq ha]
    field_simp [hZ.ne', hG.ne', hexpne]
  rw [← hval]
  exact hker

end

end RHTower
