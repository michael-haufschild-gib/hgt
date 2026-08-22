import GaloisForLFunctions.HTGeometry.AsymptoticFlatHypertranscendentalInvisibility

/-!
# The asymptotic-scale recession ladder

At rung `k` the witness is `1/Γ(z^k)`.  It is hypertranscendental because the monomial substitution
is invertible on differential algebraicity and `1/Γ` is hypertranscendental; and it is flat against
every exponential gauge `exp(-α x^m)` with `m < k`, because `Γ(x^k) ≥ (x^k/2)^N` with the *variable*
order `N ≈ 3α x^m` already beats `exp(3α x^m)` times any power.

The jet correction is `exp(-z^{k+1}) Q`, which is flat at the same gauges — the plain `e^{-z}Q` of
the previous rung is visible at every gauge deeper than `e^{-x}`, which is why the card replaces it.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- A crude but uniform lower bound: `Γ(y) ≥ (y/2)^N` whenever `N ≤ y/2` and `y ≥ 4`. -/
theorem gamma_ge_half_pow {y : ℝ} {N : ℕ} (hy : 4 ≤ y) (hN : (N : ℝ) ≤ y / 2) :
    (y / 2) ^ N ≤ Real.Gamma y := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simpa using one_le_gamma_of_two_le (by linarith)
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, N = j + 1 := ⟨N - 1, by omega⟩
    have hcast : ((j : ℝ) + 1) ≤ y / 2 := by exact_mod_cast hN
    have hge : (j : ℝ) + 3 ≤ y := by linarith
    refine le_trans ?_ (gamma_ge_pow (k := j) (x := y) hge)
    refine pow_le_pow_left₀ (by linarith) ?_ (j + 1)
    linarith

/-- **`Γ(x^k)` beats every power times every exponential gauge of lower degree.** -/
theorem tendsto_pow_mul_exp_div_gamma_pow {alpha : ℝ} (halpha : 0 < alpha) {k m : ℕ}
    (hm : m < k) (M : ℕ) :
    Tendsto (fun x : ℝ => x ^ M * Real.exp (alpha * x ^ m) / Real.Gamma (x ^ k))
      atTop (nhds 0) := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le m) hm
  have hmain : ∀ᶠ x : ℝ in atTop,
      x ^ M * Real.exp (alpha * x ^ m) / Real.Gamma (x ^ k) ≤ x⁻¹ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop ((2 : ℝ) ^ (M + 2)),
      eventually_ge_atTop (2 * (3 * alpha + (M : ℝ) + 3)), eventually_ge_atTop (6 : ℝ)]
      with x hx2 hxM hxa hx6
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hxpos : (0 : ℝ) < x := by linarith
    have hxk : x ≤ x ^ k := le_self_pow₀ hx1 (by omega)
    have hxkpos : (0 : ℝ) < x ^ k := by positivity
    have hxk6 : (6 : ℝ) ≤ x ^ k := le_trans hx6 hxk
    -- the exponent
    set N : ℕ := ⌈3 * alpha * x ^ m⌉₊ + M + 2 with hN
    have hceil : (⌈3 * alpha * x ^ m⌉₊ : ℝ) ≤ 3 * alpha * x ^ m + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hxm : x ^ m ≤ x ^ (k - 1) := pow_le_pow_right₀ hx1 (by omega)
    have hNle : (N : ℝ) ≤ x ^ k / 2 := by
      have hstep : (N : ℝ) ≤ 3 * alpha * x ^ m + (M : ℝ) + 3 := by
        rw [hN]
        push_cast
        linarith
      have hxm1 : (1 : ℝ) ≤ x ^ (k - 1) := one_le_pow₀ hx1
      have hbound : 3 * alpha * x ^ m + (M : ℝ) + 3
          ≤ (3 * alpha + (M : ℝ) + 3) * x ^ (k - 1) := by
        nlinarith [halpha.le, pow_nonneg hxpos.le m, pow_nonneg hxpos.le (k - 1)]
      have hxkfac : x ^ k = x * x ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hfin : (3 * alpha + (M : ℝ) + 3) * x ^ (k - 1) ≤ x ^ k / 2 := by
        rw [hxkfac]
        have hxm1' : (0 : ℝ) ≤ x ^ (k - 1) := pow_nonneg hxpos.le _
        nlinarith
      linarith
    have hgam : (x ^ k / 2) ^ N ≤ Real.Gamma (x ^ k) :=
      gamma_ge_half_pow (by linarith) hNle
    -- split the power
    have hbase : (Real.exp 1) ≤ x ^ k / 2 := by
      have : Real.exp 1 ≤ 3 := by
        have := Real.exp_one_lt_d9
        linarith
      linarith
    have hsplit : Real.exp (3 * alpha * x ^ m) * x ^ (M + 1) ≤ (x ^ k / 2) ^ N := by
      have hxk2pos : (0 : ℝ) < x ^ k / 2 := by linarith
      have h1 : Real.exp (3 * alpha * x ^ m) ≤ (x ^ k / 2) ^ (⌈3 * alpha * x ^ m⌉₊) := by
        calc Real.exp (3 * alpha * x ^ m)
            ≤ Real.exp 1 ^ (⌈3 * alpha * x ^ m⌉₊) := by
              rw [← Real.exp_nat_mul]
              refine Real.exp_le_exp.2 ?_
              have := Nat.le_ceil (3 * alpha * x ^ m)
              linarith
          _ ≤ (x ^ k / 2) ^ (⌈3 * alpha * x ^ m⌉₊) :=
              pow_le_pow_left₀ (Real.exp_nonneg 1) hbase _
      have h2 : x ^ (M + 1) ≤ (x ^ k / 2) ^ (M + 2) := by
        have hstep1 : x ^ (M + 1) ≤ (x / 2) ^ (M + 2) := by
          have hrw : (x / 2) ^ (M + 2) = x ^ (M + 2) / 2 ^ (M + 2) := by rw [div_pow]
          rw [hrw, le_div_iff₀ (by positivity)]
          calc x ^ (M + 1) * 2 ^ (M + 2) ≤ x ^ (M + 1) * x :=
                mul_le_mul_of_nonneg_left hxM (by positivity)
            _ = x ^ (M + 2) := by rw [← pow_succ]
        refine hstep1.trans (pow_le_pow_left₀ (by positivity) ?_ _)
        linarith
      calc Real.exp (3 * alpha * x ^ m) * x ^ (M + 1)
          ≤ (x ^ k / 2) ^ (⌈3 * alpha * x ^ m⌉₊) * (x ^ k / 2) ^ (M + 2) := by
            exact mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (x ^ k / 2) ^ N := by
            have hNsplit : N = ⌈3 * alpha * x ^ m⌉₊ + (M + 2) := by rw [hN]; omega
            rw [hNsplit]
            ring
    -- conclude
    have hgampos : (0 : ℝ) < Real.Gamma (x ^ k) := Real.Gamma_pos_of_pos hxkpos
    rw [div_le_iff₀ hgampos]
    have hkey : x ^ M * Real.exp (alpha * x ^ m) * x
        ≤ Real.exp (3 * alpha * x ^ m) * x ^ (M + 1) := by
      have hrw : x ^ M * Real.exp (alpha * x ^ m) * x = Real.exp (alpha * x ^ m) * x ^ (M + 1) := by
        rw [pow_succ]
        ring
      rw [hrw]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine Real.exp_le_exp.2 ?_
      nlinarith [pow_nonneg hxpos.le m, halpha.le]
    calc x ^ M * Real.exp (alpha * x ^ m)
        = (x ^ M * Real.exp (alpha * x ^ m) * x) * x⁻¹ := by field_simp
      _ ≤ (Real.exp (3 * alpha * x ^ m) * x ^ (M + 1)) * x⁻¹ :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ ≤ (x ^ k / 2) ^ N * x⁻¹ := mul_le_mul_of_nonneg_right hsplit (by positivity)
      _ ≤ Real.Gamma (x ^ k) * x⁻¹ := mul_le_mul_of_nonneg_right hgam (by positivity)
      _ = x⁻¹ * Real.Gamma (x ^ k) := by ring
  refine squeeze_zero' ?_ hmain tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have : (0:ℝ) < Real.Gamma (x ^ k) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ### Flatness against exponential gauges -/

/-- `E` is flat against the exponential gauge `exp (-α x^m)` along the positive real ray. -/
def FlatAtExpGauge (E : ℂ → ℂ) (alpha : ℝ) (m : ℕ) : Prop :=
  Tendsto (fun x : ℝ => ‖E (x : ℂ)‖ * Real.exp (alpha * x ^ m)) atTop (nhds 0)

theorem norm_invGamma_pow_ofReal {k : ℕ} {x : ℝ} (hx : 0 < x) :
    ‖(Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ = (Real.Gamma (x ^ k))⁻¹ := by
  have hxk : ((x : ℂ)) ^ k = ((x ^ k : ℝ) : ℂ) := by push_cast; ring
  have hpos : (0 : ℝ) < Real.Gamma (x ^ k) := Real.Gamma_pos_of_pos (by positivity)
  rw [hxk, Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- **The rung witness is flat against every lower exponential gauge.** -/
theorem flat_gauge_polynomial_mul_invGamma_pow {alpha : ℝ} (halpha : 0 < alpha) {k m : ℕ}
    (hm : m < k) (lam : ℂ) (A : Polynomial ℂ) :
    FlatAtExpGauge (fun z => lam * A.eval z * (Complex.Gamma (z ^ k))⁻¹) alpha m := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_eval_polynomial A
  refine squeeze_zero'
    (g := fun x : ℝ => (‖lam‖ * C) *
      (x ^ A.natDegree * Real.exp (alpha * x ^ m) / Real.Gamma (x ^ k))) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hgampos : (0 : ℝ) < Real.Gamma (x ^ k) := Real.Gamma_pos_of_pos (by positivity)
    show ‖lam * A.eval (x : ℂ) * (Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * Real.exp (alpha * x ^ m) ≤ _
    rw [norm_mul, norm_mul, norm_invGamma_pow_ofReal hxpos]
    calc ‖lam‖ * ‖A.eval (x : ℂ)‖ * (Real.Gamma (x ^ k))⁻¹ * Real.exp (alpha * x ^ m)
        ≤ ‖lam‖ * (C * x ^ A.natDegree) * (Real.Gamma (x ^ k))⁻¹ *
            Real.exp (alpha * x ^ m) := by
          gcongr
          exact hC x hx
      _ = (‖lam‖ * C) *
            (x ^ A.natDegree * Real.exp (alpha * x ^ m) / Real.Gamma (x ^ k)) := by
          rw [div_eq_mul_inv]
          ring
  · have := (tendsto_pow_mul_exp_div_gamma_pow halpha hm A.natDegree).const_mul (‖lam‖ * C)
    simpa using this

theorem flat_polynomial_mul_invGamma_pow {k : ℕ} (hk : 0 < k) (lam : ℂ) (A : Polynomial ℂ) :
    FlatInversePowers (fun z => lam * A.eval z * (Complex.Gamma (z ^ k))⁻¹) := by
  intro M
  obtain ⟨C, hC0, hC⟩ := exists_bound_eval_polynomial A
  refine squeeze_zero'
    (g := fun x : ℝ => (‖lam‖ * C) *
      (x ^ (A.natDegree + M) * Real.exp (1 * x ^ 0) / Real.Gamma (x ^ k))) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hgampos : (0 : ℝ) < Real.Gamma (x ^ k) := Real.Gamma_pos_of_pos (by positivity)
    have hexp1 : (1 : ℝ) ≤ Real.exp (1 * x ^ 0) := by
      rw [pow_zero, mul_one]
      exact Real.one_le_exp (by norm_num)
    show ‖lam * A.eval (x : ℂ) * (Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * x ^ M ≤ _
    rw [norm_mul, norm_mul, norm_invGamma_pow_ofReal hxpos]
    calc ‖lam‖ * ‖A.eval (x : ℂ)‖ * (Real.Gamma (x ^ k))⁻¹ * x ^ M
        ≤ ‖lam‖ * (C * x ^ A.natDegree) * (Real.Gamma (x ^ k))⁻¹ * x ^ M := by
          gcongr
          exact hC x hx
      _ = (‖lam‖ * C) * (x ^ (A.natDegree + M) / Real.Gamma (x ^ k)) := by
          rw [pow_add, div_eq_mul_inv]
          ring
      _ ≤ (‖lam‖ * C) *
            (x ^ (A.natDegree + M) * Real.exp (1 * x ^ 0) / Real.Gamma (x ^ k)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ hgampos hgampos]
          have hnn : (0:ℝ) ≤ x ^ (A.natDegree + M) * Real.Gamma (x ^ k) := by positivity
          nlinarith [mul_nonneg hnn (sub_nonneg.2 hexp1)]
  · have := (tendsto_pow_mul_exp_div_gamma_pow (alpha := 1) one_pos (m := 0) hk
      (A.natDegree + M)).const_mul (‖lam‖ * C)
    simpa using this

theorem norm_exp_neg_pow_ofReal {k : ℕ} (x : ℝ) :
    ‖Complex.exp (-((x : ℂ) ^ k))‖ = Real.exp (-(x ^ k)) := by
  have hxk : ((x : ℂ)) ^ k = ((x ^ k : ℝ) : ℂ) := by push_cast; ring
  rw [hxk, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]

theorem tendsto_pow_mul_exp_neg_half (d : ℕ) :
    Tendsto (fun x : ℝ => x ^ d * Real.exp (-(x / 2))) atTop (nhds 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d
  have hcomp := hbase.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2))
  have hmul := hcomp.const_mul ((2 : ℝ) ^ d)
  rw [mul_zero] at hmul
  refine hmul.congr fun x => ?_
  simp only [Function.comp_apply, id_eq]
  rw [div_pow]
  field_simp

/-- **The corrected jet carrier is flat against every lower exponential gauge.** -/
theorem flat_gauge_exp_neg_pow_mul_polynomial {alpha : ℝ} (halpha : 0 < alpha) {k m : ℕ}
    (hm : m < k) (Q : Polynomial ℂ) :
    FlatAtExpGauge (fun z => Complex.exp (-(z ^ k)) * Q.eval z) alpha m := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_eval_polynomial Q
  refine squeeze_zero'
    (g := fun x : ℝ => C * (x ^ Q.natDegree * Real.exp (-(x / 2)))) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (2 * alpha + 1),
      eventually_ge_atTop (2:ℝ)] with x hx hxa hx2
    have hxpos : (0 : ℝ) < x := by linarith
    have hxm : x ^ m ≤ x ^ (k - 1) := pow_le_pow_right₀ hx (by omega)
    have hxkfac : x ^ k = x * x ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hxk1 : (1 : ℝ) ≤ x ^ (k - 1) := one_le_pow₀ hx
    have hgauge : alpha * x ^ m - x ^ k ≤ -(x / 2) := by
      have h1 : alpha * x ^ m ≤ alpha * x ^ (k - 1) := by nlinarith [halpha.le]
      have h2 : x ^ k = x * x ^ (k - 1) := hxkfac
      nlinarith [halpha.le, pow_nonneg hxpos.le (k - 1)]
    show ‖Complex.exp (-((x : ℂ) ^ k)) * Q.eval (x : ℂ)‖ * Real.exp (alpha * x ^ m) ≤ _
    rw [norm_mul, norm_exp_neg_pow_ofReal]
    calc Real.exp (-(x ^ k)) * ‖Q.eval (x : ℂ)‖ * Real.exp (alpha * x ^ m)
        ≤ Real.exp (-(x ^ k)) * (C * x ^ Q.natDegree) * Real.exp (alpha * x ^ m) := by
          gcongr
          exact hC x hx
      _ = C * x ^ Q.natDegree * Real.exp (alpha * x ^ m - x ^ k) := by
          rw [Real.exp_sub, Real.exp_neg]
          field_simp
      _ ≤ C * x ^ Q.natDegree * Real.exp (-(x / 2)) := by
          gcongr
      _ = C * (x ^ Q.natDegree * Real.exp (-(x / 2))) := by ring
  · simpa using (tendsto_pow_mul_exp_neg_half Q.natDegree).const_mul C

theorem flat_exp_neg_pow_mul_polynomial {k : ℕ} (hk : 0 < k) (Q : Polynomial ℂ) :
    FlatInversePowers (fun z => Complex.exp (-(z ^ k)) * Q.eval z) := by
  intro M
  obtain ⟨C, hC0, hC⟩ := exists_bound_eval_polynomial Q
  refine squeeze_zero'
    (g := fun x : ℝ => C * (x ^ (Q.natDegree + M) * Real.exp (-(x / 2)))) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hxpos : (0 : ℝ) < x := by linarith
    have hxk : x ≤ x ^ k := le_self_pow₀ hx1 (by omega)
    have hgauge : -(x ^ k) ≤ -(x / 2) := by linarith
    show ‖Complex.exp (-((x : ℂ) ^ k)) * Q.eval (x : ℂ)‖ * x ^ M ≤ _
    rw [norm_mul, norm_exp_neg_pow_ofReal]
    calc Real.exp (-(x ^ k)) * ‖Q.eval (x : ℂ)‖ * x ^ M
        ≤ Real.exp (-(x / 2)) * (C * x ^ Q.natDegree) * x ^ M := by
          gcongr
          exact hC x hx1
      _ = C * (x ^ (Q.natDegree + M) * Real.exp (-(x / 2))) := by
          rw [pow_add]
          ring
  · simpa using (tendsto_pow_mul_exp_neg_half (Q.natDegree + M)).const_mul C

/-- The rung witness satisfies no algebraic differential equation on any nonempty open set. -/
theorem not_differentiallyAlgebraicOn_invGamma_comp_const_mul_pow {U : Set ℂ} (hU : IsOpen U)
    (hUne : U.Nonempty) {c : ℂ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    ¬ DifferentiallyAlgebraicOn (fun z => (Complex.Gamma (c * z ^ q))⁻¹) U := by
  intro hDA
  have hentire : AnalyticOnNhd ℂ (fun z : ℂ => (Complex.Gamma (c * z ^ q))⁻¹) Set.univ := by
    refine Complex.analyticOnNhd_univ_iff_differentiable.2 ?_
    exact Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  obtain ⟨n, P, hP0, hPv⟩ := differentiallyAlgebraicOn_mono_of_isPreconnected
    isPreconnected_univ hentire hU hUne (Set.subset_univ U) hDA
  exact hypertranscendental_invGamma_comp_const_mul_pow hc hq
    ⟨n, P, hP0, fun z => hPv z (Set.mem_univ z)⟩

/-! ### The rung-`k` recession theorem -/

open Polynomial in
/-- **Rung-`k` defeat.**  For every rung `k ≥ 1`, every finite jet table and every inverse-power
Poincaré expansion carried by a differentially algebraic function is carried simultaneously by a
differentially algebraic function `D` and by a punctured affine line of hypertranscendental
functions `D + λ A / Γ(z^k)`, whose differences are flat against every exponential gauge
`exp (-α x^m)` with `m < k`.  The jet correction is `exp(-z^{k+1}) Q`, which is itself flat at every
such gauge. -/
theorem exists_rung_realization {ι : Type*} [Fintype ι] {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {G : ℂ → ℂ} (hGan : AnalyticOnNhd ℂ G U) (hGDA : DifferentiallyAlgebraicOn G U)
    {b : ℕ → ℂ} (hGpo : PoincareInversePowers G b)
    (a : ι → ℂ) (ha : Function.Injective a) (haU : ∀ i, a i ∈ U)
    (m : ι → ℕ) (c : ι → ℕ → ℂ) {k : ℕ} (hk : 0 < k) :
    ∃ (D : ℂ → ℂ) (A : Polynomial ℂ), A ≠ 0 ∧ AnalyticOnNhd ℂ D U ∧
      DifferentiallyAlgebraicOn D U ∧
      (∀ i n, n ≤ m i → iteratedDeriv n D (a i) = c i n) ∧
      PoincareInversePowers D b ∧
      ∀ lam : ℂ, lam ≠ 0 →
        (∀ i n, n ≤ m i →
            iteratedDeriv n
              (fun z => D z + lam * A.eval z * (Complex.Gamma (z ^ k))⁻¹) (a i) = c i n) ∧
          ¬ DifferentiallyAlgebraicOn
              (fun z => D z + lam * A.eval z * (Complex.Gamma (z ^ k))⁻¹) U ∧
          PoincareInversePowers
              (fun z => D z + lam * A.eval z * (Complex.Gamma (z ^ k))⁻¹) b ∧
          ∀ alpha : ℝ, 0 < alpha → ∀ j : ℕ, j < k →
            FlatAtExpGauge
              (fun z => (D z + lam * A.eval z * (Complex.Gamma (z ^ k))⁻¹) - D z) alpha j := by
  classical
  obtain ⟨T, hT⟩ := exists_polynomial_iteratedDeriv_eval_eq a ha m
    (fun i n => c i n - iteratedDeriv n G (a i))
  obtain ⟨Q, hQ⟩ := exists_polynomial_iteratedDeriv_eval_eq a ha m
    (fun i n => iteratedDeriv n (fun z => Complex.exp (z ^ (k + 1)) * T.eval z) (a i))
  have hexpNeg : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Complex.exp (-(z ^ (k + 1))) :=
    (Complex.differentiable_exp.comp (by fun_prop)).contDiff
  have hexpPos : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Complex.exp (z ^ (k + 1)) :=
    (Complex.differentiable_exp.comp (by fun_prop)).contDiff
  have hQpoly : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Q.eval z :=
    (Polynomial.differentiable Q).contDiff
  have hTpoly : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => T.eval z :=
    (Polynomial.differentiable T).contDiff
  have hexpT : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Complex.exp (z ^ (k + 1)) * T.eval z :=
    hexpPos.mul hTpoly
  have hinvG : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => (Complex.Gamma (z ^ k))⁻¹ :=
    (Complex.differentiable_one_div_Gamma.comp (by fun_prop)).contDiff
  set E : ℂ → ℂ := fun z => Complex.exp (-(z ^ (k + 1))) * Q.eval z with hEdef
  have hEcd : ContDiff ℂ (⊤ : ℕ∞) E := hexpNeg.mul hQpoly
  have hEan : AnalyticOnNhd ℂ E U := fun z _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.2 (hEcd.differentiable (by simp))) z
      (Set.mem_univ z)
  have hEDA : DifferentiallyAlgebraicOn E U := by
    obtain ⟨n, P, hP0, hPv⟩ :=
      differentiallyAlgebraic_exp_poly_mul_poly (-(Polynomial.X ^ (k + 1))) Q
    refine ⟨n, P, hP0, fun z _ => ?_⟩
    have hfun : (fun s : ℂ => Complex.exp ((-(Polynomial.X ^ (k + 1)) : Polynomial ℂ).eval s)
        * Q.eval s) = E := by
      funext s
      rw [hEdef]
      congr 2
      simp
    rw [← hfun]
    exact hPv z
  have hEjet : ∀ (i : ι) (n : ℕ), n ≤ m i →
      iteratedDeriv n E (a i) = c i n - iteratedDeriv n G (a i) := by
    intro i n hn
    have hcongr := iteratedDeriv_mul_jet_congr (f := fun z : ℂ => Q.eval z)
      (g := fun z : ℂ => Complex.exp (z ^ (k + 1)) * T.eval z)
      (h := fun z : ℂ => Complex.exp (-(z ^ (k + 1))))
      (a := a i) (m := m i) hQpoly.contDiffAt hexpT.contDiffAt hexpNeg.contDiffAt
      (fun l hl => hQ i l hl) hn
    have hcollapse : (fun z : ℂ =>
        Complex.exp (-(z ^ (k + 1))) * (Complex.exp (z ^ (k + 1)) * T.eval z))
        = fun z : ℂ => T.eval z := by
      funext z
      rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
    rw [hEdef, hcongr, hcollapse, hT i n hn]
  refine ⟨fun z => G z + E z, jetModulus a m, jetModulus_ne_zero a m,
    hGan.add hEan,
    differentiallyAlgebraicOn_add hUo hUc hUne hUinf hGan hEan hGDA hEDA, ?_, ?_, ?_⟩
  · intro i n hn
    have hGcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) G (a i) :=
      ((hGan (a i) (haU i)).contDiffAt).of_le (by exact_mod_cast le_top)
    have hEcdn : ContDiffAt ℂ ((n : ℕ) : ℕ∞) E (a i) :=
      hEcd.contDiffAt.of_le (by exact_mod_cast le_top)
    have hadd : (fun z => G z + E z) = G + E := rfl
    rw [hadd, iteratedDeriv_add hGcd hEcdn, hEjet i n hn]
    ring
  · have hflatE : FlatInversePowers E := by
      have h := flat_exp_neg_pow_mul_polynomial (k := k + 1) (Nat.succ_pos k) Q
      simpa [hEdef] using h
    exact hGpo.add_flat hflatE
  · intro lam hlam
    have hAjet : ∀ (i : ι) (n : ℕ), n ≤ m i →
        iteratedDeriv n
          (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹) (a i) = 0 := by
      intro i n hn
      have hAcd : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => lam * (jetModulus a m).eval z :=
        contDiff_const.mul ((Polynomial.differentiable (jetModulus a m)).contDiff)
      have hjets : ∀ l, l ≤ m i →
          iteratedDeriv l (fun z : ℂ => lam * (jetModulus a m).eval z) (a i)
            = iteratedDeriv l (fun _ : ℂ => (0 : ℂ)) (a i) := by
        intro l hl
        have hpoly : ContDiffAt ℂ ((l : ℕ) : ℕ∞)
            (fun z : ℂ => (jetModulus a m).eval z) (a i) :=
          ((Polynomial.differentiable (jetModulus a m)).contDiff
            (n := ((l : ℕ) : ℕ∞))).contDiffAt
        rw [iteratedDeriv_const_mul (f := fun z : ℂ => (jetModulus a m).eval z) lam hpoly,
          iteratedDeriv_jetModulus_eq_zero a m i hl, mul_zero, iteratedDeriv_const]
        simp
      have hcongr := iteratedDeriv_mul_jet_congr
        (f := fun z : ℂ => lam * (jetModulus a m).eval z) (g := fun _ : ℂ => (0 : ℂ))
        (h := fun z : ℂ => (Complex.Gamma (z ^ k))⁻¹) (a := a i) (m := m i)
        hAcd.contDiffAt contDiff_const.contDiffAt hinvG.contDiffAt hjets hn
      have hswap : (fun z : ℂ => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹)
          = fun z : ℂ => (Complex.Gamma (z ^ k))⁻¹ * (lam * (jetModulus a m).eval z) := by
        funext z
        ring
      rw [hswap, hcongr]
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i n hn
      have hDcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) (fun z => G z + E z) (a i) := by
        refine ContDiffAt.add ?_ (hEcd.contDiffAt.of_le (by exact_mod_cast le_top))
        exact ((hGan (a i) (haU i)).contDiffAt).of_le (by exact_mod_cast le_top)
      have hRcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞)
          (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹) (a i) := by
        refine ContDiffAt.mul ?_ (hinvG.contDiffAt.of_le (by exact_mod_cast le_top))
        exact (contDiff_const.mul ((Polynomial.differentiable
          (jetModulus a m)).contDiff)).contDiffAt.of_le (by exact_mod_cast le_top)
      have hsum : (fun z => (fun z => G z + E z) z +
          lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹)
          = (fun z => G z + E z) + fun z => lam * (jetModulus a m).eval z *
            (Complex.Gamma (z ^ k))⁻¹ := rfl
      rw [hsum, iteratedDeriv_add hDcd hRcd, hAjet i n hn, add_zero]
      have hGcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) G (a i) :=
        ((hGan (a i) (haU i)).contDiffAt).of_le (by exact_mod_cast le_top)
      have hEcdn : ContDiffAt ℂ ((n : ℕ) : ℕ∞) E (a i) :=
        hEcd.contDiffAt.of_le (by exact_mod_cast le_top)
      have hadd : (fun z => G z + E z) = G + E := rfl
      rw [hadd, iteratedDeriv_add hGcd hEcdn, hEjet i n hn]
      ring
    · intro hDA
      have hRan : AnalyticOnNhd ℂ
          (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹) U := by
        intro z _
        exact (Complex.analyticOnNhd_univ_iff_differentiable.2
          (((contDiff_const.mul ((Polynomial.differentiable (jetModulus a m)).contDiff)).mul
            hinvG).differentiable (by simp))) z (Set.mem_univ z)
      have hDan : AnalyticOnNhd ℂ (fun z => G z + E z) U := hGan.add hEan
      have hFan : AnalyticOnNhd ℂ (fun z => (fun z => G z + E z) z +
          lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹) U := hDan.add hRan
      have hDdA : DifferentiallyAlgebraicOn (fun z => G z + E z) U :=
        differentiallyAlgebraicOn_add hUo hUc hUne hUinf hGan hEan hGDA hEDA
      have hRDA : DifferentiallyAlgebraicOn
          (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹) U := by
        have hsub := differentiallyAlgebraicOn_sub hUo hUc hUne hUinf hFan hDan hDA hDdA
        have hfun : (fun z => ((fun z => G z + E z) z +
            lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹) - (fun z => G z + E z) z)
            = fun z => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹ := by
          funext z
          ring
        rwa [hfun] at hsub
      have hinvDA : DifferentiallyAlgebraicOn (fun z => (Complex.Gamma (z ^ k))⁻¹) U := by
        refine differentiallyAlgebraicOn_of_mul_polynomial
          (fun z _ => hinvG.contDiffAt) (a := Polynomial.C lam * jetModulus a m) ?_ ?_
        · exact mul_ne_zero (by simpa using hlam) (jetModulus_ne_zero a m)
        · have hfun : (fun z => (Polynomial.C lam * jetModulus a m).eval z *
              (Complex.Gamma (z ^ k))⁻¹)
              = fun z => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹ := by
            funext z
            rw [Polynomial.eval_mul, Polynomial.eval_C]
          rw [hfun]
          exact hRDA
      have hone : (fun z : ℂ => (Complex.Gamma ((1 : ℂ) * z ^ k))⁻¹)
          = fun z : ℂ => (Complex.Gamma (z ^ k))⁻¹ := by
        funext z
        rw [one_mul]
      refine not_differentiallyAlgebraicOn_invGamma_comp_const_mul_pow hUo hUne
        (c := (1 : ℂ)) one_ne_zero hk ?_
      rw [hone]
      exact hinvDA
    · have hflatE : FlatInversePowers E := by
        have h := flat_exp_neg_pow_mul_polynomial (k := k + 1) (Nat.succ_pos k) Q
        simpa [hEdef] using h
      exact (hGpo.add_flat hflatE).add_flat
        (flat_polynomial_mul_invGamma_pow hk lam (jetModulus a m))
    · intro alpha halpha j hj
      have hfun : (fun z => ((fun z => G z + E z) z +
          lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹) - (fun z => G z + E z) z)
          = fun z => lam * (jetModulus a m).eval z * (Complex.Gamma (z ^ k))⁻¹ := by
        funext z
        ring
      rw [hfun]
      exact flat_gauge_polynomial_mul_invGamma_pow halpha hj lam (jetModulus a m)

/-! ### Sharpness of the ladder -/

/-- A crude upper bound: `Γ(y) ≤ (y+1)^{⌈y⌉₊}`. -/
theorem gamma_le_pow_ceil {y : ℝ} (hy : 2 ≤ y) :
    Real.Gamma y ≤ (y + 1) ^ (⌈y⌉₊) := by
  have hyc : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hc2 : 2 ≤ ⌈y⌉₊ := by
    have : (2 : ℝ) ≤ (⌈y⌉₊ : ℝ) := le_trans hy hyc
    exact_mod_cast this
  have hmono : Real.Gamma y ≤ Real.Gamma (⌈y⌉₊ : ℝ) := by
    rcases eq_or_lt_of_le hyc with heq | hlt
    · exact le_of_eq (congrArg Real.Gamma heq)
    · exact (Real.Gamma_strictMonoOn_Ici (Set.mem_Ici.2 hy)
        (Set.mem_Ici.2 (le_trans hy hyc)) hlt).le
  have hfact : Real.Gamma (⌈y⌉₊ : ℝ) = ((Nat.factorial (⌈y⌉₊ - 1) : ℕ) : ℝ) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌈y⌉₊ = n + 1 := ⟨⌈y⌉₊ - 1, by omega⟩
    rw [hn]
    push_cast
    rw [Real.Gamma_nat_eq_factorial n]
  refine le_trans hmono ?_
  rw [hfact]
  have hle : Nat.factorial (⌈y⌉₊ - 1) ≤ (⌈y⌉₊) ^ (⌈y⌉₊) := by
    calc Nat.factorial (⌈y⌉₊ - 1) ≤ Nat.factorial (⌈y⌉₊) := Nat.factorial_le (by omega)
      _ ≤ (⌈y⌉₊) ^ (⌈y⌉₊) := Nat.factorial_le_pow _
  have hcast : ((Nat.factorial (⌈y⌉₊ - 1) : ℕ) : ℝ) ≤ ((⌈y⌉₊ : ℝ)) ^ (⌈y⌉₊) := by
    exact_mod_cast hle
  refine hcast.trans ?_
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ y)
  linarith

/-- **The rung witness is visible at the next power gauge.**  `1/Γ(x^k)` is *not* flat against
`exp (-α x^{k+1})` for any `α > 0`: the recession ladder stops exactly at rung `k`. -/
theorem not_flatAtExpGauge_invGamma_pow_succ {alpha : ℝ} (halpha : 0 < alpha) {k : ℕ}
    (hk : 0 < k) :
    ¬ FlatAtExpGauge (fun z => (Complex.Gamma (z ^ k))⁻¹) alpha (k + 1) := by
  intro hflat
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- the logarithmic term is negligible against the next power
  have hlogsmall : ∀ᶠ x : ℝ in atTop, Real.log x ≤ alpha / (8 * k) * x := by
    have hbound := Real.isLittleO_log_id_atTop.bound
      (show (0:ℝ) < alpha / (8 * k) by positivity)
    filter_upwards [hbound, eventually_ge_atTop (1:ℝ)] with x hx hx1
    have hlognn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have hxnn : (0 : ℝ) ≤ x := by linarith
    simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hlognn, abs_of_nonneg hxnn] at hx
    exact hx
  have hgap : ∀ᶠ x : ℝ in atTop,
      alpha / 2 * x ^ (k + 1)
        ≤ alpha * x ^ (k + 1) - (x ^ k + 1) * Real.log (x ^ k + 1) := by
    filter_upwards [hlogsmall, eventually_ge_atTop (1:ℝ),
      eventually_ge_atTop (8 * Real.log 2 / alpha)] with x hlx hx1 hx2
    have hxpos : (0 : ℝ) < x := by linarith
    have hxk1 : (1 : ℝ) ≤ x ^ k := one_le_pow₀ hx1
    have hxkpos : (0 : ℝ) < x ^ k := by positivity
    have hle2 : x ^ k + 1 ≤ 2 * x ^ k := by linarith
    have hlogle : Real.log (x ^ k + 1) ≤ Real.log 2 + (k : ℝ) * Real.log x := by
      calc Real.log (x ^ k + 1) ≤ Real.log (2 * x ^ k) :=
            Real.log_le_log (by linarith) hle2
        _ = Real.log 2 + Real.log (x ^ k) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log 2 + (k : ℝ) * Real.log x := by rw [Real.log_pow]
    have hlog2 : Real.log 2 ≤ alpha / 8 * x := by
      have h2 := (div_le_iff₀ halpha).1 hx2
      nlinarith
    have hklog : (k : ℝ) * Real.log x ≤ alpha / 8 * x := by
      have := mul_le_mul_of_nonneg_left hlx hkR.le
      calc (k : ℝ) * Real.log x ≤ (k : ℝ) * (alpha / (8 * k) * x) := this
        _ = alpha / 8 * x := by field_simp
    have hlogtot : Real.log (x ^ k + 1) ≤ alpha / 4 * x := by linarith
    have hlognn : (0 : ℝ) ≤ Real.log (x ^ k + 1) := Real.log_nonneg (by linarith)
    have hprod : (x ^ k + 1) * Real.log (x ^ k + 1) ≤ 2 * x ^ k * (alpha / 4 * x) := by
      refine mul_le_mul hle2 hlogtot hlognn (by positivity)
    have hpow : (2 : ℝ) * x ^ k * (alpha / 4 * x) = alpha / 2 * x ^ (k + 1) := by
      rw [pow_succ]
      ring
    linarith [hprod, hpow]
  -- the witness dominates the gauge
  have hlower : ∀ᶠ x : ℝ in atTop,
      Real.exp (alpha / 2 * x ^ (k + 1))
        ≤ ‖(Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * Real.exp (alpha * x ^ (k + 1)) := by
    filter_upwards [hgap, eventually_ge_atTop (2:ℝ)] with x hgx hx2
    have hxpos : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hxk2 : (2 : ℝ) ≤ x ^ k := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ x ^ 1 := by simpa using hx2
        _ ≤ x ^ k := pow_le_pow_right₀ hx1 (by omega)
    have hgampos : (0 : ℝ) < Real.Gamma (x ^ k) := Real.Gamma_pos_of_pos (by positivity)
    have hupper : Real.Gamma (x ^ k) ≤ Real.exp ((x ^ k + 1) * Real.log (x ^ k + 1)) := by
      refine (gamma_le_pow_ceil hxk2).trans ?_
      have hbase : (0 : ℝ) < x ^ k + 1 := by linarith
      have hceil : ((⌈x ^ k⌉₊ : ℕ) : ℝ) ≤ x ^ k + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have hlognn : (0 : ℝ) ≤ Real.log (x ^ k + 1) := Real.log_nonneg (by linarith)
      calc (x ^ k + 1) ^ (⌈x ^ k⌉₊)
          = Real.exp (Real.log (x ^ k + 1) * (⌈x ^ k⌉₊ : ℝ)) := by
            rw [← Real.rpow_natCast (x ^ k + 1) (⌈x ^ k⌉₊), Real.rpow_def_of_pos hbase]
        _ ≤ Real.exp ((x ^ k + 1) * Real.log (x ^ k + 1)) := by
            refine Real.exp_le_exp.2 ?_
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right hceil hlognn
    rw [norm_invGamma_pow_ofReal hxpos]
    rw [← Real.exp_log hgampos] at hupper ⊢
    rw [← Real.exp_neg, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hlogle : Real.log (Real.Gamma (x ^ k)) ≤ (x ^ k + 1) * Real.log (x ^ k + 1) :=
      Real.exp_le_exp.1 hupper
    linarith
  have hto : Tendsto (fun x : ℝ => Real.exp (alpha / 2 * x ^ (k + 1))) atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    exact Filter.Tendsto.const_mul_atTop (by positivity) (tendsto_pow_atTop (by omega))
  have hev1 : ∀ᶠ x : ℝ in atTop,
      ‖(Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * Real.exp (alpha * x ^ (k + 1)) < 1 := by
    have := hflat (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with x hx
    have := Real.norm_eq_abs (‖(Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * Real.exp (alpha * x ^ (k + 1)))
    have hmem : |‖(Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * Real.exp (alpha * x ^ (k + 1))| < 1 := by
      simpa [Real.dist_eq] using hx
    calc ‖(Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * Real.exp (alpha * x ^ (k + 1))
        ≤ |‖(Complex.Gamma ((x : ℂ) ^ k))⁻¹‖ * Real.exp (alpha * x ^ (k + 1))| := le_abs_self _
      _ < 1 := hmem
  have hev2 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.exp (alpha / 2 * x ^ (k + 1)) :=
    hto.eventually_ge_atTop 1
  obtain ⟨x, hxall⟩ := ((hev1.and hev2).and hlower).exists
  obtain ⟨⟨hxa, hxb⟩, hxc⟩ := hxall
  linarith

end

end GaloisForLFunctions.HTGeometry
