import GaloisForLFunctions.RHTower.WeilConeOneSidedDeviationRH
import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction
import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare
import GaloisForLFunctions.HTGeometry.DirichletSeriesBoundedPartialSums

/-!
# Constant sign up to a conditionally convergent error: RH and the atoms

Let `lam` be full-cone Weil-positive with `lam − Λ = εu + w` on `n ≥ 2`, where `ε = ±1`,
`u ≥ 0`, and the partial sums of `Σ w(n) n^{−1/2−it}` converge for every real `t`
(`Decomposition`).

**RH** (`riemannHypothesis`).  The series `E(s) = Σ w(n) n^{−s}` continues holomorphically to
`Re s > 1/2` (bounded partial sums at `1/2`).  On `Re s > 3/2`,
`ξ'/ξ − Φ_lam = εL(u) + E`, so `L(u) = ε(ξ'/ξ − Φ_lam − E)` is holomorphic near every real point
`σ > 1/2` (where `ξ(σ) ≠ 0`).  Landau's theorem for the nonnegative series `L(u)` puts its
abscissa at `≤ 1/2`.  Then `ξ'/ξ = Φ_lam + εL(u) + E` is holomorphic on `Re s > 1/2`, and the
residue law excludes every zero there.

**Atoms** (`abs_atom_sub_le`).  Under RH, `Φ_lam = Φ_Λ − εL(u) − E` on `Re s > 1/2`.  Multiplying
by `b` at `1/2 + b + ia` and letting `b → 0⁺`: `bΦ` tends to the boundary atoms, `bE → 0` because
`E` is bounded on horizontal rays from every point of the line, and `|Re L(u)(1/2+b+ia)| ≤
L(u)(1/2+b)`.  Hence `|μ_Λ{a} − μ_lam{a}| ≤ −ε μ_lam{0}`; with `μ_Λ{0} = ord_{1/2} ξ = 0` this
forces `−ε μ_lam{0} = μ_lam{0}`, so `|μ_Λ{a} − μ_lam{a}| ≤ μ_lam{0}` (`abs_atom_sub_le_atom_zero`).
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.BoundedPartialSums

noncomputable section

namespace RHTower.WeilConditional

open WeilSpectral WeilHerglotz

/-- A decomposition `lam − Λ = εu + w` on `n ≥ 2` with `ε = ±1`, `u ≥ 0`, and convergent partial
sums of `Σ w(n) n^{−1/2−it}` for every real `t`. -/
structure Decomposition (lam : ℕ → ℝ) where
  ε : ℝ
  hε : ε = 1 ∨ ε = -1
  u : ℕ → ℝ
  w : ℕ → ℝ
  u_nonneg : ∀ n, 0 ≤ u n
  u_small : ∀ n, n < 2 → u n = 0
  w_small : ∀ n, n < 2 → w n = 0
  dec : ∀ n, 2 ≤ n → lam n - ArithmeticFunction.vonMangoldt n = ε * u n + w n
  conv : ∀ t : ℝ, ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
    LSeries.term (fun n => (w n : ℂ)) ((1 / 2 : ℂ) + t * I) n) atTop (𝓝 L)

/-- The critical point `1/2 + it`. -/
def basePt (t : ℝ) : ℂ := (1 / 2 : ℂ) + t * I

theorem basePt_re (t : ℝ) : (basePt t).re = 1 / 2 := by simp [basePt]

/-- `μ_Λ{0} = ord_{1/2} ξ = 0`. -/
theorem boundaryMeasure_vonMangoldt_real_zero
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :
    (boundaryMeasure hΛ).real {0} = 0 := by
  rw [boundaryMeasure_vonMangoldt_real_singleton hΛ 0]
  have hxi : xi ((1 / 2 : ℂ) + (0 : ℝ) * I) ≠ 0 := by
    have := xi_ne_zero_of_real (1 / 2)
    simpa using this
  have h0 : analyticOrderAt xi ((1 / 2 : ℂ) + (0 : ℝ) * I) = 0 :=
    (xi_differentiable.analyticAt _).analyticOrderAt_eq_zero.mpr hxi
  rw [analyticOrderNatAt, h0]
  simp

namespace Decomposition

variable {lam : ℕ → ℝ} (D : Decomposition lam)

/-- The coefficients of `E` and `L(u)` as complex sequences. -/
def wC : ℕ → ℂ := fun n => (D.w n : ℂ)
def uC : ℕ → ℂ := fun n => (D.u n : ℂ)

theorem ε_mul_ε : D.ε * D.ε = 1 := by rcases D.hε with h | h <;> rw [h] <;> norm_num

theorem abs_ε : |D.ε| = 1 := by rcases D.hε with h | h <;> rw [h] <;> norm_num

/-- A bound for the partial sums at `1/2 + it`. -/
def bound (t : ℝ) : ℝ :=
  Classical.choose (exists_partialSum_bound_of_tendsto (Classical.choose_spec (D.conv t)))

theorem bound_spec (t : ℝ) :
    ∀ N, ‖∑ n ∈ Finset.range N, LSeries.term D.wC (basePt t) n‖ ≤ D.bound t :=
  Classical.choose_spec (exists_partialSum_bound_of_tendsto (Classical.choose_spec (D.conv t)))

/-- The continuation `E` of `Σ w(n) n^{−s}` to `Re s > 1/2`. -/
def E : ℂ → ℂ := contLSeries D.wC (basePt 0)

theorem differentiableOn_E : DifferentiableOn ℂ D.E {s | 1 / 2 < s.re} := by
  have h := differentiableOn_contLSeries (D.bound_spec 0)
  rw [basePt_re] at h
  exact h

theorem norm_wC_le (n : ℕ) : ‖D.wC n‖ ≤ 2 * D.bound 0 * Real.sqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wC, D.w_small 0 (by norm_num)]
  have hdiff : LSeries.term D.wC (basePt 0) n =
      (∑ m ∈ Finset.range (n + 1), LSeries.term D.wC (basePt 0) m) -
        ∑ m ∈ Finset.range n, LSeries.term D.wC (basePt 0) m := by
    rw [Finset.sum_range_succ]; ring
  have hterm : ‖LSeries.term D.wC (basePt 0) n‖ ≤ 2 * D.bound 0 := by
    rw [hdiff]
    calc _ ≤ ‖∑ m ∈ Finset.range (n + 1), LSeries.term D.wC (basePt 0) m‖ +
          ‖∑ m ∈ Finset.range n, LSeries.term D.wC (basePt 0) m‖ := norm_sub_le _ _
      _ ≤ D.bound 0 + D.bound 0 := add_le_add (D.bound_spec 0 _) (D.bound_spec 0 _)
      _ = 2 * D.bound 0 := by ring
  rw [LSeries.norm_term_eq, if_neg hn.ne', basePt_re] at hterm
  have hs : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  rw [div_le_iff₀ hs, ← Real.sqrt_eq_rpow] at hterm
  exact hterm

theorem lseriesSummable_wC {s : ℂ} (hs : 3 / 2 < s.re) : LSeriesSummable D.wC s := by
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨2 * D.bound 0, fun n hn => ?_⟩
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact D.norm_wC_le n

theorem E_eq_LSeries {s : ℂ} (hs : 3 / 2 < s.re) : D.E s = LSeries D.wC s :=
  contLSeries_eq_LSeries (D.bound_spec 0) (by rw [basePt_re]; linarith) (D.lseriesSummable_wC hs)

theorem coeff_eq (n : ℕ) :
    lamC lam n - (ArithmeticFunction.vonMangoldt n : ℂ) = D.ε * D.uC n + D.wC n := by
  by_cases hn : 2 ≤ n
  · have := D.dec n hn
    simp only [lamC, if_pos hn, uC, wC]
    exact_mod_cast this
  · have h01 : n < 2 := by omega
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by interval_cases n <;> simp
    simp only [lamC, if_neg hn, uC, wC, D.u_small n h01, D.w_small n h01]
    push_cast
    rw [hΛ]
    simp

theorem lseriesSummable_uC (hW : WeilPositiveFull lam) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable D.uC s := by
  have h1 := summable_term_lamC hW (s := s) (by linarith)
  have h2 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) (by linarith)
  have h3 := D.lseriesSummable_wC hs
  refine Summable.of_norm_bounded ((h1.norm.add h2.norm).add h3.norm) fun n => ?_
  have hc : D.uC n = D.ε * (lamC lam n - (ArithmeticFunction.vonMangoldt n : ℂ) - D.wC n) := by
    rw [D.coeff_eq]
    have := D.ε_mul_ε
    have h : (D.ε : ℂ) * D.ε = 1 := by exact_mod_cast this
    linear_combination (-(D.uC n)) * h
  have hterm : LSeries.term D.uC s n = D.ε * (LSeries.term (lamC lam) s n -
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n - LSeries.term D.wC s n) := by
    simp only [LSeries.term_def]
    split_ifs
    · simp
    · rw [hc]; ring
  rw [hterm, norm_mul, Complex.norm_real, Real.norm_eq_abs, D.abs_ε, one_mul]
  calc _ ≤ ‖LSeries.term (lamC lam) s n - LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ +
        ‖LSeries.term D.wC s n‖ := norm_sub_le _ _
    _ ≤ ‖LSeries.term (lamC lam) s n‖ +
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ +
        ‖LSeries.term D.wC s n‖ := by gcongr; exact norm_sub_le _ _

/-- **The deviation identity** on `Re s > 3/2`: `ξ'/ξ − Φ_lam = εL(u) + E`. -/
theorem logDeriv_xi_sub_eq (hW : WeilPositiveFull lam) {s : ℂ} (hs : 3 / 2 < s.re) :
    logDeriv xi s - weilContinuation hW s = D.ε * LSeries D.uC s + D.E s := by
  rw [logDeriv_xi_sub_weilContinuation_eq hW (by linarith),
    ← LSeries_sub (summable_term_lamC hW (by linarith))
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by linarith)),
    D.E_eq_LSeries hs]
  have hfun : (lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (D.ε : ℂ) • D.uC + D.wC := funext fun n => by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact D.coeff_eq n
  rw [hfun, LSeries_add ((D.lseriesSummable_uC hW hs).smul _) (D.lseriesSummable_wC hs),
    LSeries_smul]

/-- The deviation identity in product form on every half-plane where `L(u)` converges. -/
theorem deriv_xi_eq (hW : WeilPositiveFull lam) {c : ℝ} (hc : 1 / 2 ≤ c)
    (hsum : ∀ τ, c < τ → Summable (gdTwistTerm D.u logFreq τ 0)) {z : ℂ} (hz : c < z.re) :
    deriv xi z = (D.ε * LSeries D.uC z + D.E z + weilContinuation hW z) * xi z := by
  set U : Set ℂ := {z | c < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt c).isPreconnected
  have hf : AnalyticOnNhd ℂ (deriv xi) U := ((xi_analyticOnNhd Set.univ).deriv).mono (subset_univ _)
  have hg : AnalyticOnNhd ℂ (fun z => (D.ε * LSeries D.uC z + D.E z + weilContinuation hW z) *
      xi z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    have hz' : c < z.re := hz
    have hzh : 1 / 2 < z.re := lt_of_le_of_lt hc hz'
    have hdU := differentiableAt_LSeries_of_gdTwistTerm D.u_nonneg (D.u_small 0 (by norm_num))
      hsum hz'
    have hdE : DifferentiableAt ℂ D.E z :=
      D.differentiableOn_E.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzh)
    have hdΦ : DifferentiableAt ℂ (weilContinuation hW) z :=
      (differentiableOn_weilContinuation hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzh)
    exact ((((hdU.const_mul _).add hdE).add hdΦ).mul (xi_differentiable z)).differentiableWithinAt
  set z₀ : ℂ := ((max c 2 + 1 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = max c 2 + 1 := by rw [hz₀]; exact ofReal_re _
  have hz₀U : z₀ ∈ U := by
    show c < z₀.re
    rw [hz₀re]; linarith [le_max_left c 2]
  have hev : deriv xi =ᶠ[𝓝 z₀] fun z =>
      (D.ε * LSeries D.uC z + D.E z + weilContinuation hW z) * xi z := by
    have h1 : 3 / 2 < z₀.re := by rw [hz₀re]; linarith [le_max_right c 2]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz
    have hz' : 3 / 2 < z.re := hz
    have hxi : xi z ≠ 0 := xi_ne_zero_of_one_lt_re (by linarith)
    have h := D.logDeriv_xi_sub_eq hW hz'
    rw [logDeriv_apply] at h
    have h' : deriv xi z / xi z = D.ε * LSeries D.uC z + D.E z + weilContinuation hW z := by
      linear_combination h
    rwa [div_eq_iff hxi] at h'
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hz₀U hev hz

theorem summable_u_two (hW : WeilPositiveFull lam) :
    Summable (gdTwistTerm D.u logFreq 2 0) := by
  have h := (D.lseriesSummable_uC hW (s := 2) (by norm_num)).norm
  refine h.congr fun n => ?_
  rw [gdTwistTerm_logFreq _ (D.u_small 0 (by norm_num)), LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [D.u_small 0 (by norm_num)]
  · rw [if_neg hn.ne', uC, Complex.norm_real, Real.norm_of_nonneg (D.u_nonneg n)]
    norm_num

/-- **Landau.** The nonnegative series `L(u)` converges on `Re s > 1/2`. -/
theorem summable_u (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (gdTwistTerm D.u logFreq σ 0) := by
  refine summable_gdTwistTerm_of_xi_continuation D.u_nonneg (D.summable_u_two hW)
    (G := fun z => D.ε * (logDeriv xi z - weilContinuation hW z - D.E z))
    (fun z hz hxz => ?_) (fun c' hc' hsum z hz hxz => ?_) hσ
  · have hdΦ : DifferentiableAt ℂ (weilContinuation hW) z :=
      (differentiableOn_weilContinuation hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hdE : DifferentiableAt ℂ D.E z :=
      D.differentiableOn_E.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hdd : DifferentiableAt ℂ (deriv xi) z :=
      ((xi_analyticOnNhd Set.univ).deriv z (mem_univ _)).differentiableAt
    have hlog : DifferentiableAt ℂ (logDeriv xi) z := by
      have : logDeriv xi = fun z => deriv xi z / xi z := funext fun z => logDeriv_apply xi z
      rw [this]
      exact hdd.div (xi_differentiable z) hxz
    exact ((hlog.sub hdΦ).sub hdE).const_mul _
  · rw [gdSeries_logFreq _ (D.u_small 0 (by norm_num))]
    have hid := D.deriv_xi_eq hW hc' hsum hz
    rw [logDeriv_apply, hid, mul_div_assoc, div_self hxz, mul_one]
    have := D.ε_mul_ε
    have h : (D.ε : ℂ) * D.ε = 1 := by exact_mod_cast this
    show _ = LSeries D.uC z
    linear_combination (LSeries D.uC z) * h

include D in
/-- **RH** for a Weil-positive system that is constant sign up to a conditionally convergent
error. -/
theorem riemannHypothesis (hW : WeilPositiveFull lam) : RiemannHypothesis := by
  have hsum : ∀ τ, 1 / 2 < τ → Summable (gdTwistTerm D.u logFreq τ 0) :=
    fun τ hτ => D.summable_u hW hτ
  refine rh_iff_xi_ne_zero_right.mpr fun ρ hρ hzero => ?_
  have hρ' : 1 / 2 < ρ.re := hρ
  set H : ℂ → ℂ := fun z => D.ε * LSeries D.uC z + D.E z with hHdef
  have hHc : ContinuousAt H ρ :=
    (((differentiableAt_LSeries_of_gdTwistTerm D.u_nonneg (D.u_small 0 (by norm_num)) hsum
      hρ').const_mul _).add (D.differentiableOn_E.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ'))).continuousAt
  have hlin : Tendsto (fun z => (z - ρ) * H z) (𝓝[≠] ρ) (𝓝 0) := by
    have h1 : ContinuousAt (fun z : ℂ => z - ρ) ρ := by fun_prop
    have h : Tendsto (fun z => (z - ρ) * H z) (𝓝 ρ) (𝓝 ((ρ - ρ) * H ρ)) := (h1.mul hHc).tendsto
    rw [sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ z in 𝓝[≠] ρ, xi z ≠ 0 := by
    rcases (xi_differentiable.analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) (xi_orderAt_ne_top ρ)
    · exact h
  have hre : ∀ᶠ z in 𝓝[≠] ρ, 1 / 2 < z.re :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ')
  have hcongr : (fun z => (z - ρ) * (logDeriv xi z - weilContinuation hW z)) =ᶠ[𝓝[≠] ρ]
      fun z => (z - ρ) * H z := by
    filter_upwards [hne, hre] with z hz hzre
    rw [logDeriv_apply, D.deriv_xi_eq hW le_rfl hsum hzre, mul_div_assoc, div_self hz, mul_one]
    simp only [hHdef]
    ring
  have h0 : (analyticOrderNatAt xi ρ : ℂ) = 0 :=
    tendsto_nhds_unique ((tendsto_sub_mul_logDeriv_xi_sub_weilContinuation hW hρ').congr' hcongr)
      hlin
  have hord : analyticOrderNatAt xi ρ = 0 := by exact_mod_cast h0
  have hord' : analyticOrderAt xi ρ = 0 := by
    rcases ENat.toNat_eq_zero.mp hord with h | h
    · exact h
    · exact absurd h (xi_orderAt_ne_top ρ)
  exact ((xi_differentiable.analyticAt ρ).analyticOrderAt_eq_zero.mp hord') hzero

/-! ## The atoms under RH -/

/-- Under RH, `Φ_lam = Φ_Λ − εL(u) − E` on `Re s > 1/2`. -/
theorem weilContinuation_eq_sub (hW : WeilPositiveFull lam)
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    weilContinuation hW z = weilContinuation hΛ z - (D.ε * LSeries D.uC z + D.E z) := by
  have hRH := D.riemannHypothesis hW
  have hxi : xi z ≠ 0 := rh_iff_xi_ne_zero_right.mp hRH z hz
  have hid := D.deriv_xi_eq hW le_rfl (fun τ hτ => D.summable_u hW hτ) hz
  rw [weilContinuation_vonMangoldt_eq hΛ hz, logDeriv_apply, hid, mul_div_assoc, div_self hxi,
    mul_one]
  ring

/-- The point `1/2 + b + ia`. -/
def lineShift (a b : ℝ) : ℂ := (((1 / 2 + b : ℝ)) : ℂ) + a * I

theorem lineShift_re (a b : ℝ) : (lineShift a b).re = 1 / 2 + b := by simp [lineShift]

theorem norm_E_lineShift_le {a b : ℝ} (hb : 0 < b) : ‖D.E (lineShift a b)‖ ≤ 3 * D.bound a := by
  have hbase : D.E (lineShift a b) = contLSeries D.wC (basePt a) (lineShift a b) :=
    contLSeries_eq_of_base (D.bound_spec 0) (D.bound_spec a)
      (by rw [basePt_re, lineShift_re]; linarith) (by rw [basePt_re, lineShift_re]; linarith)
  rw [hbase, show lineShift a b = basePt a + (b : ℂ) by
    simp only [lineShift, basePt]; push_cast; ring]
  exact norm_contLSeries_add_ofReal_le (D.bound_spec a) hb

theorem tendsto_mul_re_E (a : ℝ) :
    Tendsto (fun b : ℝ => b * (D.E (lineShift a b)).re) (𝓝[>] 0) (𝓝 0) := by
  have hM : 0 ≤ D.bound a := (norm_nonneg _).trans (D.bound_spec a 0)
  have h : Tendsto (fun b : ℝ => b * (3 * D.bound a)) (𝓝[>] 0) (𝓝 0) :=
    (Continuous.tendsto' (by fun_prop : Continuous fun b : ℝ => b * (3 * D.bound a)) 0 0
      (by simp)).mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ h
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb' : 0 < b := hb
  rw [norm_mul, Real.norm_of_nonneg hb'.le]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (D.norm_E_lineShift_le hb'))
    hb'.le

theorem norm_LSeries_uC_le (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖LSeries D.uC s‖ ≤ (LSeries D.uC (s.re : ℂ)).re := by
  have hsumR := D.summable_u hW hs
  have hnorm : ∀ n, ‖LSeries.term D.uC s n‖ = (LSeries.term D.uC (s.re : ℂ) n).re := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', LSeries.term_of_ne_zero hn.ne', uC, Complex.norm_real,
        Real.norm_of_nonneg (D.u_nonneg n)]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [show ((n : ℂ)) ^ ((s.re : ℝ) : ℂ) = (((n : ℝ) ^ s.re : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow hn0.le]; push_cast; rfl, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsum : Summable fun n => ‖LSeries.term D.uC s n‖ := by
    refine hsumR.congr fun n => ?_
    rw [gdTwistTerm_logFreq _ (D.u_small 0 (by norm_num)), LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [D.u_small 0 (by norm_num)]
    · rw [if_neg hn.ne', uC, Complex.norm_real, Real.norm_of_nonneg (D.u_nonneg n)]
  calc ‖LSeries D.uC s‖ ≤ ∑' n, ‖LSeries.term D.uC s n‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' n, (LSeries.term D.uC (s.re : ℂ) n).re := tsum_congr hnorm
    _ = (LSeries D.uC (s.re : ℂ)).re := by
        rw [LSeries, Complex.re_tsum]
        exact Summable.of_norm (hsum.congr fun n => by
          rw [hnorm n]
          have : 0 ≤ (LSeries.term D.uC (s.re : ℂ) n).re := by rw [← hnorm n]; exact norm_nonneg _
          rw [show ‖LSeries.term D.uC (s.re : ℂ) n‖ = (LSeries.term D.uC (s.re : ℂ) n).re by
            rw [← hnorm n, LSeries.norm_term_eq, LSeries.norm_term_eq]
            simp])

/-- **Atom bound.** Under the decomposition, `|μ_Λ{a} − μ_lam{a}| ≤ −ε μ_lam{0}` for every `a`. -/
theorem abs_atom_sub_le (hW : WeilPositiveFull lam)
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (a : ℝ) :
    |(boundaryMeasure hΛ).real {a} - (boundaryMeasure hW).real {a}| ≤
      -D.ε * (boundaryMeasure hW).real {0} := by
  have hlim : ∀ x : ℝ, Tendsto (fun b : ℝ => b * (LSeries D.uC (lineShift x b)).re) (𝓝[>] 0)
      (𝓝 (D.ε * ((boundaryMeasure hΛ).real {x} - (boundaryMeasure hW).real {x}))) := by
    intro x
    have h1 := tendsto_mul_re_weilContinuation_atom hW x
    have h2 := tendsto_mul_re_weilContinuation_atom hΛ x
    have h3 := D.tendsto_mul_re_E x
    have hcomb := ((h2.sub h1).sub h3).const_mul D.ε
    rw [sub_zero] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hb' : 0 < b := hb
    have hid := D.weilContinuation_eq_sub hW hΛ (z := lineShift x b) (by rw [lineShift_re]; linarith)
    change D.ε * (b * (weilContinuation hΛ (lineShift x b)).re -
      b * (weilContinuation hW (lineShift x b)).re - b * (D.E (lineShift x b)).re) = _
    rw [hid, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul]
    have := D.ε_mul_ε
    linear_combination (b * (LSeries D.uC (lineShift x b)).re) * this
  have hbound : ∀ b : ℝ, 0 < b → |b * (LSeries D.uC (lineShift a b)).re| ≤
      b * (LSeries D.uC (lineShift 0 b)).re := by
    intro b hb
    rw [abs_mul, abs_of_pos hb]
    refine mul_le_mul_of_nonneg_left ?_ hb.le
    have h := D.norm_LSeries_uC_le hW (s := lineShift a b) (by rw [lineShift_re]; linarith)
    rw [lineShift_re] at h
    have e : ((1 / 2 + b : ℝ) : ℂ) = lineShift 0 b := by simp [lineShift]
    rw [e] at h
    exact (Complex.abs_re_le_norm _).trans h
  have hle := le_of_tendsto_of_tendsto (hlim a).abs (hlim 0)
    (by filter_upwards [self_mem_nhdsWithin] with b hb; exact hbound b hb)
  rw [boundaryMeasure_vonMangoldt_real_zero hΛ, zero_sub, abs_mul, D.abs_ε, one_mul] at hle
  linarith

include D in
/-- **Atom bound, normalized.**  `|μ_Λ{a} − μ_lam{a}| ≤ μ_lam{0}` for every `a`. -/
theorem abs_atom_sub_le_atom_zero (hW : WeilPositiveFull lam)
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (a : ℝ) :
    |(boundaryMeasure hΛ).real {a} - (boundaryMeasure hW).real {a}| ≤
      (boundaryMeasure hW).real {0} := by
  have h0 := D.abs_atom_sub_le hW hΛ 0
  rw [boundaryMeasure_vonMangoldt_real_zero hΛ, zero_sub, abs_neg] at h0
  have hnn : 0 ≤ (boundaryMeasure hW).real {0} := ENNReal.toReal_nonneg
  have hε : -D.ε * (boundaryMeasure hW).real {0} = (boundaryMeasure hW).real {0} := by
    rcases D.hε with h | h
    · rw [h] at h0 ⊢
      rw [abs_of_nonneg hnn] at h0
      linarith
    · rw [h]; ring
  rw [← hε]
  exact D.abs_atom_sub_le hW hΛ a

end Decomposition

end RHTower.WeilConditional
