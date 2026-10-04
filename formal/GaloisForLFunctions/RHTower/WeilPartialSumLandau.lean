import GaloisForLFunctions.RHTower.WeilFullConeDeviationResidue
import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare
import GaloisForLFunctions.RHTower.TailMeasureLaplace
import GaloisForLFunctions.RHTower.LandauSingularAtAbscissa
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# One-signed excess partial sums force RH in the full Weil cone

**Theorem** (`riemannHypothesis_of_partialSums`).  Let `lam` be full-cone Weil-positive and
`ε = ±1`.  If every partial sum `S(N) = Σ_{2 ≤ n ≤ N} ε(lam(n) − Λ(n))` is nonnegative, then RH
holds.  For `ε = 1` this is the one-sided Chebyshev condition `Σ_{n ≤ x} lam(n) ≥ ψ(x)`.

**Proof.**  In the logarithmic variable, `∫_0^∞ S(e^u) e^{−zu} du = L(ε(lam − Λ))(z)/z` for
`Re z > 3/2` (partial summation), and on `Re z > 1` the Dirichlet series is
`ε(ξ'/ξ − Φ_lam)(z)`, which is holomorphic at every real point `σ > ½` (`ξ` has no real zero and
`Φ_lam` is the Herglotz continuation).  Thickening `S(e^u) ≥ 0` by `e^{u/4}` gives a nonnegative
measure whose Laplace abscissa `c` lies in `[¼, 2]`; Landau's theorem forbids `c > ½`.  So the
Laplace transform is holomorphic on `Re z > ½`, and `ξ'/ξ − Φ_lam` extends holomorphically to
`Re z > ½`.  At a zero `ρ` with `Re ρ > ½` the residue of `ξ'/ξ − Φ_lam` is the order of `ξ`
(`riemannHypothesis_of_extension`), so there is none.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa tailCarrier
  tailMeasure complexLaplace_ofReal hasDerivAt_complexLaplace false_of_analyticAt_abscissa
  exists_isAbscissa laplaceMass_tailMeasure_eq_top laplaceMass_tailMeasure_ne_top
  laplaceReal_tailMeasure)

noncomputable section

namespace RHTower.WeilPartialSum

open WeilSpectral WeilHerglotz

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## RH from a holomorphic extension of `ξ'/ξ − Φ_lam` -/

theorem tendsto_ofReal_nhdsNE (a : ℝ) :
    Tendsto (fun t : ℝ => ((t : ℂ))) (𝓝[≠] a) (𝓝[≠] ((a : ℂ))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (Complex.continuous_ofReal.tendsto a).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
    exact fun h => ht (Complex.ofReal_inj.mp h)

/-- A holomorphic function restricts to a real-analytic one on the real axis. -/
theorem analyticAt_ofReal_comp {f : ℂ → ℂ} {σ : ℝ} (hf : AnalyticAt ℂ f ((σ : ℂ))) :
    AnalyticAt ℝ (fun t : ℝ => f ((t : ℂ))) σ :=
  AnalyticAt.comp (x := σ) (g := f) (f := fun t : ℝ => ((t : ℂ))) hf.restrictScalars
    (Complex.ofRealCLM.analyticAt σ)

/-- **RH from an extension.**  If `ξ'/ξ − Φ_lam` agrees on a real ray `(a, ∞)` with a function
holomorphic on `Re s > ½`, then RH holds. -/
theorem riemannHypothesis_of_extension {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {s | 1 / 2 < s.re}) {a : ℝ}
    (hagree : ∀ σ : ℝ, a < σ → logDeriv xi σ - weilContinuation hW σ = H σ) :
    RiemannHypothesis := by
  set U : Set ℂ := {s | 1 / 2 < s.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hΦd : DifferentiableOn ℂ (weilContinuation hW) U := differentiableOn_weilContinuation hW
  have hf : AnalyticOnNhd ℂ (deriv xi) U :=
    ((xi_analyticOnNhd Set.univ).deriv).mono (subset_univ _)
  have hg : AnalyticOnNhd ℂ (fun z => (H z + weilContinuation hW z) * xi z) U :=
    ((hH.add hΦd).mul xi_differentiable.differentiableOn).analyticOnNhd hU
  set σ₀ : ℝ := max a 1 + 1 with hσ₀
  have hσ₀U : ((σ₀ : ℝ) : ℂ) ∈ U := by
    show 1 / 2 < ((σ₀ : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith [le_max_right a 1]
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] σ₀,
      deriv xi (t : ℂ) = (H t + weilContinuation hW t) * xi t := by
    have hopen : ∀ᶠ t in 𝓝 σ₀, max a 1 < t :=
      isOpen_Ioi.mem_nhds (show σ₀ ∈ Ioi (max a 1) by simp [hσ₀])
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hopen] with t ht
    have hta : a < t := lt_of_le_of_lt (le_max_left a 1) ht
    have ht1 : 1 < ((t : ℂ)).re := by
      rw [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_right a 1) ht
    have hxi : xi t ≠ 0 := xi_ne_zero_of_one_lt_re ht1
    have h := hagree t hta
    rw [logDeriv_apply] at h
    have h' : deriv xi t / xi t = H t + weilContinuation hW t := by linear_combination h
    rwa [div_eq_iff hxi] at h'
  have hfreq : ∃ᶠ z in 𝓝[≠] ((σ₀ : ℝ) : ℂ),
      deriv xi z = (H z + weilContinuation hW z) * xi z :=
    (tendsto_ofReal_nhdsNE σ₀).frequently hev.frequently
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg hUc hσ₀U hfreq
  refine rh_iff_xi_ne_zero_right.mpr fun ρ hρ hzero => ?_
  have hρ' : 1 / 2 < ρ.re := hρ
  have hHc : ContinuousAt H ρ := (hH.differentiableAt (hU.mem_nhds hρ')).continuousAt
  have hlin : Tendsto (fun z => (z - ρ) * H z) (𝓝[≠] ρ) (𝓝 0) := by
    have h1 : ContinuousAt (fun z : ℂ => z - ρ) ρ := by fun_prop
    have h : Tendsto (fun z => (z - ρ) * H z) (𝓝 ρ) (𝓝 ((ρ - ρ) * H ρ)) :=
      (h1.mul hHc).tendsto
    rw [sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ z in 𝓝[≠] ρ, xi z ≠ 0 := by
    rcases (xi_differentiable.analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) (xi_orderAt_ne_top ρ)
    · exact h
  have hre : ∀ᶠ z in 𝓝[≠] ρ, 1 / 2 < z.re :=
    eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hρ')
  have hcongr : (fun z => (z - ρ) * (logDeriv xi z - weilContinuation hW z)) =ᶠ[𝓝[≠] ρ]
      fun z => (z - ρ) * H z := by
    filter_upwards [hne, hre] with z hz hzre
    rw [logDeriv_apply, heq hzre, mul_div_assoc, div_self hz, mul_one]
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

/-! ## The excess partial sums -/

/-- `S(x) = Σ_{2 ≤ n ≤ x} ε(lam(n) − Λ(n))`. -/
def excessSum (ε : ℝ) (lam : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, ε * (lam n - Λ n)

/-- The excess coefficients `ε(lam − Λ)` on `n ≥ 2`, as a complex sequence. -/
def excessCoeff (ε : ℝ) (lam : ℕ → ℝ) (n : ℕ) : ℂ := (ε : ℂ) * (lamC lam n - (Λ n : ℂ))

theorem vonMangoldt_lt_two {n : ℕ} (hn : n < 2) : (Λ n : ℝ) = 0 := by
  interval_cases n <;> simp

theorem excessCoeff_of_le {ε : ℝ} {lam : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n) :
    excessCoeff ε lam n = ((ε * (lam n - Λ n) : ℝ) : ℂ) := by
  simp only [excessCoeff, lamC, if_pos hn]
  push_cast
  ring

theorem excessCoeff_of_lt {ε : ℝ} {lam : ℕ → ℝ} {n : ℕ} (hn : n < 2) :
    excessCoeff ε lam n = 0 := by
  simp [excessCoeff, lamC, if_neg (by omega : ¬ 2 ≤ n), vonMangoldt_lt_two hn]

theorem sum_Icc_one_excessCoeff (ε : ℝ) (lam : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, excessCoeff ε lam k = ((excessSum ε lam M : ℝ) : ℂ) := by
  have hsub : Finset.Icc 2 M ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc_left (by norm_num)
  rw [← Finset.sum_subset hsub fun k hk hk2 => by
    rw [Finset.mem_Icc] at hk hk2
    exact excessCoeff_of_lt (by omega)]
  unfold excessSum
  rw [Nat.floor_natCast]
  push_cast
  exact Finset.sum_congr rfl fun k hk => by
    rw [excessCoeff_of_le (Finset.mem_Icc.mp hk).1]; push_cast; ring

theorem excessSum_natFloor (ε : ℝ) (lam : ℕ → ℝ) (x : ℝ) :
    excessSum ε lam x = excessSum ε lam (⌊x⌋₊ : ℝ) := by
  simp [excessSum, Nat.floor_natCast]

theorem measurable_excessSum (ε : ℝ) (lam : ℕ → ℝ) : Measurable (excessSum ε lam) := by
  have : excessSum ε lam =
      (fun N : ℕ => ∑ n ∈ Finset.Icc 2 N, ε * (lam n - Λ n)) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

/-- The excess partial sums grow at most like `x^{3/2}`. -/
theorem exists_abs_excessSum_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {ε : ℝ}
    (hε : |ε| = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |excessSum ε lam x| ≤ C * x ^ (3 / 2 : ℝ) := by
  have hs1 := WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW
    (σ := 3 / 2) (by norm_num)
  have hs2 : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
    have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := ((3 / 2 : ℝ) : ℂ)) (by simp; norm_num)).norm
    refine h.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', Complex.ofReal_re, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  set a : ℕ → ℝ := fun n => (|lam n| + Λ n) / (n : ℝ) ^ (3 / 2 : ℝ) with ha
  have hsum : Summable a := by
    refine (hs1.add hs2).congr fun n => ?_
    simp only [ha, add_div]
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    simp only [ha]
    exact div_nonneg (add_nonneg (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨∑' n, a n, tsum_nonneg ha0, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  unfold excessSum
  calc |∑ n ∈ Finset.Icc 2 ⌊x⌋₊, ε * (lam n - Λ n)|
      ≤ ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, |ε * (lam n - Λ n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, x ^ (3 / 2 : ℝ) * a n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp hn).1
        have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).mp (Finset.mem_Icc.mp hn).2
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hpow : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
        have hle : (n : ℝ) ^ (3 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow hnpos.le hnx (by norm_num)
        rw [abs_mul, hε, one_mul, ha]
        simp only
        rw [mul_div_assoc', le_div_iff₀ hpow]
        calc |lam n - Λ n| * (n : ℝ) ^ (3 / 2 : ℝ)
            ≤ (|lam n| + Λ n) * x ^ (3 / 2 : ℝ) := by
              refine mul_le_mul ?_ hle hpow.le (add_nonneg (abs_nonneg _)
                ArithmeticFunction.vonMangoldt_nonneg)
              calc |lam n - Λ n| ≤ |lam n| + |(Λ n : ℝ)| := abs_sub _ _
                _ = |lam n| + Λ n := by
                    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          _ = x ^ (3 / 2 : ℝ) * (|lam n| + Λ n) := by ring
    _ = x ^ (3 / 2 : ℝ) * ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n := by rw [Finset.mul_sum]
    _ ≤ x ^ (3 / 2 : ℝ) * ∑' n, a n :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun n _ => ha0 n)
          (Real.rpow_nonneg hx0 _)
    _ = (∑' n, a n) * x ^ (3 / 2 : ℝ) := by ring

theorem lseriesSummable_excessCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (ε : ℝ) {z : ℂ}
    (hz : 1 < z.re) : LSeriesSummable (excessCoeff ε lam) z := by
  have h := (LSeriesSummable.sub (f := lamC lam) (summable_term_lamC hW hz)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hz)).smul (ε : ℂ)
  convert h using 1
  funext n
  simp [excessCoeff]

theorem LSeries_excessCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (ε : ℝ) {z : ℂ}
    (hz : 1 < z.re) :
    LSeries (excessCoeff ε lam) z = (ε : ℂ) * (logDeriv xi z - weilContinuation hW z) := by
  have hfun : excessCoeff ε lam = (ε : ℂ) • (lamC lam - fun n => (Λ n : ℂ)) := by
    funext n; simp [excessCoeff]
  rw [hfun, LSeries_smul, LSeries_sub (summable_term_lamC hW hz)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hz),
    logDeriv_xi_sub_weilContinuation_eq hW hz]

theorem image_exp_Ioi_zero' : Real.exp '' Ioi 0 = Ioi 1 := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Real.one_lt_exp_iff.mpr hu
  · intro hy
    have hy0 : 0 < y := lt_trans one_pos hy
    exact ⟨Real.log y, Real.log_pos hy, Real.exp_log hy0⟩

/-- **Partial summation in the logarithmic variable**:
`∫_0^∞ S(e^u) e^{−zu} du = L(ε(lam − Λ))(z)/z` for `Re z > 3/2`. -/
theorem integral_excessSum_exp_mul_cexp {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {ε : ℝ}
    (hε : |ε| = 1) {z : ℂ} (hz : 3 / 2 < z.re) :
    ∫ u in Ioi (0 : ℝ), (excessSum ε lam (Real.exp u) : ℂ) * Complex.exp (-z * u) =
      LSeries (excessCoeff ε lam) z / z := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_excessSum_le hW hε
  have hz0 : z ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, excessCoeff ε lam k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [sum_Icc_one_excessCoeff, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact hC n (by exact_mod_cast hn)
  have hL := LSeries_eq_mul_integral (excessCoeff ε lam) (r := 3 / 2) (by norm_num) hz
    (lseriesSummable_excessCoeff hW ε (by linarith)) hO
  rw [← image_exp_Ioi_zero', integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn] at hL
  have hcongr : ∫ u in Ioi (0 : ℝ), |Real.exp u| • ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊,
        excessCoeff ε lam k) * ((Real.exp u : ℝ) : ℂ) ^ (-(z + 1)))
      = ∫ u in Ioi (0 : ℝ), (excessSum ε lam (Real.exp u) : ℂ) * Complex.exp (-z * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hcpow : ((Real.exp u : ℝ) : ℂ) ^ (-(z + 1)) = Complex.exp (u * (-(z + 1))) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
        ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    rw [abs_of_pos (Real.exp_pos u), hcpow, Complex.real_smul, Complex.ofReal_exp,
      sum_Icc_one_excessCoeff, ← excessSum_natFloor]
    rw [mul_comm (Complex.exp (u : ℂ)), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hcongr] at hL
  rw [hL, mul_div_cancel_left₀ _ hz0]

/-! ## Landau -/

/-- The candidate continuation `ε(ξ'/ξ − Φ_lam)(z)/z + 1/(z − ¼)`. -/
def continuation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (ε : ℝ) (z : ℂ) : ℂ :=
  (ε : ℂ) * (logDeriv xi z - weilContinuation hW z) / z + 1 / (z - 1 / 4)

theorem analyticAt_continuation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (ε : ℝ) {z : ℂ}
    (hz : 1 / 2 < z.re) (hxi : xi z ≠ 0) : AnalyticAt ℂ (continuation hW ε) z := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΦ : AnalyticAt ℂ (weilContinuation hW) z :=
    (differentiableOn_weilContinuation hW).analyticAt (hU.mem_nhds hz)
  have hd : AnalyticAt ℂ (deriv xi) z := (xi_analyticOnNhd Set.univ).deriv z (mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv xi) z := by
    have : logDeriv xi = fun s => deriv xi s / xi s := funext fun s => logDeriv_apply xi s
    rw [this]
    exact hd.div (xi_differentiable.analyticAt z) hxi
  have hz0 : z ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz; linarith
  have hz4 : z - 1 / 4 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold continuation
  exact ((analyticAt_const.mul (hlog.sub hΦ)).div analyticAt_id hz0).add
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hz4)

/-- **One-signed excess partial sums force RH.** -/
theorem riemannHypothesis_of_partialSums {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hS : ∀ N : ℕ, 0 ≤ ∑ n ∈ Finset.Icc 2 N, ε * (lam n - Λ n)) :
    RiemannHypothesis := by
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεsq : (ε : ℂ) * ε = 1 := by
    rcases hε with h | h <;> rw [h] <;> push_cast <;> ring
  set g : ℝ → ℝ := fun u => excessSum ε lam (Real.exp u) with hgdef
  have hg : Measurable g := (measurable_excessSum ε lam).comp Real.measurable_exp
  have hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (0 + u) := fun u _ => hS _
  obtain ⟨C, hC0, hC⟩ := exists_abs_excessSum_le hW hεabs
  -- integrability right of `3/2`
  have hgint : ∀ σ : ℝ, 3 / 2 < σ →
      IntegrableOn (fun u : ℝ => g u * Real.exp (-σ * u)) (Ioi 0) := by
    intro σ hσ
    refine ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ - 3 / 2)).const_mul C).mono' ?_ ?_
    · exact ((hg.mul (Real.measurable_exp.comp
        (measurable_const.mul measurable_id))).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      have hb := hC (Real.exp u) (Real.one_le_exp hu0.le)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hpow : Real.exp u ^ (3 / 2 : ℝ) = Real.exp (3 / 2 * u) := by
        rw [← Real.exp_mul]; ring_nf
      rw [hpow] at hb
      calc |g u| * Real.exp (-σ * u) ≤ C * Real.exp (3 / 2 * u) * Real.exp (-σ * u) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = C * Real.exp (-(σ - 3 / 2) * u) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have key : ∀ σ u : ℝ, g u * Real.exp (-σ * u) + Real.exp (-(σ - 1 / 4) * u) =
      Real.exp (-σ * u) * tailCarrier g 0 u := by
    intro σ u
    simp only [tailCarrier, zero_add]
    rw [show -(σ - 1 / 4) * u = -σ * u + u / 4 by ring, Real.exp_add]
    ring
  have hcarrier : ∀ σ : ℝ, 3 / 2 < σ →
      IntegrableOn (fun u : ℝ => Real.exp (-σ * u) * tailCarrier g 0 u) (Ioi 0) := by
    intro σ hσ
    have h2 : IntegrableOn (fun u : ℝ => Real.exp (-(σ - 1 / 4) * u)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (by linarith)
    exact ((hgint σ hσ).add h2).congr_fun (fun u _ => key σ u) measurableSet_Ioi
  set ν : Measure ℝ := tailMeasure g 0 with hνdef
  obtain ⟨c, hc⟩ := exists_isAbscissa (ν := ν)
    ⟨2, laplaceMass_tailMeasure_ne_top hg hpos (hcarrier 2 (by norm_num))⟩
    ⟨0, laplaceMass_tailMeasure_eq_top hg hpos (by norm_num)⟩
  -- the real transform right of `3/2`
  have hreal : ∀ σ : ℝ, 3 / 2 < σ →
      ((laplaceReal ν σ : ℝ) : ℂ) = continuation hW ε σ := by
    intro σ hσ
    have hσc : 3 / 2 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ
    rw [laplaceReal_tailMeasure hg hpos]
    have hsplit : ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * tailCarrier g 0 u =
        (∫ u in Ioi (0 : ℝ), g u * Real.exp (-σ * u)) +
          ∫ u in Ioi (0 : ℝ), Real.exp (-(σ - 1 / 4) * u) := by
      rw [← integral_add (hgint σ hσ) (exp_neg_integrableOn_Ioi 0 (by linarith))]
      exact setIntegral_congr_fun measurableSet_Ioi fun u _ => (key σ u).symm
    have hexp : ∫ u in Ioi (0 : ℝ), Real.exp (-(σ - 1 / 4) * u) = 1 / (σ - 1 / 4) := by
      rw [integral_exp_mul_Ioi (by linarith : -(σ - 1 / 4) < 0) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp
    have hgc : ((∫ u in Ioi (0 : ℝ), g u * Real.exp (-σ * u) : ℝ) : ℂ) =
        LSeries (excessCoeff ε lam) σ / σ := by
      rw [← integral_excessSum_exp_mul_cexp hW hεabs hσc, ← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      congr 2
      push_cast
      ring
    rw [hsplit, hexp, Complex.ofReal_add, hgc, LSeries_excessCoeff hW ε (by linarith),
      continuation]
    push_cast
    ring
  -- analyticity of the transform right of the abscissa
  have hCLan : ∀ z : ℂ, c < z.re → AnalyticAt ℂ (complexLaplace ν) z := by
    intro z hz
    have hopen : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | c < w.re} := fun w hw =>
      ((hasDerivAt_complexLaplace hc hw).differentiableAt).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds hz)
  have hcont_real : ∀ t : ℝ, 1 / 2 < t → AnalyticAt ℂ (continuation hW ε) (t : ℂ) := fun t ht =>
    analyticAt_continuation hW ε (by rw [Complex.ofReal_re]; exact ht) (xi_ne_zero_of_real t)
  -- the transform equals the continuation on the real ray right of `max c ½`
  have hray : ∀ σ : ℝ, max c (1 / 2) < σ →
      complexLaplace ν (σ : ℂ) = continuation hW ε σ := by
    have h1 : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν (t : ℂ)) (Ioi (max c (1 / 2))) := by
      intro t ht
      exact analyticAt_ofReal_comp
        (hCLan _ (by rw [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_left _ _) ht))
    have h2 : AnalyticOnNhd ℝ (fun t : ℝ => continuation hW ε (t : ℂ)) (Ioi (max c (1 / 2))) := by
      intro t ht
      exact analyticAt_ofReal_comp (hcont_real t (lt_of_le_of_lt (le_max_right _ _) ht))
    set z₀ : ℝ := max (max c (1 / 2)) 2 + 1 with hz₀
    have hz₀mem : z₀ ∈ Ioi (max c (1 / 2)) := by
      show max c (1 / 2) < z₀
      linarith [le_max_left (max c (1 / 2)) 2]
    have hev : (fun t : ℝ => complexLaplace ν (t : ℂ)) =ᶠ[𝓝 z₀]
        fun t : ℝ => continuation hW ε (t : ℂ) := by
      have hbig : (3 : ℝ) / 2 < z₀ := by linarith [le_max_right (max c (1 / 2)) 2]
      filter_upwards [isOpen_Ioi.mem_nhds (show z₀ ∈ Ioi ((3 : ℝ) / 2) from hbig)] with t ht
      rw [complexLaplace_ofReal, hreal t ht]
    exact fun σ hσ =>
      h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_Ioi hz₀mem hev hσ
  -- Landau: the abscissa is at most `½`
  have hcle : c ≤ 1 / 2 := by
    by_contra hgt
    rw [not_le] at hgt
    have hxic : xi (c : ℂ) ≠ 0 := xi_ne_zero_of_real c
    have hopenxi : IsOpen {w : ℂ | xi w ≠ 0} :=
      isOpen_compl_singleton.preimage xi_differentiable.continuous
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.isOpen_iff.mp hopenxi _ hxic
    set δ : ℝ := min δ₁ (c - 1 / 2) with hδdef
    have hδpos : 0 < δ := lt_min hδ₁ (by linarith)
    refine false_of_analyticAt_abscissa (Φ := continuation hW ε) hc hδpos ?_ ?_
    · intro z hz
      have hdist : dist z (c : ℂ) < δ := Metric.mem_ball.mp hz
      have hre : |z.re - c| < δ := by
        have h1 : |z.re - ((c : ℂ)).re| ≤ ‖z - (c : ℂ)‖ := by
          have := Complex.abs_re_le_norm (z - (c : ℂ))
          simpa using this
        have h2 : ‖z - (c : ℂ)‖ < δ := by rw [← Complex.dist_eq]; exact hdist
        simpa using lt_of_le_of_lt h1 h2
      have hzre : 1 / 2 < z.re := by
        have hlt : δ ≤ c - 1 / 2 := min_le_right _ _
        linarith [(abs_lt.mp hre).1]
      exact analyticAt_continuation hW ε hzre
        (hsub (Metric.mem_ball.mpr (lt_of_lt_of_le hdist (min_le_left _ _))))
    · intro σ h1 _
      rw [← complexLaplace_ofReal, hray σ (by rw [max_eq_left hgt.le]; exact h1)]
  -- the extension
  set H : ℂ → ℂ := fun z => (ε : ℂ) * z * (complexLaplace ν z - 1 / (z - 1 / 4)) with hHdef
  have hH : DifferentiableOn ℂ H {s | 1 / 2 < s.re} := by
    intro z hz
    have hz' : 1 / 2 < z.re := hz
    have hz4 : z - 1 / 4 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    exact ((analyticAt_const.mul analyticAt_id).mul ((hCLan z (by linarith)).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hz4))).differentiableAt
      |>.differentiableWithinAt
  refine riemannHypothesis_of_extension hW hH (a := 1 / 2) fun σ hσ => ?_
  have hσ' : max c (1 / 2) < σ := by rw [max_eq_right hcle]; exact hσ
  have h := hray σ hσ'
  have hσ0 : (σ : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  show logDeriv xi σ - weilContinuation hW σ =
    (ε : ℂ) * σ * (complexLaplace ν σ - 1 / (σ - 1 / 4))
  rw [h, continuation, add_sub_cancel_right]
  have e1 : (ε : ℂ) * σ * ((ε : ℂ) * (logDeriv xi σ - weilContinuation hW σ) / σ) =
      ((ε : ℂ) * ε) * (logDeriv xi σ - weilContinuation hW σ) := by
    field_simp
  rw [e1, hεsq, one_mul]

end RHTower.WeilPartialSum
