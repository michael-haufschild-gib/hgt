import GaloisForLFunctions.RHTower.WeilFullConeDeviationResidue
import GaloisForLFunctions.RHTower.LandauRelativeRigidity
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.WeilAbscissaRigidity

/-!
# A Weil-positive system whose excess over `Λ` is small forces RH

Let `lam` be full-cone Weil-positive.  Split its deviation from the von Mangoldt function on
`n ≥ 2` into nonnegative parts, `lam − Λ = P − N` (`deviationPos`, `deviationNeg`).

**Theorem** (`riemannHypothesis_of_weilPositiveFull_of_summable_deviationPos`).  If
`Σ P(n) n^{−σ} < ∞` for every `σ > 1/2`, then RH holds.

**Balanced abscissae** (`summable_deviationPos_iff_summable_deviationNeg`).  Right of every
`c ≥ 1/2`, `P` and `N` converge together.  With absolute-abscissa rigidity this gives
`not_summable_deviation_of_ne`: a Weil-positive `lam ≠ Λ` has `Σ P(n) n^{−s} = Σ N(n) n^{−s} = ∞`
for every `s < 1`, i.e. it exceeds and falls short of `Λ` at full prime-number-theorem scale.
Equivalently (`eq_vonMangoldt_of_weilPositiveFull_of_summable_deviation`), convergence of either
part at a single `s < 1` forces `lam = Λ`.

**Proof.**
* On `Re s > 1`, `ξ'/ξ − Φ_lam = L(P) − L(N)`, where `Φ_lam` is the Herglotz continuation of the
  Weil function.  Equivalently `ξ' = (L(P) − L(N) + Φ_lam) ξ`.  Both sides are holomorphic on every
  half-plane where `L(N)` converges, so the identity holds there.
* Landau.  If the real abscissa `σ_c` of the nonnegative series `L(N)` exceeded `1/2`, then
  `G = L(P) + Φ_lam − ξ'/ξ` would be holomorphic on a disk around the real point `σ_c` (where
  `ξ ≠ 0`) and equal to `L(N)` to the right of `σ_c`.  This contradicts Landau's theorem
  (`gdSeries_no_continuation_at_abscissa`).  So `L(N)` converges on `Re s > 1/2`.
* Then `ξ'/ξ − Φ_lam = L(P) − L(N)` is regular at every point `ρ` with `Re ρ > 1/2`.  The residue
  law `tendsto_sub_mul_logDeriv_xi_sub_weilContinuation` forces `ord_ρ ξ = 0`.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- The positive part of `lam − Λ` on `n ≥ 2`. -/
def deviationPos (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 else 0

/-- The negative part of `lam − Λ` on `n ≥ 2`. -/
def deviationNeg (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 else 0

/-- The frequencies `log n` of an ordinary Dirichlet series. -/
def logFreq (n : ℕ) : ℝ := Real.log n

theorem logFreq_nonneg (n : ℕ) : 0 ≤ logFreq n := Real.log_natCast_nonneg n

theorem deviationPos_nonneg (lam : ℕ → ℝ) (n : ℕ) : 0 ≤ deviationPos lam n := by
  unfold deviationPos; split_ifs <;> simp

theorem deviationNeg_nonneg (lam : ℕ → ℝ) (n : ℕ) : 0 ≤ deviationNeg lam n := by
  unfold deviationNeg; split_ifs <;> simp

theorem deviationPos_zero (lam : ℕ → ℝ) : deviationPos lam 0 = 0 := by simp [deviationPos]

theorem deviationNeg_zero (lam : ℕ → ℝ) : deviationNeg lam 0 = 0 := by simp [deviationNeg]

theorem deviationPos_le (lam : ℕ → ℝ) (n : ℕ) : deviationPos lam n ≤ |lam n| := by
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  unfold deviationPos
  split_ifs
  · exact max_le (by linarith [le_abs_self (lam n)]) (abs_nonneg _)
  · exact abs_nonneg _

theorem deviationNeg_le (lam : ℕ → ℝ) (n : ℕ) :
    deviationNeg lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) + |lam n| := by
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  unfold deviationNeg
  split_ifs
  · exact max_le (by linarith [neg_abs_le (lam n)]) (by positivity)
  · positivity

theorem lamC_sub_vonMangoldt (lam : ℕ → ℝ) (n : ℕ) :
    lamC lam n - (ArithmeticFunction.vonMangoldt n : ℂ) =
      (deviationPos lam n : ℂ) - (deviationNeg lam n : ℂ) := by
  unfold lamC deviationPos deviationNeg
  split_ifs with h
  · have key := max_zero_sub_max_neg_zero_eq_self (lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
    rw [neg_sub] at key
    exact_mod_cast key.symm
  · push Not at h
    interval_cases n <;> simp

/-! ## Ordinary Dirichlet series as general Dirichlet series -/

theorem gdTwistTerm_logFreq (a : ℕ → ℝ) (ha0 : a 0 = 0) (σ : ℝ) (n : ℕ) :
    gdTwistTerm a logFreq σ 0 n = a n / (n : ℝ) ^ σ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gdTwistTerm, ha0]
  · have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [gdTwistTerm, logFreq, pow_zero, mul_one, Real.rpow_def_of_pos hpos, div_eq_mul_inv,
      ← Real.exp_neg]
    ring_nf

theorem gdSeries_logFreq (a : ℕ → ℝ) (ha0 : a 0 = 0) (s : ℂ) :
    gdSeries a logFreq s = LSeries (fun n => (a n : ℂ)) s := by
  unfold gdSeries LSeries
  congr 1
  ext n
  rw [LSeries.term_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [if_neg hn.ne', cpow_def_of_ne_zero hn0, logFreq, Complex.natCast_log, div_eq_mul_inv,
      ← Complex.exp_neg]
    ring_nf

theorem lSeriesSummable_of_gdTwistTerm {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) {s : ℂ}
    (h : Summable (gdTwistTerm a logFreq s.re 0)) : LSeriesSummable (fun n => (a n : ℂ)) s := by
  refine Summable.of_norm (h.congr fun n => ?_)
  rw [LSeries.norm_term_eq, gdTwistTerm_logFreq a ha0]
  split_ifs with hn
  · subst hn; simp [ha0]
  · rw [Complex.norm_real, Real.norm_of_nonneg (ha n)]

theorem differentiableAt_LSeries_of_gdTwistTerm {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0)
    {σ : ℝ} (hsum : ∀ τ, σ < τ → Summable (gdTwistTerm a logFreq τ 0)) {s : ℂ} (hs : σ < s.re) :
    DifferentiableAt ℂ (LSeries fun n => (a n : ℂ)) s := by
  set τ : ℝ := (σ + s.re) / 2 with hτdef
  have hτ : σ < τ := by rw [hτdef]; linarith
  have hτs : τ < s.re := by rw [hτdef]; linarith
  have hS : LSeriesSummable (fun n => (a n : ℂ)) (τ : ℂ) :=
    lSeriesSummable_of_gdTwistTerm ha ha0 (by simpa using hsum τ hτ)
  have hab : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < (s.re : EReal) := by
    have h1 := hS.abscissaOfAbsConv_le
    simp only [ofReal_re] at h1
    exact lt_of_le_of_lt h1 (by exact_mod_cast hτs)
  exact (LSeries_hasDerivAt hab).differentiableAt

theorem summable_gdTwistTerm_deviationPos {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ}
    (hσ : 1 < σ) : Summable (gdTwistTerm (deviationPos lam) logFreq σ 0) := by
  refine Summable.of_nonneg_of_le
    (gdTwistTerm_nonneg (deviationPos_nonneg lam) logFreq_nonneg σ 0) (fun n => ?_)
    (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ)
  rw [gdTwistTerm_logFreq _ (deviationPos_zero lam)]
  exact div_le_div_of_nonneg_right (deviationPos_le lam n) (by positivity)

theorem summable_gdTwistTerm_deviationNeg_of_one_lt {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) : Summable (gdTwistTerm (deviationNeg lam) logFreq σ 0) := by
  refine Summable.of_nonneg_of_le
    (gdTwistTerm_nonneg (deviationNeg_nonneg lam) logFreq_nonneg σ 0) (fun n => ?_)
    ((RHTower.summable_vonMangoldt_div_rpow hσ).add
      (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ))
  rw [gdTwistTerm_logFreq _ (deviationNeg_zero lam), ← add_div]
  exact div_le_div_of_nonneg_right (deviationNeg_le lam n) (by positivity)

/-! ## The deviation identity for `ξ'` -/

/-- On `Re s > 1`, `ξ' = (L(P) − L(N) + Φ_lam) ξ`. -/
theorem deriv_xi_eq_of_one_lt_re {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) :
    deriv xi s = (LSeries (fun n => (deviationPos lam n : ℂ)) s -
      LSeries (fun n => (deviationNeg lam n : ℂ)) s + weilContinuation hW s) * xi s := by
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_lt_re hs
  have h := logDeriv_xi_sub_weilContinuation_eq hW hs
  have hP : LSeriesSummable (fun n => (deviationPos lam n : ℂ)) s :=
    lSeriesSummable_of_gdTwistTerm (deviationPos_nonneg lam) (deviationPos_zero lam)
      (summable_gdTwistTerm_deviationPos hW hs)
  have hN : LSeriesSummable (fun n => (deviationNeg lam n : ℂ)) s :=
    lSeriesSummable_of_gdTwistTerm (deviationNeg_nonneg lam) (deviationNeg_zero lam)
      (summable_gdTwistTerm_deviationNeg_of_one_lt hW hs)
  rw [← LSeries_sub (summable_term_lamC hW hs) (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
    at h
  have hfun : (lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (fun n => (deviationPos lam n : ℂ)) - fun n => (deviationNeg lam n : ℂ) :=
    funext (lamC_sub_vonMangoldt lam)
  rw [hfun, LSeries_sub hP hN, logDeriv_apply] at h
  have h' : deriv xi s / xi s = LSeries (fun n => (deviationPos lam n : ℂ)) s -
      LSeries (fun n => (deviationNeg lam n : ℂ)) s + weilContinuation hW s := by
    linear_combination h
  rwa [div_eq_iff hxi] at h'

/-- The deviation identity holds on every half-plane `Re s > c` (`c ≥ 1/2`) on which both parts
converge. -/
theorem deriv_xi_eq_of_lt_re {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {c : ℝ} (hc : 1 / 2 ≤ c)
    (hN : ∀ τ, c < τ → Summable (gdTwistTerm (deviationNeg lam) logFreq τ 0))
    (hP : ∀ τ, c < τ → Summable (gdTwistTerm (deviationPos lam) logFreq τ 0))
    {s : ℂ} (hs : c < s.re) :
    deriv xi s = (LSeries (fun n => (deviationPos lam n : ℂ)) s -
      LSeries (fun n => (deviationNeg lam n : ℂ)) s + weilContinuation hW s) * xi s := by
  set U : Set ℂ := {z | c < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt c).isPreconnected
  have hf : AnalyticOnNhd ℂ (deriv xi) U := ((xi_analyticOnNhd Set.univ).deriv).mono (subset_univ _)
  have hg : AnalyticOnNhd ℂ (fun z => (LSeries (fun n => (deviationPos lam n : ℂ)) z -
      LSeries (fun n => (deviationNeg lam n : ℂ)) z + weilContinuation hW z) * xi z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    have hz' : c < z.re := hz
    have hzh : 1 / 2 < z.re := lt_of_le_of_lt hc hz'
    have hdP := differentiableAt_LSeries_of_gdTwistTerm (deviationPos_nonneg lam)
      (deviationPos_zero lam) hP hz'
    have hdN := differentiableAt_LSeries_of_gdTwistTerm (deviationNeg_nonneg lam)
      (deviationNeg_zero lam) hN hz'
    have hdΦ : DifferentiableAt ℂ (weilContinuation hW) z :=
      (differentiableOn_weilContinuation hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzh)
    exact (((hdP.sub hdN).add hdΦ).mul (xi_differentiable z)).differentiableWithinAt
  set z₀ : ℂ := ((max c 1 + 1 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = max c 1 + 1 := by rw [hz₀]; exact ofReal_re _
  have hz₀U : z₀ ∈ U := by
    show c < z₀.re
    rw [hz₀re]; linarith [le_max_left c 1]
  have hev : deriv xi =ᶠ[𝓝 z₀] fun z => (LSeries (fun n => (deviationPos lam n : ℂ)) z -
      LSeries (fun n => (deviationNeg lam n : ℂ)) z + weilContinuation hW z) * xi z := by
    have h1 : 1 < z₀.re := by rw [hz₀re]; linarith [le_max_right c 1]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz
    exact deriv_xi_eq_of_one_lt_re hW hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hz₀U hev hs

/-! ## Landau at a real abscissa where `ξ` does not vanish -/

/-- Let `a ≥ 0` be summable somewhere, and let `G` be holomorphic at every point `z` with
`Re z > c` and `ξ(z) ≠ 0`.  Suppose `G` agrees with the series `Σ a(n) n^{−z}` wherever the
series converges on a half-plane `Re z > c' ≥ c` and `ξ(z) ≠ 0`.  Then the series converges on
`Re z > c`: a real abscissa `σ_c > c` would be a real point where `ξ ≠ 0`, around which `G`
continues the series, contradicting Landau. -/
theorem summable_gdTwistTerm_of_xi_continuation {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {c : ℝ} {τ₀ : ℝ} (h₀ : Summable (gdTwistTerm a logFreq τ₀ 0))
    {G : ℂ → ℂ} (hG : ∀ z : ℂ, c < z.re → xi z ≠ 0 → DifferentiableAt ℂ G z)
    (hagree : ∀ c', c ≤ c' → (∀ τ, c' < τ → Summable (gdTwistTerm a logFreq τ 0)) →
      ∀ z : ℂ, c' < z.re → xi z ≠ 0 → G z = gdSeries a logFreq z)
    {σ : ℝ} (hσ : c < σ) : Summable (gdTwistTerm a logFreq σ 0) := by
  by_contra hns
  set S : Set ℝ := {τ | Summable (gdTwistTerm a logFreq τ 0)} with hSdef
  have hne : S.Nonempty := ⟨τ₀, h₀⟩
  have hlow : ∀ τ ∈ S, σ < τ := fun τ hτ => by
    by_contra hle
    exact hns (summable_gdTwistTerm_of_le ha logFreq_nonneg hτ (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨σ, fun τ hτ => (hlow τ hτ).le⟩
  set σc : ℝ := sInf S with hσcdef
  have hσc : σ ≤ σc := le_csInf hne fun τ hτ => (hlow τ hτ).le
  have hsum : ∀ τ, σc < τ → Summable (gdTwistTerm a logFreq τ 0) := by
    intro τ hτ
    obtain ⟨τ', hτ'S, hτ'lt⟩ := exists_lt_of_csInf_lt hne hτ
    exact summable_gdTwistTerm_of_le ha logFreq_nonneg hτ'S hτ'lt.le
  have hdiv : ∀ τ, τ < σc → ¬ Summable (gdTwistTerm a logFreq τ 0) :=
    fun τ hτ hS => absurd (csInf_le hbdd hS) (not_le.mpr hτ)
  obtain ⟨r₀, hr₀, hball⟩ : ∃ r₀ > 0, ball (σc : ℂ) r₀ ⊆ {z | xi z ≠ 0} :=
    Metric.isOpen_iff.mp (isOpen_ne_fun xi_differentiable.continuous continuous_const) _
      (xi_ne_zero_of_real σc)
  set r : ℝ := min r₀ (σc - c) with hrdef
  have hr : 0 < r := lt_min hr₀ (by linarith)
  have hmem : ∀ z ∈ ball (σc : ℂ) r, xi z ≠ 0 ∧ c < z.re := by
    intro z hz
    refine ⟨hball (ball_subset_ball (min_le_left _ _) hz), ?_⟩
    have hd : dist z (σc : ℂ) < σc - c := lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _)
    have hre : |z.re - σc| ≤ dist z (σc : ℂ) := by
      rw [Complex.dist_eq]
      simpa using Complex.abs_re_le_norm (z - σc)
    linarith [neg_abs_le (z.re - σc)]
  refine gdSeries_no_continuation_at_abscissa ha logFreq_nonneg hsum hdiv hr
    (fun z hz => (hG z (hmem z hz).2 (hmem z hz).1).differentiableWithinAt) fun z hz hzre => ?_
  exact hagree σc (by linarith) hsum z hzre (hmem z hz).1

/-- The negative part converges wherever the positive part does, right of `c ≥ 1/2`. -/
theorem summable_gdTwistTerm_deviationNeg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {c : ℝ} (hc : 1 / 2 ≤ c)
    (hP : ∀ τ, c < τ → Summable (gdTwistTerm (deviationPos lam) logFreq τ 0))
    {σ : ℝ} (hσ : c < σ) : Summable (gdTwistTerm (deviationNeg lam) logFreq σ 0) := by
  refine summable_gdTwistTerm_of_xi_continuation (deviationNeg_nonneg lam)
    (summable_gdTwistTerm_deviationNeg_of_one_lt hW (σ := 2) (by norm_num))
    (G := fun z => LSeries (fun n => (deviationPos lam n : ℂ)) z + weilContinuation hW z -
      deriv xi z / xi z) (fun z hz hxz => ?_) (fun c' hc' hsum z hz hxz => ?_) hσ
  · have hzh : 1 / 2 < z.re := lt_of_le_of_lt hc hz
    have hdP := differentiableAt_LSeries_of_gdTwistTerm (deviationPos_nonneg lam)
      (deviationPos_zero lam) hP hz
    have hdΦ : DifferentiableAt ℂ (weilContinuation hW) z :=
      (differentiableOn_weilContinuation hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzh)
    have hdd : DifferentiableAt ℂ (deriv xi) z :=
      ((xi_analyticOnNhd Set.univ).deriv z (mem_univ _)).differentiableAt
    exact (hdP.add hdΦ).sub (hdd.div (xi_differentiable z) hxz)
  · rw [gdSeries_logFreq _ (deviationNeg_zero lam)]
    have hid := deriv_xi_eq_of_lt_re hW (le_trans hc hc') hsum
      (fun τ hτ => hP τ (lt_of_le_of_lt hc' hτ)) hz
    rw [hid, mul_div_assoc, div_self hxz, mul_one]
    ring

/-- The positive part converges wherever the negative part does, right of `c ≥ 1/2`. -/
theorem summable_gdTwistTerm_deviationPos_of_neg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {c : ℝ} (hc : 1 / 2 ≤ c)
    (hN : ∀ τ, c < τ → Summable (gdTwistTerm (deviationNeg lam) logFreq τ 0))
    {σ : ℝ} (hσ : c < σ) : Summable (gdTwistTerm (deviationPos lam) logFreq σ 0) := by
  refine summable_gdTwistTerm_of_xi_continuation (deviationPos_nonneg lam)
    (summable_gdTwistTerm_deviationPos hW (σ := 2) (by norm_num))
    (G := fun z => LSeries (fun n => (deviationNeg lam n : ℂ)) z - weilContinuation hW z +
      deriv xi z / xi z) (fun z hz hxz => ?_) (fun c' hc' hsum z hz hxz => ?_) hσ
  · have hzh : 1 / 2 < z.re := lt_of_le_of_lt hc hz
    have hdN := differentiableAt_LSeries_of_gdTwistTerm (deviationNeg_nonneg lam)
      (deviationNeg_zero lam) hN hz
    have hdΦ : DifferentiableAt ℂ (weilContinuation hW) z :=
      (differentiableOn_weilContinuation hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzh)
    have hdd : DifferentiableAt ℂ (deriv xi) z :=
      ((xi_analyticOnNhd Set.univ).deriv z (mem_univ _)).differentiableAt
    exact (hdN.sub hdΦ).add (hdd.div (xi_differentiable z) hxz)
  · rw [gdSeries_logFreq _ (deviationPos_zero lam)]
    have hid := deriv_xi_eq_of_lt_re hW (le_trans hc hc')
      (fun τ hτ => hN τ (lt_of_le_of_lt hc' hτ)) hsum hz
    rw [hid, mul_div_assoc, div_self hxz, mul_one]
    ring

/-! ## The theorem -/

/-- **A Weil-positive system whose excess over `Λ` is summable on `Re s > 1/2` forces RH.** -/
theorem riemannHypothesis_of_weilPositiveFull_of_summable_deviationPos {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hP : ∀ σ : ℝ, 1 / 2 < σ → Summable fun n : ℕ => deviationPos lam n / (n : ℝ) ^ σ) :
    RiemannHypothesis := by
  have hP' : ∀ τ, 1 / 2 < τ → Summable (gdTwistTerm (deviationPos lam) logFreq τ 0) :=
    fun τ hτ => (hP τ hτ).congr fun n => (gdTwistTerm_logFreq _ (deviationPos_zero lam) τ n).symm
  have hN : ∀ τ, 1 / 2 < τ → Summable (gdTwistTerm (deviationNeg lam) logFreq τ 0) :=
    fun τ hτ => summable_gdTwistTerm_deviationNeg hW le_rfl hP' hτ
  refine rh_iff_xi_ne_zero_right.mpr fun ρ hρ hzero => ?_
  have hρ' : 1 / 2 < ρ.re := hρ
  set H : ℂ → ℂ := fun z => LSeries (fun n => (deviationPos lam n : ℂ)) z -
    LSeries (fun n => (deviationNeg lam n : ℂ)) z with hHdef
  have hHc : ContinuousAt H ρ :=
    ((differentiableAt_LSeries_of_gdTwistTerm (deviationPos_nonneg lam) (deviationPos_zero lam)
      hP' hρ').sub (differentiableAt_LSeries_of_gdTwistTerm (deviationNeg_nonneg lam)
      (deviationNeg_zero lam) hN hρ')).continuousAt
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
    rw [logDeriv_apply, deriv_xi_eq_of_lt_re hW le_rfl hN hP' hzre, mul_div_assoc, div_self hz,
      mul_one]
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

/-! ## Balanced abscissae of the excess and the deficit -/

theorem gdTwistTerm_deviationPos_eq (lam : ℕ → ℝ) (σ : ℝ) :
    gdTwistTerm (deviationPos lam) logFreq σ 0 = fun n : ℕ => deviationPos lam n / (n : ℝ) ^ σ :=
  funext (gdTwistTerm_logFreq _ (deviationPos_zero lam) σ)

theorem gdTwistTerm_deviationNeg_eq (lam : ℕ → ℝ) (σ : ℝ) :
    gdTwistTerm (deviationNeg lam) logFreq σ 0 = fun n : ℕ => deviationNeg lam n / (n : ℝ) ^ σ :=
  funext (gdTwistTerm_logFreq _ (deviationNeg_zero lam) σ)

/-- **Balanced abscissae.**  Right of any `c ≥ 1/2`, the excess `P` and the deficit `N` of a
Weil-positive system over `Λ` converge together: `L(P) − L(N) = ξ'/ξ − Φ_lam` is regular at every
real point right of `1/2`, so Landau forbids either part to have the larger real abscissa. -/
theorem summable_deviationPos_iff_summable_deviationNeg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {c : ℝ} (hc : 1 / 2 ≤ c) :
    (∀ σ, c < σ → Summable fun n : ℕ => deviationPos lam n / (n : ℝ) ^ σ) ↔
      ∀ σ, c < σ → Summable fun n : ℕ => deviationNeg lam n / (n : ℝ) ^ σ := by
  simp only [← gdTwistTerm_deviationPos_eq, ← gdTwistTerm_deviationNeg_eq]
  exact ⟨fun hP σ hσ => summable_gdTwistTerm_deviationNeg hW hc hP hσ,
    fun hN σ hσ => summable_gdTwistTerm_deviationPos_of_neg hW hc hN hσ⟩

/-- **A second Weil-positive system overshoots and undershoots `Λ` at full abscissa.**  If
`lam ≠ Λ` at some `n ≥ 2`, then for every `s < 1` neither the excess series `Σ P(n) n^{−s}` nor the
deficit series `Σ N(n) n^{−s}` converges.  Balanced abscissae reduce either convergence to
convergence of `Σ |lam − Λ| n^{−t}` at some `t < 1`, which forces `lam = Λ` (absolute abscissa
rigidity, `WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable`). -/
theorem not_summable_deviation_of_ne {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hne : ∃ n, 2 ≤ n ∧ lam n ≠ ArithmeticFunction.vonMangoldt n) {s : ℝ} (hs : s < 1) :
    (¬ Summable fun n : ℕ => deviationPos lam n / (n : ℝ) ^ s) ∧
      ¬ Summable fun n : ℕ => deviationNeg lam n / (n : ℝ) ^ s := by
  set c : ℝ := max s (1 / 2) with hcdef
  have hc : 1 / 2 ≤ c := le_max_right _ _
  have hc1 : c < 1 := max_lt hs (by norm_num)
  have key : (∀ σ, c < σ → Summable fun n : ℕ => deviationPos lam n / (n : ℝ) ^ σ) → False := by
    intro hP
    have hN := (summable_deviationPos_iff_summable_deviationNeg hW hc).mp hP
    set t : ℝ := (c + 1) / 2 with htdef
    have hct : c < t := by rw [htdef]; linarith
    have ht1 : t < 1 := by rw [htdef]; linarith
    have hsum : Summable fun n : ℕ =>
        |lam (n + 2) - ArithmeticFunction.vonMangoldt (n + 2)| * ((n + 2 : ℕ) : ℝ) ^ (-t) := by
      refine ((((hP t hct).add (hN t hct))).comp_injective (add_left_injective 2)).congr
        fun n => ?_
      have h2 : 2 ≤ n + 2 := by omega
      have hpos : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by positivity
      have habs := max_zero_add_max_neg_zero_eq_abs_self
        (lam (n + 2) - (ArithmeticFunction.vonMangoldt (n + 2) : ℝ))
      rw [neg_sub] at habs
      simp only [Function.comp_apply, deviationPos, deviationNeg, if_pos h2]
      rw [← add_div, habs, Real.rpow_neg hpos, div_eq_mul_inv]
    have heq := WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable hW ht1
      ((summable_nat_add_iff 2).mp hsum)
    obtain ⟨n, hn, hneq⟩ := hne
    exact hneq (heq n hn)
  have hmonoP : (Summable fun n : ℕ => deviationPos lam n / (n : ℝ) ^ s) →
      ∀ σ, c < σ → Summable fun n : ℕ => deviationPos lam n / (n : ℝ) ^ σ := by
    intro h σ hσ
    rw [← gdTwistTerm_deviationPos_eq] at h ⊢
    exact summable_gdTwistTerm_of_le (deviationPos_nonneg lam) logFreq_nonneg h
      (le_trans (le_max_left _ _) hσ.le)
  have hmonoN : (Summable fun n : ℕ => deviationNeg lam n / (n : ℝ) ^ s) →
      ∀ σ, c < σ → Summable fun n : ℕ => deviationNeg lam n / (n : ℝ) ^ σ := by
    intro h σ hσ
    rw [← gdTwistTerm_deviationNeg_eq] at h ⊢
    exact summable_gdTwistTerm_of_le (deviationNeg_nonneg lam) logFreq_nonneg h
      (le_trans (le_max_left _ _) hσ.le)
  exact ⟨fun h => key (hmonoP h),
    fun h => key ((summable_deviationPos_iff_summable_deviationNeg hW hc).mpr (hmonoN h))⟩

/-- **Either part summable below abscissa one forces `Λ`.** -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_deviation {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℝ} (hs : s < 1)
    (h : (Summable fun n : ℕ => deviationPos lam n / (n : ℝ) ^ s) ∨
      Summable fun n : ℕ => deviationNeg lam n / (n : ℝ) ^ s) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  by_contra hne
  push Not at hne
  obtain ⟨hP, hN⟩ := not_summable_deviation_of_ne hW hne hs
  rcases h with h | h
  · exact hP h
  · exact hN h

end RHTower.WeilSpectral
