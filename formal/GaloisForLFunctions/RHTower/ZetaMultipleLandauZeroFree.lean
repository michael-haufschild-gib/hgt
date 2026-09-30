import GaloisForLFunctions.RHTower.IntegerBeurlingPerturbation
import GaloisForLFunctions.RHTower.LandauSummabilityTransfer
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# Zeta multiples with nonnegative coefficients: partial sums bound the zero abscissa

Let `a` be a real sequence with `|a n| ≤ 1` and `g ≥ 0` a sequence with
`L(a)(s) ζ(s) = L(g)(s)` on `Re s > 1`, where `L(g)` does not vanish wherever it converges
absolutely.  Suppose

* `Σ_{n ≤ x} a n = O(x^θ)` with `0 ≤ θ < 1`, and
* `g` is sparse at `s = 1`: `(σ - 1) L(g)(σ) → 0` as `σ ↓ 1`.

Then `L(g)` converges absolutely at every real `σ > θ` (`summable_of_isBigO`) and `ζ(s) ≠ 0`
for `Re s > θ` (`riemannZeta_ne_zero_of_isBigO`).  With Hardy's theorem, `θ ≥ 1/2`
(`half_le_of_isBigO`).

**Mechanism.**  Partial summation continues `F = L(a)` to `Re s > θ`.  Sparsity gives
`F(1) = F(σ)ζ(σ)/ζ(σ) → 0`, so `G = (F/(s-1))·(s-1)ζ` is holomorphic on `Re s > θ` and equals
the nonnegative series `L(g)` right of `1`.  Landau's theorem moves the abscissa of `L(g)` down
to `θ`; there `L(g) = G = Fζ` is nonzero, so `ζ` has no zeros.
-/

open Filter Topology Complex Asymptotics Set Metric LSeries

noncomputable section

namespace RHTower

namespace ZetaMultiple

variable (a : ℕ → ℝ)

/-- The continuation of `L(a)` by partial summation: `s ∫_1^∞ (Σ_{n ≤ t} a n) t^{-s-1} dt`. -/
def continuation (z : ℂ) : ℂ := z * IntegerBeurling.countDefectIntegral a 0 z

/-- `L(a)` with its zero at `s = 1` divided out, times the residue factor `(s-1)ζ(s)`. -/
def regularized (z : ℂ) : ℂ := dslope (continuation a) 1 z * zetaResidueFactor z

variable {a}

section Continuation

variable (ha : ∀ n, |a n| ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ)
  (hM : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) =O[atTop] fun x => x ^ θ)
include hθ hM

theorem differentiableAt_continuation {z : ℂ} (hz : θ < z.re) :
    DifferentiableAt ℂ (continuation a) z := by
  have hN : (fun x : ℝ => IntegerBeurling.count a x - 0 * x) =O[atTop] fun x => x ^ θ := by
    simpa [IntegerBeurling.count] using hM
  exact differentiableAt_id.mul (IntegerBeurling.differentiableAt_countDefectIntegral hθ hN hz)

include ha in
theorem LSeries_eq_continuation {z : ℂ} (hz : 1 < z.re) (hθz : θ < z.re) :
    LSeries (IntegerBeurling.countSeq a) z = continuation a z := by
  have hN : (fun x : ℝ => IntegerBeurling.count a x - 0 * x) =O[atTop] fun x => x ^ θ := by
    simpa [IntegerBeurling.count] using hM
  have h := IntegerBeurling.LSeries_countSeq_sub ha hθ hN hz hθz
  rw [Complex.ofReal_zero, zero_mul, sub_zero] at h
  rw [h, continuation]

theorem differentiableOn_regularized (hθ1 : θ < 1) :
    DifferentiableOn ℂ (regularized a) {z : ℂ | θ < z.re} := by
  have hU : IsOpen {z : ℂ | θ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (continuation a) {z : ℂ | θ < z.re} := fun z hz =>
    (differentiableAt_continuation hθ hM hz).differentiableWithinAt
  have h1 : (1 : ℂ) ∈ {z : ℂ | θ < z.re} := by simpa using hθ1
  exact ((Complex.differentiableOn_dslope (hU.mem_nhds h1)).mpr hF).mul
    differentiable_zetaResidueFactor.differentiableOn

end Continuation

theorem regularized_eq (hF1 : continuation a 1 = 0) {z : ℂ} (hz : z ≠ 1) :
    regularized a z = continuation a z * riemannZeta z := by
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  rw [regularized, dslope_of_ne _ hz, slope_def_field, zetaResidueFactor_of_ne hz, hF1, sub_zero]
  field_simp

section Landau

variable {g : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1) (hg0 : ∀ n, 0 ≤ g n)
  (hg2 : LSeriesSummable (fun n => (g n : ℂ)) 2)
  (hmul : ∀ s : ℂ, 1 < s.re →
    LSeries (IntegerBeurling.countSeq a) s * riemannZeta s = LSeries (fun n => (g n : ℂ)) s)
  {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
  (hM : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) =O[atTop] fun x => x ^ θ)
  (hD : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries (fun n => (g n : ℂ)) σ) (𝓝[>] 1) (𝓝 0))
include ha hmul hθ hθ1 hM hD

/-- **Sparsity at `s = 1` forces `L(a)(1) = 0`.** -/
theorem continuation_one : continuation a 1 = 0 := by
  have hof : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun σ : ℝ => continuation a σ) (𝓝[>] 1) (𝓝 (continuation a 1)) :=
    ((differentiableAt_continuation hθ hM (by simpa using hθ1)).continuousAt.tendsto).comp hof
  have hof' : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[{1}ᶜ] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hof, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [mem_compl_iff, mem_singleton_iff]
    exact fun h => (ne_of_gt (show (1 : ℝ) < σ from hσ)) (by exact_mod_cast h)
  have hres : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta σ) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hof'
  have h2 : Tendsto (fun σ : ℝ => continuation a σ) (𝓝[>] 1) (𝓝 0) := by
    have hq := hD.div hres one_ne_zero
    rw [zero_div] at hq
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1 : ℝ) < σ := hσ
    have hre : 1 < ((σ : ℂ)).re := by simpa using hσ1
    have hne : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hσ1.ne')
    have hζ : riemannZeta σ ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre.le
    rw [Pi.div_apply, ← hmul σ hre,
      LSeries_eq_continuation ha hθ hM hre (by simpa using hθ1.trans hσ1)]
    field_simp
  exact tendsto_nhds_unique h1 h2

theorem regularized_eq_LSeries {z : ℂ} (hz : 1 < z.re) :
    regularized a z = LSeries (fun n => (g n : ℂ)) z := by
  have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hz; exact lt_irrefl _ hz
  rw [regularized_eq (continuation_one ha hmul hθ hθ1 hM hD) hz1,
    ← LSeries_eq_continuation ha hθ hM hz (hθ1.trans hz), hmul z hz]

include hg0 hg2 in
/-- **Landau's theorem moves the abscissa of `L(g)` down to `θ`.** -/
theorem summable_of_isBigO {σ : ℝ} (hσ : θ < σ) :
    LSeriesSummable (fun n => (g n : ℂ)) σ := by
  rcases le_or_gt 2 σ with h2 | h2
  · exact hg2.of_re_le_re (by simpa using h2)
  have hR0 : (0 : ℝ) ≤ 3 - (θ + σ) / 2 := by linarith
  set R : NNReal := ⟨3 - (θ + σ) / 2, hR0⟩ with hRdef
  have hRval : (R : ℝ) = 3 - (θ + σ) / 2 := rfl
  have hball : closedBall (((2 : ℝ) + 1 : ℝ) : ℂ) (R : ℝ) ⊆ {z : ℂ | θ < z.re} := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - (((2 : ℝ) + 1 : ℝ) : ℂ))
    rw [hRval] at hz
    have h4 := neg_abs_le (z - (((2 : ℝ) + 1 : ℝ) : ℂ)).re
    have h5 : (z - (((2 : ℝ) + 1 : ℝ) : ℂ)).re = z.re - 3 := by
      rw [Complex.sub_re, Complex.ofReal_re]; norm_num
    show θ < z.re
    have h6 := h1.trans hz
    rw [h5] at h4 h6
    have h7 : -(3 - (θ + σ) / 2) ≤ z.re - 3 := le_trans (neg_le_neg h6) h4
    linarith
  have hGd : DifferentiableOn ℂ (regularized a) (closedBall (((2 : ℝ) + 1 : ℝ) : ℂ) (R : ℝ)) :=
    (differentiableOn_regularized hθ hM hθ1).mono hball
  have hagree : ∀ s : ℂ, (2 : ℝ) < s.re → regularized a s = LSeries (fun n => (g n : ℂ)) s :=
    fun s hs => regularized_eq_LSeries ha hmul hθ hθ1 hM hD (by linarith)
  have hsum2 : LSeriesSummable (fun n => (g n : ℂ)) ((2 : ℝ) : ℂ) := by simpa using hg2
  exact landau_local_summability_transfer hg0 one_pos hsum2 hGd hagree (by rw [hRval]; linarith)

include hg0 hg2 in
theorem LSeries_eq_regularized {z : ℂ} (hz : θ < z.re) :
    LSeries (fun n => (g n : ℂ)) z = regularized a z := by
  set U : Set ℂ := {z : ℂ | θ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hH : AnalyticOnNhd ℂ (LSeries (fun n => (g n : ℂ))) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hw' : θ < w.re := hw
    have hσ : θ < (θ + w.re) / 2 := by linarith
    have habs : abscissaOfAbsConv (fun n => (g n : ℂ)) < (w.re : EReal) := by
      refine lt_of_le_of_lt
        (summable_of_isBigO ha hg0 hg2 hmul hθ hθ1 hM hD hσ).abscissaOfAbsConv_le ?_
      simp only [Complex.ofReal_re]
      exact_mod_cast (by linarith : (θ + w.re) / 2 < w.re)
    exact (LSeries_hasDerivAt habs).differentiableAt.differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (regularized a) U :=
    (differentiableOn_regularized hθ hM hθ1).analyticOnNhd hUo
  have h2U : (2 : ℂ) ∈ U := by show θ < (2 : ℂ).re; norm_num; linarith
  have hEq : EqOn (LSeries (fun n => (g n : ℂ))) (regularized a) U := by
    refine hH.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt θ).isPreconnected
      h2U ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    exact (regularized_eq_LSeries ha hmul hθ hθ1 hM hD hw).symm
  exact hEq hz

include hg0 hg2 in
/-- **Main theorem.**  `ζ(s) ≠ 0` for `Re s > θ`. -/
theorem riemannZeta_ne_zero_of_isBigO
    (hne : ∀ s : ℂ, LSeriesSummable (fun n => (g n : ℂ)) s → LSeries (fun n => (g n : ℂ)) s ≠ 0)
    {z : ℂ} (hz : θ < z.re) : riemannZeta z ≠ 0 := by
  intro h0
  rcases le_or_gt 1 z.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 h0
  have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  have hsum : LSeriesSummable (fun n => (g n : ℂ)) z :=
    (LSeriesSummable_iff_of_re_eq_re (by simp)).mp
      (summable_of_isBigO ha hg0 hg2 hmul hθ hθ1 hM hD hz)
  have hH := hne z hsum
  rw [LSeries_eq_regularized ha hg0 hg2 hmul hθ hθ1 hM hD hz,
    regularized_eq (continuation_one ha hmul hθ hθ1 hM hD) hz1, h0, mul_zero] at hH
  exact hH rfl

end Landau

/-- Hardy's theorem supplies a zero of `ζ` on the critical line. -/
theorem exists_riemannZeta_zero_re_half : ∃ s : ℂ, s.re = 1 / 2 ∧ riemannZeta s = 0 := by
  obtain ⟨t, -, ht⟩ := exists_Xi_zero_gt 0
  refine ⟨1 / 2 + (t : ℂ) * Complex.I, by simp, ?_⟩
  have hc := completedRiemannZeta_critical_eq_Xi t
  rw [ht] at hc
  have hne : (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [riemannZeta_def_of_ne_zero hne, hc]
  simp

/-- **Cancellation stops at the half power.**  Under the hypotheses of the main theorem,
`Σ_{n ≤ x} a n = O(x^θ)` forces `θ ≥ 1/2`. -/
theorem half_le_of_isBigO {g : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1) (hg0 : ∀ n, 0 ≤ g n)
    (hg2 : LSeriesSummable (fun n => (g n : ℂ)) 2)
    (hmul : ∀ s : ℂ, 1 < s.re →
      LSeries (IntegerBeurling.countSeq a) s * riemannZeta s = LSeries (fun n => (g n : ℂ)) s)
    (hne : ∀ s : ℂ, LSeriesSummable (fun n => (g n : ℂ)) s → LSeries (fun n => (g n : ℂ)) s ≠ 0)
    (hD : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries (fun n => (g n : ℂ)) σ) (𝓝[>] 1) (𝓝 0))
    {θ : ℝ} (hM : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) =O[atTop] fun x => x ^ θ) :
    1 / 2 ≤ θ := by
  by_contra hlt
  push Not at hlt
  set θ' : ℝ := max θ 0 with hθ'
  have hM' : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) =O[atTop] fun x => x ^ θ' := by
    refine hM.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  obtain ⟨s, hs, hs0⟩ := exists_riemannZeta_zero_re_half
  have hθ'half : θ' < 1 / 2 := max_lt hlt (by norm_num)
  exact riemannZeta_ne_zero_of_isBigO ha hg0 hg2 hmul (le_max_right _ _) (by linarith) hM' hD hne
    (by rw [hs]; exact hθ'half) hs0

/-- **A nonnegative series with `Σ g(n)/n < ∞` is sparse at `s = 1`.** -/
theorem tendsto_sub_one_mul_LSeries_of_summable {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hS : Summable fun n : ℕ => g n / n) :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries (fun n => (g n : ℂ)) σ) (𝓝[>] 1) (𝓝 0) := by
  set C : ℝ := ∑' n, g n / n with hC
  have hlim : Tendsto (fun σ : ℝ => (σ - 1) * C) (𝓝[>] 1) (𝓝 0) := by
    have := ((continuous_id.sub continuous_const).mul continuous_const).tendsto (1 : ℝ)
      (f := fun σ : ℝ => (σ - 1) * C)
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : (1 : ℝ) < σ := hσ
  have hterm : ∀ n, ‖term (fun n => (g n : ℂ)) σ n‖ ≤ g n / n := by
    intro n
    rw [norm_term_eq]
    split_ifs with hn
    · rw [hn]; simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [Complex.norm_real, Real.norm_of_nonneg (hg0 n), Complex.ofReal_re]
      refine div_le_div_of_nonneg_left (hg0 n) (by linarith) ?_
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 hσ1.le
  have hsumm : Summable fun n => ‖term (fun n => (g n : ℂ)) σ n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hS
  rw [norm_mul]
  have h1 : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_le_tsum hterm hS)

end ZetaMultiple

end RHTower
