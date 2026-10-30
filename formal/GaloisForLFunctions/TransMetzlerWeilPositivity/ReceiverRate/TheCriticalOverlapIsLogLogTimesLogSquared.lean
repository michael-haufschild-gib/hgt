import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.ABoundedOverlapRateSeesASemilocalWindow
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The critical overlap of a logarithmic Denjoy–Carleman profile

A profile with `∫ |φ^{(q)}| ≤ A B^q q! (log(q + 3))^{2q}` has `|φ̂(ξ)| ≤ A μ_B(2π|ξ|)`, where
`μ_B(c) = inf_q B^q q! (log(q + 3))^{2q} / c^q` is the derivative majorant of its Fourier tail
(`dcMajorant`, `norm_fourier_le_dcMajorant`). The **critical overlap** `c*_N` is the least `c ≥ 1`
with `μ_B(c)² log N ≤ 1` (`dcCriticalOverlap`): the tail energy, which is both the margin of the
complete Weil form and its synthesis error, equals the Weil weight `1/log N` there.

* `log (1/μ_B(c)) ≍ c / (log c)²` (`dcMajorant_le_exp`, `exp_le_dcMajorant`), hence
  `c*_N ≍ L (log L)²`, `L = log log N` (`eventually_dcCriticalOverlap_le`,
  `eventually_le_dcCriticalOverlap`).
* **Rate law.** Every overlap `r_N c*_N` with `r_N → ∞` is an RH receiver
  (`riemannHypothesis_iff_nonneg_of_critical_rate`). RH holds iff every bounded multiple `K c*_N`
  is eventually nonnegative (`riemannHypothesis_iff_forall_critical_multiple`). A single bounded
  multiple `K` gives Weil positivity on every `C²` test supported in `[−R, R]` with
  `24 e B ⌈1 + e^{2(R+1)}⌉ < K/(32 e)` (`nonneg_of_critical_multiple`): its window radius is
  `½ log K + O(1)`.
-/

noncomputable section

open Filter Topology RHTower
open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The derivative majorant of the Fourier tail of the logarithmic Denjoy–Carleman class with
base `B`: `μ_B(c) = inf_q B^q q! (log(q + 3))^{2q} / c^q`. -/
def dcMajorant (B c : ℝ) : ℝ := ⨅ q : ℕ, B ^ q * dcLogWeight q / c ^ q

/-- The critical overlap at horizon `N`: the least `c ≥ 1` with `μ_B(c)² log N ≤ 1`. -/
def dcCriticalOverlap (B : ℝ) (N : ℕ) : ℝ :=
  sInf {c : ℝ | 1 ≤ c ∧ dcMajorant B c ^ 2 * Real.log N ≤ 1}

/-! ### The majorant -/

private theorem dcMajorant_bddBelow {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    BddBelow (Set.range fun q : ℕ => B ^ q * dcLogWeight q / c ^ q) :=
  ⟨0, by rintro _ ⟨q, rfl⟩; have := dcLogWeight_pos q; positivity⟩

theorem dcMajorant_le_term {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (q : ℕ) :
    dcMajorant B c ≤ B ^ q * dcLogWeight q / c ^ q :=
  ciInf_le (dcMajorant_bddBelow hB hc) q

private theorem one_le_log_add_three' {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Real.log (x + 3) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- **Upper bound.** `μ_B(c) ≤ e^{1 − c/(e B log²(c + 3))}`: take `q = ⌊c/(e B log²(c + 3))⌋`
and `q! ≤ q^q`, so each factor of the `q`-th term is at most `e^{−1}`. -/
theorem dcMajorant_le_exp {B c : ℝ} (hB : 1 ≤ B) (hc : 1 ≤ c) :
    dcMajorant B c ≤ Real.exp (1 - c / (Real.exp 1 * B * Real.log (c + 3) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hl := one_le_log_add_three' hc0.le
  have he := Real.add_one_le_exp 1
  set D := Real.exp 1 * B * Real.log (c + 3) ^ 2 with hD
  have hl2 : 1 ≤ Real.log (c + 3) ^ 2 := one_le_pow₀ hl
  have hD1 : 1 ≤ D := by
    have h1 : 1 ≤ Real.exp 1 * B := by nlinarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp 1 * B * Real.log (c + 3) ^ 2 := mul_le_mul h1 hl2 zero_le_one (by linarith)
  set x := c / D with hx
  have hx0 : 0 ≤ x := by positivity
  have hxc : x ≤ c := div_le_self hc0.le hD1
  set q := ⌊x⌋₊
  have hqx : (q : ℝ) ≤ x := Nat.floor_le hx0
  have hxq : x < q + 1 := Nat.lt_floor_add_one x
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine (dcMajorant_le_term (by linarith) hc0 q).trans ?_
  have hlogq : Real.log ((q : ℝ) + 3) ≤ Real.log (c + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlq0 : 0 ≤ Real.log ((q : ℝ) + 3) := (one_le_log_add_three' hq0).trans' zero_le_one
  have hfac : ((q.factorial : ℕ) : ℝ) ≤ (q : ℝ) ^ q := by exact_mod_cast Nat.factorial_le_pow q
  have hbase : B * q * Real.log (c + 3) ^ 2 / c ≤ Real.exp (-1) := by
    have hDx : D * x = c := by rw [hx]; field_simp
    have h1 : D * q ≤ c := by
      have := mul_le_mul_of_nonneg_left hqx (by linarith : (0 : ℝ) ≤ D)
      linarith
    rw [div_le_iff₀ hc0, Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos 1)]
    have : B * q * Real.log (c + 3) ^ 2 * Real.exp 1 = D * q := by rw [hD]; ring
    linarith
  calc B ^ q * dcLogWeight q / c ^ q
      ≤ B ^ q * ((q : ℝ) ^ q * Real.log (c + 3) ^ (2 * q)) / c ^ q := by
        unfold dcLogWeight
        gcongr
    _ = (B * q * Real.log (c + 3) ^ 2 / c) ^ q := by ring
    _ ≤ Real.exp (-1) ^ q := pow_le_pow_left₀ (by positivity) hbase q
    _ = Real.exp (-(q : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (1 - x) := Real.exp_le_exp.mpr (by linarith)

/-- **Lower bound.** For `B ≥ 1`, `c ≥ e`, every term of the majorant is at least
`exp(−(4 e c/log² c + √c log(e c)))`: with `y = B q log²(q+3)/(e c)` and `q! ≥ q^q e^{−q}` the
term is at least `y^q`; `q log y ≥ −e c/(B log²(q+3))` (from `t log t ≥ −1`) when `q + 3 ≥ √c`,
and `q log y ≥ −q log(e c)` otherwise. -/
theorem exp_le_dcMajorant {B c : ℝ} (hB : 1 ≤ B) (hc : Real.exp 1 ≤ c) :
    Real.exp (-(4 * Real.exp 1 * c / Real.log c ^ 2 + Real.sqrt c * Real.log (Real.exp 1 * c)))
      ≤ dcMajorant B c := by
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hc1 : 1 ≤ c := he1.trans hc
  have hc0 : 0 < c := by linarith
  have hlc : 1 ≤ Real.log c := by rwa [Real.le_log_iff_exp_le hc0]
  have hlec : 0 ≤ Real.log (Real.exp 1 * c) := Real.log_nonneg (by nlinarith)
  have hs0 : 0 ≤ Real.sqrt c * Real.log (Real.exp 1 * c) := by positivity
  have hf0 : 0 ≤ 4 * Real.exp 1 * c / Real.log c ^ 2 := by positivity
  refine le_ciInf fun q => ?_
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero, dcLogWeight_zero, mul_one, div_one]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlq := one_le_log_add_three' hq0.le
  set l := Real.log ((q : ℝ) + 3) with hl
  set ε := Real.exp (-1) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hεe : ε * Real.exp 1 = 1 := by rw [hε, ← Real.exp_add]; norm_num
  set y := ε * B * q * l ^ 2 / c with hy
  have hy0 : 0 < y := by positivity
  -- `q! ≥ q^q e^{−q}` gives `term ≥ y^q`
  have hfac : (q : ℝ) ^ q * ε ^ q ≤ (q.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (q : ℝ) hq0.le q
    have hf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
    rw [div_le_iff₀ hf] at h
    have hεq : ε ^ q * Real.exp q = 1 := by
      rw [hε, ← Real.exp_nat_mul, ← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_left h (pow_nonneg hε0.le q)
    nlinarith
  have hterm : y ^ q ≤ B ^ q * dcLogWeight q / c ^ q := by
    have hyq : y ^ q = B ^ q * ((q : ℝ) ^ q * ε ^ q * l ^ (2 * q)) / c ^ q := by
      rw [hy]; ring
    rw [hyq]
    unfold dcLogWeight
    gcongr
  refine le_trans ?_ hterm
  rcases le_or_gt 1 y with hy1 | hy1
  · exact (Real.exp_le_one_iff.mpr (by linarith)).trans (one_le_pow₀ hy1)
  rw [← Real.exp_log (pow_pos hy0 q), Real.log_pow, Real.exp_le_exp]
  have hylog : -1 ≤ y * Real.log y := by
    have h1 := Real.one_sub_inv_le_log_of_pos hy0
    have h2 : y * (1 - y⁻¹) ≤ y * Real.log y := mul_le_mul_of_nonneg_left h1 hy0.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hy0.ne'] at h2
    linarith
  rcases le_or_gt (Real.sqrt c) ((q : ℝ) + 3) with hqs | hqs
  · have hlog2 : Real.log c ≤ 2 * l := by
      have := Real.log_le_log (Real.sqrt_pos.mpr hc0) hqs
      rw [Real.log_sqrt hc0.le] at this
      linarith
    -- `q log y = (y log y)/a ≥ −1/a`, `a = ε B l²/c`, and `1/a ≤ 4 e c / log² c`
    set a := ε * B * l ^ 2 / c with ha
    have ha0 : 0 < a := by positivity
    have hya : y = a * q := by rw [hy, ha]; ring
    have h1 : -1 / a ≤ (q : ℝ) * Real.log y := by
      have : (q : ℝ) * Real.log y = (y * Real.log y) / a := by
        rw [hya]; field_simp
      rw [this]
      exact div_le_div_of_nonneg_right hylog ha0.le
    have hL0 : 0 < Real.log c ^ 2 := by positivity
    have h2 : 1 / a ≤ 4 * Real.exp 1 * c / Real.log c ^ 2 := by
      rw [ha, one_div_div, div_le_div_iff₀ (by positivity) hL0]
      have hsq : Real.log c ^ 2 ≤ 4 * l ^ 2 := by nlinarith
      -- `c log² c ≤ 4 e c ε B l²` since `ε e = 1`, `B ≥ 1`
      have hB' : 4 * l ^ 2 ≤ 4 * Real.exp 1 * (ε * B * l ^ 2) := by
        have : 4 * Real.exp 1 * (ε * B * l ^ 2) = 4 * B * l ^ 2 := by
          rw [show 4 * Real.exp 1 * (ε * B * l ^ 2) = 4 * (ε * Real.exp 1) * B * l ^ 2 by ring,
            hεe]; ring
        rw [this]; nlinarith [sq_nonneg l]
      nlinarith [mul_le_mul_of_nonneg_left (hsq.trans hB') hc0.le]
    have : -(4 * Real.exp 1 * c / Real.log c ^ 2) ≤ -1 / a := by
      rw [neg_div]; exact neg_le_neg h2
    linarith
  · -- `q < √c` and `y ≥ 1/(e c)`
    have hyl : ε / c ≤ y := by
      rw [hy]
      apply div_le_div_of_nonneg_right _ hc0.le
      have : (1 : ℝ) ≤ l ^ 2 := one_le_pow₀ hlq
      have h1 : 1 ≤ B * q := by nlinarith
      have h2 : 1 ≤ B * q * l ^ 2 := by nlinarith
      nlinarith
    have hly : -Real.log (Real.exp 1 * c) ≤ Real.log y := by
      have := Real.log_le_log (by positivity) hyl
      have e : Real.log (ε / c) = -Real.log (Real.exp 1 * c) := by
        rw [hε, Real.log_div (Real.exp_pos _).ne' hc0.ne', Real.log_exp,
          Real.log_mul he0.ne' hc0.ne', Real.log_exp]; ring
      linarith
    have hqc : (q : ℝ) ≤ Real.sqrt c := by linarith
    have h1 : -(Real.sqrt c * Real.log (Real.exp 1 * c)) ≤ (q : ℝ) * Real.log y := by
      have h3 := mul_le_mul_of_nonneg_left hly hq0.le
      have h4 := mul_le_mul_of_nonneg_right hqc hlec
      linarith
    linarith

/-- Eventually in `c`, `√c log(e c) ≤ 4 e c / log² c`, so `μ_B(c) ≥ exp(−8 e c / log² c)`. -/
theorem eventually_exp_le_dcMajorant {B : ℝ} (hB : 1 ≤ B) :
    ∀ᶠ c : ℝ in atTop, Real.exp (-(8 * Real.exp 1 * c / Real.log c ^ 2)) ≤ dcMajorant B c := by
  have ho := (isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [ho, eventually_ge_atTop (Real.exp 1)] with c hoc hc
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hc0 : 0 < c := by linarith
  have hlc : 1 ≤ Real.log c := by rwa [Real.le_log_iff_exp_le hc0]
  refine le_trans (Real.exp_le_exp.mpr ?_) (exp_le_dcMajorant hB hc)
  rw [neg_le_neg_iff]
  have hl3 : Real.log c ^ 3 ≤ Real.sqrt c := by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
      ← Real.sqrt_eq_rpow, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hoc
    exact hoc
  have hlec : Real.log (Real.exp 1 * c) = 1 + Real.log c := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hc0.ne', Real.log_exp]
  have hsc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hs0 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hL0 : 0 < Real.log c ^ 2 := by positivity
  have key : Real.sqrt c * Real.log (Real.exp 1 * c) ≤ 4 * Real.exp 1 * c / Real.log c ^ 2 := by
    rw [le_div_iff₀ hL0, hlec]
    have h1 : Real.sqrt c * (1 + Real.log c) * Real.log c ^ 2 ≤
        2 * (Real.sqrt c * Real.log c ^ 3) := by
      have : (1 + Real.log c) * Real.log c ^ 2 ≤ 2 * Real.log c ^ 3 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hs0]
    have h2 : Real.sqrt c * Real.log c ^ 3 ≤ c :=
      (mul_le_mul_of_nonneg_left hl3 hs0).trans hsc.le
    nlinarith
  have e8 : 8 * Real.exp 1 * c / Real.log c ^ 2 =
      4 * Real.exp 1 * c / Real.log c ^ 2 + 4 * Real.exp 1 * c / Real.log c ^ 2 := by ring
  linarith

theorem dcMajorant_antitone {B c c' : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hcc : c ≤ c') :
    dcMajorant B c' ≤ dcMajorant B c :=
  le_ciInf fun q => (dcMajorant_le_term hB (hc.trans_le hcc) q).trans
    (div_le_div_of_nonneg_left (by have := dcLogWeight_pos q; positivity) (pow_pos hc q)
      (pow_le_pow_left₀ hc.le hcc q))

/-! ### The majorant bounds the Fourier transform -/

/-- Iterated derivatives commute with `ℝ → ℂ`. -/
private theorem iteratedDeriv_ofReal_comp' {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => ((g u : ℝ) : ℂ)) = fun u : ℝ => ((iteratedDeriv n g u : ℝ) : ℂ) := by
  induction n with
  | zero => funext u; simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext u
      rw [iteratedDeriv_succ]
      have hd : HasDerivAt (iteratedDeriv n g) (deriv (iteratedDeriv n g) u) u :=
        ((hg.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)) u).hasDerivAt
      exact hd.ofReal_comp.deriv

/-- **The majorant bounds the Fourier transform**: `|φ̂(ξ)| ≤ A μ_B(2π|ξ|)` for `ξ ≠ 0`, since
`(2π|ξ|)^q |φ̂(ξ)| = |(φ^{(q)})^(ξ)| ≤ ∫ |φ^{(q)}|`. -/
theorem norm_fourier_le_dcMajorant {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {A B : ℝ} (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * dcLogWeight q)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (fun x : ℝ => (φ x : ℂ)) ξ‖ ≤ A * dcMajorant B (2 * Real.pi * |ξ|) := by
  set ψ : ℝ → ℂ := fun x => (φ x : ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hφ
  have hcs : ∀ n : ℕ, HasCompactSupport (iteratedDeriv n φ) := fun n => by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hφc
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hint : ∀ n : ℕ, MeasureTheory.Integrable (iteratedDeriv n ψ) := fun n => by
    rw [iteratedDeriv_ofReal_comp' hφ n]
    exact (Complex.continuous_ofReal.comp (hφ.continuous_iteratedDeriv n
      (by exact_mod_cast le_top))).integrable_of_hasCompactSupport
      ((hcs n).comp_left Complex.ofReal_zero)
  have hc0 : 0 < 2 * Real.pi * |ξ| := by positivity
  have hbound : ∀ q : ℕ, ‖𝓕 ψ ξ‖ * (2 * Real.pi * |ξ|) ^ q ≤ A * B ^ q * dcLogWeight q := by
    intro q
    have hF := congrFun (Real.fourier_iteratedDeriv (N := ⊤) (n := q) hψ (fun n _ => hint n)
      (by exact_mod_cast le_top)) ξ
    have h1 : ‖𝓕 (iteratedDeriv q ψ) ξ‖ ≤ ∫ t, |iteratedDeriv q φ t| := by
      refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans (le_of_eq ?_)
      rw [iteratedDeriv_ofReal_comp' hφ q]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [hF, norm_smul, norm_pow] at h1
    have hn : ‖2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    rw [hn] at h1
    linarith [hA q, mul_comm (‖𝓕 ψ ξ‖) ((2 * Real.pi * |ξ|) ^ q)]
  have hA0 : 0 ≤ A := by
    have h0 := (MeasureTheory.integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simp only [pow_zero, mul_one] at h0
    rw [dcLogWeight_zero, mul_one] at h0; exact h0
  rw [dcMajorant, Real.mul_iInf_of_nonneg hA0]
  refine le_ciInf fun q => ?_
  rw [← mul_div_assoc, le_div_iff₀ (pow_pos hc0 q)]
  exact (hbound q).trans_eq (by ring)

/-! ### The critical overlap -/

private theorem loglog_atTop' :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Upper bound.** Eventually `c*_N ≤ 4 e B L (log L)²`, and that overlap lies in the defining set. -/
theorem eventually_dcCriticalOverlap_le {B : ℝ} (hB : 1 ≤ B) :
    ∀ᶠ N : ℕ in atTop, dcCriticalOverlap B N ≤ 4 * Real.exp 1 * B * dcScale N ∧
      (4 * Real.exp 1 * B * dcScale N) ∈
        {c : ℝ | 1 ≤ c ∧ dcMajorant B c ^ 2 * Real.log N ≤ 1} := by
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  set C := 4 * Real.exp 1 * B with hC
  have hC1 : 1 ≤ C := by rw [hC]; nlinarith
  have ho := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)).bound
    (show (0 : ℝ) < 1 / (2 * C) by positivity)
  have hP : ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧ 1 ≤ Real.log L ∧ C * L * Real.log L ^ 2 + 3 ≤ L ^ 2 := by
    filter_upwards [ho, eventually_ge_atTop (Real.exp 1 + 6)] with L hoL hL
    have hL0 : 0 < L := by linarith
    have hlL : 1 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le hL0]; linarith
    refine ⟨by linarith, hlL, ?_⟩
    rw [Real.rpow_two, Real.rpow_one, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg hL0.le] at hoL
    have h1 : C * L * Real.log L ^ 2 ≤ L ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hoL (by positivity : (0 : ℝ) ≤ C * L)
      have e : C * L * (1 / (2 * C) * L) = L ^ 2 / 2 := by field_simp
      linarith
    nlinarith
  filter_upwards [loglog_atTop'.eventually hP] with N ⟨hL2, hl1, hLL⟩
  set L := Real.log (Real.log N) with hLdef
  have hL0 : 0 < L := by linarith
  have hlogN : 0 < Real.log N := by
    rcases (Real.log_natCast_nonneg N).lt_or_eq with h | h
    · exact h
    · exfalso; rw [hLdef, ← h, Real.log_zero] at hL0; exact lt_irrefl _ hL0
  set c₀ := C * dcScale N with hc₀
  have hc₀eq : c₀ = C * L * Real.log L ^ 2 := by rw [hc₀, dcScale]; ring
  have hc₀1 : 1 ≤ c₀ := by
    rw [hc₀eq]
    have : 1 ≤ Real.log L ^ 2 := one_le_pow₀ hl1
    have h2 : 1 ≤ C * L := by nlinarith
    nlinarith
  have hmem : c₀ ∈ {c : ℝ | 1 ≤ c ∧ dcMajorant B c ^ 2 * Real.log N ≤ 1} := by
    refine ⟨hc₀1, ?_⟩
    have hμ := dcMajorant_le_exp hB hc₀1
    have hμ0 : 0 ≤ dcMajorant B c₀ := le_ciInf fun q => by
      have := dcLogWeight_pos q; have : 0 < c₀ := by linarith
      positivity
    have hlog : Real.log (c₀ + 3) ≤ 2 * Real.log L := by
      have h := Real.log_le_log (show (0 : ℝ) < c₀ + 3 by linarith)
        (show c₀ + 3 ≤ L ^ 2 by rw [hc₀eq]; exact hLL)
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have hl3 : 1 ≤ Real.log (c₀ + 3) := one_le_log_add_three' (by linarith)
    have hx : L ≤ c₀ / (Real.exp 1 * B * Real.log (c₀ + 3) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hsq : Real.log (c₀ + 3) ^ 2 ≤ 4 * Real.log L ^ 2 := by nlinarith
      have hEB : 0 ≤ Real.exp 1 * B := by positivity
      have h1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hL0.le hEB)
      have h2 : L * (Real.exp 1 * B) * (4 * Real.log L ^ 2) = c₀ := by rw [hc₀eq, hC]; ring
      nlinarith
    calc dcMajorant B c₀ ^ 2 * Real.log N
        ≤ Real.exp (1 - c₀ / (Real.exp 1 * B * Real.log (c₀ + 3) ^ 2)) ^ 2 * Real.exp L := by
          rw [hLdef, Real.exp_log hlogN]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hμ0 hμ 2) hlogN.le
      _ = Real.exp (2 * (1 - c₀ / (Real.exp 1 * B * Real.log (c₀ + 3) ^ 2)) + L) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact ⟨csInf_le ⟨1, fun _ h => h.1⟩ hmem, hmem⟩

/-- **Lower bound.** Eventually `L (log L)²/(32 e) ≤ c*_N`: below that overlap the majorant still
exceeds `(log N)^{−1/4}`. -/
theorem eventually_le_dcCriticalOverlap {B : ℝ} (hB : 1 ≤ B) :
    ∀ᶠ N : ℕ in atTop, dcScale N / (32 * Real.exp 1) ≤ dcCriticalOverlap B N := by
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  set δ := 1 / (32 * Real.exp 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hc₀ : Tendsto (fun L : ℝ => δ * L * Real.log L ^ 2) atTop atTop := by
    have h1 : Tendsto (fun L : ℝ => δ * L) atTop atTop := tendsto_id.const_mul_atTop hδ0
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with L hL
    have hL0 : 0 < L := by linarith
    have : 1 ≤ Real.log L := by rw [Real.le_log_iff_exp_le hL0]; exact hL
    have : 1 ≤ Real.log L ^ 2 := one_le_pow₀ this
    have h2 : 0 ≤ δ * L := by positivity
    nlinarith
  have hsq : Tendsto (fun L : ℝ => δ * Real.log L ^ 2) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop).const_mul_atTop
      hδ0
  have hP : ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧ 1 ≤ δ * Real.log L ^ 2 ∧
      Real.exp (-(8 * Real.exp 1 * (δ * L * Real.log L ^ 2) /
        Real.log (δ * L * Real.log L ^ 2) ^ 2)) ≤ dcMajorant B (δ * L * Real.log L ^ 2) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1), hsq.eventually_ge_atTop 1,
      hc₀.eventually (eventually_exp_le_dcMajorant hB)] with L h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [loglog_atTop'.eventually hP, eventually_dcCriticalOverlap_le hB]
    with N ⟨hLe, hδl, hμ⟩ ⟨_, hmem⟩
  set L := Real.log (Real.log N) with hLdef
  have hL0 : 0 < L := by linarith
  have hlogN : 0 < Real.log N := by
    rcases (Real.log_natCast_nonneg N).lt_or_eq with h | h
    · exact h
    · exfalso; rw [hLdef, ← h, Real.log_zero] at hL0; exact lt_irrefl _ hL0
  have hlL : 1 ≤ Real.log L := by rw [Real.le_log_iff_exp_le hL0]; exact hLe
  set c₀ := δ * L * Real.log L ^ 2 with hc₀def
  have hscale : dcScale N / (32 * Real.exp 1) = c₀ := by
    rw [hc₀def, hδ, dcScale]; ring
  rw [hscale]
  have hc₀L : L ≤ c₀ := by
    have := mul_le_mul_of_nonneg_left hδl hL0.le
    rw [hc₀def]; nlinarith
  refine le_csInf ⟨_, hmem⟩ fun c ⟨hc1, hcμ⟩ => ?_
  by_contra hlt
  push Not at hlt
  have hlogc₀ : Real.log L ≤ Real.log c₀ := Real.log_le_log hL0 hc₀L
  have hE : 8 * Real.exp 1 * c₀ / Real.log c₀ ^ 2 ≤ L / 4 := by
    have hlc0 : 0 < Real.log c₀ ^ 2 := by
      have : 0 < Real.log c₀ := by linarith
      positivity
    rw [div_le_iff₀ hlc0]
    have hsq' : Real.log L ^ 2 ≤ Real.log c₀ ^ 2 := pow_le_pow_left₀ (by linarith) hlogc₀ 2
    have : 8 * Real.exp 1 * c₀ = L / 4 * Real.log L ^ 2 := by
      rw [hc₀def, hδ]; field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq' (by linarith)
  have hμc : Real.exp (-(L / 4)) ≤ dcMajorant B c :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hμ.trans
      (dcMajorant_antitone (by linarith) (by linarith) hlt.le))
  have hsq2 : Real.exp (-(L / 4)) ^ 2 * Real.log N ≤ dcMajorant B c ^ 2 * Real.log N :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hμc 2) hlogN.le
  have hgt : 1 < Real.exp (-(L / 4)) ^ 2 * Real.log N := by
    rw [← Real.exp_log hlogN, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.one_lt_exp_iff.mpr (by push_cast; linarith)
  linarith

/-! ### The rate law in units of the critical overlap -/

private theorem eventually_critical_pos {B : ℝ} (hB : 1 ≤ B) :
    ∀ᶠ N : ℕ in atTop, 0 < dcCriticalOverlap B N := by
  filter_upwards [eventually_le_dcCriticalOverlap hB, dcScale_atTop.eventually_gt_atTop 0]
    with N h hS
  exact lt_of_lt_of_le (by positivity) h

/-- The dilation `N/(K c*_N)` tends to infinity. -/
theorem tendsto_div_mul_dcCriticalOverlap {B K : ℝ} (hB : 1 ≤ B) (hK : 0 < K) :
    Tendsto (fun N : ℕ => (N : ℝ) / (K * dcCriticalOverlap B N)) atTop atTop := by
  have he1 : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_div_const_mul_dcScale (show (0 : ℝ) < K * (4 * Real.exp 1 * B) by positivity))
  filter_upwards [eventually_dcCriticalOverlap_le hB, eventually_critical_pos hB] with N hle hpos
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
  have := mul_le_mul_of_nonneg_left hle.1 hK.le
  linarith

/-- **Every divergent multiple of the critical overlap is a receiver.** -/
theorem riemannHypothesis_iff_nonneg_of_critical_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    {A B : ℝ} (hB : 1 ≤ B)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * dcLogWeight q)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hrN : Tendsto (fun N : ℕ => (N : ℝ) / (r N * dcCriticalOverlap B N)) atTop atTop) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (r N * dcCriticalOverlap B N)) φ)) := by
  refine riemannHypothesis_iff_nonneg_of_divergent_rate hφ hφ1 hφint (by linarith) hA ?_ hrN
  have hδ : (0 : ℝ) < 1 / (32 * Real.exp 1) := by positivity
  refine tendsto_atTop_mono' atTop ?_ (hr.atTop_mul_const hδ)
  filter_upwards [eventually_le_dcCriticalOverlap hB, dcScale_atTop.eventually_gt_atTop 0,
    hr.eventually_ge_atTop 0] with N h hS hr0
  rw [le_div_iff₀ hS]
  have := mul_le_mul_of_nonneg_left h hr0
  calc r N * (1 / (32 * Real.exp 1)) * dcScale N = r N * (dcScale N / (32 * Real.exp 1)) := by
        ring
    _ ≤ r N * dcCriticalOverlap B N := this

/-- **A single bounded multiple of the critical overlap sees a window of radius `½ log K + O(1)`.**
Eventual nonnegativity at overlap `K c*_N` gives Weil positivity on every `C²` test supported in
`[−R, R]` with `24 e B ⌈1 + e^{2(R+1)}⌉ < K/(32 e)`. -/
theorem nonneg_of_critical_multiple {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    {A B : ℝ} (hB : 1 ≤ B)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * dcLogWeight q)
    {K : ℝ} (hK : 32 * Real.exp 1 ≤ K)
    (H : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * dcCriticalOverlap B N)) φ)))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgR : SupportedIn R g)
    (hRK : 24 * B * blockSize (R + 1) * Real.exp 1 < K / (32 * Real.exp 1)) :
    0 ≤ weilQuad g := by
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K / (32 * Real.exp 1) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hcN := tendsto_div_mul_dcCriticalOverlap hB hK0
  have hrate : ∀ᶠ N : ℕ in atTop, K / (32 * Real.exp 1) ≤
      dcRate (fun N : ℕ => (N : ℝ) / (K * dcCriticalOverlap B N)) N := by
    have hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ K * dcCriticalOverlap B N := by
      filter_upwards [eventually_le_dcCriticalOverlap hB,
        dcScale_atTop.eventually_ge_atTop (32 * Real.exp 1)] with N h hS
      have h1 : 1 ≤ dcScale N / (32 * Real.exp 1) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h2 : 1 ≤ K := by have := Real.add_one_le_exp 1; linarith
      nlinarith
    filter_upwards [eventually_div_dcScale_le_dcRate hcN hc1, eventually_le_dcCriticalOverlap hB,
      dcScale_atTop.eventually_gt_atTop 0] with N h hlow hS
    refine le_trans ?_ h
    rw [le_div_iff₀ hS]
    calc K / (32 * Real.exp 1) * dcScale N = K * (dcScale N / (32 * Real.exp 1)) := by ring
      _ ≤ K * dcCriticalOverlap B N := mul_le_mul_of_nonneg_left hlow hK0.le
  exact nonneg_of_atomicFamilies_nonneg_of_rate stableForm_weilQuad hφ hφ1 hφint
    (by linarith : (0 : ℝ) ≤ B) hA hcN hK1 hrate H hg hR hgR hRK

/-- **RH is the union of the bounded multiples of the critical overlap.** -/
theorem riemannHypothesis_iff_forall_critical_multiple {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    {A B : ℝ} (hB : 1 ≤ B)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * B ^ q * dcLogWeight q) :
    RiemannHypothesis ↔ ∀ K : ℝ, 1 ≤ K → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * dcCriticalOverlap B N)) φ)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  constructor
  · intro hRH K hK
    filter_upwards [(tendsto_div_mul_dcCriticalOverlap hB
      (by linarith : (0 : ℝ) < K)).eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ2 hφ1 hk N x
    exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc
  · intro H
    refine RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mpr fun g hg hgc => ?_
    obtain ⟨R, -, -, hR, hgR, -, -⟩ := exists_test_bounds hg hgc
    have he0 : 0 < Real.exp 1 := Real.exp_pos 1
    set K : ℝ := 32 * Real.exp 1 * (24 * B * blockSize (R + 1) * Real.exp 1 + 1)
    have hK32 : 32 * Real.exp 1 ≤ K := by
      have : (0 : ℝ) ≤ 24 * B * blockSize (R + 1) * Real.exp 1 := by
        have : (0 : ℝ) ≤ B := by linarith
        positivity
      nlinarith
    have hK1 : 1 ≤ K := by
      have : (1 : ℝ) ≤ 32 * Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
      linarith
    refine nonneg_of_critical_multiple hφ hφ1 hφint hB hA hK32 (H K hK1) hg hR hgR ?_
    have hKdiv : K / (32 * Real.exp 1) = 24 * B * blockSize (R + 1) * Real.exp 1 + 1 :=
      mul_div_cancel_left₀ _ (by positivity)
    rw [hKdiv]
    linarith

/-- **The Steklov profile.** RH holds iff every bounded multiple of its critical overlap
(`B = 12`) is eventually nonnegative, and every divergent multiple is a receiver. -/
theorem riemannHypothesis_iff_steklovDCProfile_critical_multiples :
    (RiemannHypothesis ↔ ∀ K : ℝ, 1 ≤ K → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x
        (dilate ((N : ℝ) / (K * dcCriticalOverlap 12 N)) steklovDCProfile))) ∧
    ∀ r : ℕ → ℝ, Tendsto r atTop atTop →
      Tendsto (fun N : ℕ => (N : ℝ) / (r N * dcCriticalOverlap 12 N)) atTop atTop →
      (RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N x
          (dilate ((N : ℝ) / (r N * dcCriticalOverlap 12 N)) steklovDCProfile))) :=
  ⟨riemannHypothesis_iff_forall_critical_multiple contDiff_steklovDCProfile
      steklovDCProfile_vanishesOff integral_steklovDCProfile (by norm_num)
      integral_abs_iteratedDeriv_steklovDCProfile_le,
    fun _ hr hrN => riemannHypothesis_iff_nonneg_of_critical_rate contDiff_steklovDCProfile
      steklovDCProfile_vanishesOff integral_steklovDCProfile (by norm_num)
      integral_abs_iteratedDeriv_steklovDCProfile_le hr hrN⟩

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_forall_critical_multiple
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_nonneg_of_critical_rate
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.nonneg_of_critical_multiple
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.norm_fourier_le_dcMajorant
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_le_dcCriticalOverlap
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_dcCriticalOverlap_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_steklovDCProfile_critical_multiples
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_forall_bounded_rate
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.steklovDCProfile_window
