/-
# Monic polynomial asymptotics at ∞ (from scratch, over ℂ)

Toward the far-field anchor `explicitBranch c n = bottcherCoord c` of the connected Böttcher uniformization
(`BasinBranchGlue`): the explicit branch is asymptotic to `bottcherCoord` at `∞` only because the orbit
`f_c^[n] z` is asymptotic to `z^{2^n}`. Mathlib's polynomial-at-∞ asymptotics are stated for ordered fields
(ℝ); over ℂ (the cobounded filter) they are absent, so this file builds them from scratch:

* `norm_eval_le_of_one_le` — the elementary growth bound `‖Q(z)‖ ≤ (∑‖coeffᵢ‖)·‖z‖^{deg Q}` for `‖z‖ ≥ 1`;
* `tendsto_eval_div_pow_zero` — a polynomial of degree `< d` over `z^d` tends to `0` at `∞`;
* `tendsto_quadraticPolyIterate_div` — the monic-iterate asymptotic `f_c^[n] z / z^{2^n} → 1` at `∞`.

These feed the principal-sector log analysis `log(f_c^[n] z) − 2^n log z → 0` that pins the anchor.

New file (hRigid / connected lane, the basin-branch far-field anchor seed). General ℂ-polynomial asymptotics.
-/
import GaloisForLFunctions.Bottcher.BasinBranchGlue
import GaloisForLFunctions.Bottcher.BottcherAsymptotic

open Complex Set Filter Topology Bornology Polynomial

namespace Bottcher

/-- **Elementary polynomial growth bound.** For `‖z‖ ≥ 1`, `‖Q(z)‖ ≤ (∑ᵢ ‖Qᵢ‖)·‖z‖^{deg Q}`: bound the
support sum termwise, using `‖z‖^i ≤ ‖z‖^{deg Q}` for `i ≤ deg Q`. -/
theorem norm_eval_le_of_one_le {Q : Polynomial ℂ} {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖Q.eval z‖ ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖) * ‖z‖ ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply norm_sum_le_of_le
  intro i hi
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_right₀ hz; rw [Finset.mem_range] at hi; omega

/-- **A polynomial of degree `< d` over `z^d` vanishes at `∞`.** `Q.eval z / z^d → 0` along the cobounded
filter, by the growth bound (`Q.eval z / z^d ≍ ‖z‖^{deg Q - d} → 0`). -/
theorem tendsto_eval_div_pow_zero {Q : Polynomial ℂ} {d : ℕ} (hQd : Q.natDegree < d) :
    Tendsto (fun z => Q.eval z / z ^ d) (cobounded ℂ) (𝓝 0) := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (cobounded ℂ) atTop := tendsto_norm_cobounded_atTop
  set C := ∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖ with hC
  have hbd : Tendsto (fun z : ℂ => C * ‖z‖ ^ Q.natDegree / ‖z‖ ^ d) (cobounded ℂ) (𝓝 0) := by
    have heq : (fun z : ℂ => C * ‖z‖ ^ Q.natDegree / ‖z‖ ^ d)
        =ᶠ[cobounded ℂ] (fun z => C / ‖z‖ ^ (d - Q.natDegree)) := by
      filter_upwards [hnorm.eventually_gt_atTop 0] with z hz0
      have hd : ‖z‖ ^ d = ‖z‖ ^ Q.natDegree * ‖z‖ ^ (d - Q.natDegree) := by
        rw [← pow_add]; congr 1; omega
      rw [hd]; field_simp
    rw [tendsto_congr' heq]
    exact tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by omega : d - Q.natDegree ≠ 0)).comp hnorm)
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hnorm.eventually_ge_atTop 1] with z hz1
  rw [norm_div, norm_pow]
  have hpos : (0 : ℝ) < ‖z‖ ^ d := by have : (1 : ℝ) ≤ ‖z‖ := hz1; positivity
  rw [div_le_div_iff_of_pos_right hpos]
  exact norm_eval_le_of_one_le hz1

/-- The quadratic polynomial `z^2 + c` is monic. -/
theorem quadraticPoly_monic (c : ℂ) : (quadraticPoly c).Monic := by
  unfold quadraticPoly
  exact monic_X_pow_add (lt_of_le_of_lt degree_C_le (by decide))

/-- The iterate polynomial `f_c^[n]` is monic (a composite of monics, inner non-constant). -/
theorem quadraticPolyIterate_monic (c : ℂ) (n : ℕ) : (quadraticPolyIterate c n).Monic := by
  induction n with
  | zero => simp only [quadraticPolyIterate]; exact monic_X
  | succ n ih =>
    rw [quadraticPolyIterate]
    exact (quadraticPoly_monic c).comp ih (by rw [quadraticPolyIterate_natDegree]; positivity)

/-- `f_c^[n] − X^{2^n}` has degree `< 2^n` (the leading `X^{2^n}` terms of the two monics cancel). -/
theorem natDegree_quadraticPolyIterate_sub_lt (c : ℂ) (n : ℕ) :
    (quadraticPolyIterate c n - X ^ (2 ^ n)).natDegree < 2 ^ n := by
  set d := 2 ^ n with hd
  have hmonic := quadraticPolyIterate_monic c n
  have hdegP : (quadraticPolyIterate c n).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, quadraticPolyIterate_natDegree]
  have hsub : (quadraticPolyIterate c n - X ^ d).degree < (d : WithBot ℕ) := by
    have h := Polynomial.degree_sub_lt (p := quadraticPolyIterate c n) (q := X ^ d)
      (by rw [hdegP, degree_X_pow]) hmonic.ne_zero
      (by rw [hmonic.leadingCoeff, (monic_X_pow d).leadingCoeff])
    rwa [hdegP] at h
  rcases eq_or_ne (quadraticPolyIterate c n - X ^ d) 0 with h0 | h0
  · rw [h0, natDegree_zero]; positivity
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hsub

/-- **The monic-iterate asymptotic** `f_c^[n] z / z^{2^n} → 1` as `z → ∞`. Writing
`f_c^[n] = z^{2^n} + (f_c^[n] − z^{2^n})` with the remainder of degree `< 2^n`, the ratio is
`1 + (remainder)/z^{2^n} → 1 + 0`. This is the orbit asymptotic underlying the far-field anchor. -/
theorem tendsto_quadraticPolyIterate_div (c : ℂ) (n : ℕ) :
    Tendsto (fun z => (quadratic c)^[n] z / z ^ (2 ^ n)) (cobounded ℂ) (𝓝 1) := by
  have hev : (fun z => (quadratic c)^[n] z / z ^ (2 ^ n))
      =ᶠ[cobounded ℂ]
        (fun z => 1 + (quadraticPolyIterate c n - X ^ (2 ^ n)).eval z / z ^ (2 ^ n)) := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz0
    have hzd : z ^ (2 ^ n) ≠ 0 := pow_ne_zero _ (by intro h; rw [h, norm_zero] at hz0; linarith)
    rw [← quadraticPolyIterate_eval c n z, eval_sub, eval_pow, eval_X]
    field_simp; ring
  rw [tendsto_congr' hev]
  simpa using
    tendsto_const_nhds.add (tendsto_eval_div_pow_zero (natDegree_quadraticPolyIterate_sub_lt c n))

/-- **`Complex.log` of the orbit ratio vanishes at `∞`:** `log(f_c^[n] z / z^{2^n}) → 0`. (The ratio `→ 1`
and `Complex.log` is continuous at `1`.) A factor of the principal-sector identity
`log(f_c^[n] z) − 2^n·log z → 0`. -/
theorem tendsto_clog_ratio (c : ℂ) (n : ℕ) :
    Tendsto (fun z => Complex.log ((quadratic c)^[n] z / z ^ (2 ^ n))) (cobounded ℂ) (𝓝 0) := by
  have h1 := tendsto_quadraticPolyIterate_div c n
  have h1mem : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num]; exact Complex.ofReal_mem_slitPlane.mpr one_pos
  have hcont : ContinuousAt Complex.log 1 := (Complex.hasDerivAt_log h1mem).continuousAt
  simpa only [Function.comp_apply, Complex.log_one] using! hcont.tendsto.comp h1

/-- **Principal-branch power-log identity (sector form).** `Complex.log (z^k) = k·Complex.log z` whenever
`k·arg z ∈ (-π, π]` (and `z ≠ 0`): `z^k = exp(k·log z)` and `log∘exp` is the identity on the horizontal
strip `im ∈ (-π, π]`. This is the branch ingredient of `log(z^{2^n}) = 2^n·log z` in the principal sector
`|arg z| < π/2^n` — the last input to the far-field anchor `eb(n)=bottcherCoord`. -/
theorem clog_pow_of_arg {z : ℂ} {k : ℕ} (hz : z ≠ 0)
    (h1 : -Real.pi < (k : ℝ) * z.arg) (h2 : (k : ℝ) * z.arg ≤ Real.pi) :
    Complex.log (z ^ k) = (k : ℂ) * Complex.log z := by
  have hzk : z ^ k = Complex.exp ((k : ℂ) * Complex.log z) := by
    rw [Complex.exp_nat_mul, Complex.exp_log hz]
  have him : ((k : ℂ) * Complex.log z).im = (k : ℝ) * z.arg := by
    rw [Complex.mul_im]; simp [Complex.log_im]
  rw [hzk, Complex.log_exp (by rw [him]; exact h1) (by rw [him]; exact h2)]

/-! ### The far-field anchor along the positive real ray -/

/-- `(t : ℂ) → ∞` (cobounded) as `t → ∞` along the reals. -/
theorem tendsto_ofReal_cobounded : Tendsto (fun t : ℝ => (t : ℂ)) atTop (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]; simpa using tendsto_abs_atTop_atTop

/-- The orbit ratio `f_c^[n] t / t^{2^n} → 1` along the positive real ray. -/
theorem tendsto_ratio_real (c : ℂ) (n : ℕ) :
    Tendsto (fun t : ℝ => (quadratic c)^[n] (t : ℂ) / (t : ℂ) ^ (2 ^ n)) atTop (𝓝 1) :=
  (tendsto_quadraticPolyIterate_div c n).comp tendsto_ofReal_cobounded

/-- The orbit `f_c^[n] (t : ℂ) → ∞` along the positive real ray (`z ↦ z²+c` maps `∞` to `∞`). -/
theorem tendsto_iterate_real_cobounded (c : ℂ) (n : ℕ) :
    Tendsto (fun t : ℝ => (quadratic c)^[n] (t : ℂ)) atTop (cobounded ℂ) := by
  have hqn : Tendsto ((quadratic c)^[n]) (cobounded ℂ) (cobounded ℂ) := by
    induction n with
    | zero => simpa using tendsto_id
    | succ n ih => rw [Function.iterate_succ']; exact (tendsto_sq_add_cobounded c).comp ih
  exact hqn.comp tendsto_ofReal_cobounded

/-- **The principal-branch log functional equation, asymptotically along the real ray.**
`log(f_c^[n] t) − 2^n·log t → 0` as `t → ∞`. On the positive real ray `arg t = 0`, so `t^{2^n}` is
positive (`log(t^{2^n}) = 2^n log t`, `clog_pow_of_arg`) and `f_c^[n] t = t^{2^n}·(ratio)` with `ratio → 1`,
so by `Complex.log_mul_eq_add_log_iff` the log of the product splits and the difference is `log(ratio) → 0`
(`tendsto_clog_ratio`). The branch winding vanishes because everything is principal on the ray. -/
theorem tendsto_clog_iterate_sub (c : ℂ) (n : ℕ) :
    Tendsto (fun t : ℝ => Complex.log ((quadratic c)^[n] (t : ℂ)) - (2 ^ n : ℂ) * Complex.log (t : ℂ))
      atTop (𝓝 0) := by
  have hlogratio : Tendsto (fun t : ℝ => Complex.log ((quadratic c)^[n] (t:ℂ) / (t:ℂ) ^ (2^n)))
      atTop (𝓝 0) := (tendsto_clog_ratio c n).comp tendsto_ofReal_cobounded
  have hev : (fun t : ℝ => Complex.log ((quadratic c)^[n] (t:ℂ)) - (2^n : ℂ) * Complex.log (t:ℂ))
      =ᶠ[atTop] (fun t => Complex.log ((quadratic c)^[n] (t:ℂ) / (t:ℂ) ^ (2^n))) := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (tendsto_ratio_real c n).eventually_ne (show (1:ℂ) ≠ 0 by norm_num)] with t ht hrne
    have hz : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hzpow : (t:ℂ) ^ (2^n) ≠ 0 := pow_ne_zero _ hz
    have hargz : ((t:ℂ)).arg = 0 := Complex.arg_ofReal_of_nonneg (le_of_lt ht)
    have hargzpow : ((t:ℂ) ^ (2^n)).arg = 0 := by
      rw [← Complex.ofReal_pow]; exact Complex.arg_ofReal_of_nonneg (by positivity)
    have hfn : (quadratic c)^[n] (t:ℂ)
        = (t:ℂ) ^ (2^n) * ((quadratic c)^[n] (t:ℂ) / (t:ℂ) ^ (2^n)) := by field_simp
    have hclogpow : Complex.log ((t:ℂ) ^ (2^n)) = (2^n : ℂ) * Complex.log (t:ℂ) := by
      have h := clog_pow_of_arg (k := 2^n) hz
        (by rw [hargz, mul_zero]; linarith [Real.pi_pos])
        (by rw [hargz, mul_zero]; linarith [Real.pi_pos])
      rw [h]; push_cast; ring
    have hlogmul : Complex.log ((quadratic c)^[n] (t:ℂ))
        = Complex.log ((t:ℂ) ^ (2^n)) + Complex.log ((quadratic c)^[n] (t:ℂ) / (t:ℂ) ^ (2^n)) := by
      conv_lhs => rw [hfn]
      refine (Complex.log_mul_eq_add_log_iff hzpow hrne).mpr ?_
      rw [hargzpow, zero_add]
      exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    rw [hlogmul, hclogpow]; ring
  rw [tendsto_congr' hev]; exact hlogratio

/-- **The far-field anchor's analytic limit.** `W(t) := 2⁻ⁿ·bottcherLog(f_c^[n] t) − bottcherLog t → 0`
along the positive real ray. Decompose `W = 2⁻ⁿ(log(f^[n]t)−2^n log t) + 2⁻ⁿ(bottcherLog−log)(f^[n]t) −
(bottcherLog−log)(t)`; the first → 0 (`tendsto_clog_iterate_sub`), the last two → 0
(`tendsto_bottcherLog_sub_log`, orbit `→ ∞`). Since `explicitBranch c n t / bottcherCoord c t = exp(W t)`,
this gives `explicitBranch c n t / bottcherCoord c t → 1` — pinning the ζ=1 sheet. -/
theorem tendsto_W_real (c : ℂ) (n : ℕ) :
    Tendsto (fun t : ℝ => (((2 : ℝ) ^ n)⁻¹ : ℂ) * bottcherLog c ((quadratic c)^[n] (t:ℂ))
        - bottcherLog c (t:ℂ)) atTop (𝓝 0) := by
  have hS_t : Tendsto (fun t : ℝ => bottcherLog c (t:ℂ) - Complex.log (t:ℂ)) atTop (𝓝 0) :=
    (tendsto_bottcherLog_sub_log c).comp tendsto_ofReal_cobounded
  have hS_fn : Tendsto (fun t : ℝ => bottcherLog c ((quadratic c)^[n] (t:ℂ))
      - Complex.log ((quadratic c)^[n] (t:ℂ))) atTop (𝓝 0) :=
    (tendsto_bottcherLog_sub_log c).comp (tendsto_iterate_real_cobounded c n)
  have hclog := tendsto_clog_iterate_sub c n
  have hcombine : (fun t : ℝ => (((2:ℝ) ^ n)⁻¹ : ℂ) * bottcherLog c ((quadratic c)^[n] (t:ℂ))
        - bottcherLog c (t:ℂ))
      = (fun t : ℝ => (((2:ℝ) ^ n)⁻¹ : ℂ)
            * (Complex.log ((quadratic c)^[n] (t:ℂ)) - (2 ^ n:ℂ) * Complex.log (t:ℂ))
          + (((2:ℝ) ^ n)⁻¹ : ℂ) * (bottcherLog c ((quadratic c)^[n] (t:ℂ))
            - Complex.log ((quadratic c)^[n] (t:ℂ)))
          - (bottcherLog c (t:ℂ) - Complex.log (t:ℂ))) := by
    funext t
    have hkey : (((2:ℝ) ^ n)⁻¹ : ℂ) * (2 ^ n : ℂ) = 1 := by
      push_cast; exact inv_mul_cancel₀ (pow_ne_zero n two_ne_zero)
    linear_combination (Complex.log (t:ℂ)) * hkey
  rw [hcombine]
  simpa using ((hclog.const_mul (((2:ℝ) ^ n)⁻¹ : ℂ)).add
    (hS_fn.const_mul (((2:ℝ) ^ n)⁻¹ : ℂ))).sub hS_t

/-- **`explicitBranch c n / bottcherCoord c → 1` along the positive real ray.** Since
`explicitBranch c n t = exp(2⁻ⁿ·bottcherLog(f^[n]t))` and `bottcherCoord c t = exp(bottcherLog t)`, their
ratio is `exp(W t)`, and `W → 0` (`tendsto_W_real`). This is the limit that pins the ζ=1 sheet to `1`. -/
theorem tendsto_explicitBranch_div_bottcherCoord (c : ℂ) (n : ℕ) :
    Tendsto (fun t : ℝ => explicitBranch c n (t : ℂ) / bottcherCoord c (t : ℂ)) atTop (𝓝 1) := by
  have hW := tendsto_W_real c n
  have heq : (fun t : ℝ => explicitBranch c n (t : ℂ) / bottcherCoord c (t : ℂ))
      = (fun t : ℝ => Complex.exp ((((2 : ℝ) ^ n)⁻¹ : ℂ) * bottcherLog c ((quadratic c)^[n] (t:ℂ))
          - bottcherLog c (t:ℂ))) := by
    funext t
    rw [explicitBranch, bottcherCoord, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [heq]
  simpa only [Function.comp_apply, Complex.exp_zero] using!
    (Complex.continuous_exp.continuousAt.tendsto.comp hW)

/-- **The far-field anchor: `explicitBranch c n = bottcherCoord c`.** On a preconnected far-field region
`V ⊆ explicitDomain c n ∩ escapeOpen c` that contains the positive real ray eventually (`hray`), the explicit
level-`n` branch equals `bottcherCoord c` throughout `V`. The discrepancy `ξ = eb(n)/bottcherCoord` is a
`2^n`-th root of unity (`explicitBranch_isRootOfUnity_smul`), continuous, hence constant on `V`
(`const_of_pow_eq_one`); along the real ray `ξ → 1` (`tendsto_explicitBranch_div_bottcherCoord`), so the
constant value is `1`. This discharges the anchor hypotheses of `explicitBranch_FE_relation_of_anchor` —
the basin branch carries the genuine `φ_c` relation and functional equation, anchored on the principal
far field — with the only remaining input a geometric one: the connected far-field region `V` reaching the
cycle point (the colimit). -/
theorem explicitBranch_eq_bottcherCoord_of_realray (c : ℂ) (n : ℕ) {V : Set ℂ}
    (hVc : IsPreconnected V) (hVdom : V ⊆ explicitDomain c n) (hVesc : V ⊆ escapeOpen c)
    (hray : ∀ᶠ t : ℝ in atTop, (t : ℂ) ∈ V) {z₀ : ℂ} (hz₀ : z₀ ∈ V) :
    explicitBranch c n z₀ = bottcherCoord c z₀ := by
  set ξ : ℂ → ℂ := fun z => explicitBranch c n z / bottcherCoord c z with hξdef
  have hpow : ∀ z ∈ V, ξ z ^ (2 ^ n) = 1 := by
    intro z hz
    obtain ⟨ζ, hζ, hsmul⟩ := explicitBranch_isRootOfUnity_smul c n (hVesc hz)
    show (explicitBranch c n z / bottcherCoord c z) ^ (2 ^ n) = 1
    rw [hsmul, mul_div_assoc, div_self (bottcherCoord_ne_zero c z), mul_one, hζ]
  have hξc : ContinuousOn ξ V := by
    apply ContinuousOn.div
    · exact ((analyticOnNhd_explicitBranch c n).continuousOn).mono hVdom
    · exact (differentiableOn_bottcherCoord c).continuousOn.mono hVesc
    · exact fun z _ => bottcherCoord_ne_zero c z
  have hconst : ∀ᶠ t : ℝ in atTop, ξ ((t : ℂ)) = ξ z₀ := by
    filter_upwards [hray] with t ht
    exact const_of_pow_eq_one hVc hξc (by positivity) hpow ht hz₀
  have hlim' : Tendsto (fun t : ℝ => ξ ((t : ℂ))) atTop (𝓝 1) :=
    tendsto_explicitBranch_div_bottcherCoord c n
  have heq : Tendsto (fun _ : ℝ => ξ z₀) atTop (𝓝 1) := hlim'.congr' (hconst.mono (fun t h => h))
  have hξ1 : ξ z₀ = 1 := tendsto_nhds_unique tendsto_const_nhds heq
  exact (div_eq_one_iff_eq (bottcherCoord_ne_zero c z₀)).mp hξ1

/-- **The positive real ray lands in `explicitDomain c n` far enough out.** For large real `t`, the
orbit `f_c^[n](t)` is in the escape regime (`‖f^[n](t)‖ → ∞`) and in the slit plane
(`Re f^[n](t) > 0`, since `f^[n](t)/t^{2ⁿ} → 1` and `t^{2ⁿ} > 0`). So `(t:ℂ) ∈ explicitDomain c n`
eventually — the geometric input that makes the real ray a legitimate anchor region. -/
theorem eventually_ofReal_mem_explicitDomain (c : ℂ) (n : ℕ) :
    ∀ᶠ t : ℝ in atTop, (t : ℂ) ∈ explicitDomain c n := by
  have hesc : ∀ᶠ t : ℝ in atTop, (quadratic c)^[n] (t:ℂ) ∈ escapeOpen c := by
    have hnorm : Tendsto (fun t : ℝ => ‖(quadratic c)^[n] (t:ℂ)‖) atTop atTop :=
      tendsto_norm_cobounded_atTop.comp (tendsto_iterate_real_cobounded c n)
    filter_upwards [hnorm.eventually_gt_atTop (max 2 ‖c‖)] with t ht
    exact ht
  have hre : Tendsto (fun t : ℝ => ((quadratic c)^[n] (t:ℂ) / (t:ℂ)^(2^n)).re) atTop (𝓝 1) :=
    (Complex.continuous_re.continuousAt.tendsto).comp (tendsto_ratio_real c n)
  have hslit : ∀ᶠ t : ℝ in atTop, (quadratic c)^[n] (t:ℂ) ∈ Complex.slitPlane := by
    filter_upwards [hre.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 1)),
      eventually_gt_atTop 0] with t hrt ht
    have hfn : (quadratic c)^[n] (t:ℂ) = ((t:ℂ)^(2^n)) * ((quadratic c)^[n] (t:ℂ) / (t:ℂ)^(2^n)) := by
      have hzpow : (t:ℂ)^(2^n) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))
      field_simp
    have hreal : ((t:ℂ)^(2^n)) = (((t^(2^n) : ℝ)) : ℂ) := by push_cast; ring
    rw [Complex.mem_slitPlane_iff]; left
    rw [hreal] at hrt
    rw [hfn, hreal, Complex.re_ofReal_mul]
    exact mul_pos (by positivity) hrt
  filter_upwards [hesc, hslit] with t h1 h2
  exact ⟨h1, h2⟩

/-- **The explicit `2ⁿ`-th-root branch equals the Böttcher coordinate along the whole positive real ray**
(far enough out): `eb(n)(t) = φ_c(t)` for all large real `t`. The anchor region is the ray far field
`V = ofReal '' Ioi T` — preconnected, inside `explicitDomain c n ∩ escapeOpen c` past `T`, with the real
ray eventually in it — so `explicitBranch_eq_bottcherCoord_of_realray` pins the `ζ = 1` sheet there. This
is the concrete far-field anchor point the basin-branch colimit is launched from. -/
theorem eventually_explicitBranch_eq_bottcherCoord_real (c : ℂ) (n : ℕ) :
    ∀ᶠ t : ℝ in atTop, explicitBranch c n (t:ℂ) = bottcherCoord c (t:ℂ) := by
  obtain ⟨T₁, hT₁⟩ := (eventually_ofReal_mem_explicitDomain c n).exists_forall_of_atTop
  set T : ℝ := max T₁ (max 2 ‖c‖) with hT
  have hT1le : T₁ ≤ T := hT ▸ le_max_left _ _
  have hTc : max 2 ‖c‖ ≤ T := hT ▸ le_max_right _ _
  set V : Set ℂ := (Complex.ofReal) '' (Set.Ioi T) with hVdef
  have hVc : IsPreconnected V := (isPreconnected_Ioi).image _ continuous_ofReal.continuousOn
  have hVdom : V ⊆ explicitDomain c n := by
    rintro z ⟨t, ht, rfl⟩
    exact hT₁ t (le_of_lt (lt_of_le_of_lt hT1le ht))
  have hVesc : V ⊆ escapeOpen c := by
    rintro z ⟨t, ht, rfl⟩
    have htpos : 0 < t := lt_of_le_of_lt (le_trans (by norm_num) (le_trans (le_max_left _ _) hTc)) ht
    show max 2 ‖c‖ < ‖(t:ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt htpos)]
    exact lt_of_le_of_lt hTc ht
  have hray : ∀ᶠ t : ℝ in atTop, (t : ℂ) ∈ V := by
    filter_upwards [eventually_gt_atTop T] with t ht
    exact ⟨t, ht, rfl⟩
  filter_upwards [eventually_gt_atTop T] with t ht
  exact explicitBranch_eq_bottcherCoord_of_realray c n hVc hVdom hVesc hray ⟨t, ht, rfl⟩

end Bottcher

namespace Bottcher

/-- **Transition square-defect along the real far-field ray.**
If `ψ₁` is the far inverse of `φ_{c₁}`, then along `w=φ_{c₁}(t)` with `t → +∞`, the transition
function `H(w)=φ_{c₂}(ψ₁(w))` satisfies
`H(w²)-H(w)² → c₁-c₂`.

This turns the pointwise defect identity into an actual asymptotic signal for the direct
`H(w)`-transcendence route. -/
theorem tendsto_value_transition_square_defect_along_real_bottcher_ray
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {R : ℝ}
    (hψleft : ∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) :
    Tendsto (fun t : ℝ =>
      bottcherCoord c₂ (ψ₁ ((bottcherCoord c₁ (t : ℂ)) ^ 2)) -
        (bottcherCoord c₂ (ψ₁ (bottcherCoord c₁ (t : ℂ)))) ^ 2)
      atTop (𝓝 (c₁ - c₂)) := by
  have hdefect : Tendsto (fun t : ℝ => bottcherCoord c₂ (quadratic c₁ (t : ℂ)) -
        bottcherCoord c₂ (quadratic c₂ (t : ℂ))) atTop (𝓝 (c₁ - c₂)) := by
    let E₁ : ℝ → ℂ := fun t => bottcherCoord c₂ (quadratic c₁ (t : ℂ)) - quadratic c₁ (t : ℂ)
    let E₂ : ℝ → ℂ := fun t => bottcherCoord c₂ (quadratic c₂ (t : ℂ)) - quadratic c₂ (t : ℂ)
    have hE₁ : Tendsto E₁ atTop (𝓝 0) :=
      ((tendsto_bottcherCoord_sub_id c₂).comp (tendsto_sq_add_cobounded c₁)).comp
        tendsto_ofReal_cobounded
    have hE₂ : Tendsto E₂ atTop (𝓝 0) :=
      ((tendsto_bottcherCoord_sub_id c₂).comp (tendsto_sq_add_cobounded c₂)).comp
        tendsto_ofReal_cobounded
    have hmain : Tendsto (fun t => E₁ t - E₂ t + (c₁ - c₂)) atTop (𝓝 (c₁ - c₂)) := by
      simpa using (hE₁.sub hE₂).add tendsto_const_nhds
    convert hmain using 1
    funext t
    simp [E₁, E₂, quadratic]
    ring
  have hev : (fun t : ℝ =>
      bottcherCoord c₂ (ψ₁ ((bottcherCoord c₁ (t : ℂ)) ^ 2)) -
        (bottcherCoord c₂ (ψ₁ (bottcherCoord c₁ (t : ℂ)))) ^ 2)
      =ᶠ[atTop]
      (fun t : ℝ => bottcherCoord c₂ (quadratic c₁ (t : ℂ)) -
        bottcherCoord c₂ (quadratic c₂ (t : ℂ))) := by
    let T : ℝ := max 3 (max ‖c₁‖ (max ‖c₂‖ (R + ‖c₁‖ + 1)))
    filter_upwards [eventually_gt_atTop T] with t ht
    have ht3 : (3 : ℝ) < t := lt_of_le_of_lt (le_max_left _ _) ht
    have htpos : 0 < t := by linarith
    have hnormt : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt htpos)]
    have hc₁t : ‖c₁‖ ≤ ‖(t : ℂ)‖ := by
      rw [hnormt]
      exact le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 3 _)) ht)
    have hc₂t : ‖c₂‖ ≤ ‖(t : ℂ)‖ := by
      rw [hnormt]
      exact le_of_lt (lt_of_le_of_lt
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right 3 _))) ht)
    have h2t : 2 < ‖(t : ℂ)‖ := by rw [hnormt]; linarith
    have hRt : R < ‖(t : ℂ)‖ := by
      rw [hnormt]
      have hRle : R ≤ R + ‖c₁‖ + 1 := by nlinarith [norm_nonneg c₁]
      exact lt_of_le_of_lt hRle (lt_of_le_of_lt
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right 3 _))) ht)
    have hqR : R < ‖quadratic c₁ (t : ℂ)‖ := by
      have hlow : ‖(t : ℂ)‖ ^ 2 - ‖c₁‖ ≤ ‖quadratic c₁ (t : ℂ)‖ := by
        have h := norm_sub_le (quadratic c₁ (t : ℂ)) c₁
        rw [quadratic, add_sub_cancel_right, norm_pow] at h
        change ‖(t : ℂ)‖ ^ 2 - ‖c₁‖ ≤ ‖(t : ℂ) ^ 2 + c₁‖
        linarith
      have hRt2 : R < ‖(t : ℂ)‖ ^ 2 - ‖c₁‖ := by
        rw [hnormt]
        have hTtail : R + ‖c₁‖ + 1 < t := lt_of_le_of_lt
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right 3 _))) ht
        nlinarith
      exact lt_of_lt_of_le hRt2 hlow
    have hψt : ψ₁ (bottcherCoord c₁ (t : ℂ)) = (t : ℂ) := hψleft (t : ℂ) hRt
    have hφsq : bottcherCoord c₁ (quadratic c₁ (t : ℂ)) = (bottcherCoord c₁ (t : ℂ)) ^ 2 :=
      bottcherCoord_quadratic hc₁t h2t
    have hψsq : ψ₁ ((bottcherCoord c₁ (t : ℂ)) ^ 2) = quadratic c₁ (t : ℂ) := by
      rw [← hφsq]
      exact hψleft (quadratic c₁ (t : ℂ)) hqR
    have hφ₂sq : bottcherCoord c₂ (quadratic c₂ (t : ℂ)) = (bottcherCoord c₂ (t : ℂ)) ^ 2 :=
      bottcherCoord_quadratic hc₂t h2t
    rw [hψsq, hψt, ← hφ₂sq]
  exact hdefect.congr' hev.symm

end Bottcher

namespace Bottcher

/-- **Transferred quadratic asymptotic in the `c₁` value coordinate.**
Along `w=φ_{c₁}(t)`, the `c₂` quadratic map transported into the `c₁` Böttcher-value coordinate has
leading defect `c₂-c₁`:
`φ₁(t²+c₂)-φ₁(t)² → c₂-c₁` as `t → +∞`. -/
theorem tendsto_transferred_quadratic_minus_square_along_real_bottcher_ray (c₁ c₂ : ℂ) :
    Tendsto (fun t : ℝ =>
      bottcherCoord c₁ (quadratic c₂ (t : ℂ)) - (bottcherCoord c₁ (t : ℂ)) ^ 2)
      atTop (𝓝 (c₂ - c₁)) := by
  have hdefect : Tendsto (fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
        bottcherCoord c₁ (quadratic c₁ (t : ℂ))) atTop (𝓝 (c₂ - c₁)) := by
    let E₂ : ℝ → ℂ := fun t => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) - quadratic c₂ (t : ℂ)
    let E₁ : ℝ → ℂ := fun t => bottcherCoord c₁ (quadratic c₁ (t : ℂ)) - quadratic c₁ (t : ℂ)
    have hE₂ : Tendsto E₂ atTop (𝓝 0) :=
      ((tendsto_bottcherCoord_sub_id c₁).comp (tendsto_sq_add_cobounded c₂)).comp
        tendsto_ofReal_cobounded
    have hE₁ : Tendsto E₁ atTop (𝓝 0) :=
      ((tendsto_bottcherCoord_sub_id c₁).comp (tendsto_sq_add_cobounded c₁)).comp
        tendsto_ofReal_cobounded
    have hmain : Tendsto (fun t => E₂ t - E₁ t + (c₂ - c₁)) atTop (𝓝 (c₂ - c₁)) := by
      simpa using (hE₂.sub hE₁).add tendsto_const_nhds
    convert hmain using 1
    funext t
    simp [E₂, E₁, quadratic]
    ring
  have hev : (fun t : ℝ =>
      bottcherCoord c₁ (quadratic c₂ (t : ℂ)) - (bottcherCoord c₁ (t : ℂ)) ^ 2)
      =ᶠ[atTop]
      (fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
        bottcherCoord c₁ (quadratic c₁ (t : ℂ))) := by
    let T : ℝ := max 3 ‖c₁‖
    filter_upwards [eventually_gt_atTop T] with t ht
    have ht3 : (3 : ℝ) < t := lt_of_le_of_lt (le_max_left _ _) ht
    have htpos : 0 < t := by linarith
    have hnormt : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt htpos)]
    have hc₁t : ‖c₁‖ ≤ ‖(t : ℂ)‖ := by
      rw [hnormt]
      exact le_of_lt (lt_of_le_of_lt (le_max_right 3 ‖c₁‖) ht)
    have h2t : 2 < ‖(t : ℂ)‖ := by rw [hnormt]; linarith
    rw [bottcherCoord_quadratic hc₁t h2t]
  exact hdefect.congr' hev.symm

end Bottcher

namespace Bottcher

/-- **Quadratic-like weighted Laurent top peel.**
If `x → 0`, `S x → 1`, and an exact filtered relation
`∑ A_w(x) x^(W-w) S(x)^w = 0` holds eventually, then the top coefficient `A_W(0)` vanishes.

This is the Böttcher-side Laurent extraction for a transported coordinate with
`T(1/x) = x⁻² S(x)` and `S(x) → 1`; it is the weighted analogue of the Hurwitz Laurent peel. -/
theorem quadraticLike_weighted_filtration_top {W : ℕ} {A : Fin (W + 1) → ℂ → ℂ} {S : ℂ → ℂ}
    {l : Filter ℂ} [l.NeBot]
    (hid : Tendsto (fun x : ℂ => x) l (𝓝 0))
    (hS : Tendsto S l (𝓝 1))
    (hA : ∀ w : Fin (W + 1), Tendsto (A w) l (𝓝 (A w 0)))
    (hrel : ∀ᶠ x in l,
      ∑ w : Fin (W + 1), A w x * x ^ (W - (w : ℕ)) * (S x) ^ (w : ℕ) = 0) :
    A (Fin.last W) 0 = 0 := by
  have hterm : ∀ w : Fin (W + 1),
      Tendsto (fun x => A w x * x ^ (W - (w : ℕ)) * (S x) ^ (w : ℕ)) l
        (𝓝 (if w = Fin.last W then A (Fin.last W) 0 else 0)) := by
    intro w
    have hSw : Tendsto (fun x => (S x) ^ (w : ℕ)) l (𝓝 (1 ^ (w : ℕ))) := hS.pow (w : ℕ)
    by_cases hw : w = Fin.last W
    · subst hw
      simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one]
      simpa using (hA _).mul hSw
    · rw [if_neg hw]
      have hlt : (w : ℕ) < W := by
        have hwlt := w.isLt
        have hne : (w : ℕ) ≠ W := fun hc => hw (Fin.ext (by rw [Fin.val_last]; exact hc))
        omega
      have hpow : Tendsto (fun x : ℂ => x ^ (W - (w : ℕ))) l (𝓝 0) := by
        have hp := hid.pow (W - (w : ℕ))
        rwa [zero_pow (by omega : W - (w : ℕ) ≠ 0)] at hp
      have hAw := (hA w).mul hpow
      have hall := hAw.mul hSw
      simpa [mul_assoc] using hall
  have hsum := tendsto_finsetSum Finset.univ (fun w _ => hterm w)
  rw [Finset.sum_ite_eq' Finset.univ (Fin.last W) (fun _ => A (Fin.last W) 0)] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hzero : Tendsto
      (fun x => ∑ w : Fin (W + 1), A w x * x ^ (W - (w : ℕ)) * (S x) ^ (w : ℕ)) l
      (𝓝 0) := tendsto_const_nhds.congr' (hrel.mono fun x hx => hx.symm)
  exact tendsto_nhds_unique hsum hzero

end Bottcher

namespace Bottcher

/-- `(t : ℂ)⁻¹ → 0` as real `t → +∞`. -/
theorem tendsto_inv_ofReal_atTop_bottcher : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  simp only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] at h
  exact h

/-- **Böttcher coordinate has unit scale on the positive real ray.**
`φ_c(t)/t → 1` as `t → +∞`. -/
theorem tendsto_bottcherCoord_real_div_atTop (c : ℂ) :
    Tendsto (fun t : ℝ => bottcherCoord c (t : ℂ) / (t : ℂ)) atTop (𝓝 1) := by
  have hE : Tendsto (fun t : ℝ => bottcherCoord c (t : ℂ) - (t : ℂ)) atTop (𝓝 0) :=
    (tendsto_bottcherCoord_sub_id c).comp tendsto_ofReal_cobounded
  have hprod : Tendsto
      (fun t : ℝ => (bottcherCoord c (t : ℂ) - (t : ℂ)) * ((t : ℂ)⁻¹)) atTop (𝓝 0) := by
    simpa using hE.mul tendsto_inv_ofReal_atTop_bottcher
  have heq : (fun t : ℝ => bottcherCoord c (t : ℂ) / (t : ℂ))
      =ᶠ[atTop] (fun t : ℝ => 1 + (bottcherCoord c (t : ℂ) - (t : ℂ)) * ((t : ℂ)⁻¹)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    field_simp [htne]
    ring
  rw [tendsto_congr' heq]
  simpa using tendsto_const_nhds.add hprod

/-- **Transferred quadratic has unit weighted scale on the positive real ray.**
`φ_{c₁}(t²+c₂)/t² → 1` as `t → +∞`. -/
theorem tendsto_transferred_quadratic_real_div_sq_atTop (c₁ c₂ : ℂ) :
    Tendsto (fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2))
      atTop (𝓝 1) := by
  have hE : Tendsto (fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) - quadratic c₂ (t : ℂ))
      atTop (𝓝 0) :=
    ((tendsto_bottcherCoord_sub_id c₁).comp (tendsto_sq_add_cobounded c₂)).comp
      tendsto_ofReal_cobounded
  have hinv : Tendsto (fun t : ℝ => ((t : ℂ) ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa [inv_pow] using (tendsto_inv_ofReal_atTop_bottcher.pow 2)
  have hsmall : Tendsto
      (fun t : ℝ => (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) - quadratic c₂ (t : ℂ)) *
        (((t : ℂ) ^ 2)⁻¹)) atTop (𝓝 0) := by
    simpa using hE.mul hinv
  have hconst : Tendsto (fun t : ℝ => c₂ * (((t : ℂ) ^ 2)⁻¹)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have heq : (fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2))
      =ᶠ[atTop] (fun t : ℝ => 1 +
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) - quadratic c₂ (t : ℂ)) * (((t : ℂ) ^ 2)⁻¹)
          + c₂ * (((t : ℂ) ^ 2)⁻¹)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have ht2ne : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ htne
    field_simp [ht2ne]
    rw [quadratic]
    ring
  rw [tendsto_congr' heq]
  simpa using (tendsto_const_nhds.add hsmall).add hconst

end Bottcher

namespace Bottcher

/-- **Finite weighted top extraction.**
If `x → 0`, the two scaled factors `P,Q → 1`, all monomials have weighted degree
`I k + 2 J k ≤ W`, and the weighted relation
`∑ a_k x^(W-(I_k+2J_k)) P^I_k Q^J_k = 0` holds eventually, then the top weighted
coefficient sum vanishes. This is the finite Laurent gate used after pulling a transported Böttcher
relation back to the real far ray and dividing by `t^W`. -/
theorem weighted_top_sum_zero_of_eventual_relation_filter {α ι : Type*} [Fintype ι]
    {l : Filter α} [l.NeBot]
    {W : ℕ} {a : ι → ℂ} {I J : ι → ℕ} {x P Q : α → ℂ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hx : Tendsto x l (𝓝 0))
    (hP : Tendsto P l (𝓝 1))
    (hQ : Tendsto Q l (𝓝 1))
    (hrel : ∀ᶠ t in l,
      ∑ k : ι, a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k = 0) :
    ∑ k : ι, (if I k + 2 * J k = W then a k else 0) = 0 := by
  have hterm : ∀ k : ι,
      Tendsto (fun t : α => a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) l
        (𝓝 (if I k + 2 * J k = W then a k else 0)) := by
    intro k
    by_cases hk : I k + 2 * J k = W
    · have hxpow : Tendsto (fun t : α => x t ^ (W - (I k + 2 * J k))) l (𝓝 1) := by
        rw [hk, Nat.sub_self]
        simp
      have hlim := (((tendsto_const_nhds (x := a k)).mul hxpow).mul (hP.pow (I k))).mul (hQ.pow (J k))
      rw [if_pos hk]
      simpa using hlim
    · have hlt : I k + 2 * J k < W := Nat.lt_of_le_of_ne (hweight k) hk
      have hxpow : Tendsto (fun t : α => x t ^ (W - (I k + 2 * J k))) l (𝓝 0) := by
        have hp := hx.pow (W - (I k + 2 * J k))
        rwa [zero_pow (by omega : W - (I k + 2 * J k) ≠ 0)] at hp
      have hlim := (((tendsto_const_nhds (x := a k)).mul hxpow).mul (hP.pow (I k))).mul (hQ.pow (J k))
      rw [if_neg hk]
      simpa using hlim
  have hsum := tendsto_finsetSum Finset.univ (fun k _ => hterm k)
  have hzero : Tendsto
      (fun t : α => ∑ k : ι, a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) l
      (𝓝 0) := tendsto_const_nhds.congr' (hrel.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique hsum hzero

/-- **Böttcher real-ray weighted top extraction.**
For the transported quadratic pair
`P(t)=φ_{c₁}(t)/t`, `Q(t)=φ_{c₁}(t²+c₂)/t²`, both scaled factors tend to `1`; hence any eventual
weighted relation in the divided form forces its top weighted coefficient sum to vanish. -/
theorem bottcher_weighted_top_sum_zero_of_eventual_relation
    (c₁ c₂ : ℂ) {ι : Type*} [Fintype ι]
    {W : ℕ} {a : ι → ℂ} {I J : ι → ℕ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hrel : ∀ᶠ t : ℝ in atTop,
      ∑ k : ι, a k * ((t : ℂ)⁻¹) ^ (W - (I k + 2 * J k)) *
        (bottcherCoord c₁ (t : ℂ) / (t : ℂ)) ^ I k *
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2)) ^ J k = 0) :
    ∑ k : ι, (if I k + 2 * J k = W then a k else 0) = 0 := by
  exact weighted_top_sum_zero_of_eventual_relation_filter
    (l := (atTop : Filter ℝ)) (W := W) (a := a) (I := I) (J := J)
    (x := fun t : ℝ => ((t : ℂ)⁻¹))
    (P := fun t : ℝ => bottcherCoord c₁ (t : ℂ) / (t : ℂ))
    (Q := fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2))
    hweight tendsto_inv_ofReal_atTop_bottcher (tendsto_bottcherCoord_real_div_atTop c₁)
    (tendsto_transferred_quadratic_real_div_sq_atTop c₁ c₂) hrel

end Bottcher

namespace Bottcher

/-- Scaling one weighted monomial by `t^{-W}`. -/
lemma weighted_scale_term_identity {z A B a : ℂ} {i j W : ℕ} (hw : i + 2 * j ≤ W) :
    a * z⁻¹ ^ (W - (i + 2 * j)) * (A / z) ^ i * (B / z ^ 2) ^ j =
      z⁻¹ ^ W * (a * A ^ i * B ^ j) := by
  rw [div_eq_mul_inv A z, div_eq_mul_inv B (z ^ 2), mul_pow, mul_pow]
  rw [show (z ^ 2)⁻¹ = z⁻¹ ^ 2 by rw [inv_pow]]
  have hpow : z⁻¹ ^ (W - (i + 2 * j)) * z⁻¹ ^ i * (z⁻¹ ^ 2) ^ j = z⁻¹ ^ W := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [show a * z⁻¹ ^ (W - (i + 2 * j)) * (A ^ i * z⁻¹ ^ i) * (B ^ j * (z⁻¹ ^ 2) ^ j)
        = (z⁻¹ ^ (W - (i + 2 * j)) * z⁻¹ ^ i * (z⁻¹ ^ 2) ^ j) * (a * A ^ i * B ^ j) by ring]
  rw [hpow]

/-- **Raw Böttcher real-ray weighted top extraction.**
If a finite raw relation in `φ_{c₁}(t)` and `φ_{c₁}(t²+c₂)` holds eventually on the positive real ray
and every monomial has weighted degree `i+2j ≤ W`, then the top weighted coefficient sum is zero.
This is the directly usable Laurent gate for a pulled-back transported-map relation. -/
theorem bottcher_weighted_top_sum_zero_of_raw_eventual_relation
    (c₁ c₂ : ℂ) {ι : Type*} [Fintype ι]
    {W : ℕ} {a : ι → ℂ} {I J : ι → ℕ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hraw : ∀ᶠ t : ℝ in atTop,
      ∑ k : ι, a k * (bottcherCoord c₁ (t : ℂ)) ^ I k *
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) ^ J k = 0) :
    ∑ k : ι, (if I k + 2 * J k = W then a k else 0) = 0 := by
  refine bottcher_weighted_top_sum_zero_of_eventual_relation c₁ c₂ hweight ?_
  filter_upwards [hraw] with t hrawt
  have hscaled :
      (∑ k : ι, a k * ((t : ℂ)⁻¹) ^ (W - (I k + 2 * J k)) *
        (bottcherCoord c₁ (t : ℂ) / (t : ℂ)) ^ I k *
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2)) ^ J k)
        = ((t : ℂ)⁻¹) ^ W *
          (∑ k : ι, a k * (bottcherCoord c₁ (t : ℂ)) ^ I k *
            (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) ^ J k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    exact weighted_scale_term_identity (z := (t : ℂ))
      (A := bottcherCoord c₁ (t : ℂ))
      (B := bottcherCoord c₁ (quadratic c₂ (t : ℂ)))
      (a := a k) (i := I k) (j := J k) (W := W) (hweight k)
  rw [hscaled, hrawt, mul_zero]

end Bottcher

namespace Bottcher

/-- Expand a bivariate polynomial `R(W,Z)` into its nested coefficient sum. -/
lemma eval₂_eq_sum_coeff_fin (R : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    R.eval₂ (Polynomial.evalRingHom x) y =
      ∑ j : Fin (R.natDegree + 1),
        ∑ i : Fin ((R.coeff (j : ℕ)).natDegree + 1),
          (R.coeff (j : ℕ)).coeff (i : ℕ) * x ^ (i : ℕ) * y ^ (j : ℕ) := by
  rw [Polynomial.eval₂_eq_sum_range]
  conv_rhs =>
    rw [Fin.sum_univ_eq_sum_range
      (fun j => ∑ i : Fin ((R.coeff j).natDegree + 1),
        (R.coeff j).coeff (i : ℕ) * x ^ (i : ℕ) * y ^ j)
      (R.natDegree + 1)]
  refine Finset.sum_congr rfl ?_
  intro j _
  change (R.coeff j).eval x * y ^ j = ∑ i : Fin ((R.coeff j).natDegree + 1),
      (R.coeff j).coeff (i : ℕ) * x ^ (i : ℕ) * y ^ j
  rw [Polynomial.eval_eq_sum_range]
  conv_rhs =>
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (R.coeff j).coeff i * x ^ i * y ^ j)
      ((R.coeff j).natDegree + 1)]
  rw [Finset.sum_mul]

end Bottcher

namespace Bottcher

/-- **Polynomial Böttcher real-ray weighted top extraction.**
If a bivariate polynomial relation `R(φ_{c₁}(t), φ_{c₁}(t²+c₂))=0` holds eventually on the positive
real ray and all retained coefficient monomials have weighted degree `i+2j ≤ W`, then the top weighted
coefficient slice of `R` vanishes. This is the polynomial-form Laurent obstruction for the transported
quadratic relation. -/
theorem bottcher_weighted_top_sum_zero_of_polynomial_eventual_relation
    (c₁ c₂ : ℂ) (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hrel : ∀ᶠ t : ℝ in atTop,
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) = 0) :
    ∑ s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)),
      (if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
        (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0) = 0 := by
  refine bottcher_weighted_top_sum_zero_of_raw_eventual_relation c₁ c₂
    (ι := Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)))
    (W := W)
    (a := fun s => (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ))
    (I := fun s => (s.2 : ℕ)) (J := fun s => (s.1 : ℕ)) ?_ ?_
  · intro s
    exact hweight s.1 s.2
  · filter_upwards [hrel] with t ht
    rw [← ht]
    rw [eval₂_eq_sum_coeff_fin]
    rw [Fintype.sum_sigma]

end Bottcher

namespace Bottcher

/-- **First Laurent coefficient of the Böttcher coordinate on the positive real ray.**
The functional equation and normalization force
`t * (φ_c(t)-t) → c/2`. This is the next coefficient after `φ_c(t)/t → 1` and is the first
nontrivial Laurent datum needed for sharper transported-quadratic descent. -/
theorem tendsto_real_mul_bottcherCoord_sub_id_atTop (c : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) * (bottcherCoord c (t : ℂ) - (t : ℂ))) atTop (𝓝 (c / 2)) := by
  let E : ℝ → ℂ := fun t => bottcherCoord c (quadratic c (t : ℂ)) - quadratic c (t : ℂ)
  have hE : Tendsto E atTop (𝓝 0) :=
    ((tendsto_bottcherCoord_sub_id c).comp (tendsto_sq_add_cobounded c)).comp tendsto_ofReal_cobounded
  have hdelta : Tendsto (fun t : ℝ => bottcherCoord c (t : ℂ) - (t : ℂ)) atTop (𝓝 0) :=
    (tendsto_bottcherCoord_sub_id c).comp tendsto_ofReal_cobounded
  have hsquare : Tendsto (fun t : ℝ => (bottcherCoord c (t : ℂ) - (t : ℂ)) ^ 2) atTop (𝓝 0) := by
    simpa using hdelta.pow 2
  have htwice : Tendsto (fun t : ℝ => 2 * ((t : ℂ) * (bottcherCoord c (t : ℂ) - (t : ℂ))))
      atTop (𝓝 c) := by
    have hrhs : Tendsto (fun t : ℝ => E t - (bottcherCoord c (t : ℂ) - (t : ℂ)) ^ 2 + c)
        atTop (𝓝 c) := by
      simpa using (hE.sub hsquare).add tendsto_const_nhds
    refine hrhs.congr' ?_
    let T : ℝ := max 3 ‖c‖
    filter_upwards [eventually_gt_atTop T] with t ht
    have ht3 : (3 : ℝ) < t := lt_of_le_of_lt (le_max_left _ _) ht
    have htpos : 0 < t := by linarith
    have hnormt : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt htpos)]
    have hct : ‖c‖ ≤ ‖(t : ℂ)‖ := by
      rw [hnormt]
      exact le_of_lt (lt_of_le_of_lt (le_max_right 3 ‖c‖) ht)
    have h2t : 2 < ‖(t : ℂ)‖ := by rw [hnormt]; linarith
    have hfe := bottcherCoord_quadratic (c := c) hct h2t
    simp [quadratic] at hfe
    dsimp [E]
    rw [hfe]
    ring
  have hhalf := htwice.const_mul ((2 : ℂ)⁻¹)
  convert hhalf using 1
  · funext t; ring
  · field_simp

/-- Quantitative normalization estimate for the Böttcher coordinate:
`‖φ_c(z)-z‖ ≤ 4‖c‖/‖z‖` deep in the escape regime. -/
theorem norm_bottcherCoord_sub_id_le {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ‖bottcherCoord c z - z‖ ≤ 4 * ‖c‖ / ‖z‖ := by
  have hzpos : (0 : ℝ) < ‖z‖ := lt_trans (by norm_num) hz
  have hzne : z ≠ 0 := by intro h; rw [h, norm_zero] at hzpos; linarith
  set S := ∑' k, bottcherLogTerm c z k with hSdef
  have hSbd : ‖S‖ ≤ 2 * ‖c‖ / ‖z‖ ^ 2 := by
    have h := norm_bottcherLog_sub_log_le hc hz
    rw [bottcherLog, add_sub_cancel_left] at h
    rw [hSdef]
    exact h
  have hSle1 : ‖S‖ ≤ 1 := by
    have h2 : 2 * ‖c‖ / ‖z‖ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hc, hz, norm_nonneg z]
    linarith
  rw [bottcherCoord_eq_mul_exp hzne, ← hSdef,
    show z * Complex.exp S - z = z * (Complex.exp S - 1) by ring, norm_mul]
  calc
    ‖z‖ * ‖Complex.exp S - 1‖
        ≤ ‖z‖ * (2 * ‖S‖) := by
          gcongr
          exact Complex.norm_exp_sub_one_le hSle1
    _ ≤ ‖z‖ * (2 * (2 * ‖c‖ / ‖z‖ ^ 2)) := by gcongr
    _ = 4 * ‖c‖ / ‖z‖ := by field_simp; ring

/-- `t²+a` has unit quadratic scale on the positive real ray. -/
theorem tendsto_quadratic_real_div_sq_atTop (a : ℂ) :
    Tendsto (fun t : ℝ => quadratic a (t : ℂ) / ((t : ℂ) ^ 2)) atTop (𝓝 1) := by
  have hinv2 : Tendsto (fun t : ℝ => (((t : ℂ) ^ 2)⁻¹)) atTop (𝓝 0) := by
    simpa [inv_pow] using (tendsto_inv_ofReal_atTop_bottcher.pow 2)
  have hconst : Tendsto (fun t : ℝ => a * (((t : ℂ) ^ 2)⁻¹)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv2
  have heq : (fun t : ℝ => quadratic a (t : ℂ) / ((t : ℂ) ^ 2))
      =ᶠ[atTop] (fun t : ℝ => 1 + a * (((t : ℂ) ^ 2)⁻¹)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have ht2ne : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ htne
    rw [quadratic]
    field_simp [ht2ne]
  rw [tendsto_congr' heq]
  simpa using tendsto_const_nhds.add hconst

/-- Along every quadratic real ray, the Böttcher normalization error is `o(1/t)`. -/
theorem tendsto_real_mul_bottcherCoord_quadratic_sub_quadratic_atTop (c a : ℂ) :
    Tendsto (fun t : ℝ =>
      (t : ℂ) * (bottcherCoord c (quadratic a (t : ℂ)) - quadratic a (t : ℂ))) atTop
      (𝓝 0) := by
  let Z : ℝ → ℂ := fun t => quadratic a (t : ℂ)
  have hZcob : Tendsto Z atTop (cobounded ℂ) :=
    (tendsto_sq_add_cobounded a).comp tendsto_ofReal_cobounded
  have hratio : Tendsto (fun t : ℝ => (t : ℂ) / Z t) atTop (𝓝 0) := by
    have hnum : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_ofReal_atTop_bottcher
    have hden : Tendsto (fun t : ℝ => Z t / ((t : ℂ) ^ 2)) atTop (𝓝 1) :=
      tendsto_quadratic_real_div_sq_atTop a
    have hdiv := hnum.div hden (by norm_num : (1 : ℂ) ≠ 0)
    have heqratio :
        ((fun t : ℝ => ((t : ℂ)⁻¹)) / fun t : ℝ => Z t / ((t : ℂ) ^ 2))
          =ᶠ[atTop] (fun t : ℝ => (t : ℂ) / Z t) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ),
        hden.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with t ht hZratio_ne
      have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      have ht2ne : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ htne
      have hZne : Z t ≠ 0 := by
        intro h
        exact hZratio_ne (by rw [h, zero_div])
      change ((t : ℂ)⁻¹) / (Z t / ((t : ℂ) ^ 2)) = (t : ℂ) / Z t
      field_simp [Z, htne, ht2ne, hZne]
    simpa using hdiv.congr' heqratio
  have hbd : Tendsto (fun t : ℝ => 4 * ‖c‖ * ‖(t : ℂ) / Z t‖) atTop (𝓝 0) := by
    have hn := (continuous_norm.tendsto 0).comp hratio
    simpa using tendsto_const_nhds.mul hn
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hZcob.eventually (tendsto_norm_cobounded_atTop.eventually_gt_atTop (max 2 ‖c‖))]
    with t htZ
  have hcZ : ‖c‖ ≤ ‖Z t‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) htZ)
  have h2Z : 2 < ‖Z t‖ := lt_of_le_of_lt (le_max_left _ _) htZ
  have hZne : Z t ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2Z
    norm_num at h2Z
  have hnorm := norm_bottcherCoord_sub_id_le (c := c) (z := Z t) hcZ h2Z
  calc
    ‖(t : ℂ) * (bottcherCoord c (Z t) - Z t)‖
        = ‖(t : ℂ)‖ * ‖bottcherCoord c (Z t) - Z t‖ := by rw [norm_mul]
    _ ≤ ‖(t : ℂ)‖ * (4 * ‖c‖ / ‖Z t‖) := by gcongr
    _ = 4 * ‖c‖ * ‖(t : ℂ) / Z t‖ := by
      rw [norm_div]
      field_simp [norm_ne_zero_iff.mpr hZne]

/-- The transported shifted-parabola defect gains one inverse power:
`t * (φ_{c₁}(t²+c₂) - (φ_{c₁}(t)^2 + c₂-c₁)) → 0`. -/
theorem tendsto_real_mul_transported_quadratic_defect_atTop (c₁ c₂ : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
        ((bottcherCoord c₁ (t : ℂ)) ^ 2 + (c₂ - c₁)))) atTop (𝓝 0) := by
  have h₂ := tendsto_real_mul_bottcherCoord_quadratic_sub_quadratic_atTop c₁ c₂
  have h₁ := tendsto_real_mul_bottcherCoord_quadratic_sub_quadratic_atTop c₁ c₁
  have hsub := h₂.sub h₁
  have heqdef :
      (fun t : ℝ =>
        (t : ℂ) * (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) - quadratic c₂ (t : ℂ)) -
          (t : ℂ) * (bottcherCoord c₁ (quadratic c₁ (t : ℂ)) - quadratic c₁ (t : ℂ)))
        =ᶠ[atTop]
      (fun t : ℝ => (t : ℂ) *
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
          ((bottcherCoord c₁ (t : ℂ)) ^ 2 + (c₂ - c₁)))) := by
    let T : ℝ := max 3 ‖c₁‖
    filter_upwards [eventually_gt_atTop T] with t ht
    have htpos : 0 < t := by
      have h3 : (3 : ℝ) < t := lt_of_le_of_lt (le_max_left _ _) ht
      linarith
    have hnormt : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt htpos)]
    have hc₁t : ‖c₁‖ ≤ ‖(t : ℂ)‖ := by
      rw [hnormt]
      exact le_of_lt (lt_of_le_of_lt (le_max_right 3 ‖c₁‖) ht)
    have h2t : 2 < ‖(t : ℂ)‖ := by
      rw [hnormt]
      have h3 : (3 : ℝ) < t := lt_of_le_of_lt (le_max_left _ _) ht
      linarith
    have hfe := bottcherCoord_quadratic (c := c₁) hc₁t h2t
    have hfe' : bottcherCoord c₁ ((t : ℂ) ^ 2 + c₁) = bottcherCoord c₁ (t : ℂ) ^ 2 := by
      simpa [quadratic] using hfe
    dsimp [quadratic]
    rw [hfe']
    ring
  simpa using hsub.congr' heqdef

end Bottcher

namespace Bottcher

/-- The positive real ray is eventually far both in the source coordinate and in Böttcher value. -/
theorem eventually_real_mem_bottcher_pullback_far (c : ℂ) (Rfar R' : ℝ) :
    ∀ᶠ t : ℝ in atTop, Rfar < ‖(t : ℂ)‖ ∧ R' < ‖bottcherCoord c (t : ℂ)‖ := by
  have hratio : Tendsto
      ((fun z : ℂ => ‖z‖) ∘ fun t : ℝ => bottcherCoord c (t : ℂ) / (t : ℂ))
      atTop (𝓝 1) := by
    simpa using (continuous_norm.continuousAt.tendsto).comp (tendsto_bottcherCoord_real_div_atTop c)
  filter_upwards [eventually_gt_atTop (max 1 (max Rfar (2 * R'))),
    hratio.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with t ht hratio_gt
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt (lt_of_le_of_lt (le_max_left _ _) ht))
  have hnormt : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt htpos)]
  constructor
  · rw [hnormt]
    exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 1 _)) ht
  · have htR : R' < t / 2 := by
      have h2Rle : 2 * R' ≤ max Rfar (2 * R') := le_max_right _ _
      have hle : 2 * R' ≤ max 1 (max Rfar (2 * R')) := le_trans h2Rle (le_max_right _ _)
      nlinarith
    have hnorm_ratio : ‖bottcherCoord c (t : ℂ) / (t : ℂ)‖ = ‖bottcherCoord c (t : ℂ)‖ / t := by
      rw [norm_div, hnormt]
    change (1 / 2 : ℝ) < ‖bottcherCoord c (t : ℂ) / (t : ℂ)‖ at hratio_gt
    rw [hnorm_ratio] at hratio_gt
    have hmul : t / 2 < ‖bottcherCoord c (t : ℂ)‖ := by
      have hmul' := mul_lt_mul_of_pos_right hratio_gt htpos
      rw [div_mul_cancel₀ _ (ne_of_gt htpos)] at hmul'
      linarith
    exact lt_trans htR hmul

end Bottcher

namespace Bottcher

/-- **Finite weighted top extraction with a vanishing tail.**
The divided weighted relation may carry an extra term tending to `0`; it still cannot contribute to the
top weighted coefficient. This is the tail-aware form needed after subtracting a shifted parabola factor,
where the remaining error is multiplied by the small defect `Z(t)-W(t)^2-d`. -/
theorem weighted_top_sum_zero_of_eventual_relation_filter_with_tail {α ι : Type*} [Fintype ι]
    {l : Filter α} [l.NeBot]
    {W : ℕ} {a : ι → ℂ} {I J : ι → ℕ} {x P Q Tail : α → ℂ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hx : Tendsto x l (𝓝 0))
    (hP : Tendsto P l (𝓝 1))
    (hQ : Tendsto Q l (𝓝 1))
    (hTail : Tendsto Tail l (𝓝 0))
    (hrel : ∀ᶠ t in l,
      (∑ k : ι, a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) + Tail t = 0) :
    ∑ k : ι, (if I k + 2 * J k = W then a k else 0) = 0 := by
  have hterm : ∀ k : ι,
      Tendsto (fun t : α => a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) l
        (𝓝 (if I k + 2 * J k = W then a k else 0)) := by
    intro k
    by_cases hk : I k + 2 * J k = W
    · have hxpow : Tendsto (fun t : α => x t ^ (W - (I k + 2 * J k))) l (𝓝 1) := by
        rw [hk, Nat.sub_self]
        simp
      have hlim := (((tendsto_const_nhds (x := a k)).mul hxpow).mul (hP.pow (I k))).mul (hQ.pow (J k))
      rw [if_pos hk]
      simpa using hlim
    · have hlt : I k + 2 * J k < W := Nat.lt_of_le_of_ne (hweight k) hk
      have hxpow : Tendsto (fun t : α => x t ^ (W - (I k + 2 * J k))) l (𝓝 0) := by
        have hp := hx.pow (W - (I k + 2 * J k))
        rwa [zero_pow (by omega : W - (I k + 2 * J k) ≠ 0)] at hp
      have hlim := (((tendsto_const_nhds (x := a k)).mul hxpow).mul (hP.pow (I k))).mul (hQ.pow (J k))
      rw [if_neg hk]
      simpa using hlim
  have hsum := tendsto_finsetSum Finset.univ (fun k _ => hterm k)
  have htotal : Tendsto
      (fun t : α => (∑ k : ι, a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) + Tail t) l
      (𝓝 ((∑ k : ι, (if I k + 2 * J k = W then a k else 0)) + 0)) := hsum.add hTail
  have hzero : Tendsto
      (fun t : α => (∑ k : ι, a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) + Tail t) l
      (𝓝 0) := tendsto_const_nhds.congr' (hrel.mono fun t ht => ht.symm)
  simpa using tendsto_nhds_unique htotal hzero

/-- Böttcher real-ray weighted top extraction in divided form, with a vanishing divided tail. -/
theorem bottcher_weighted_top_sum_zero_of_eventual_relation_with_tail
    (c₁ c₂ : ℂ) {ι : Type*} [Fintype ι]
    {W : ℕ} {a : ι → ℂ} {I J : ι → ℕ} {Tail : ℝ → ℂ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hTail : Tendsto Tail atTop (𝓝 0))
    (hrel : ∀ᶠ t : ℝ in atTop,
      (∑ k : ι, a k * ((t : ℂ)⁻¹) ^ (W - (I k + 2 * J k)) *
        (bottcherCoord c₁ (t : ℂ) / (t : ℂ)) ^ I k *
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2)) ^ J k) + Tail t = 0) :
    ∑ k : ι, (if I k + 2 * J k = W then a k else 0) = 0 := by
  exact weighted_top_sum_zero_of_eventual_relation_filter_with_tail
    (l := (atTop : Filter ℝ)) (W := W) (a := a) (I := I) (J := J)
    (x := fun t : ℝ => ((t : ℂ)⁻¹))
    (P := fun t : ℝ => bottcherCoord c₁ (t : ℂ) / (t : ℂ))
    (Q := fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2))
    (Tail := Tail)
    hweight tendsto_inv_ofReal_atTop_bottcher (tendsto_bottcherCoord_real_div_atTop c₁)
    (tendsto_transferred_quadratic_real_div_sq_atTop c₁ c₂) hTail hrel

/-- Raw Böttcher relation with a tail whose weighted scaling tends to zero. -/
theorem bottcher_weighted_top_sum_zero_of_raw_eventual_relation_with_scaled_tail
    (c₁ c₂ : ℂ) {ι : Type*} [Fintype ι]
    {W : ℕ} {a : ι → ℂ} {I J : ι → ℕ} {Tail : ℝ → ℂ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hTail : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail t) atTop (𝓝 0))
    (hraw : ∀ᶠ t : ℝ in atTop,
      (∑ k : ι, a k * (bottcherCoord c₁ (t : ℂ)) ^ I k *
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) ^ J k) + Tail t = 0) :
    ∑ k : ι, (if I k + 2 * J k = W then a k else 0) = 0 := by
  refine bottcher_weighted_top_sum_zero_of_eventual_relation_with_tail c₁ c₂ hweight hTail ?_
  filter_upwards [hraw] with t hrawt
  have hscaled :
      (∑ k : ι, a k * ((t : ℂ)⁻¹) ^ (W - (I k + 2 * J k)) *
        (bottcherCoord c₁ (t : ℂ) / (t : ℂ)) ^ I k *
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2)) ^ J k)
        = ((t : ℂ)⁻¹) ^ W *
          (∑ k : ι, a k * (bottcherCoord c₁ (t : ℂ)) ^ I k *
            (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) ^ J k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    exact weighted_scale_term_identity (z := (t : ℂ))
      (A := bottcherCoord c₁ (t : ℂ))
      (B := bottcherCoord c₁ (quadratic c₂ (t : ℂ)))
      (a := a k) (i := I k) (j := J k) (W := W) (hweight k)
  rw [hscaled, ← mul_add, hrawt, mul_zero]

end Bottcher

namespace Bottcher

/-- Polynomial Böttcher weighted top extraction with a scaled tail. -/
theorem bottcher_weighted_top_sum_zero_of_polynomial_eventual_relation_with_scaled_tail
    (c₁ c₂ : ℂ) (R : Polynomial (Polynomial ℂ)) {W : ℕ} {Tail : ℝ → ℂ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hTail : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail t) atTop (𝓝 0))
    (hrel : ∀ᶠ t : ℝ in atTop,
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) + Tail t = 0) :
    ∑ s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)),
      (if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
        (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0) = 0 := by
  refine bottcher_weighted_top_sum_zero_of_raw_eventual_relation_with_scaled_tail c₁ c₂
    (ι := Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)))
    (W := W)
    (a := fun s => (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ))
    (I := fun s => (s.2 : ℕ)) (J := fun s => (s.1 : ℕ)) ?_ hTail ?_
  · intro s
    exact hweight s.1 s.2
  · filter_upwards [hrel] with t ht
    have hraweq :
        (∑ s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)),
          (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) *
            (bottcherCoord c₁ (t : ℂ)) ^ (s.2 : ℕ) *
            (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) ^ (s.1 : ℕ)) =
        R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
          (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) := by
      rw [eval₂_eq_sum_coeff_fin]
      rw [Fintype.sum_sigma]
    rw [hraweq]
    exact ht

end Bottcher

namespace Bottcher

/-- The divided finite weighted sum tends to its top weighted coefficient sum. -/
theorem weighted_sum_tendsto_top_filter {α ι : Type*} [Fintype ι]
    {l : Filter α} [l.NeBot]
    {W : ℕ} {a : ι → ℂ} {I J : ι → ℕ} {x P Q : α → ℂ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hx : Tendsto x l (𝓝 0))
    (hP : Tendsto P l (𝓝 1))
    (hQ : Tendsto Q l (𝓝 1)) :
    Tendsto (fun t : α =>
      ∑ k : ι, a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) l
      (𝓝 (∑ k : ι, (if I k + 2 * J k = W then a k else 0))) := by
  have hterm : ∀ k : ι,
      Tendsto (fun t : α => a k * x t ^ (W - (I k + 2 * J k)) * P t ^ I k * Q t ^ J k) l
        (𝓝 (if I k + 2 * J k = W then a k else 0)) := by
    intro k
    by_cases hk : I k + 2 * J k = W
    · have hxpow : Tendsto (fun t : α => x t ^ (W - (I k + 2 * J k))) l (𝓝 1) := by
        rw [hk, Nat.sub_self]
        simp
      have hlim := (((tendsto_const_nhds (x := a k)).mul hxpow).mul (hP.pow (I k))).mul (hQ.pow (J k))
      rw [if_pos hk]
      simpa using hlim
    · have hlt : I k + 2 * J k < W := Nat.lt_of_le_of_ne (hweight k) hk
      have hxpow : Tendsto (fun t : α => x t ^ (W - (I k + 2 * J k))) l (𝓝 0) := by
        have hp := hx.pow (W - (I k + 2 * J k))
        rwa [zero_pow (by omega : W - (I k + 2 * J k) ≠ 0)] at hp
      have hlim := (((tendsto_const_nhds (x := a k)).mul hxpow).mul (hP.pow (I k))).mul (hQ.pow (J k))
      rw [if_neg hk]
      simpa using hlim
  exact tendsto_finsetSum Finset.univ (fun k _ => hterm k)

/-- Böttcher divided weighted polynomial evaluation has a finite top-weight limit. -/
theorem bottcher_weighted_scaled_eval_tendsto_top_sum
    (c₁ c₂ : ℂ) (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W *
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)))) atTop
      (𝓝 (∑ s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)),
        (if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
          (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0))) := by
  have hdiv := weighted_sum_tendsto_top_filter
    (l := (atTop : Filter ℝ))
    (W := W)
    (a := fun s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)) =>
      (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ))
    (I := fun s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)) =>
      (s.2 : ℕ))
    (J := fun s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)) =>
      (s.1 : ℕ))
    (x := fun t : ℝ => ((t : ℂ)⁻¹))
    (P := fun t : ℝ => bottcherCoord c₁ (t : ℂ) / (t : ℂ))
    (Q := fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2))
    (fun s => hweight s.1 s.2)
    tendsto_inv_ofReal_atTop_bottcher (tendsto_bottcherCoord_real_div_atTop c₁)
    (tendsto_transferred_quadratic_real_div_sq_atTop c₁ c₂)
  refine hdiv.congr' ?_
  filter_upwards with t
  rw [eval₂_eq_sum_coeff_fin, Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact (weighted_scale_term_identity (z := (t : ℂ))
    (A := bottcherCoord c₁ (t : ℂ))
    (B := bottcherCoord c₁ (quadratic c₂ (t : ℂ)))
    (a := (R.coeff (j : ℕ)).coeff (i : ℕ))
    (i := (i : ℕ)) (j := (j : ℕ)) (W := W) (hweight j i))

/-- A univariate polynomial's leading term survives along any real-ray coordinate `A(t)` with
`A(t)/t → 1`.  This is the exact asymptotic gate needed for the shifted-parabola remainder:
once an exact-division argument proves the left-hand side tends to `0`, the univariate
remainder must be zero. -/
theorem univariate_scaled_eval_tendsto_leadingCoeff_of_tendsto_div
    {A : ℝ → ℂ} (p : Polynomial ℂ)
    (hA : Tendsto (fun t : ℝ => A t / (t : ℂ)) atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ p.natDegree * p.eval (A t)) atTop
      (𝓝 p.leadingCoeff) := by
  classical
  have hlim := weighted_sum_tendsto_top_filter
    (l := (atTop : Filter ℝ))
    (W := p.natDegree)
    (a := fun k : Fin (p.natDegree + 1) => p.coeff (k : ℕ))
    (I := fun k : Fin (p.natDegree + 1) => (k : ℕ))
    (J := fun _ : Fin (p.natDegree + 1) => 0)
    (x := fun t : ℝ => ((t : ℂ)⁻¹))
    (P := fun t : ℝ => A t / (t : ℂ))
    (Q := fun _ : ℝ => (1 : ℂ))
    (by
      intro k
      simpa using Nat.le_of_lt_succ k.isLt)
    tendsto_inv_ofReal_atTop_bottcher hA tendsto_const_nhds
  have htop :
      (∑ k : Fin (p.natDegree + 1),
        (if (k : ℕ) + 2 * 0 = p.natDegree then p.coeff (k : ℕ) else 0)) =
        p.leadingCoeff := by
    rw [Polynomial.leadingCoeff]
    rw [Finset.sum_eq_single (Fin.last p.natDegree)]
    · simp
    · intro k _ hk
      have hkval : (k : ℕ) ≠ p.natDegree := by
        intro h
        apply hk
        ext
        simpa [Fin.val_last] using h
      simp [hkval]
    · intro hnot
      simp at hnot
  rw [htop] at hlim
  refine hlim.congr' ?_
  filter_upwards with t
  have hscaled :
      (∑ k : Fin (p.natDegree + 1),
        p.coeff (k : ℕ) * ((t : ℂ)⁻¹) ^ (p.natDegree - ((k : ℕ) + 2 * 0)) *
          (A t / (t : ℂ)) ^ (k : ℕ) * (1 : ℂ) ^ 0) =
        ((t : ℂ)⁻¹) ^ p.natDegree *
          (∑ k : Fin (p.natDegree + 1), p.coeff (k : ℕ) * (A t) ^ (k : ℕ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (weighted_scale_term_identity (z := (t : ℂ)) (A := A t) (B := 1)
        (a := p.coeff (k : ℕ)) (i := (k : ℕ)) (j := 0) (W := p.natDegree)
        (by simpa using Nat.le_of_lt_succ k.isLt))
  have hfin :
      (∑ k : Fin (p.natDegree + 1), p.coeff (k : ℕ) * (A t) ^ (k : ℕ)) =
        p.eval (A t) := by
    rw [Polynomial.eval_eq_sum_range]
    exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i * (A t) ^ i) (p.natDegree + 1)
  rw [hscaled, hfin]

/-- If a univariate polynomial evaluated along `A(t) ~ t` is smaller than its own leading scale,
then the polynomial is zero.  The analytic burden in the Böttcher remainder route is therefore
precisely to prove the scaled-zero hypothesis for the shifted-parabola remainder. -/
theorem polynomial_eq_zero_of_scaled_eval_tendsto_zero_of_tendsto_div
    {A : ℝ → ℂ} (p : Polynomial ℂ)
    (hA : Tendsto (fun t : ℝ => A t / (t : ℂ)) atTop (𝓝 1))
    (hsmall : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ p.natDegree * p.eval (A t)) atTop
      (𝓝 0)) :
    p = 0 := by
  have hlead := univariate_scaled_eval_tendsto_leadingCoeff_of_tendsto_div p hA
  have hlead0 : p.leadingCoeff = 0 := tendsto_nhds_unique hlead hsmall
  by_contra hp
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp) hlead0

/-- Böttcher-specialized zero criterion for a univariate shifted-parabola remainder. -/
theorem polynomial_eq_zero_of_bottcher_scaled_eval_tendsto_zero
    (c : ℂ) (p : Polynomial ℂ)
    (hsmall : Tendsto
      (fun t : ℝ => ((t : ℂ)⁻¹) ^ p.natDegree * p.eval (bottcherCoord c (t : ℂ))) atTop
      (𝓝 0)) :
    p = 0 :=
  polynomial_eq_zero_of_scaled_eval_tendsto_zero_of_tendsto_div p
    (tendsto_bottcherCoord_real_div_atTop c) hsmall

end Bottcher
