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
  simpa [Complex.log_one] using hcont.tendsto.comp h1

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
  simpa using (Complex.continuous_exp.continuousAt.tendsto.comp hW)

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
