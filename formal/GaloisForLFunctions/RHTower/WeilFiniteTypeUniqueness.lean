import GaloisForLFunctions.RHTower.WeilFiniteTypeDirichletRigidity
import GaloisForLFunctions.RHTower.XiEdgeLogDerivativeBlindness
import GaloisForLFunctions.RHTower.EisensteinLineHeightOneMean
import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Finite-type uniqueness of Weil-positive completions

**Theorem** (`finiteType_uniqueness`).  If `lam = Λ ⋆ a + μ ⋆ f + v` is full-cone Weil-positive, with
`a`, `f` supported in `[1, N]`, `f(1) = 0` and `v` regular (its Dirichlet series continues to `E`,
holomorphic on `Re s > ½ − η₀` with polynomial growth on vertical strips), then `a = δ₁`, `f = 0` and
`v = 0`.  So within this class a Weil-positive completion exists iff `Λ` is Weil-positive iff RH
(`exists_finiteType_weilPositive_iff`).

`a = δ₁` and `f = 0` are `dirichletPart_eq_delta`, `moebiusPart_eq_zero`.  Then the master identity
reads `Φ = ξ'/ξ − E` on `Re s > ½` off the zeros of `ζ`, with `Re Φ ≥ 0`.

* **The critical line** (`re_regularPart_criticalLine_le`).  `Re ξ'/ξ(½ + it) = 0` wherever
  `ξ(½ + it) ≠ 0`; letting `σ ↓ ½` gives `Re E(½ + it) ≤ 0` there, and since the zeros of `ξ` are
  isolated, everywhere by continuity.  No hypothesis on the location of the zeros is used.
* **Phragmén–Lindelöf** (`re_regularPart_le_of_strip`).  `E` has polynomial growth on
  `½ ≤ σ ≤ σ₁`, so `|e^E|` is bounded by its boundary values: `Re E ≤ Σ_n |v(n)| n^{−σ₁}` on the strip.
  This is `≤ 2^{−m} Σ_n |v(n)| n^{−2}` for `σ₁ = m + 2`, so `Re E ≤ 0` on `Re s ≥ ½`.
* **The leading coefficient** (`regularPart_eq_zero`).  If `n₀ ≥ 2` is the least `n` with
  `v(n) ≠ 0`, then on `Re s = m + 2` the tail beyond `n₀` is `≤ (n₀ + 1)^{−m} Σ|v(n)| n^{−2}`, while
  at `Im s = 0` or `π/log n₀` the leading term has real part `|v(n₀)| n₀^{−m−2}`; for large `m`
  this makes `Re E > 0`.
-/

open Complex Filter Topology Set
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.GaussZeroSum

namespace RHTower.WeilFiniteType

noncomputable section

/-! ## `ξ'/ξ` in the strip -/

theorem logDeriv_xi_eq_datum_add {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv xi s = zetaArchimedeanDatum s + 1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hxi : xi s ≠ 0 := fun h => hζ ((xi_eq_zero_iff hs hs1).mp h)
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hev : completedRiemannZeta =ᶠ[𝓝 s] fun w => Complex.Gammaℝ w * riemannZeta w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have hΓw : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hw
    rw [riemannZeta_def_of_ne_zero hw0]
    field_simp
  have hlog : logDeriv completedRiemannZeta s =
      logDeriv (fun w => Complex.Gammaℝ w * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [logDeriv_xi_eq_of_ne hs0 hs1 hxi, hlog, logDeriv_mul s hΓ hζ
    (hasDerivAt_Gammaℝ_of_re_pos hs).differentiableAt (differentiableAt_riemannZeta hs1),
    logDeriv_Gammaℝ_of_re_pos hs, logDeriv_apply, zetaArchimedeanDatum]
  ring

/-! ## `Re E ≤ Re ξ'/ξ` -/

theorem dirPoly_eq_one {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) (s : ℂ) : dirPoly N a s = 1 := by
  have hδ := dirichletPart_eq_delta ha hf hf1 hv hW
  have h1 := dirPoly_one_eq_one ha hf hf1 hv hW
  have hN : 1 ≤ N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [dirPoly, hN0] at h1
    simp at h1
  rw [dirPoly_eq_of_support hN (fun n hn => by rw [hδ n, if_neg (by omega)]), hδ 1, if_pos rfl]
  simp

theorem dirPoly_moebiusPart_eq_zero {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) (s : ℂ) : dirPoly N f s = 0 := by
  unfold dirPoly
  simp [moebiusPart_eq_zero ha hf hf1 hv hW]

theorem re_regularPart_le_re_logDeriv_xi {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) : (E s).re ≤ (logDeriv xi s).re := by
  have h := zeta_mul_eq ha hf hf1 hv hW hs hs1
  rw [dirPoly_eq_one ha hf hf1 hv hW, dirPoly_moebiusPart_eq_zero ha hf hf1 hv hW, one_mul,
    sub_zero] at h
  have h2 : weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + E s =
      deriv riemannZeta s / riemannZeta s := by
    rw [eq_div_iff hζ, mul_comm]; exact h
  have hpos := re_weilContinuation_nonneg hW hs
  rw [logDeriv_xi_eq_datum_add (by linarith) hs1 hζ]
  have h3 : weilContinuation hW s = (zetaArchimedeanDatum s + 1 / (s - 1) +
      deriv riemannZeta s / riemannZeta s) - E s := by linear_combination h2
  rw [h3, Complex.sub_re] at hpos
  linarith

/-! ## The critical line -/

theorem continuousAt_regularPart {v : ℕ → ℝ} {E : ℂ → ℂ} (hv : RegularPart v E) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : ContinuousAt E s := by
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  exact (hEd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show 1 / 2 - η₀ < s.re by linarith))).continuousAt

theorem re_regularPart_criticalLine_le_of_xi_ne_zero {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {t : ℝ}
    (hxi : xi ((1 / 2 : ℂ) + I * t) ≠ 0) : (E ((1 / 2 : ℂ) + I * t)).re ≤ 0 := by
  set s₀ : ℂ := (1 / 2 : ℂ) + I * t with hs₀
  have hs₀re : s₀.re = 1 / 2 := by simp [hs₀]
  have hEc := continuousAt_regularPart hv (s := s₀) hs₀re.ge
  have hxic : ContinuousAt xi s₀ := xi_differentiable.continuous.continuousAt
  have hdxic : ContinuousAt (deriv xi) s₀ := ((xi_differentiable.analyticAt s₀).deriv).continuousAt
  have hLc : ContinuousAt (fun s => logDeriv xi s) s₀ := by
    have e : (fun s => logDeriv xi s) = fun s => deriv xi s / xi s := funext fun s => logDeriv_apply _ _
    rw [e]
    exact hdxic.div hxic hxi
  set p : ℝ → ℂ := fun σ => (σ : ℂ) + I * t with hp
  have hpc : Continuous p := by rw [hp]; fun_prop
  have hp0 : p (1 / 2) = s₀ := by simp [hp, hs₀]
  set g : ℝ → ℝ := fun σ => (logDeriv xi (p σ)).re - (E (p σ)).re with hg
  have hgc : ContinuousAt g (1 / 2) := by
    have h1 : ContinuousAt (fun σ => logDeriv xi (p σ)) (1 / 2) := by
      rw [← hp0] at hLc; exact hLc.comp hpc.continuousAt
    have h2 : ContinuousAt (fun σ => E (p σ)) (1 / 2) := by
      rw [← hp0] at hEc; exact hEc.comp hpc.continuousAt
    exact (Complex.continuous_re.continuousAt.comp h1).sub (Complex.continuous_re.continuousAt.comp h2)
  have hxi_ev : ∀ᶠ σ in 𝓝 (1 / 2 : ℝ), xi (p σ) ≠ 0 := by
    have h := hxic.eventually_ne hxi
    rw [← hp0] at h
    exact (hpc.tendsto (1 / 2)).eventually h
  have hev : ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), 0 ≤ g σ := by
    filter_upwards [self_mem_nhdsWithin, (hxi_ev.and (eventually_lt_nhds
      (show (1 / 2 : ℝ) < 1 by norm_num))).filter_mono nhdsWithin_le_nhds] with σ hσ hσ'
    obtain ⟨hxσ, hσ1⟩ := hσ'
    have hre : (p σ).re = σ := by simp [hp]
    have hne1 : p σ ≠ 1 := fun h => by
      have := congrArg Complex.re h
      rw [hre, Complex.one_re] at this
      linarith
    have hζ : riemannZeta (p σ) ≠ 0 := fun h =>
      hxσ ((xi_eq_zero_iff (by rw [hre]; linarith [show (1 / 2 : ℝ) < σ from hσ]) hne1).mpr h)
    have := re_regularPart_le_re_logDeriv_xi ha hf hf1 hv hW
      (by rw [hre]; exact hσ) hne1 hζ
    simp only [hg]
    linarith
  have hg0 : 0 ≤ g (1 / 2) := ge_of_tendsto (hgc.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hL0 : (logDeriv xi s₀).re = 0 := by
    rw [logDeriv_apply]
    exact re_logDeriv_xi_criticalLine t
  simp only [hg, hp0] at hg0
  linarith

/-- **`Re E ≤ 0` on the critical line.** -/
theorem re_regularPart_criticalLine_le {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) (t : ℝ) :
    (E ((1 / 2 : ℂ) + I * t)).re ≤ 0 := by
  set q : ℝ → ℂ := fun τ => (1 / 2 : ℂ) + I * τ with hq
  have hqc : Continuous q := by rw [hq]; fun_prop
  have hnot : ¬ ∀ᶠ z in 𝓝 (q t), xi z = 0 := by
    intro h
    have hall := (xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
      ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ (q t)) h
      (Set.mem_univ 0)
    have h0 : xi 0 = 0 := hall
    rw [xi] at h0
    norm_num at h0
  have hpunct : ∀ᶠ z in 𝓝[≠] (q t), xi z ≠ 0 :=
    (xi_differentiable.analyticAt (q t)).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
  have hqt : Tendsto q (𝓝[≠] t) (𝓝[≠] (q t)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((hqc.tendsto t).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    intro h
    apply hτ
    have := congrArg Complex.im h
    simpa [hq] using this
  have hev : ∀ᶠ τ in 𝓝[≠] t, (E (q τ)).re ≤ 0 := by
    filter_upwards [hqt.eventually hpunct] with τ hτ
    exact re_regularPart_criticalLine_le_of_xi_ne_zero ha hf hf1 hv hW hτ
  have hEc : ContinuousAt (fun τ => (E (q τ)).re) t := by
    have h : ContinuousAt E (q t) := continuousAt_regularPart hv (by simp [hq])
    exact Complex.continuous_re.continuousAt.comp (h.comp hqc.continuousAt)
  exact le_of_tendsto (hEc.tendsto.mono_left nhdsWithin_le_nhds) hev

/-! ## Phragmén–Lindelöf -/

/-- `C (1 + |y|)^k ≤ B e^{c|y|}` for every `c > 0`. -/
theorem exists_poly_le_exp {Cg c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ B : ℝ, ∀ y : ℝ, Cg * (1 + |y|) ^ k ≤ B * Real.exp (c * |y|) := by
  refine ⟨|Cg| * k.factorial * Real.exp c / c ^ k, fun y => ?_⟩
  have hck : 0 < c ^ k := pow_pos hc k
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have h := Real.pow_div_factorial_le_exp (c * (1 + |y|)) (by positivity) k
  rw [mul_pow, div_le_iff₀ hfac,
    show Real.exp (c * (1 + |y|)) = Real.exp c * Real.exp (c * |y|) by
      rw [← Real.exp_add]; ring_nf] at h
  have h1 : (1 + |y|) ^ k ≤ k.factorial * Real.exp c / c ^ k * Real.exp (c * |y|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hck]
    calc (1 + |y|) ^ k * c ^ k = c ^ k * (1 + |y|) ^ k := by ring
      _ ≤ Real.exp c * Real.exp (c * |y|) * k.factorial := h
      _ = _ := by ring
  calc Cg * (1 + |y|) ^ k ≤ |Cg| * (1 + |y|) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |Cg| * (k.factorial * Real.exp c / c ^ k * Real.exp (c * |y|)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

/-- **Phragmén–Lindelöf**: `Re E ≤ Σ_n |v(n)| n^{−σ₁}` on `½ ≤ Re s ≤ σ₁`. -/
theorem re_regularPart_le_of_strip {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {σ₁ : ℝ} (hσ₁ : 1 < σ₁) {z : ℂ}
    (hz1 : 1 / 2 ≤ z.re) (hz2 : z.re ≤ σ₁) :
    (E z).re ≤ ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) σ₁ n‖ := by
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  obtain ⟨Cg, k, hg⟩ := hv.growth σ₁
  set δ := ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) σ₁ n‖ with hδ
  have hδ0 : 0 ≤ δ := tsum_nonneg fun _ => norm_nonneg _
  have hcrit := re_regularPart_criticalLine_le ha hf hf1 hv hW
  set c : ℝ := Real.pi / (2 * (σ₁ - 1 / 2)) with hc
  have hw : 0 < σ₁ - 1 / 2 := by linarith
  have hc0 : 0 < c := by positivity
  have hcπ : c < Real.pi / (σ₁ - 1 / 2) := by
    rw [hc]
    exact div_lt_div_of_pos_left Real.pi_pos hw (by linarith)
  obtain ⟨B, hB⟩ := exists_poly_le_exp (Cg := Cg) hc0 k
  have hle := PhragmenLindelof.vertical_strip (f := fun z => cexp (E z)) (a := 1 / 2) (b := σ₁)
    (C := Real.exp δ) (z := z) ?_ ?_ ?_ ?_ hz1 hz2
  · simp only [Complex.norm_exp] at hle
    exact Real.exp_le_exp.mp hle
  · apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_preimage_re, closure_Ioo (by linarith : (1 / 2 : ℝ) ≠ σ₁)]
    refine (hEd.mono fun w hw' => ?_).cexp
    simp only [mem_preimage, mem_Icc] at hw'
    show 1 / 2 - η₀ < w.re
    linarith [hw'.1]
  · refine ⟨c, hcπ, B, Asymptotics.IsBigO.of_bound 1 ?_⟩
    rw [Filter.eventually_inf_principal]
    refine Eventually.of_forall fun w hw' => ?_
    simp only [mem_preimage, mem_Ioo] at hw'
    simp only [Complex.norm_exp, Real.norm_eq_abs, one_mul]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc (E w).re ≤ ‖E w‖ := Complex.re_le_norm _
      _ ≤ Cg * (1 + |w.im|) ^ k := hg w hw'.1.le hw'.2.le
      _ ≤ B * Real.exp (c * |w.im|) := hB _
  · intro w hw'
    simp only [Complex.norm_exp]
    have hw'' : w = (1 / 2 : ℂ) + I * (w.im : ℂ) := by
      apply Complex.ext <;> simp [hw']
    have h := hcrit w.im
    rw [← hw''] at h
    exact (Real.exp_le_one_iff.mpr h).trans (Real.one_le_exp hδ0)
  · intro w hw'
    simp only [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [hv.series w (by rw [hw']; exact hσ₁)]
    exact (Complex.re_le_norm _).trans
      (norm_LSeries_le_of_re hw' (hv.summable σ₁ (by simpa using hσ₁)))

theorem norm_term_le_pow {v : ℕ → ℝ} (hv1 : v 1 = 0) (m : ℕ) (n : ℕ) :
    ‖LSeries.term (fun n => (v n : ℂ)) (((m : ℝ) + 2 : ℝ) : ℂ) n‖ ≤
      (1 / 2) ^ m * ‖LSeries.term (fun n => (v n : ℂ)) ((2 : ℝ) : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with h0
  · simp
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : n = 1 := by omega
    subst this
    simp [hv1]
  have hn0 : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Complex.ofReal_re]
  rw [Real.rpow_add hn0, Real.rpow_natCast, mul_comm ((n : ℝ) ^ m), ← div_div]
  have hpow : (2 : ℝ) ^ m ≤ (n : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) hn2 m
  have hA : 0 ≤ ‖(v n : ℂ)‖ / (n : ℝ) ^ (2 : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity), one_div, inv_pow, mul_comm ((2 : ℝ)⁻¹ ^ m), mul_assoc,
    inv_mul_eq_div]
  have : 1 ≤ (n : ℝ) ^ m / 2 ^ m := by rw [le_div_iff₀ (by positivity), one_mul]; exact hpow
  calc ‖(v n : ℂ)‖ / (n : ℝ) ^ (2 : ℝ) = ‖(v n : ℂ)‖ / (n : ℝ) ^ (2 : ℝ) * 1 := (mul_one _).symm
    _ ≤ ‖(v n : ℂ)‖ / (n : ℝ) ^ (2 : ℝ) * ((n : ℝ) ^ m / 2 ^ m) :=
        mul_le_mul_of_nonneg_left this hA

/-- **`Re E ≤ 0` on `Re s ≥ ½`.** -/
theorem re_regularPart_nonpos {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    (E z).re ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set δ₂ := ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) ((2 : ℝ) : ℂ) n‖ with hδ₂
  have hδ₂0 : 0 ≤ δ₂ := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨m₁, hm₁⟩ := exists_pow_lt_of_lt_one (div_pos hpos (by linarith : (0 : ℝ) < δ₂ + 1))
    (by norm_num : (1 / 2 : ℝ) < 1)
  set m := max m₁ ⌈z.re⌉₊ with hm
  have hσ₁ : 1 < (m : ℝ) + 2 := by positivity
  have hzm : z.re ≤ (m : ℝ) + 2 := by
    have h1 : z.re ≤ (⌈z.re⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈z.re⌉₊ : ℝ) ≤ m := by exact_mod_cast le_max_right _ _
    linarith
  have h1 := re_regularPart_le_of_strip ha hf hf1 hv hW hσ₁ hz hzm
  have hs1 : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (v n : ℂ)) s := hv.summable
  have h2 : ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (((m : ℝ) + 2 : ℝ) : ℂ) n‖ ≤
      (1 / 2) ^ m * δ₂ := by
    rw [hδ₂, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (norm_term_le_pow hv.one m)
      (hs1 _ (by simpa using hσ₁)).norm ((hs1 _ (by norm_num)).norm.mul_left _)
  have h3 : (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ m₁ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  have h4 : (1 / 2 : ℝ) ^ m₁ * (δ₂ + 1) < (E z).re := by
    rwa [lt_div_iff₀ (by linarith)] at hm₁
  have h5 : (1 / 2 : ℝ) ^ m * δ₂ ≤ (1 / 2) ^ m₁ * (δ₂ + 1) := by
    calc (1 / 2 : ℝ) ^ m * δ₂ ≤ (1 / 2) ^ m₁ * δ₂ := mul_le_mul_of_nonneg_right h3 hδ₂0
      _ ≤ (1 / 2) ^ m₁ * (δ₂ + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-! ## The leading coefficient -/

/-- `n₀^{iτ} = ±1` at `τ = 0` and `τ = π/log n₀`. -/
theorem natCast_cpow_phase {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (σ : ℝ) (pos : Bool) :
    (n₀ : ℂ) ^ ((σ : ℂ) + ((if pos then 0 else Real.pi / Real.log n₀ : ℝ) : ℂ) * I) =
      (((n₀ : ℝ) ^ σ : ℝ) : ℂ) * (if pos then 1 else -1) := by
  have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : n₀ ≠ 0)
  have hlog : 0 < Real.log n₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < n₀))
  rw [Complex.cpow_add _ _ hn0, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  cases pos
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hlog' : ((Real.log n₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
    have e : ((Real.log n₀ : ℝ) : ℂ) * ((((Real.pi / Real.log n₀ : ℝ)) : ℂ) * I) = Real.pi * I := by
      push_cast
      field_simp
    rw [e]
    exact Complex.exp_pi_mul_I
  · simp

/-- **`v = 0`.** -/
theorem regularPart_eq_zero {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) : ∀ n, v n = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set n₀ := Nat.find hcon with hn₀def
  have hn₀ : v n₀ ≠ 0 := Nat.find_spec hcon
  have hlt : ∀ n < n₀, v n = 0 := fun n hn => not_not.mp (Nat.find_min hcon hn)
  have hn₀2 : 2 ≤ n₀ := by
    have h0 : n₀ ≠ 0 := fun h => hn₀ (h ▸ hv.zero)
    have h1 : n₀ ≠ 1 := fun h => hn₀ (h ▸ hv.one)
    omega
  have hn₀pos : (0 : ℝ) < n₀ := by positivity
  set δ₂ := ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) ((2 : ℝ) : ℂ) n‖ with hδ₂
  have hδ₂0 : 0 ≤ δ₂ := tsum_nonneg fun _ => norm_nonneg _
  have hva : 0 < |v n₀| := abs_pos.mpr hn₀
  -- choose `m` with `δ₂ n₀² / |v(n₀)| < ((n₀+1)/n₀)^m`
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (δ₂ * (n₀ : ℝ) ^ 2 / |v n₀|)
    (show (1 : ℝ) < ((n₀ : ℝ) + 1) / n₀ by rw [lt_div_iff₀ hn₀pos]; linarith)
  set σ : ℝ := (m : ℝ) + 2 with hσ
  have hσ1 : 1 < σ := by positivity
  set pos : Bool := decide (0 < v n₀) with hposdef
  set τ : ℝ := if pos then 0 else Real.pi / Real.log n₀ with hτ
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsum : LSeriesSummable (fun n => (v n : ℂ)) s := hv.summable s (by rw [hsre]; exact hσ1)
  have hE : E s = LSeries (fun n => (v n : ℂ)) s := hv.series s (by rw [hsre]; exact hσ1)
  -- the leading term
  have hlead : LSeries.term (fun n => (v n : ℂ)) s n₀ =
      (v n₀ : ℂ) / ((((n₀ : ℝ) ^ σ : ℝ) : ℂ) * (if pos then 1 else -1)) := by
    rw [LSeries.term_of_ne_zero (by omega), hs, hτ, natCast_cpow_phase hn₀2]
  have hleadre : (LSeries.term (fun n => (v n : ℂ)) s n₀).re = |v n₀| / (n₀ : ℝ) ^ σ := by
    rw [hlead]
    have hpow : 0 < (n₀ : ℝ) ^ σ := Real.rpow_pos_of_pos hn₀pos σ
    by_cases hp : 0 < v n₀
    · have : pos = true := by simp [hposdef, hp]
      rw [this, if_pos rfl, mul_one, ← Complex.ofReal_div, Complex.ofReal_re, abs_of_pos hp]
    · have : pos = false := by simp [hposdef, hp]
      rw [this, if_neg (by simp), mul_neg_one, div_neg, ← Complex.ofReal_div, Complex.neg_re,
        Complex.ofReal_re, abs_of_neg (lt_of_le_of_ne (not_lt.mp hp) hn₀), neg_div]
  -- the tail
  have htail : ‖∑' n, (if n = n₀ then 0 else LSeries.term (fun n => (v n : ℂ)) s n)‖ ≤
      δ₂ / ((n₀ : ℝ) + 1) ^ m := by
    have hpt : ∀ n, ‖(if n = n₀ then 0 else LSeries.term (fun n => (v n : ℂ)) s n)‖ ≤
        ‖LSeries.term (fun n => (v n : ℂ)) ((2 : ℝ) : ℂ) n‖ / ((n₀ : ℝ) + 1) ^ m := by
      intro n
      split_ifs with hn
      · rw [norm_zero]; positivity
      rcases lt_or_gt_of_ne hn with hlt' | hgt
      · have h0 : LSeries.term (fun n => (v n : ℂ)) s n = 0 := by simp [LSeries.term, hlt n hlt']
        rw [h0, norm_zero]
        positivity
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg (by omega), if_neg (by omega), hsre,
        Complex.ofReal_re]
      have hn1 : ((n₀ : ℝ) + 1) ≤ n := by exact_mod_cast hgt
      have hnpos : (0 : ℝ) < n := by linarith
      rw [hσ, Real.rpow_add hnpos, Real.rpow_natCast, div_div, mul_comm ((n : ℝ) ^ (2 : ℝ))]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn1 m) (by positivity)
    have hs2 := (hv.summable ((2 : ℝ) : ℂ) (by norm_num)).norm
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hs2.div_const _)
    · rw [hδ₂, ← tsum_div_const]
      exact Summable.tsum_le_tsum hpt
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hs2.div_const _)) (hs2.div_const _)
  -- the tail is smaller than the leading term
  have hsmall : δ₂ / ((n₀ : ℝ) + 1) ^ m < |v n₀| / (n₀ : ℝ) ^ σ := by
    have hpow : (n₀ : ℝ) ^ σ = (n₀ : ℝ) ^ m * (n₀ : ℝ) ^ 2 := by
      rw [hσ, Real.rpow_add hn₀pos, Real.rpow_natCast, Real.rpow_two]
    rw [hpow, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm' : δ₂ * (n₀ : ℝ) ^ 2 / |v n₀| < ((n₀ : ℝ) + 1) ^ m / (n₀ : ℝ) ^ m := by
      rwa [div_pow] at hm
    rw [div_lt_div_iff₀ hva (by positivity)] at hm'
    calc δ₂ * ((n₀ : ℝ) ^ m * (n₀ : ℝ) ^ 2) = δ₂ * (n₀ : ℝ) ^ 2 * (n₀ : ℝ) ^ m := by ring
      _ < ((n₀ : ℝ) + 1) ^ m * |v n₀| := hm'
      _ = _ := by ring
  have hsplit := hsum.tsum_eq_add_tsum_ite n₀
  have hre : 0 < (E s).re := by
    rw [hE, LSeries, hsplit, Complex.add_re, hleadre]
    have := (Complex.abs_re_le_norm _).trans htail
    have h' := neg_abs_le (∑' n, (if n = n₀ then 0 else LSeries.term (fun n => (v n : ℂ)) s n)).re
    linarith
  have hnonpos := re_regularPart_nonpos ha hf hf1 hv hW (z := s) (by rw [hsre]; linarith)
  linarith

/-! ## The theorem -/

/-- **Finite-type uniqueness.** -/
theorem finiteType_uniqueness {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    (∀ n, a n = if n = 1 then 1 else 0) ∧ (∀ n, f n = 0) ∧ ∀ n, v n = 0 :=
  ⟨dirichletPart_eq_delta ha hf hf1 hv hW, moebiusPart_eq_zero ha hf hf1 hv hW,
    regularPart_eq_zero ha hf hf1 hv hW⟩

theorem finiteTypeSeq_delta_zero_zero :
    finiteTypeSeq (fun n => if n = 1 then 1 else 0) (fun _ => 0) (fun _ => 0) =
      fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  funext n
  unfold finiteTypeSeq
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [Finset.sum_eq_single (n, 1)]
  · simp
  · intro p hp hne
    have hmul := Nat.mem_divisorsAntidiagonal.mp hp
    have h2 : p.2 ≠ 1 := by
      intro h
      apply hne
      rw [Prod.ext_iff]
      refine ⟨?_, h⟩
      rw [← hmul.1, h, mul_one]
    simp [h2]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn.ne'⟩) h

theorem regularPart_zero : RegularPart (fun _ => 0) (fun _ => 0) where
  zero := rfl
  one := rfl
  summable s _ := by simpa using (LSeriesSummable_zero (s := s))
  series s _ := by
    have : (fun n : ℕ => (((fun _ : ℕ => (0 : ℝ)) n : ℝ) : ℂ)) = 0 := by funext n; simp
    rw [this, LSeries_zero]
    rfl
  holo := ⟨1, one_pos, differentiableOn_const 0⟩
  growth _ := ⟨0, 0, fun s _ _ => by simp⟩

/-- **Within finite type, a Weil-positive completion exists iff RH.** -/
theorem exists_finiteType_weilPositive_iff :
    (∃ (N : ℕ) (a f v : ℕ → ℝ) (E : ℂ → ℂ), SupportedIn N a ∧ SupportedIn N f ∧ f 1 = 0 ∧
      RegularPart v E ∧ WeilPositiveFull (finiteTypeSeq a f v)) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_weilPositiveFull_vonMangoldt]
  constructor
  · rintro ⟨N, a, f, v, E, ha, hf, hf1, hv, hW⟩
    obtain ⟨h1, h2, h3⟩ := finiteType_uniqueness ha hf hf1 hv hW
    have ha' : a = fun n => if n = 1 then 1 else 0 := funext h1
    have hf' : f = fun _ => 0 := funext h2
    have hv' : v = fun _ => 0 := funext h3
    rw [ha', hf', hv', finiteTypeSeq_delta_zero_zero] at hW
    exact hW
  · intro hW
    refine ⟨1, fun n => if n = 1 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0,
      ⟨by simp, fun n hn => if_neg (by omega)⟩, ⟨rfl, fun _ _ => rfl⟩, rfl, regularPart_zero, ?_⟩
    rw [finiteTypeSeq_delta_zero_zero]
    exact hW

end

end RHTower.WeilFiniteType
