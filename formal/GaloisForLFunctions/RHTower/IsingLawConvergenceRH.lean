import GaloisForLFunctions.HTGeometry.IsingCharRealRootedApprox
import GaloisForLFunctions.RHTower.IsingHarmonicMagnetizationNoGo
import GaloisForLFunctions.RHTower.IsingSlowFieldCriticality
import GaloisForLFunctions.RHTower.EntireMontel
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Convergence in law of ferromagnetic Ising magnetizations to Riemann's distribution forces RH

Let `X_n = Σ_k c_{n,k} σ_k` be zero-field ferromagnetic Ising magnetizations (`J ≥ 0`, positive
masses `c`), and let `φ_n(t) = E[e^{itX_n}]`. Suppose `φ_n → Ξ(t)/Ξ(0)` uniformly on every compact
real interval, i.e. `X_n` converges in law to the Riemann distribution `Φ(u)du/Ξ(0)`.

**Theorem** (`riemannHypothesis_of_isingChar_tendstoUniformlyOn_real`). Then RH holds.

**Proof.**
* `φ_n` is a locally uniform limit of even real-rooted polynomials
  (`HTGeometry.LeeYang.exists_even_realRooted_approx`). Hence `‖φ_n(z)‖² ≤ exp(L_n‖z‖²)` and
  `|φ_n(1)|² ≤ exp(−L_n)` as long as `φ_n` has no zero on `[−1, 1]`. Here `L_n = (lagRatio φ_n).re`.
* `Ξ` has no real zero in `[−1, 1]`, so eventually `|φ_n| ≥ c₀/2` there, which gives the uniform
  bound `L_n ≤ K`.
* Montel gives a subsequence converging locally uniformly on `ℂ` to an entire `g`. Then `g = Ξ/Ξ(0)`
  on `ℝ`, hence on `ℂ`.
* The zeros of `φ_n` are real (Lee–Yang), so by Hurwitz the zeros of `Ξ` are real.

Convergence in law is the weakest natural form of a Griffiths–Simon producer. No growth control off
the real axis is assumed: Lee–Yang supplies it.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

namespace RHTower.GriffithsSimon

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.LeeYang

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isingChar_eq_isingCharFn (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) :
    isingChar J E c = isingCharFn J E c := rfl

/-- `conj φ(t) = φ(−t)` for real `t`. -/
theorem conj_isingCharFn_ofReal (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (t : ℝ) :
    conj (isingCharFn J E c t) = isingCharFn J E c (-(t : ℂ)) := by
  rw [isingCharFn, isingCharFn, map_div₀, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, conj_I, Complex.conj_ofReal]
  ring

theorem norm_sq_isingCharFn_one_le {J : V → V → ℝ} {E : Finset (V × V)} {c : V → ℝ}
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (hc : ∀ k, 0 ≤ c k)
    (hne : ∀ s : ℝ, |s| ≤ 1 → isingCharFn J E c s ≠ 0) :
    ‖isingCharFn J E c 1‖ ^ 2 ≤ Real.exp (-(lagRatio (isingCharFn J E c)).re) := by
  have h := isingCharFn_mul_neg_le hJ hc (t := 1) (fun s hs => hne s (by simpa using hs))
  have hc1 : isingCharFn J E c (-1) = conj (isingCharFn J E c 1) := by
    have := conj_isingCharFn_ofReal J E c 1
    simp only [Complex.ofReal_one] at this
    exact this.symm
  simp only [Complex.ofReal_one, one_pow, one_mul] at h
  rw [hc1, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] at h
  exact h

/-- `Ξ` has no zero on `[−1, 1]`. -/
theorem xiRatio_ne_zero_of_abs_le_one {s : ℝ} (hs : |s| ≤ 1) : XiC s / XiC 0 ≠ 0 := by
  refine div_ne_zero ?_ XiC_zero_ne
  intro h0
  apply xi_ne_zero_of_im_sq_le (s := 1 / 2 + (s : ℂ) * I) ?_
  · exact h0
  · simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, add_zero]
    norm_num
    nlinarith [abs_le.mp hs, sq_abs s]

theorem continuous_XiC' : Continuous XiC :=
  continuous_iff_continuousAt.mpr fun z => (XiC_analytic z (mem_univ z)).continuousAt

/-- **Variance control from the real line.** If the characteristic functions converge to `Ξ/Ξ(0)`
uniformly on `[−1, 1]`, then eventually `L(φ_n) ≤ K`. -/
theorem exists_eventually_lagRatio_le
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => isingCharFn (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-1) 1)) :
    ∃ n₀ : ℕ, ∃ K : ℝ, ∀ n, n₀ ≤ n → (lagRatio (isingCharFn (J n) (E n) (c n))).re ≤ K := by
  set φ : ℕ → ℂ → ℂ := fun n => isingCharFn (J n) (E n) (c n) with hφ
  set F : ℂ → ℂ := fun z => XiC z / XiC 0 with hF
  have hFcont : Continuous fun s : ℝ => F s := by
    rw [hF]; exact (continuous_XiC'.comp Complex.continuous_ofReal).div_const _
  obtain ⟨c₀, hc₀, hc₀le⟩ : ∃ c₀ > 0, ∀ s ∈ Icc (-1 : ℝ) 1, c₀ ≤ ‖F s‖ := by
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
      (continuous_norm.comp hFcont).continuousOn
    exact ⟨‖F s₀‖, norm_pos_iff.mpr (xiRatio_ne_zero_of_abs_le_one (abs_le.mpr ⟨hs₀.1, hs₀.2⟩)),
      fun s hs => hmin hs⟩
  have hev : ∀ᶠ n in atTop, ∀ s ∈ Icc (-1 : ℝ) 1, c₀ / 2 < ‖φ n s‖ := by
    have := Metric.tendstoUniformlyOn_iff.mp hconv (c₀ / 2) (by positivity)
    filter_upwards [this] with n hn s hs
    have h1 := hn s hs
    have h2 := hc₀le s hs
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (F s) (φ n s)
    simp only [hF, hφ] at h1 h2 this ⊢
    linarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀, Real.log (4 / c₀ ^ 2), fun n hn => ?_⟩
  have hne : ∀ s : ℝ, |s| ≤ 1 → φ n s ≠ 0 := by
    intro s hs h0
    have := hn₀ n hn s (abs_le.mp hs)
    rw [h0, norm_zero] at this
    linarith
  have h := norm_sq_isingCharFn_one_le (hJ n) (hc n) hne
  have h1 : c₀ / 2 < ‖φ n 1‖ := by
    have := hn₀ n hn 1 ⟨by norm_num, le_rfl⟩
    simpa using this
  have h2 : (c₀ / 2) ^ 2 < Real.exp (-(lagRatio (φ n)).re) :=
    lt_of_lt_of_le (pow_lt_pow_left₀ h1 (by positivity) (by norm_num)) h
  have h3 := Real.log_lt_log (by positivity) h2
  rw [Real.log_exp] at h3
  have h4 : Real.log ((c₀ / 2) ^ 2) = -Real.log (4 / c₀ ^ 2) := by
    rw [← Real.log_inv]; congr 1; field_simp; ring
  linarith

/-- **Normal family from a variance bound.** If `L(φ_n) ≤ K` for `n ≥ n₀`, every subsequence of the
characteristic functions has a further subsequence converging locally uniformly on `ℂ` to an entire
function. -/
theorem exists_subseq_of_lagRatio_le
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    {n₀ : ℕ} {K : ℝ}
    (hL : ∀ n, n₀ ≤ n → (lagRatio (isingCharFn (J n) (E n) (c n))).re ≤ K)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, Tendsto ms atTop atTop ∧ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      TendstoLocallyUniformly
        (fun k => isingCharFn (J (ns (ms k))) (E (ns (ms k))) (c (ns (ms k)))) g atTop := by
  set φ : ℕ → ℂ → ℂ := fun n => isingCharFn (J n) (E n) (c n) with hφ
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hns.eventually (eventually_ge_atTop n₀))
  set ψ : ℕ → ℂ → ℂ := fun k => φ (ns (k + k₀)) with hψ
  have hψdiff : ∀ k, Differentiable ℂ (ψ k) := fun k => differentiable_isingCharFn _ _ _
  have hbd : ∀ R : ℝ, ∃ C : ℝ, ∀ k, ∀ z ∈ Metric.ball (0 : ℂ) R, ‖ψ k z‖ ≤ C := by
    intro R
    refine ⟨Real.exp (R ^ 2 * max K 0), fun k z hz => ?_⟩
    have hzR : ‖z‖ ≤ R := by
      have := mem_ball_zero_iff.mp hz; linarith
    have hm := hk₀ (k + k₀) (by omega)
    have h := norm_sq_isingCharFn_le (hJ (ns (k + k₀))) (hc (ns (k + k₀))) z
    have hLk := hL (ns (k + k₀)) hm
    have h1 : ‖z‖ ^ 2 * (lagRatio (φ (ns (k + k₀)))).re ≤ R ^ 2 * max K 0 := by
      have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR 2
      calc ‖z‖ ^ 2 * (lagRatio (φ (ns (k + k₀)))).re ≤ ‖z‖ ^ 2 * max K 0 :=
            mul_le_mul_of_nonneg_left (hLk.trans (le_max_left _ _)) (by positivity)
        _ ≤ R ^ 2 * max K 0 := mul_le_mul_of_nonneg_right hz2 (le_max_right _ _)
    have h2 : ‖ψ k z‖ ^ 2 ≤ Real.exp (R ^ 2 * max K 0) :=
      h.trans (Real.exp_le_exp.mpr h1)
    have h3 : Real.exp (R ^ 2 * max K 0) ≤ Real.exp (R ^ 2 * max K 0) ^ 2 := by
      have : 1 ≤ Real.exp (R ^ 2 * max K 0) := Real.one_le_exp (by positivity)
      nlinarith
    nlinarith [norm_nonneg (ψ k z), Real.exp_pos (R ^ 2 * max K 0)]
  obtain ⟨σ, g, hσ, hgconv⟩ := exists_subseq_tendstoLocallyUniformly hψdiff hbd
  have hgdiff : Differentiable ℂ g := by
    rw [← differentiableOn_univ]
    exact (tendstoLocallyUniformlyOn_univ.2 hgconv).differentiableOn
      (Eventually.of_forall fun k => (hψdiff (σ k)).differentiableOn) isOpen_univ
  exact ⟨fun k => σ k + k₀, (tendsto_add_atTop_nat k₀).comp hσ.tendsto_atTop, g, hgdiff, hgconv⟩

/-- **Subsequence principle.** Under convergence in law, every subsequence has a further
subsequence along which the characteristic functions converge to `Ξ/Ξ(0)` locally uniformly on
all of `ℂ`. -/
theorem exists_subseq_tendstoLocallyUniformly_xi
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hconv : ∀ R : ℝ, TendstoUniformlyOn (fun n (t : ℝ) => isingCharFn (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-R) R))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, Tendsto ms atTop atTop ∧
      TendstoLocallyUniformly (fun k => isingCharFn (J (ns (ms k))) (E (ns (ms k))) (c (ns (ms k))))
        (fun z => XiC z / XiC 0) atTop := by
  set F : ℂ → ℂ := fun z => XiC z / XiC 0 with hF
  obtain ⟨n₀, K, hL⟩ := exists_eventually_lagRatio_le J E hJ c hc (hconv 1)
  obtain ⟨ms, hms, g, hgdiff, hgconv⟩ := exists_subseq_of_lagRatio_le J E hJ c hc hL ns hns
  have hgreal : ∀ t : ℝ, g t = F t := by
    intro t
    have h1 := (tendstoLocallyUniformlyOn_univ.2 hgconv).tendsto_at (mem_univ (t : ℂ))
    have h2 : Tendsto (fun k => isingCharFn (J (ns (ms k))) (E (ns (ms k))) (c (ns (ms k))) t)
        atTop (𝓝 (F t)) := by
      have hu := (hconv (|t|)).tendsto_at (show t ∈ Icc (-|t|) |t| from
        ⟨neg_abs_le t, le_abs_self t⟩)
      exact hu.comp (hns.comp hms)
    exact tendsto_nhds_unique h1 h2
  have hgF : g = F := by
    have hFan : AnalyticOnNhd ℂ F univ := fun z _ =>
      (XiC_analytic z (mem_univ z)).div_const
    have hgan : AnalyticOnNhd ℂ g univ := fun z _ => hgdiff.analyticAt z
    have hseq : Tendsto (fun k : ℕ => (((1 : ℝ) / (k + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [Function.comp_def] using this
      · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = F z :=
      hseq.frequently (Frequently.of_forall fun k => hgreal _)
    funext z
    exact hgan.eqOn_of_preconnected_of_frequently_eq hFan isPreconnected_univ (mem_univ 0)
      hfreq (mem_univ z)
  refine ⟨ms, hms, ?_⟩
  rw [← hgF]
  exact hgconv

/-- **Convergence in law upgrades to locally uniform convergence on `ℂ`.** For zero-field
ferromagnetic Ising magnetizations (`J ≥ 0`, `c ≥ 0`), uniform convergence of the characteristic
functions to `Ξ/Ξ(0)` on compact real intervals implies locally uniform convergence of their entire
extensions on `ℂ`. -/
theorem tendstoLocallyUniformly_of_tendstoUniformlyOn_real
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hconv : ∀ R : ℝ, TendstoUniformlyOn (fun n (t : ℝ) => isingCharFn (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-R) R)) :
    TendstoLocallyUniformly (fun n => isingCharFn (J n) (E n) (c n)) (fun z => XiC z / XiC 0)
      atTop := by
  let x : ℕ → C(ℂ, ℂ) := fun n =>
    ⟨isingCharFn (J n) (E n) (c n), (differentiable_isingCharFn _ _ _).continuous⟩
  let f : C(ℂ, ℂ) := ⟨fun z => XiC z / XiC 0, continuous_XiC'.div_const _⟩
  have h : Tendsto x atTop (𝓝 f) := by
    refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, -, hms⟩ := exists_subseq_tendstoLocallyUniformly_xi J E hJ c hc hconv ns hns
    exact ⟨ms, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr hms⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h

/-- **Convergence in law suffices.** -/
theorem riemannHypothesis_of_isingCharFn_tendstoUniformlyOn_real
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hconv : ∀ R : ℝ, TendstoUniformlyOn (fun n (t : ℝ) => isingCharFn (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-R) R)) :
    RiemannHypothesis := by
  have hloc := tendstoLocallyUniformly_of_tendstoUniformlyOn_real J E hJ c hc hconv
  have hX0 := XiC_zero_ne
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hFan : AnalyticOnNhd ℂ (fun z => XiC z / XiC 0) univ := fun w _ =>
    (XiC_analytic w (mem_univ w)).div_const
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly hloc hFan
    (Eventually.of_forall fun n => differentiable_isingCharFn _ _ _)
    (isClosed_eq Complex.continuous_im continuous_const)
    (Eventually.of_forall fun n w hw => im_eq_zero_of_isingCharFn_eq_zero (hJ n) (hc n) hw)
    (a := 0) (div_ne_zero hX0 hX0) (show XiC z / XiC 0 = 0 by rw [hXiC, zero_div])
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) (by linarith)

/-- **Griffiths–Simon producers in law.** If the magnetizations of zero-field ferromagnetic Ising
models with nonnegative masses converge in law to Riemann's distribution `Φ(u)du/Ξ(0)` (their
characteristic functions converge uniformly on compact real intervals), then RH holds. -/
theorem riemannHypothesis_of_isingChar_tendstoUniformlyOn_real
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hconv : ∀ R : ℝ, TendstoUniformlyOn (fun n (t : ℝ) => isingChar (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-R) R)) :
    RiemannHypothesis :=
  riemannHypothesis_of_isingCharFn_tendstoUniformlyOn_real J E hJ c hc hconv

/-! ## The Griffiths–Simon no-gos hold for producers in law -/

/-- Free magnetization dominance for producers in law. -/
theorem eventually_freeMag_le_xiRealLogDeriv_of_law
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hconv : ∀ R : ℝ, TendstoUniformlyOn (fun n (t : ℝ) => isingChar (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-R) R)) {w : ℝ} (hw : 0 ≤ w) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∑ k, c n k * Real.tanh (c n k * w) ≤ xiRealLogDeriv w + ε :=
  eventually_freeMag_le_xiRealLogDeriv J E hJ c hc
    (tendstoLocallyUniformly_of_tendstoUniformlyOn_real J E hJ c hc hconv) hw hε

/-- Slow-field producers in law have free variance tending to `0`. -/
theorem tendsto_freeVariance_zero_of_law
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hslow : ∀ δ > 0, ∀ᶠ n in atTop, ∀ k, c n k ≤ δ)
    (hconv : ∀ R : ℝ, TendstoUniformlyOn (fun n (t : ℝ) => isingChar (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-R) R)) :
    Tendsto (fun n => ∑ k, c n k ^ 2) atTop (𝓝 0) :=
  tendsto_freeVariance_zero J E hJ c hc hslow
    (tendstoLocallyUniformly_of_tendstoUniformlyOn_real J E hJ c hc hconv)

/-- The harmonic Griffiths–Simon program with `K ≤ 7` fails already in law. -/
theorem not_tendstoUniformlyOn_real_harmonic_isingChar
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    {K : ℕ} (hK : K ≤ 7) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (e : ∀ n, Finset.Icc K (N n) → ι n) (he : ∀ n, Function.Injective (e n))
    (hce : ∀ n (k : Finset.Icc K (N n)), c n (e n k) = 1 / (2 * ((k : ℕ) : ℝ))) :
    ¬ ∀ R : ℝ, TendstoUniformlyOn (fun n (t : ℝ) => isingChar (J n) (E n) (c n) t)
      (fun t : ℝ => XiC t / XiC 0) atTop (Icc (-R) R) := fun hconv =>
  not_tendstoLocallyUniformly_harmonic_isingChar J E hJ c hc hK N hN e he hce
    (tendstoLocallyUniformly_of_tendstoUniformlyOn_real J E hJ c hc hconv)

end

end RHTower.GriffithsSimon
