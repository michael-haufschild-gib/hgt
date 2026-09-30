import GaloisForLFunctions.RHTower.WeilFullConeWindowPinning
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpSelfRateOne

/-!
# The prime number theorem in square-root-normalized log windows

Let `g` be a real `C²` function supported in `[−¼, ¼]` and `ρ(x) = ∫ g(t) g(t − x) dt` its
autocorrelation. The smoothed log-window of a weight sequence is
`S_L(lam) = Σ_{n≥2} lam(n)(ρ(log n − L) + ρ(log n + L))/√n` (`windowSum`).

**Theorem** (`exists_abs_windowSum_vonMangoldt_sub_le`). Unconditionally there are `C` and `L₀`
such that for every `L ≥ L₀`

`|S_L(Λ) − 2 P₊ P₋ cosh(L/2)| ≤ C (1 + e^{L/2} e^{−√L/1920000})`,

where `P_± = ∫ g(u) e^{∓u/2} du`. Window pinning (`exists_abs_windowSum_sub_le`) gives the same main
term with an `O(1)` error for every full-cone Weil-positive sequence, so the windows of
`lam − Λ` are `O(1 + e^{L/2} e^{−c√L})` for every member `lam` of the Weil cone.

**Proof.** For `L ≥ 1` the window is `w(n) = G(log n)` with `G(u) = e^{−u/2} ρ(u − L)`.
- *Primes.* Put `E(N) = Σ_{n≤N} Λ(n) − N`. Summation by parts gives
  `Σ_n (Λ(n) − 1) w(n) = −Σ_n E(n)(w(n+1) − w(n))`. Only `n ≥ e^{L−3/2}` contribute, and there
  `|w(n+1) − w(n)| ≤ (K + H) n^{−3/2}` while `|E(n)| ≤ B n e^{−√(log n)/960000}`.
- *Integers.* Each `w(n)` differs from `∫_n^{n+1} G(log x) dx` by `O(e^{−3L/2})`, and there are
  `O(e^{L})` active `n`. The substitution `x = e^u` gives
  `∫ G(log x) dx = ∫ e^{u/2} ρ(u − L) du = e^{L/2} ∫ ρ(v) e^{v/2} dv = e^{L/2} P₊ P₋`, where the
  last identity is the Fourier factorization of an autocorrelation at `−i/2`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finsupp
open scoped Real
open Zeta23

namespace RHTower.WeilOneSided

variable {g : ℝ → ℝ}

/-! ## The window as a finite sum -/

theorem windowValue_eq_zero_of_le (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L : ℝ} {n : ℕ}
    (hn : Real.exp (|L| + 1) ≤ n) : windowValue g L n = 0 := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have hlog : |L| + 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]; exact hn
  unfold windowValue
  rw [autoCorr_eq_zero hsupp (by
      rw [abs_of_pos (by linarith [le_abs_self L, neg_abs_le L])]
      linarith [le_abs_self L]),
    autoCorr_eq_zero hsupp (by
      rw [abs_of_pos (by linarith [neg_abs_le L])]
      linarith [neg_abs_le L]), add_zero, zero_div]

/-- **The window as a finite sum**: for `M ≥ e^{|L|+1}`,
`S_L(lam) = Σ_{2 ≤ n < M} lam(n) w_L(n)`. -/
theorem windowSum_eq_sum (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (lam : ℕ → ℝ) {L : ℝ} {M : ℕ}
    (hM : Real.exp (|L| + 1) ≤ M) :
    windowSum hg hgc hsupp lam L =
      ∑ n ∈ Finset.range M, if 2 ≤ n then lam n * windowValue g L n else 0 := by
  unfold windowSum
  rw [Finsupp.linearCombination_apply]
  set s : Finset LogIndex := (Finset.range M).subtype (fun n => 2 ≤ n) with hs
  have hsub : (windowVector hg hgc hsupp L).support ⊆ s := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj
    rw [hs, Finset.mem_subtype, Finset.mem_range]
    by_contra hlt
    push Not at hlt
    apply hj
    show windowValue g L j = 0
    exact windowValue_eq_zero_of_le hsupp (hM.trans (by exact_mod_cast hlt))
  rw [Finsupp.sum_of_support_subset _ hsub (fun (j : LogIndex) (a : ℝ) => a • lam j)
    (fun j _ => zero_smul ℝ _)]
  have e : ∑ j ∈ s, (windowVector hg hgc hsupp L) j • lam j =
      ∑ j ∈ s, (fun n : ℕ => lam n * windowValue g L n) j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [windowVector, Finsupp.ofSupportFinite_coe, smul_eq_mul]
    ring
  rw [e, hs, ← Finset.sum_filter]
  exact Finset.sum_subtype_eq_sum_filter (s := Finset.range M) (p := fun n : ℕ => 2 ≤ n)
    (fun n => lam n * windowValue g L n)

theorem windowSum_sub (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (lam₁ lam₂ : ℕ → ℝ) (L : ℝ) :
    windowSum hg hgc hsupp lam₁ L - windowSum hg hgc hsupp lam₂ L =
      windowSum hg hgc hsupp (fun n => lam₁ n - lam₂ n) L := by
  obtain ⟨M, hM⟩ := exists_nat_ge (Real.exp (|L| + 1))
  rw [windowSum_eq_sum hg hgc hsupp _ hM, windowSum_eq_sum hg hgc hsupp _ hM,
    windowSum_eq_sum hg hgc hsupp _ hM, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-! ## Regularity of the autocorrelation -/

theorem autoCorr_nonneg_of_nonneg (hg0 : ∀ u, 0 ≤ g u) (x : ℝ) : 0 ≤ autoCorr g x :=
  integral_nonneg fun t => mul_nonneg (hg0 t) (hg0 _)

theorem integrable_mul_translate (hgcont : Continuous g) (hgc : HasCompactSupport g) (z : ℝ) :
    Integrable fun t => g t * g (t - z) :=
  (hgcont.mul (hgcont.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    hgc.mul_right

/-- `ρ` is Lipschitz with constant `K ‖g‖₁` when `g` is `K`-Lipschitz. -/
theorem abs_autoCorr_sub_le (hgcont : Continuous g) (hgc : HasCompactSupport g) {K : NNReal}
    (hK : LipschitzWith K g) (x y : ℝ) :
    |autoCorr g x - autoCorr g y| ≤ K * (∫ t, |g t|) * |x - y| := by
  have hgi : Integrable g := hgcont.integrable_of_hasCompactSupport hgc
  unfold autoCorr
  rw [← integral_sub (integrable_mul_translate hgcont hgc x) (integrable_mul_translate hgcont hgc y)]
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ t, |g t * g (t - x) - g t * g (t - y)| ≤ K * |x - y| * |g t| := by
    intro t
    rw [← mul_sub, abs_mul]
    have h := hK.dist_le_mul (t - x) (t - y)
    rw [Real.dist_eq, Real.dist_eq, show t - x - (t - y) = y - x by ring, abs_sub_comm y x] at h
    calc |g t| * |g (t - x) - g (t - y)| ≤ |g t| * (K * |x - y|) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = K * |x - y| * |g t| := by ring
  calc ∫ t, |g t * g (t - x) - g t * g (t - y)| ≤ ∫ t, K * |x - y| * |g t| :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
          (hgi.abs.const_mul _) (Eventually.of_forall hpt)
    _ = K * (∫ t, |g t|) * |x - y| := by rw [integral_const_mul]; ring

theorem abs_autoCorr_le (hgcont : Continuous g) (hgc : HasCompactSupport g) {H₀ : ℝ}
    (hH : ∀ a, |g a| ≤ H₀) (x : ℝ) : |autoCorr g x| ≤ H₀ * ∫ t, |g t| := by
  have hgi : Integrable g := hgcont.integrable_of_hasCompactSupport hgc
  unfold autoCorr
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ t, |g t * g (t - x)| ≤ ∫ t, H₀ * |g t| :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
          (hgi.abs.const_mul _) (Eventually.of_forall fun t => by
            show |g t * g (t - x)| ≤ H₀ * |g t|
            rw [abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hH _) (abs_nonneg _))
    _ = H₀ * ∫ t, |g t| := integral_const_mul _ _

theorem continuous_autoCorr (hgcont : Continuous g) (hgc : HasCompactSupport g) {K : NNReal}
    (hK : LipschitzWith K g) : Continuous (autoCorr g) := by
  have h0 : 0 ≤ (K : ℝ) * ∫ t, |g t| := mul_nonneg K.2 (integral_nonneg fun t => abs_nonneg _)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨_, h0⟩) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact abs_autoCorr_sub_le hgcont hgc hK x y

/-- The autocorrelation has regularity constants: it is Lipschitz, bounded and continuous. -/
theorem exists_autoCorr_constants (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∃ Kρ Hρ : ℝ, 0 ≤ Kρ ∧ 0 ≤ Hρ ∧ (∀ x y, |autoCorr g x - autoCorr g y| ≤ Kρ * |x - y|) ∧
      (∀ x, |autoCorr g x| ≤ Hρ) ∧ Continuous (autoCorr g) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  obtain ⟨H₀, hH₀⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hH : ∀ a, |g a| ≤ H₀ := fun a => by simpa [Real.norm_eq_abs] using hH₀ a
  have hI : 0 ≤ ∫ t, |g t| := integral_nonneg fun t => abs_nonneg _
  have hH0 : 0 ≤ H₀ := (abs_nonneg _).trans (hH 0)
  exact ⟨K * ∫ t, |g t|, H₀ * ∫ t, |g t|, mul_nonneg K.2 hI, mul_nonneg hH0 hI,
    abs_autoCorr_sub_le hg.continuous hgc hK, abs_autoCorr_le hg.continuous hgc hH,
    continuous_autoCorr hg.continuous hgc hK⟩

/-- **The main-term constant**: `∫ ρ(v) e^{v/2} dv = P₊ P₋`. This is the factorization
`\widehat{g ⋆ g̃}(−i/2) = ĝ(−i/2) · conj(ĝ(i/2))` of the Fourier transform of an autocorrelation. -/
theorem integral_autoCorr_mul_exp_half (hgcont : Continuous g) (hgc : HasCompactSupport g) :
    ∫ v, autoCorr g v * Real.exp (v / 2) =
      (∫ u, g u * Real.exp (-u / 2)) * ∫ u, g u * Real.exp (u / 2) := by
  have hc : Continuous (liftC g) := Complex.continuous_ofReal.comp hgcont
  have hcs := hasCompactSupport_liftC hgc
  have h := EF.paperFT_weilTest hc hc hcs hcs (-I / 2)
  have hconj : (starRingEnd ℂ) (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hconj, paperFT_liftC_half_I, paperFT_liftC_neg_half_I, Complex.conj_ofReal] at h
  have hl : paperFT (EF.weilTest (liftC g) (liftC g)) (-I / 2) =
      ((∫ v, autoCorr g v * Real.exp (v / 2) : ℝ) : ℂ) := by
    rw [paperFT, ← integral_complex_ofReal]
    congr 1; funext v
    rw [weilTest_liftC, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    rw [show I * (-I / 2) * (v : ℂ) = -(I * I) * v / 2 by ring, Complex.I_mul_I]
    ring
  rw [hl, ← Complex.ofReal_mul] at h
  rw [mul_comm]
  exact_mod_cast h

/-! ## The window in the log variable -/

/-- The log-window `G(u) = e^{−u/2} ρ(u − L)`. -/
def logWindow (g : ℝ → ℝ) (L u : ℝ) : ℝ := Real.exp (-u / 2) * autoCorr g (u - L)

theorem logWindow_eq_zero (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L u : ℝ} (h : 1 / 2 < |u - L|) :
    logWindow g L u = 0 := by
  rw [logWindow, autoCorr_eq_zero hsupp h, mul_zero]

theorem abs_sub_le_of_logWindow_ne_zero (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L u : ℝ}
    (h : logWindow g L u ≠ 0) : |u - L| ≤ 1 / 2 := by
  by_contra h'
  exact h (logWindow_eq_zero hsupp (not_le.mp h'))

theorem windowValue_eq_logWindow (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L : ℝ} (hL : 1 ≤ L)
    (n : ℕ) : windowValue g L n = logWindow g L (Real.log n) := by
  have h0 := Real.log_natCast_nonneg n
  have h2 : autoCorr g (Real.log n + L) = 0 :=
    autoCorr_eq_zero hsupp (by rw [abs_of_pos (by linarith)]; linarith)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : autoCorr g (-L) = 0 :=
      autoCorr_eq_zero hsupp (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    simp [windowValue, logWindow, h1]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt n = Real.exp (Real.log n / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]; ring_nf
    rw [windowValue, logWindow, h2, add_zero, hs, div_eq_mul_inv, ← Real.exp_neg, neg_div,
      mul_comm]

/-- The Lipschitz bound of `G(u) = e^{−u/2} h(u − L)` on `[a, ∞)`. -/
theorem abs_expWindow_sub_le {h : ℝ → ℝ} {K H : ℝ} (hK : ∀ x y, |h x - h y| ≤ K * |x - y|)
    (hH : ∀ x, |h x| ≤ H) (L : ℝ) {a u v : ℝ} (hu : a ≤ u) (hv : a ≤ v) :
    |Real.exp (-u / 2) * h (u - L) - Real.exp (-v / 2) * h (v - L)| ≤
      Real.exp (-a / 2) * (K + H) * |u - v| := by
  have e : Real.exp (-u / 2) * h (u - L) - Real.exp (-v / 2) * h (v - L) =
      Real.exp (-u / 2) * (h (u - L) - h (v - L)) +
        (Real.exp (-u / 2) - Real.exp (-v / 2)) * h (v - L) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := hK (u - L) (v - L)
  rw [show u - L - (v - L) = u - v by ring] at h1
  have h2 := abs_exp_neg_half_sub_le hu hv
  have h3 := hH (v - L)
  have h4 : Real.exp (-u / 2) ≤ Real.exp (-a / 2) := Real.exp_le_exp.mpr (by linarith)
  have hH0 : 0 ≤ H := (abs_nonneg _).trans h3
  have he := Real.exp_pos (-a / 2)
  have hab := abs_nonneg (u - v)
  calc Real.exp (-u / 2) * |h (u - L) - h (v - L)| + |Real.exp (-u / 2) - Real.exp (-v / 2)| *
        |h (v - L)|
      ≤ Real.exp (-a / 2) * (K * |u - v|) + (1 / 2 * Real.exp (-a / 2) * |u - v|) * H :=
        add_le_add (mul_le_mul h4 h1 (abs_nonneg _) he.le)
          (mul_le_mul h2 h3 (abs_nonneg _) (by positivity))
    _ ≤ Real.exp (-a / 2) * (K + H) * |u - v| := by
        nlinarith [mul_nonneg (mul_nonneg he.le hH0) hab]
where
  abs_exp_neg_half_sub_le {a u v : ℝ} (hu : a ≤ u) (hv : a ≤ v) :
      |Real.exp (-u / 2) - Real.exp (-v / 2)| ≤ 1 / 2 * Real.exp (-a / 2) * |u - v| := by
    wlog huv : u ≤ v generalizing u v
    · rw [abs_sub_comm, abs_sub_comm u v]; exact this hv hu (by linarith)
    have h1 : Real.exp (-v / 2) ≤ Real.exp (-u / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-u / 2) * (1 + (-v / 2 - -u / 2)) ≤ Real.exp (-v / 2) := by
      have := Real.add_one_le_exp (-v / 2 - -u / 2)
      have e : Real.exp (-v / 2) = Real.exp (-u / 2) * Real.exp (-v / 2 - -u / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    have h3 : Real.exp (-u / 2) ≤ Real.exp (-a / 2) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.exp_pos (-u / 2)]

theorem log_sub_log_le {m x : ℝ} (hm : 0 < m) (hx : m ≤ x) :
    Real.log x - Real.log m ≤ (x - m) / m := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  rw [← Real.log_div hx0.ne' hm.ne', sub_div, div_self hm.ne']
  exact Real.log_le_sub_one_of_pos (div_pos hx0 hm)

/-! ## Summation by parts against the Chebyshev error -/

theorem sum_range_sub_mul_eq (A F : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ Finset.range M, (A (n + 1) - A n) * F (n + 1) =
      A M * F M - A 0 * F 0 - ∑ n ∈ Finset.range M, A n * (F (n + 1) - F n) := by
  induction M with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

/-- The Chebyshev error `E(N) = Σ_{n ≤ N} Λ(n) − N`. -/
def psiRemainderNat (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) - N

theorem psiRemainderNat_zero : psiRemainderNat 0 = 0 := by simp [psiRemainderNat]

theorem psiRemainderNat_succ_sub (N : ℕ) :
    psiRemainderNat (N + 1) - psiRemainderNat N = ArithmeticFunction.vonMangoldt (N + 1) - 1 := by
  unfold psiRemainderNat
  rw [Finset.sum_range_succ _ (N + 1)]
  push_cast; ring

theorem exists_abs_psiRemainderNat_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      |psiRemainderNat n| ≤ B * n * Real.exp (-(Real.sqrt (Real.log n) / 960000)) := by
  obtain ⟨B, hB, hev⟩ := RHTower.Sieve.exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
  refine ⟨B, hB, ⌈a⌉₊, fun n hn => ?_⟩
  have h := ha n (Nat.ceil_le.mp hn)
  rw [Nat.floor_natCast] at h
  exact h

/-- A consecutive window difference is nonzero only for `n ≥ 1` with `log n ≥ L − 3/2`. -/
theorem active_of_logWindow_sub_ne_zero (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L : ℝ} {n : ℕ}
    (h : logWindow g L (Real.log (n + 1 : ℕ)) - logWindow g L (Real.log n) ≠ 0) :
    1 ≤ n ∧ L - 3 / 2 ≤ Real.log n := by
  have hn : 1 ≤ n := by
    by_contra h0
    obtain rfl : n = 0 := by omega
    simp at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmono : Real.log n ≤ Real.log (n + 1 : ℕ) := Real.log_le_log hn0 (by push_cast; linarith)
  have key : L - 1 / 2 ≤ Real.log (n + 1 : ℕ) := by
    by_cases h1 : logWindow g L (Real.log (n + 1 : ℕ)) = 0
    · have h2 : logWindow g L (Real.log n) ≠ 0 := by
        intro h2; exact h (by rw [h1, h2, sub_zero])
      linarith [(abs_le.mp (abs_sub_le_of_logWindow_ne_zero hsupp h2)).1]
    · linarith [(abs_le.mp (abs_sub_le_of_logWindow_ne_zero hsupp h1)).1]
  have h2n : Real.log (n + 1 : ℕ) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul two_ne_zero hn0.ne']
    exact Real.log_le_log (by positivity) (by push_cast; linarith)
  exact ⟨hn, by linarith [Real.log_two_lt_d9]⟩

/-- **The prime part.** `|Σ_{n<M} (Λ(n+1) − 1) w(n+1)| ≤ M · B(K + H) e^{−(L−3/2)/2}
e^{−√(L−3/2)/960000}` once `e^{L−3/2}` passes the threshold of the Chebyshev bound. -/
theorem abs_sum_vonMangoldt_sub_one_mul_logWindow_le (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    {Kρ Hρ : ℝ} (hK0 : 0 ≤ Kρ) (hK : ∀ x y, |autoCorr g x - autoCorr g y| ≤ Kρ * |x - y|)
    (hH : ∀ x, |autoCorr g x| ≤ Hρ) {B : ℝ} (hB : 0 ≤ B) {N₀ : ℕ}
    (hE : ∀ n : ℕ, N₀ ≤ n →
      |psiRemainderNat n| ≤ B * n * Real.exp (-(Real.sqrt (Real.log n) / 960000)))
    {L : ℝ} (hL₀ : (N₀ : ℝ) ≤ Real.exp (L - 3 / 2)) {M : ℕ} (hM : Real.exp (L + 1) ≤ M) :
    |∑ n ∈ Finset.range M, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) - 1) *
        logWindow g L (Real.log (n + 1 : ℕ))| ≤
      M * (B * (Kρ + Hρ) * Real.exp (-(L - 3 / 2) / 2) *
        Real.exp (-(Real.sqrt (L - 3 / 2) / 960000))) := by
  set w : ℕ → ℝ := fun n => logWindow g L (Real.log n) with hw
  have hH0 : 0 ≤ Hρ := (abs_nonneg _).trans (hH 0)
  have e1 : ∑ n ∈ Finset.range M, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) - 1) *
      logWindow g L (Real.log (n + 1 : ℕ)) =
      ∑ n ∈ Finset.range M, (psiRemainderNat (n + 1) - psiRemainderNat n) * w (n + 1) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [psiRemainderNat_succ_sub]
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos _) hM
  have hwM : w M = 0 := by
    have : L + 1 ≤ Real.log M := (Real.le_log_iff_exp_le hM0).mpr hM
    exact logWindow_eq_zero hsupp (by rw [abs_of_pos (by linarith)]; linarith)
  rw [e1, sum_range_sub_mul_eq, hwM, psiRemainderNat_zero, mul_zero, zero_mul, sub_zero, zero_sub,
    abs_neg]
  set β := B * (Kρ + Hρ) * Real.exp (-(L - 3 / 2) / 2) *
    Real.exp (-(Real.sqrt (L - 3 / 2) / 960000)) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hterm : ∀ n ∈ Finset.range M, |psiRemainderNat n * (w (n + 1) - w n)| ≤ β := by
    intro n _
    by_cases hz : w (n + 1) - w n = 0
    · rw [hz, mul_zero, abs_zero]; exact hβ0
    obtain ⟨hn1, hlog⟩ := active_of_logWindow_sub_ne_zero hsupp hz
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : N₀ ≤ n := by
      have : Real.exp (L - 3 / 2) ≤ n := by
        rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hlog
      exact_mod_cast hL₀.trans this
    have hEn := hE n hnN
    have hlogd : |Real.log (n + 1 : ℕ) - Real.log n| ≤ 1 / n := by
      have h1 := log_sub_log_le hn0 (show (n : ℝ) ≤ (n + 1 : ℕ) by push_cast; linarith)
      have h2 : Real.log n ≤ Real.log (n + 1 : ℕ) := Real.log_le_log hn0 (by push_cast; linarith)
      rw [abs_of_nonneg (by linarith)]
      calc Real.log (n + 1 : ℕ) - Real.log n ≤ (((n + 1 : ℕ) : ℝ) - n) / n := h1
        _ = 1 / n := by push_cast; ring
    have hwd : |w (n + 1) - w n| ≤ Real.exp (-Real.log n / 2) * (Kρ + Hρ) * (1 / n) := by
      have := abs_expWindow_sub_le hK hH L (a := Real.log n)
        (u := Real.log (n + 1 : ℕ)) (v := Real.log n)
        (Real.log_le_log hn0 (by push_cast; linarith)) le_rfl
      refine this.trans (mul_le_mul_of_nonneg_left hlogd (by positivity))
    have hX : Real.exp (-(Real.sqrt (Real.log n) / 960000)) ≤
        Real.exp (-(Real.sqrt (L - 3 / 2) / 960000)) := by
      rw [Real.exp_le_exp]
      have := Real.sqrt_le_sqrt hlog
      linarith
    have hY : Real.exp (-Real.log n / 2) ≤ Real.exp (-(L - 3 / 2) / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [abs_mul]
    calc |psiRemainderNat n| * |w (n + 1) - w n|
        ≤ (B * n * Real.exp (-(Real.sqrt (Real.log n) / 960000))) *
            (Real.exp (-Real.log n / 2) * (Kρ + Hρ) * (1 / n)) :=
          mul_le_mul hEn hwd (abs_nonneg _) (by positivity)
      _ = B * (Kρ + Hρ) * Real.exp (-Real.log n / 2) *
            Real.exp (-(Real.sqrt (Real.log n) / 960000)) := by
          field_simp
      _ ≤ β := by
          rw [hβ]
          have hBK : 0 ≤ B * (Kρ + Hρ) := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hY hBK) hX (by positivity) (by positivity)
  calc |∑ n ∈ Finset.range M, psiRemainderNat n * (w (n + 1) - w n)|
      ≤ ∑ n ∈ Finset.range M, |psiRemainderNat n * (w (n + 1) - w n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range M, β := Finset.sum_le_sum hterm
    _ = M * β := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## The integer sum against the integral -/

theorem continuous_logWindow (hcont : Continuous (autoCorr g)) (L : ℝ) :
    Continuous (logWindow g L) := by
  unfold logWindow; fun_prop

theorem continuousOn_logWindow_log (hcont : Continuous (autoCorr g)) (L : ℝ) :
    ContinuousOn (fun x => logWindow g L (Real.log x)) {0}ᶜ :=
  (continuous_logWindow hcont L).comp_continuousOn Real.continuousOn_log

/-- **The substitution `x = e^u`**: `∫_1^X G(log x) dx = e^{L/2} ∫ ρ(v) e^{v/2} dv` once the
window lies inside `[1, X]`. -/
theorem integral_logWindow_log_eq (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L : ℝ} (hL : 1 ≤ L)
    {X : ℝ} (hX : Real.exp (L + 1) ≤ X) :
    ∫ x in (1 : ℝ)..X, logWindow g L (Real.log x) =
      Real.exp (L / 2) * ∫ v, autoCorr g v * Real.exp (v / 2) := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX : L + 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).mpr hX
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := Real.log X)
    (f := Real.exp) (f' := Real.exp) (g := fun x => logWindow g L (Real.log x))
    Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => (Real.exp_pos x).le)
  rw [Real.exp_zero, Real.exp_log hX0] at hsub
  rw [← hsub]
  have hpt : ∀ u : ℝ, ((fun x => logWindow g L (Real.log x)) ∘ Real.exp) u * Real.exp u =
      Real.exp (u / 2) * autoCorr g (u - L) := by
    intro u
    simp only [Function.comp, Real.log_exp, logWindow]
    rw [mul_comm, ← mul_assoc, ← Real.exp_add]
    ring_nf
  simp_rw [hpt]
  rw [intervalIntegral.integral_of_le (by linarith), setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun u hu => by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
      rw [autoCorr_eq_zero hsupp, mul_zero]
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)]
  rw [← integral_add_right_eq_self (fun u => Real.exp (u / 2) * autoCorr g (u - L)) L,
    ← integral_const_mul]
  congr 1; funext v
  rw [add_sub_cancel_right, show (v + L) / 2 = L / 2 + v / 2 by ring, Real.exp_add]
  ring

/-- **The integer part.** `|Σ_{n<M} w(n+1) − ∫_1^{M+1} G(log x) dx| ≤ M (K + H) e^{−3(L−3/2)/2}`. -/
theorem abs_sum_logWindow_sub_integral_le (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {Kρ Hρ : ℝ}
    (hK0 : 0 ≤ Kρ) (hK : ∀ x y, |autoCorr g x - autoCorr g y| ≤ Kρ * |x - y|)
    (hH : ∀ x, |autoCorr g x| ≤ Hρ) (hcont : Continuous (autoCorr g)) (L : ℝ) (M : ℕ) :
    |∑ n ∈ Finset.range M, logWindow g L (Real.log (n + 1 : ℕ)) -
        ∫ x in (1 : ℝ)..(M + 1 : ℝ), logWindow g L (Real.log x)| ≤
      M * ((Kρ + Hρ) * Real.exp (-(3 * (L - 3 / 2) / 2))) := by
  set F : ℝ → ℝ := fun x => logWindow g L (Real.log x) with hF
  have hH0 : 0 ≤ Hρ := (abs_nonneg _).trans (hH 0)
  have hII : ∀ k : ℕ, IntervalIntegrable F volume ((k : ℝ) + 1) (((k + 1 : ℕ) : ℝ) + 1) := by
    intro k
    refine ((continuousOn_logWindow_log hcont L).mono fun x hx => ?_).intervalIntegrable
    rw [Set.mem_uIcc] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast at hx
    rcases hx with hx | hx <;> linarith [hx.1, hx.2]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (f := F) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) + 1) (n := M) (fun k _ => hII k)
  simp only [Nat.cast_zero, zero_add] at hsplit
  rw [← hsplit, ← Finset.sum_sub_distrib]
  set γ := (Kρ + Hρ) * Real.exp (-(3 * (L - 3 / 2) / 2)) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hterm : ∀ n ∈ Finset.range M, |logWindow g L (Real.log (n + 1 : ℕ)) -
      ∫ x in (n : ℝ) + 1..((n + 1 : ℕ) : ℝ) + 1, F x| ≤ γ := by
    intro n _
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hconst : logWindow g L (Real.log (n + 1 : ℕ)) =
        ∫ _x in (n : ℝ) + 1..((n + 1 : ℕ) : ℝ) + 1, F ((n : ℝ) + 1) := by
      rw [intervalIntegral.integral_const]; push_cast
      rw [show (n : ℝ) + 1 + 1 - (n + 1) = 1 by ring, one_smul]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hII n)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (n : ℝ) + 1)
      (b := ((n + 1 : ℕ) : ℝ) + 1) (C := γ) (f := fun x => F ((n : ℝ) + 1) - F x) (fun x hx => by
        rw [Set.uIoc_of_le (by push_cast; linarith), Set.mem_Ioc] at hx
        push_cast at hx
        obtain ⟨hx1, hx2⟩ := hx
        have hx0 : 0 < x := by linarith
        rw [Real.norm_eq_abs]
        by_cases hact : L - 3 / 2 ≤ Real.log ((n : ℝ) + 1)
        · have hle : Real.log ((n : ℝ) + 1) ≤ Real.log x := Real.log_le_log hn1 hx1.le
          have h1 := abs_expWindow_sub_le hK hH L (a := Real.log ((n : ℝ) + 1)) le_rfl hle
          have hd : |Real.log ((n : ℝ) + 1) - Real.log x| ≤ Real.exp (-Real.log ((n : ℝ) + 1)) := by
            rw [abs_sub_comm, abs_of_nonneg (by linarith), Real.exp_neg, Real.exp_log hn1]
            calc Real.log x - Real.log ((n : ℝ) + 1) ≤ (x - ((n : ℝ) + 1)) / ((n : ℝ) + 1) :=
                  log_sub_log_le hn1 hx1.le
              _ ≤ 1 / ((n : ℝ) + 1) := by
                  apply div_le_div_of_nonneg_right _ hn1.le; linarith
              _ = ((n : ℝ) + 1)⁻¹ := one_div _
          calc |F ((n : ℝ) + 1) - F x|
              ≤ Real.exp (-Real.log ((n : ℝ) + 1) / 2) * (Kρ + Hρ) *
                  |Real.log ((n : ℝ) + 1) - Real.log x| := h1
            _ ≤ Real.exp (-Real.log ((n : ℝ) + 1) / 2) * (Kρ + Hρ) *
                  Real.exp (-Real.log ((n : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left hd (by positivity)
            _ = (Kρ + Hρ) * Real.exp (-(3 * Real.log ((n : ℝ) + 1) / 2)) := by
                rw [mul_comm (Real.exp _) (Kρ + Hρ), mul_assoc, ← Real.exp_add]; ring_nf
            _ ≤ γ := by
                rw [hγ]
                exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
                  (by linarith)
        · push Not at hact
          have hlx : Real.log x ≤ Real.log 2 + Real.log ((n : ℝ) + 1) := by
            rw [← Real.log_mul two_ne_zero hn1.ne']
            exact Real.log_le_log hx0 (by linarith)
          have e1 : F ((n : ℝ) + 1) = 0 :=
            logWindow_eq_zero hsupp (by rw [abs_of_neg (by linarith)]; linarith)
          have e2 : F x = 0 :=
            logWindow_eq_zero hsupp (by
              rw [abs_of_neg (by linarith [Real.log_two_lt_d9])]
              linarith [Real.log_two_lt_d9])
          rw [e1, e2, sub_zero, abs_zero]; exact hγ0)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans (le_of_eq ?_)
    push_cast
    rw [show (n : ℝ) + 1 + 1 - (n + 1) = 1 by ring, abs_one, mul_one]
  calc |∑ n ∈ Finset.range M, (logWindow g L (Real.log (n + 1 : ℕ)) -
          ∫ x in (n : ℝ) + 1..((n + 1 : ℕ) : ℝ) + 1, F x)|
      ≤ ∑ n ∈ Finset.range M, |logWindow g L (Real.log (n + 1 : ℕ)) -
          ∫ x in (n : ℝ) + 1..((n + 1 : ℕ) : ℝ) + 1, F x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range M, γ := Finset.sum_le_sum hterm
    _ = M * γ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## The smoothed prime number theorem for the log-windows -/

theorem windowSum_vonMangoldt_eq_sum_logWindow (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L : ℝ} (hL : 1 ≤ L) {M : ℕ}
    (hM : Real.exp (L + 1) ≤ M) :
    windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L =
      ∑ n ∈ Finset.range M, (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        logWindow g L (Real.log (n + 1 : ℕ)) := by
  have hM1 : Real.exp (|L| + 1) ≤ ((M + 1 : ℕ) : ℝ) := by
    rw [abs_of_pos (by linarith)]; push_cast; linarith
  rw [windowSum_eq_sum hg hgc hsupp _ hM1, Finset.sum_range_succ', if_neg (by omega), add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [windowValue_eq_logWindow hsupp hL]
  split_ifs with h2
  · rfl
  · obtain rfl : n = 0 := by omega
    simp

/-- **The smoothed prime number theorem in log-windows.** Unconditionally,
`|S_L(Λ) − 2P₊P₋ cosh(L/2)| ≤ C (1 + e^{L/2} e^{−√L/1920000})` for all large `L`. -/
theorem exists_abs_windowSum_vonMangoldt_sub_le (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    ∃ C L₀ : ℝ, ∀ L, L₀ ≤ L →
      |windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L -
          2 * (∫ u, g u * Real.exp (-u / 2)) * (∫ u, g u * Real.exp (u / 2)) *
            Real.cosh (L / 2)| ≤
        C * (1 + Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := by
  obtain ⟨Kρ, Hρ, hK0, hH0, hK, hH, hcont⟩ := exists_autoCorr_constants hg hgc
  obtain ⟨B, hB, N₀, hE⟩ := exists_abs_psiRemainderNat_le
  set Pp := ∫ u, g u * Real.exp (-u / 2) with hPp
  set Pm := ∫ u, g u * Real.exp (u / 2) with hPm
  have hP := integral_autoCorr_mul_exp_half hg.continuous hgc
  set C₁ := 2 * Real.exp (7 / 4) * B * (Kρ + Hρ) with hC₁
  set C₂ := 2 * Real.exp (13 / 4) * (Kρ + Hρ) + |Pp * Pm| with hC₂
  refine ⟨C₁ + C₂, max 3 (Real.log N₀ + 3 / 2), fun L hL => ?_⟩
  have hL3 : 3 ≤ L := le_of_max_le_left hL
  have hLN : (N₀ : ℝ) ≤ Real.exp (L - 3 / 2) := by
    rcases Nat.eq_zero_or_pos N₀ with h | h
    · rw [h, Nat.cast_zero]; exact (Real.exp_pos _).le
    · rw [← Real.exp_log (Nat.cast_pos.mpr h)]
      exact Real.exp_le_exp.mpr (by linarith [le_of_max_le_right hL])
  set M := ⌈Real.exp (L + 1)⌉₊ with hMdef
  have hM : Real.exp (L + 1) ≤ M := Nat.le_ceil _
  have hMle : (M : ℝ) ≤ 2 * Real.exp (L + 1) := by
    have h1 := Nat.ceil_lt_add_one (Real.exp_pos (L + 1)).le
    have h2 : 1 ≤ Real.exp (L + 1) := Real.one_le_exp (by linarith)
    linarith
  have hS := windowSum_vonMangoldt_eq_sum_logWindow hg hgc hsupp (by linarith) hM
  have hprime := abs_sum_vonMangoldt_sub_one_mul_logWindow_le hsupp hK0 hK hH hB hE hLN hM
  have hint := abs_sum_logWindow_sub_integral_le hsupp hK0 hK hH hcont L M
  rw [integral_logWindow_log_eq hsupp (L := L) (by linarith) (X := (M : ℝ) + 1) (by linarith),
    hP] at hint
  set X := ∑ n ∈ Finset.range M, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) - 1) *
    logWindow g L (Real.log (n + 1 : ℕ)) with hXdef
  set Y := ∑ n ∈ Finset.range M, logWindow g L (Real.log (n + 1 : ℕ)) -
    Real.exp (L / 2) * (Pp * Pm) with hYdef
  have hdec : windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L -
      2 * Pp * Pm * Real.cosh (L / 2) = X + Y - Pp * Pm * Real.exp (-(L / 2)) := by
    have hsplit : ∑ n ∈ Finset.range M, (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        logWindow g L (Real.log (n + 1 : ℕ)) =
        X + ∑ n ∈ Finset.range M, logWindow g L (Real.log (n + 1 : ℕ)) := by
      rw [hXdef, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hS, hsplit, Real.cosh_eq, hYdef]
    ring
  have e1 : Real.exp (L + 1) * Real.exp (-(L - 3 / 2) / 2) =
      Real.exp (7 / 4) * Real.exp (L / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (L + 1) * Real.exp (-(3 * (L - 3 / 2) / 2)) =
      Real.exp (13 / 4) * Real.exp (-(L / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hsq : Real.sqrt L / 2 ≤ Real.sqrt (L - 3 / 2) := by
    rw [Real.le_sqrt (by positivity) (by linarith), div_pow, Real.sq_sqrt (by linarith)]
    linarith
  have hXs : Real.exp (-(Real.sqrt (L - 3 / 2) / 960000)) ≤
      Real.exp (-(Real.sqrt L / 1920000)) := by
    rw [Real.exp_le_exp]; linarith
  have hmL : Real.exp (-(L / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hKH : 0 ≤ Kρ + Hρ := by linarith
  have hXb : |X| ≤ C₁ * (Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := by
    calc |X| ≤ M * (B * (Kρ + Hρ) * Real.exp (-(L - 3 / 2) / 2) *
          Real.exp (-(Real.sqrt (L - 3 / 2) / 960000))) := hprime
      _ ≤ (2 * Real.exp (L + 1)) * (B * (Kρ + Hρ) * Real.exp (-(L - 3 / 2) / 2) *
          Real.exp (-(Real.sqrt (L - 3 / 2) / 960000))) :=
          mul_le_mul_of_nonneg_right hMle (by positivity)
      _ = 2 * B * (Kρ + Hρ) * (Real.exp (L + 1) * Real.exp (-(L - 3 / 2) / 2)) *
          Real.exp (-(Real.sqrt (L - 3 / 2) / 960000)) := by ring
      _ = 2 * B * (Kρ + Hρ) * (Real.exp (7 / 4) * Real.exp (L / 2)) *
          Real.exp (-(Real.sqrt (L - 3 / 2) / 960000)) := by rw [e1]
      _ ≤ 2 * B * (Kρ + Hρ) * (Real.exp (7 / 4) * Real.exp (L / 2)) *
          Real.exp (-(Real.sqrt L / 1920000)) :=
          mul_le_mul_of_nonneg_left hXs (by positivity)
      _ = C₁ * (Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := by rw [hC₁]; ring
  have hYb : |Y| ≤ 2 * Real.exp (13 / 4) * (Kρ + Hρ) := by
    calc |Y| ≤ M * ((Kρ + Hρ) * Real.exp (-(3 * (L - 3 / 2) / 2))) := hint
      _ ≤ (2 * Real.exp (L + 1)) * ((Kρ + Hρ) * Real.exp (-(3 * (L - 3 / 2) / 2))) :=
          mul_le_mul_of_nonneg_right hMle (by positivity)
      _ = 2 * (Kρ + Hρ) * (Real.exp (L + 1) * Real.exp (-(3 * (L - 3 / 2) / 2))) := by ring
      _ = 2 * (Kρ + Hρ) * Real.exp (13 / 4) * Real.exp (-(L / 2)) := by rw [e2]; ring
      _ ≤ 2 * (Kρ + Hρ) * Real.exp (13 / 4) * 1 :=
          mul_le_mul_of_nonneg_left hmL (by positivity)
      _ = 2 * Real.exp (13 / 4) * (Kρ + Hρ) := by ring
  have hZb : |Pp * Pm * Real.exp (-(L / 2))| ≤ |Pp * Pm| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) hmL
  have hE0 : 0 ≤ Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000)) := by positivity
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  rw [hdec]
  calc |X + Y - Pp * Pm * Real.exp (-(L / 2))|
      ≤ |X| + |Y| + |Pp * Pm * Real.exp (-(L / 2))| := by
        refine (abs_sub _ _).trans ?_
        linarith [abs_add_le X Y]
    _ ≤ C₁ * (Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) + C₂ := by
        rw [hC₂]; linarith
    _ ≤ (C₁ + C₂) * (1 + Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := by
        nlinarith [mul_nonneg hC₂0 hE0]

end RHTower.WeilOneSided
