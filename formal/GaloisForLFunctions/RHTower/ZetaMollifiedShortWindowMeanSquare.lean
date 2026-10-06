import GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentLimit
import GaloisForLFunctions.RHTower.PoissonArithmeticProgressionBound

/-!
# The mollified mean square of `ζ` on short windows of the critical line

Let `M_N(s) = Σ_{h ≤ N} b(h) h^{−s}`, `b(h) = μ(h) log(N/h)/log N`, with `N = ⌊T^θ⌋`, and let
`W = T^{1−η}` with `θ + η < ½`.

**Theorem** (`exists_eventually_shortWindow_meanSquare_le`).  There is `C` such that for all large
`T` and every `y₀ ∈ [T/2, 2T]`,

`∫_{y₀}^{y₀+W} |ζ(½ + it) M_N(½ + it)|² dt ≤ C W`.

**Proof.**  Integrate the quadruple expansion
`|ζ M_N|²(½ + it) = 2 Σ_{P,h,k} c_q V(2πmn/t) e^{itλ_q} + O(N log t/√t)` against a smooth window
`ψ((t − y₀)/W)`.

* The terms with `nk = mh` (`λ_q = 0`) sum to the ratio form `F(1, 1, t)`, which is bounded
  uniformly for `t ≍ T`.
* For `nk ≠ mh`, `|λ_q| ≥ 1/(N √(2mn))` (`le_abs_log_sub_log`).  On the Mellin line `Re w = 1`,
  `V(c/t) = (1/2π) ∫ c^{−w} t^w e^{w²}/w dv`, and `K`-fold integration by parts in `t` gives
  `|∫ ψ((t−y₀)/W) V(c/t) e^{iλt} dt| ≪_K T W/(c (W|λ|)^K)`
  (`exists_norm_integral_window_cutoff_cexp_le`).  For `mn ≤ T^{1+ε}` this is `T^{−Kδ}`-small
  (`δ = ½ − θ − η − ε/2`).  For `mn > T^{1+ε}` the power decay of `V` suffices.
* The approximate functional equation error contributes `O(W N log T/√T)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform

namespace RHTower.VerticalAP

noncomputable section

open ZetaNotch (pairAmp pairFreq pairProd)

/-! ## The window-power weight -/

/-- `φ_w(t) = ψ((t − y₀)/W) t^w`. -/
def windowPowerWeight (ψ : ℝ → ℂ) (y₀ W : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  ψ ((t - y₀) / W) * (t : ℂ) ^ w

theorem support_window_subset {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc (-1) 2) {W : ℝ}
    (hW : 0 < W) (y₀ : ℝ) (F : ℝ → ℂ) :
    Function.support (fun t => ψ ((t - y₀) / W) * F t) ⊆ Icc (y₀ - W) (y₀ + 2 * W) := by
  intro t ht
  have h1 : ψ ((t - y₀) / W) ≠ 0 := left_ne_zero_of_mul ht
  obtain ⟨h21, h22⟩ := hsupp h1
  rw [le_div_iff₀ hW] at h21
  rw [div_le_iff₀ hW] at h22
  exact ⟨by linarith, by linarith⟩

theorem window_eventually_zero {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc (-1) 2) {W : ℝ}
    (hW : 0 < W) (y₀ : ℝ) (F : ℝ → ℂ) {x : ℝ} (hx : x < y₀ - W ∨ y₀ + 2 * W < x) :
    (fun t => ψ ((t - y₀) / W) * F t) =ᶠ[nhds x] fun _ => 0 := by
  have hopen : IsOpen {t : ℝ | t < y₀ - W ∨ y₀ + 2 * W < t} :=
    (isOpen_gt' _).union (isOpen_lt' _)
  filter_upwards [hopen.mem_nhds hx] with t ht
  have : ψ ((t - y₀) / W) = 0 := by
    by_contra h
    obtain ⟨h21, h22⟩ := hsupp h
    rw [le_div_iff₀ hW] at h21
    rw [div_le_iff₀ hW] at h22
    rcases ht with ht | ht <;> linarith
  simp [this]

theorem cpow_eq_affine (w : ℂ) : (fun t : ℝ => (t : ℂ) ^ w) =
    fun y : ℝ => (((1 * y + 0 : ℝ)) : ℂ) ^ w := by
  funext y; simp

theorem contDiff_windowPowerWeight {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc (-1) 2) {y₀ W : ℝ} (hW : 0 < W) (hWy : W < y₀) (w : ℂ)
    (k : ℕ) : ContDiff ℝ k (windowPowerWeight ψ y₀ W w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : y₀ - W ≤ x ∧ x ≤ y₀ + 2 * W
  · have hpos : 0 < 1 * x + 0 := by linarith [hx.1]
    have h1 : ContDiffAt ℝ k (fun t => ψ ((t - y₀) / W)) x :=
      ((hψ k).comp ((contDiff_id.sub contDiff_const).div_const W)).contDiffAt
    have h2 := contDiffAt_affine_cpow (α := 1) (β := 0) w hpos k
    rw [← cpow_eq_affine] at h2
    exact h1.mul h2
  · have hx' : x < y₀ - W ∨ y₀ + 2 * W < x := by
      rcases not_and_or.mp hx with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    exact contDiffAt_const.congr_of_eventuallyEq
      (window_eventually_zero hsupp hW y₀ (fun t => (t : ℂ) ^ w) hx')

theorem iteratedDeriv_window (hψ : ∀ k : ℕ, ContDiff ℝ k (ψ : ℝ → ℂ)) {y₀ : ℝ} (W : ℝ)
    (i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun t => ψ ((t - y₀) / W)) x =
      (W⁻¹) ^ i • iteratedDeriv i ψ (W⁻¹ * (x - y₀)) := by
  have hfun : (fun t => ψ ((t - y₀) / W)) = fun t => (fun u => ψ (W⁻¹ * u)) (t - y₀) := by
    funext t; rw [div_eq_inv_mul]
  have h1 := congrFun (iteratedDeriv_comp_sub_const (n := i) (f := fun u => ψ (W⁻¹ * u))
    (s := y₀)) x
  have h2 := congrFun (iteratedDeriv_comp_const_smul (hψ i) W⁻¹) (x - y₀)
  rw [hfun]
  exact h1.trans h2

/-- **Derivative bound for the window-power weight.**  With `‖ψ^{(j)}‖ ≤ Ψ_j`, `2W ≤ y₀` and
`Re w ≥ 0`: `‖φ_w^{(k)}‖ ≤ (Σ_j C(k,j) Ψ_j) (‖w‖ + k)^k (y₀ + 2W)^{Re w} / W^k`. -/
theorem norm_iteratedDeriv_windowPowerWeight_le {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc (-1) 2) {Ψ : ℕ → ℝ} (hΨ : ∀ j y, ‖iteratedDeriv j ψ y‖ ≤ Ψ j)
    {y₀ W : ℝ} (hW : 0 < W) (hWy : 2 * W ≤ y₀) {w : ℂ} (hw : 0 ≤ w.re) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (windowPowerWeight ψ y₀ W w) x‖ ≤
      (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Ψ j) * (‖w‖ + k) ^ k *
        (y₀ + 2 * W) ^ w.re / W ^ k := by
  have hΨ0 : ∀ j, 0 ≤ Ψ j := fun j => (norm_nonneg _).trans (hΨ j 0)
  have hR : 0 ≤ (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Ψ j) * (‖w‖ + k) ^ k *
      (y₀ + 2 * W) ^ w.re / W ^ k := by
    have : 0 ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Ψ j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hΨ0 j)
    have : 0 ≤ (y₀ + 2 * W) ^ w.re := Real.rpow_nonneg (by linarith) _
    positivity
  by_cases hx : y₀ - W ≤ x ∧ x ≤ y₀ + 2 * W
  · have hxW : W ≤ x := by linarith [hx.1]
    have hpos : 0 < x := lt_of_lt_of_le hW hxW
    have hpos' : 0 < 1 * x + 0 := by linarith
    have h1 : ∀ n : ℕ, ContDiffAt ℝ n (fun t => ψ ((t - y₀) / W)) x := fun n =>
      ((hψ n).comp ((contDiff_id.sub contDiff_const).div_const W)).contDiffAt
    have h2 : ∀ n : ℕ, ContDiffAt ℝ n (fun t : ℝ => (t : ℂ) ^ w) x := fun n => by
      have := contDiffAt_affine_cpow (α := 1) (β := 0) w hpos' n
      rwa [← cpow_eq_affine] at this
    have hmul : iteratedDeriv k (windowPowerWeight ψ y₀ W w) x =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℂ) *
          iteratedDeriv i (fun t => ψ ((t - y₀) / W)) x *
          iteratedDeriv (k - i) (fun t : ℝ => (t : ℂ) ^ w) x := by
      have hdef : windowPowerWeight ψ y₀ W w =
          (fun t => ψ ((t - y₀) / W)) * fun t : ℝ => (t : ℂ) ^ w := rfl
      rw [hdef]
      exact iteratedDeriv_mul (h1 k) (h2 k)
    rw [hmul]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℂ) * iteratedDeriv i (fun t => ψ ((t - y₀) / W)) x *
          iteratedDeriv (k - i) (fun t : ℝ => (t : ℂ) ^ w) x‖ ≤
        (k.choose i : ℝ) * Ψ i * (‖w‖ + k) ^ k * (y₀ + 2 * W) ^ w.re / W ^ k := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpow_fun : iteratedDeriv (k - i) (fun t : ℝ => (t : ℂ) ^ w) x =
          ((1 : ℝ) : ℂ) ^ (k - i) * (descPochhammer ℂ (k - i)).eval w *
            (((1 * x + 0 : ℝ)) : ℂ) ^ (w - (k - i : ℕ)) := by
        rw [cpow_eq_affine]
        exact iteratedDeriv_affine_cpow (k - i) w hpos'
      rw [norm_mul, norm_mul, Complex.norm_natCast, iteratedDeriv_window hψ W, norm_smul,
        norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hW, hpow_fun, norm_mul, norm_mul,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_one, one_pow, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hpos']
      have hpoch := norm_descPochhammer_eval_le (k - i) w
      have hre : (w - ((k - i : ℕ) : ℂ)).re = w.re - (k - i : ℕ) := by simp
      rw [hre, show 1 * x + 0 = x by ring]
      have hψi := hΨ i (W⁻¹ * (x - y₀))
      have hxpow : x ^ (w.re - (k - i : ℕ)) ≤ (y₀ + 2 * W) ^ w.re * (W⁻¹) ^ (k - i) := by
        rw [Real.rpow_sub hpos, Real.rpow_natCast, div_eq_mul_inv]
        refine mul_le_mul (Real.rpow_le_rpow hpos.le hx.2 hw) ?_ (by positivity)
          (Real.rpow_nonneg (by linarith) _)
        rw [← inv_pow]
        exact pow_le_pow_left₀ (by positivity) ((inv_le_inv₀ hpos hW).mpr hxW) _
      have hbase : (‖w‖ + (k - i : ℕ)) ^ (k - i) ≤ (‖w‖ + k) ^ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0; simp
        · have h1k : 1 ≤ ‖w‖ + k := by
            have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
            linarith [norm_nonneg w]
          calc (‖w‖ + (k - i : ℕ)) ^ (k - i) ≤ (‖w‖ + k) ^ (k - i) := by
                refine pow_le_pow_left₀ (by positivity) ?_ _
                have : ((k - i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k i
                linarith
            _ ≤ (‖w‖ + k) ^ k := pow_le_pow_right₀ h1k (Nat.sub_le k i)
      have hWk : (W⁻¹) ^ i * (W⁻¹) ^ (k - i) = 1 / W ^ k := by
        rw [← pow_add, Nat.add_sub_cancel' hik, inv_pow, one_div]
      calc (k.choose i : ℝ) * ((W⁻¹) ^ i * ‖iteratedDeriv i ψ (W⁻¹ * (x - y₀))‖) *
            (‖(descPochhammer ℂ (k - i)).eval w‖ * x ^ (w.re - (k - i : ℕ)))
          ≤ (k.choose i : ℝ) * ((W⁻¹) ^ i * Ψ i) *
            ((‖w‖ + k) ^ k * ((y₀ + 2 * W) ^ w.re * (W⁻¹) ^ (k - i))) := by
            have hΨi := hΨ0 i
            refine mul_le_mul (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hψi (by positivity)) (by positivity))
              (mul_le_mul (hpoch.trans hbase) hxpow (Real.rpow_nonneg hpos.le _) (by positivity))
              (by positivity) (by positivity)
        _ = (k.choose i : ℝ) * Ψ i * (‖w‖ + k) ^ k * (y₀ + 2 * W) ^ w.re *
              ((W⁻¹) ^ i * (W⁻¹) ^ (k - i)) := by ring
        _ = (k.choose i : ℝ) * Ψ i * (‖w‖ + k) ^ k * (y₀ + 2 * W) ^ w.re / W ^ k := by
            rw [hWk]; ring
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    simp only [Finset.sum_mul, Finset.sum_div]
  · have hx' : x < y₀ - W ∨ y₀ + 2 * W < x := by
      rcases not_and_or.mp hx with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    have h0 := (window_eventually_zero hsupp hW y₀ (fun t => (t : ℂ) ^ w) hx').iteratedDeriv_eq k
    have hdef : windowPowerWeight ψ y₀ W w = fun t => ψ ((t - y₀) / W) * (t : ℂ) ^ w := rfl
    rw [hdef, h0]
    simpa using hR

/-! ## Oscillation of the window against `e^{iλt}` -/

theorem iteratedDeriv_window_eq_zero {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc (-1) 2)
    {y₀ W : ℝ} (hW : 0 < W) (w : ℂ) (j : ℕ) {x : ℝ} (hx : x ∉ Icc (y₀ - W) (y₀ + 2 * W)) :
    iteratedDeriv j (windowPowerWeight ψ y₀ W w) x = 0 := by
  have hx' : x < y₀ - W ∨ y₀ + 2 * W < x := by
    rcases not_and_or.mp hx with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)
  have h0 := (window_eventually_zero hsupp hW y₀ (fun t => (t : ℂ) ^ w) hx').iteratedDeriv_eq j
  have hdef : windowPowerWeight ψ y₀ W w = fun t => ψ ((t - y₀) / W) * (t : ℂ) ^ w := rfl
  rw [hdef, h0]
  simp

theorem integrable_iteratedDeriv_window {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc (-1) 2) {y₀ W : ℝ} (hW : 0 < W) (hWy : W < y₀) (w : ℂ)
    {j k : ℕ} (hjk : j ≤ k) : Integrable (iteratedDeriv j (windowPowerWeight ψ y₀ W w)) := by
  have hc : Continuous (iteratedDeriv j (windowPowerWeight ψ y₀ W w)) :=
    (contDiff_windowPowerWeight hψ hsupp hW hWy w k).continuous_iteratedDeriv j
      (by exact_mod_cast hjk)
  refine hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := y₀ - W) (b := y₀ + 2 * W)) fun x hx => ?_)
  exact iteratedDeriv_window_eq_zero hsupp hW w j hx

/-- **Integration by parts.** `‖∫ φ_w(t) e^{iλt} dt‖ ≤ 3W · B_k / |λ|^k`. -/
theorem norm_integral_windowPowerWeight_cexp_le {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc (-1) 2) {Ψ : ℕ → ℝ} (hΨ : ∀ j y, ‖iteratedDeriv j ψ y‖ ≤ Ψ j)
    {y₀ W : ℝ} (hW : 0 < W) (hWy : 2 * W ≤ y₀) {w : ℂ} (hw : 0 ≤ w.re) {lam : ℝ} (hlam : lam ≠ 0)
    (k : ℕ) :
    ‖∫ t, windowPowerWeight ψ y₀ W w t * Complex.exp ((lam * t : ℝ) * I)‖ ≤
      3 * W * ((∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Ψ j) * (‖w‖ + k) ^ k *
        (y₀ + 2 * W) ^ w.re / W ^ k) / |lam| ^ k := by
  set f := windowPowerWeight ψ y₀ W w with hf
  set B : ℝ := (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Ψ j) * (‖w‖ + k) ^ k *
    (y₀ + 2 * W) ^ w.re / W ^ k with hB
  have hWy' : W < y₀ := by linarith
  have hfour : ∫ t, f t * Complex.exp ((lam * t : ℝ) * I) = 𝓕 f (-(lam / (2 * Real.pi))) := by
    rw [Real.fourier_real_eq]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [mul_comm]
    congr 2
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hibp := pow_mul_norm_fourier_le_of_iteratedDeriv
    (contDiff_windowPowerWeight hψ hsupp hW hWy' w k)
    (fun j hj => integrable_iteratedDeriv_window hψ hsupp hW hWy' w hj) (-(lam / (2 * Real.pi)))
  have hξ : 2 * Real.pi * |-(lam / (2 * Real.pi))| = |lam| := by
    rw [abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    field_simp
  rw [hξ] at hibp
  have hint : ∫ x, ‖iteratedDeriv k f x‖ ≤ 3 * W * B := by
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _)
      (norm_iteratedDeriv_windowPowerWeight_le hψ hsupp hΨ hW hWy hw k 0)
    have hle : ∀ x, ‖iteratedDeriv k f x‖ ≤ (Icc (y₀ - W) (y₀ + 2 * W)).indicator (fun _ => B) x := by
      intro x
      by_cases hx : x ∈ Icc (y₀ - W) (y₀ + 2 * W)
      · rw [indicator_of_mem hx]
        exact norm_iteratedDeriv_windowPowerWeight_le hψ hsupp hΨ hW hWy hw k x
      · rw [indicator_of_notMem hx, iteratedDeriv_window_eq_zero hsupp hW w k hx, norm_zero]
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
      (Eventually.of_forall hle)).trans (le_of_eq ?_)
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
      smul_eq_mul]
    ring
  rw [hfour, le_div_iff₀ (pow_pos (abs_pos.mpr hlam) k), mul_comm]
  exact hibp.trans hint


/-! ## The Gaussian cutoff against a window -/

theorem le_of_window_ne_zero {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc (-1) 2) {y₀ W t : ℝ}
    (hW : 0 < W) (h : ψ ((t - y₀) / W) ≠ 0) : y₀ - W ≤ t ∧ t ≤ y₀ + 2 * W := by
  obtain ⟨h1, h2⟩ := hsupp h
  rw [le_div_iff₀ hW] at h1
  rw [div_le_iff₀ hW] at h2
  exact ⟨by linarith, by linarith⟩

/-- **Oscillation of the cutoff against a window.**  For `λ ≠ 0`,
`‖∫ ψ((t − y₀)/W) V(c/t) e^{iλt} dt‖ ≤ C_k (y₀ + 2W) W / (c W^k |λ|^k)`. -/
theorem exists_norm_integral_window_cutoff_cexp_le {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc (-1) 2) {Ψ : ℕ → ℝ} (hΨ : ∀ j y, ‖iteratedDeriv j ψ y‖ ≤ Ψ j)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y₀ W : ℝ, 0 < W → 2 * W ≤ y₀ → ∀ c : ℝ, 0 < c → ∀ lam : ℝ, lam ≠ 0 →
      ‖∫ t, ψ ((t - y₀) / W) * smoothAFECutoff (c / t) * Complex.exp ((lam * t : ℝ) * I)‖ ≤
        C * (y₀ + 2 * W) * W / (c * W ^ k * |lam| ^ k) := by
  have hΨ0 : ∀ j, 0 ≤ Ψ j := fun j => (norm_nonneg _).trans (hΨ j 0)
  set Ak : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Ψ j with hAk
  have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hΨ0 j)
  set wl : ℝ → ℂ := fun v => ((1 : ℝ) : ℂ) + (v : ℂ) * I with hwl
  have hwl_re : ∀ v, (wl v).re = 1 := fun v => by simp [hwl]
  have hwl_ne : ∀ v, wl v ≠ 0 := fun v h => by
    have := congrArg Complex.re h; simp [hwl] at this
  have hwl_norm : ∀ v, 1 ≤ ‖wl v‖ := fun v => by
    have := Complex.abs_re_le_norm (wl v); rw [hwl_re, abs_one] at this; exact this
  have hc1 : Continuous wl := by fun_prop
  have hcG : Continuous fun v => smoothAFEGaussianKernel (wl v) := by
    unfold smoothAFEGaussianKernel
    exact Continuous.div (by fun_prop) hc1 hwl_ne
  set bnd : ℝ → ℝ := fun v => ‖smoothAFEGaussianKernel (wl v)‖ * (‖wl v‖ + k) ^ k with hbnd
  have hbnd_int : Integrable bnd := by
    have hmaj : Integrable (fun v : ℝ =>
        Real.exp 1 * (k + 2) ^ k * ((1 + |v|) ^ k * Real.exp (-(v ^ 2)))) :=
      (ZetaNotch.integrable_one_add_abs_pow_mul_exp_neg_sq k).const_mul _
    refine hmaj.mono' ((hcG.norm.mul ((hc1.norm.add continuous_const).pow k)).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    have hK := norm_smoothAFEGaussianKernel_vertical_le one_pos v
    have hw : ‖wl v‖ ≤ 1 + |v| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have hpow : (‖wl v‖ + k) ^ k ≤ (k + 2) ^ k * (1 + |v|) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      nlinarith [abs_nonneg v]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖smoothAFEGaussianKernel (wl v)‖ * (‖wl v‖ + k) ^ k
        ≤ (Real.exp (1 ^ 2) / 1 * Real.exp (-(v ^ 2))) * ((k + 2) ^ k * (1 + |v|) ^ k) :=
          mul_le_mul (by simpa [hwl] using hK) hpow (by positivity) (by positivity)
      _ = Real.exp 1 * (k + 2) ^ k * ((1 + |v|) ^ k * Real.exp (-(v ^ 2))) := by ring_nf
  have hG_int : Integrable fun v => ‖smoothAFEGaussianKernel (wl v)‖ := by
    refine hbnd_int.mono' hcG.norm.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h1 : 1 ≤ (‖wl v‖ + k) ^ k := one_le_pow₀ (by linarith [hwl_norm v])
    simp only [hbnd]
    nlinarith [norm_nonneg (smoothAFEGaussianKernel (wl v))]
  set Ik : ℝ := ∫ v, bnd v with hIk
  have hIk0 : 0 ≤ Ik := integral_nonneg fun v => by positivity
  refine ⟨1 / (2 * Real.pi) * (3 * Ak * Ik), by positivity, ?_⟩
  intro y₀ W hW hWy c hc lam hlam
  have hWy' : W < y₀ := by linarith
  have hψc : Continuous ψ := (hψ 0).continuous
  set F : ℝ → ℝ → ℂ := fun t v => ψ ((t - y₀) / W) * Complex.exp ((lam * t : ℝ) * I) *
    ((1 / (2 * Real.pi) : ℂ) * ((c : ℂ) ^ (-wl v) * (((max t W : ℝ)) : ℂ) ^ (wl v) *
      smoothAFEGaussianKernel (wl v))) with hF
  have hrep : ∀ t, ψ ((t - y₀) / W) * smoothAFECutoff (c / t) *
      Complex.exp ((lam * t : ℝ) * I) = ∫ v, F t v := by
    intro t
    by_cases h0 : ψ ((t - y₀) / W) = 0
    · simp [hF, h0]
    · have ht := le_of_window_ne_zero hsupp hW h0
      have htW : W ≤ t := by linarith [ht.1]
      have htpos : 0 < t := lt_of_lt_of_le hW htW
      have hmax : max t W = t := max_eq_left htW
      rw [smoothAFECutoff_div_eq_integral hc htpos]
      simp only [hF, hmax]
      rw [integral_const_mul, integral_const_mul]
      ring
  -- joint integrability
  set a : ℝ → ℝ := fun t => ‖ψ ((t - y₀) / W)‖ * max t W * (1 / (2 * Real.pi) * c⁻¹) with ha
  have ha_cont : Continuous a := by
    simp only [ha]
    exact ((hψc.comp ((continuous_id.sub continuous_const).div_const W)).norm.mul
      (continuous_id.max continuous_const)).mul continuous_const
  have ha_int : Integrable a := by
    refine ha_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := y₀ - W) (b := y₀ + 2 * W)) fun t ht => ?_)
    have h0 : ψ ((t - y₀) / W) = 0 := by
      by_contra h
      exact ht ⟨(le_of_window_ne_zero hsupp hW h).1, (le_of_window_ne_zero hsupp hW h).2⟩
    simp [ha, h0]
  have hFcont : Continuous (Function.uncurry F) := by
    have hmaxpos : ∀ z : ℝ × ℝ, 0 < max z.1 W := fun z => lt_of_lt_of_le hW (le_max_right _ _)
    have hbase : Continuous fun z : ℝ × ℝ => (((max z.1 W : ℝ)) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_fst.max continuous_const)
    have hpow : Continuous fun z : ℝ × ℝ => (((max z.1 W : ℝ)) : ℂ) ^ (wl z.2) :=
      hbase.cpow (hc1.comp continuous_snd) fun z =>
        Complex.ofReal_mem_slitPlane.mpr (hmaxpos z)
    have hcpow : Continuous fun z : ℝ × ℝ => (c : ℂ) ^ (-wl z.2) :=
      (hc1.comp continuous_snd).neg.const_cpow (Or.inl (by exact_mod_cast hc.ne'))
    have h1 : Continuous fun z : ℝ × ℝ => ψ ((z.1 - y₀) / W) :=
      hψc.comp ((continuous_fst.sub continuous_const).div_const W)
    have h2 : Continuous fun z : ℝ × ℝ => Complex.exp ((lam * z.1 : ℝ) * I) := by fun_prop
    exact (h1.mul h2).mul (continuous_const.mul ((hcpow.mul hpow).mul (hcG.comp continuous_snd)))
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (ha_int.mul_prod hG_int).mono' hFcont.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    obtain ⟨t, v⟩ := z
    simp only [Function.uncurry_apply_pair, hF, ha]
    have hmaxpos : 0 < max t W := lt_of_lt_of_le hW (le_max_right _ _)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_cpow_eq_rpow_re_of_pos hc, Complex.norm_cpow_eq_rpow_re_of_pos hmaxpos]
    have hre1 : (-wl v).re = -1 := by simp [hwl]
    rw [hre1, hwl_re, Real.rpow_neg_one, Real.rpow_one]
    have hnorm2pi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnorm2pi]
    apply le_of_eq
    ring
  -- swap and bound
  have hswap : ∫ t, ψ ((t - y₀) / W) * smoothAFECutoff (c / t) *
      Complex.exp ((lam * t : ℝ) * I) = ∫ v, ∫ t, F t v := by
    rw [integral_congr_ae (Eventually.of_forall hrep)]
    exact integral_integral_swap hFint
  have hinner : ∀ v, ∫ t, F t v = (1 / (2 * Real.pi) : ℂ) * ((c : ℂ) ^ (-wl v) *
      smoothAFEGaussianKernel (wl v)) *
      ∫ t, windowPowerWeight ψ y₀ W (wl v) t * Complex.exp ((lam * t : ℝ) * I) := by
    intro v
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, windowPowerWeight]
    by_cases h0 : ψ ((t - y₀) / W) = 0
    · simp [h0]
    · have ht := le_of_window_ne_zero hsupp hW h0
      have htW : W ≤ t := by linarith [ht.1]
      rw [max_eq_left htW]
      ring
  rw [hswap]
  have hpt : ∀ v, ‖∫ t, F t v‖ ≤
      (1 / (2 * Real.pi) * c⁻¹ * (3 * W * (Ak * (y₀ + 2 * W) / W ^ k) / |lam| ^ k)) * bnd v := by
    intro v
    rw [hinner v, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc]
    have hre1 : (-wl v).re = -1 := by simp [hwl]
    rw [hre1, Real.rpow_neg_one]
    have hnorm2pi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnorm2pi]
    have hibp := norm_integral_windowPowerWeight_cexp_le hψ hsupp hΨ hW hWy
      (by rw [hwl_re]; norm_num : 0 ≤ (wl v).re) hlam k
    rw [hwl_re, Real.rpow_one] at hibp
    have hibp' : ‖∫ t, windowPowerWeight ψ y₀ W (wl v) t * Complex.exp ((lam * t : ℝ) * I)‖ ≤
        3 * W * (Ak * (y₀ + 2 * W) / W ^ k) / |lam| ^ k * (‖wl v‖ + k) ^ k := by
      refine hibp.trans (le_of_eq ?_)
      rw [hAk]
      ring
    calc 1 / (2 * Real.pi) * (c⁻¹ * ‖smoothAFEGaussianKernel (wl v)‖) *
          ‖∫ t, windowPowerWeight ψ y₀ W (wl v) t * Complex.exp ((lam * t : ℝ) * I)‖
        ≤ 1 / (2 * Real.pi) * (c⁻¹ * ‖smoothAFEGaussianKernel (wl v)‖) *
          (3 * W * (Ak * (y₀ + 2 * W) / W ^ k) / |lam| ^ k * (‖wl v‖ + k) ^ k) :=
          mul_le_mul_of_nonneg_left hibp' (by positivity)
      _ = _ := by simp only [hbnd]; ring
  refine (norm_integral_le_of_norm_le (hbnd_int.const_mul _) (Eventually.of_forall hpt)).trans
    (le_of_eq ?_)
  rw [integral_const_mul, ← hIk]
  have hl : 0 < |lam| := abs_pos.mpr hlam
  field_simp

/-! ## Frequencies of the off-diagonal quadruples -/

/-- `|log x − log y| ≥ 1/√(2xy)` for distinct positive integers. -/
theorem inv_sqrt_le_abs_log_sub_log {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    (Real.sqrt (2 * x * y))⁻¹ ≤ |Real.log x - Real.log y| := by
  wlog hlt : y < x generalizing x y
  · have h := this hy hx hxy.symm (lt_of_le_of_ne (not_lt.mp hlt) hxy)
    rwa [abs_sub_comm, show (2 : ℝ) * y * x = 2 * x * y by ring] at h
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hlog : Real.log x - Real.log y = Real.log ((x : ℝ) / y) :=
    (Real.log_div hxR.ne' hyR.ne').symm
  have hpos : 0 ≤ Real.log x - Real.log y := by
    rw [sub_nonneg]; exact Real.log_le_log hyR (by exact_mod_cast hlt.le)
  rw [abs_of_nonneg hpos]
  by_cases h2 : 2 * y ≤ x
  · have hl2 : Real.log 2 ≤ Real.log x - Real.log y := by
      rw [hlog]
      exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hyR]; exact_mod_cast h2)
    have h4 : (4 : ℝ) ≤ 2 * x * y := by
      have : (2 : ℝ) ≤ x := by exact_mod_cast (by omega : 2 ≤ x)
      have : (1 : ℝ) ≤ y := by exact_mod_cast hy
      nlinarith
    have hs : 2 ≤ Real.sqrt (2 * x * y) := by
      have h := Real.abs_le_sqrt (show (2 : ℝ) ^ 2 ≤ 2 * x * y by nlinarith)
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    have hinv : (Real.sqrt (2 * x * y))⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hs
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    linarith
  · have hlt2 : x < 2 * y := by omega
    have h1 : 1 - (y : ℝ) / x ≤ Real.log x - Real.log y := by
      rw [hlog]
      have := Real.one_sub_inv_le_log_of_pos (div_pos hxR hyR)
      rwa [inv_div] at this
    have h2' : (1 : ℝ) / x ≤ 1 - (y : ℝ) / x := by
      have hy1 : (y : ℝ) + 1 ≤ x := by exact_mod_cast hlt
      rw [div_le_iff₀ hxR, sub_mul, div_mul_cancel₀ _ hxR.ne', one_mul]
      linarith
    have hsq : (x : ℝ) ≤ Real.sqrt (2 * x * y) := by
      have : (x : ℝ) < 2 * y := by exact_mod_cast hlt2
      have h := Real.abs_le_sqrt (show (x : ℝ) ^ 2 ≤ 2 * x * y by nlinarith)
      rwa [abs_of_pos hxR] at h
    have : (Real.sqrt (2 * x * y))⁻¹ ≤ 1 / x := by rw [one_div]; exact inv_anti₀ hxR hsq
    linarith

theorem quadFreq_eq_log_sub (P : ℕ × ℕ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    quadFreq P h k =
      Real.log (((P.2 + 1) * k : ℕ) : ℝ) - Real.log (((P.1 + 1) * h : ℕ) : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold quadFreq pairFreq
  push_cast
  rw [Real.log_mul (by positivity) hkR.ne', Real.log_mul (by positivity) hhR.ne']
  ring

/-- **Off-diagonal frequencies.**  If `nk ≠ mh` then `|λ_q| ≥ 1/(N √(2mn))`. -/
theorem inv_le_abs_quadFreq {N : ℕ} {P : ℕ × ℕ} {h k : ℕ} (hh : h ∈ Finset.Icc 1 N)
    (hk : k ∈ Finset.Icc 1 N) (hne : quadRatio P h k ≠ (1, 1)) :
    ((N : ℝ) * Real.sqrt (2 * pairProd P))⁻¹ ≤ |quadFreq P h k| := by
  obtain ⟨hh1, hhN⟩ := Finset.mem_Icc.mp hh
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  have hne' : (P.2 + 1) * k ≠ (P.1 + 1) * h := by
    intro heq
    apply hne
    rw [quadRatio_eq_iff (by omega) (Nat.coprime_one_left 1) one_pos]
    simp only [mul_one]
    exact heq.symm
  have hmain := inv_sqrt_le_abs_log_sub_log (Nat.mul_pos (Nat.succ_pos _) (by omega))
    (Nat.mul_pos (Nat.succ_pos _) (by omega)) hne'
  rw [← quadFreq_eq_log_sub P (by omega) (by omega)] at hmain
  refine le_trans ?_ hmain
  have hhR : (h : ℝ) ≤ N := by exact_mod_cast hhN
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpp : 0 < pairProd P := ZetaNotch.pairProd_pos P
  have hprod : (2 * (((P.2 + 1) * k : ℕ) : ℝ) * (((P.1 + 1) * h : ℕ) : ℝ)) ≤
      ((N : ℝ) * Real.sqrt (2 * pairProd P)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    unfold pairProd
    push_cast
    have : (h : ℝ) * k ≤ (N : ℝ) ^ 2 := by nlinarith
    have hm : (0 : ℝ) ≤ ((P.1 : ℝ) + 1) * ((P.2 : ℝ) + 1) := by positivity
    nlinarith
  have hpos : 0 < Real.sqrt (2 * (((P.2 + 1) * k : ℕ) : ℝ) * (((P.1 + 1) * h : ℕ) : ℝ)) := by
    apply Real.sqrt_pos.mpr; positivity
  refine inv_anti₀ hpos ?_
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (N : ℝ) * Real.sqrt (2 * pairProd P))]
  exact Real.sqrt_le_sqrt hprod


/-! ## Diagonal and off-diagonal quadruples -/

/-- The quadruple term restricted to the diagonal fibre `nk = mh`. -/
def diagQuad (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) (t : ℝ) : ℂ :=
  if quadRatio P h k = (1, 1) then quadPoint N P h k t else 0

/-- The quadruple term off the diagonal fibre. -/
def offQuad (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) (t : ℝ) : ℂ :=
  if quadRatio P h k = (1, 1) then 0 else quadPoint N P h k t

theorem diagQuad_add_offQuad (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) (t : ℝ) :
    diagQuad N P h k t + offQuad N P h k t = quadPoint N P h k t := by
  unfold diagQuad offQuad; split_ifs <;> simp

theorem norm_diagQuad_le (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) (t : ℝ) :
    ‖diagQuad N P h k t‖ ≤ ‖quadPoint N P h k t‖ := by
  unfold diagQuad; split_ifs <;> simp

theorem norm_offQuad_le (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) (t : ℝ) :
    ‖offQuad N P h k t‖ ≤ ‖quadPoint N P h k t‖ := by
  unfold offQuad; split_ifs <;> simp

theorem summable_diagQuad (N : ℕ) {t : ℝ} (ht : 0 < t) (h k : ℕ) :
    Summable fun P => diagQuad N P h k t :=
  (summable_norm_quadPoint ht N h k).of_norm_bounded fun P => norm_diagQuad_le N P h k t

theorem summable_offQuad (N : ℕ) {t : ℝ} (ht : 0 < t) (h k : ℕ) :
    Summable fun P => offQuad N P h k t :=
  (summable_norm_quadPoint ht N h k).of_norm_bounded fun P => norm_offQuad_le N P h k t

/-- **The diagonal fibre is the ratio form** `F(1, 1, t)`. -/
theorem tsum_diagQuad_eq (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, diagQuad N P h k t =
      ratioForm N 1 1 t := by
  rw [Summable.tsum_finsetSum fun h _ => summable_sum fun k _ => summable_diagQuad N ht h k]
  have hfib := sum_fiber_quadPoint N (Nat.coprime_one_left 1) one_pos one_pos ht
  simp only [Nat.cast_one, mul_one, Real.sqrt_one, inv_one, Real.log_one, sub_self, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul] at hfib
  rw [← hfib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Summable.tsum_finsetSum fun k _ => summable_diagQuad N ht h k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_subtype {P : ℕ × ℕ | quadRatio P h k = (1, 1)} (fun P => quadPoint N P h k t)]
  refine tsum_congr fun P => ?_
  unfold diagQuad
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

/-- `Σ_q quadPoint = F(1, 1, t) + Σ_{q off the diagonal} quadPoint`. -/
theorem tsum_quadPoint_eq (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, quadPoint N P h k t =
      ratioForm N 1 1 t +
        ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t := by
  have hd : Summable fun P => ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, diagQuad N P h k t :=
    summable_sum fun h _ => summable_sum fun k _ => summable_diagQuad N ht h k
  have ho : Summable fun P => ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t :=
    summable_sum fun h _ => summable_sum fun k _ => summable_offQuad N ht h k
  rw [← tsum_diagQuad_eq N ht, ← hd.tsum_add ho]
  refine tsum_congr fun P => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (diagQuad_add_offQuad N P h k t).symm

/-- `|M_N(½ + it)|² ≤ 4N`. -/
theorem normSq_linMoll_le (N : ℕ) (t : ℝ) : ‖linMoll N (critPt t)‖ ^ 2 ≤ 4 * N := by
  rw [linMoll_critPt_eq]
  have h1 : ‖∑ h ∈ Finset.Icc 1 N, (mollAmp N h : ℂ) * Complex.exp (-(↑t * ↑(Real.log h)) * I)‖ ≤
      ∑ h ∈ Finset.Icc 1 N, |mollAmp N h| := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun h _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖Complex.exp (-(↑t * ↑(Real.log h)) * I)‖ = 1 := by
      rw [show -(↑t * ↑(Real.log h)) * I = ((-(t * Real.log h) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]
  have h2 : (∑ h ∈ Finset.Icc 1 N, |mollAmp N h|) ^ 2 ≤ 4 * N := by
    rw [sq, Finset.sum_mul_sum]
    exact sum_abs_mollAmp_mul_le N
  calc ‖_‖ ^ 2 ≤ (∑ h ∈ Finset.Icc 1 N, |mollAmp N h|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ 4 * N := h2


/-! ## Window integrals of the quadruple terms -/

theorem continuousOn_smoothAFECutoff_div {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun t : ℝ => smoothAFECutoff (c / t)) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  exact ((hasDerivAt_smoothAFECutoff (div_pos hc ht0)).continuousAt.comp
    (continuousAt_const.div continuousAt_id ht0.ne')).continuousWithinAt

theorem continuousOn_quadPoint (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) :
    ContinuousOn (quadPoint N P h k) (Ioi 0) := by
  unfold quadPoint
  have hc : 0 < 2 * Real.pi * pairProd P := by
    have := ZetaNotch.pairProd_pos P; positivity
  refine (continuousOn_const.mul (continuousOn_smoothAFECutoff_div hc)).mul ?_
  exact (Continuous.continuousOn (by fun_prop))

theorem continuousOn_offQuad (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) :
    ContinuousOn (offQuad N P h k) (Ioi 0) := by
  unfold offQuad
  split_ifs
  · exact continuousOn_const
  · exact continuousOn_quadPoint N P h k

/-- A window times a function continuous on `(0, ∞)` is integrable. -/
theorem integrable_window_mul {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hsupp : Function.support ψ ⊆ Icc (-1) 2) {y₀ W : ℝ} (hW : 0 < W) (hWy : 2 * W ≤ y₀)
    {F : ℝ → ℂ} (hF : ContinuousOn F (Ioi 0)) :
    Integrable fun t => ψ ((t - y₀) / W) * F t := by
  have hsub : Icc (y₀ - W) (y₀ + 2 * W) ⊆ Ioi 0 := fun t ht => by
    show (0 : ℝ) < t; linarith [ht.1]
  have hcont : ContinuousOn (fun t => ψ ((t - y₀) / W) * F t) (Icc (y₀ - W) (y₀ + 2 * W)) :=
    ((hψc.comp ((continuous_id.sub continuous_const).div_const W)).continuousOn).mul
      (hF.mono hsub)
  refine (hcont.integrableOn_compact isCompact_Icc).integrable_of_forall_notMem_eq_zero
    fun t ht => ?_
  have h0 : ψ ((t - y₀) / W) = 0 := by
    by_contra h
    exact ht (le_of_window_ne_zero hsupp hW h)
  simp [h0]

/-- **One off-diagonal quadruple against the window.** -/
theorem norm_integral_window_offQuad_le {ψ : ℝ → ℂ} {K : ℕ} {Cosc : ℝ}
    (hosc : ∀ y₀ W : ℝ, 0 < W → 2 * W ≤ y₀ → ∀ c : ℝ, 0 < c → ∀ lam : ℝ, lam ≠ 0 →
      ‖∫ t, ψ ((t - y₀) / W) * smoothAFECutoff (c / t) * Complex.exp ((lam * t : ℝ) * I)‖ ≤
        Cosc * (y₀ + 2 * W) * W / (c * W ^ K * |lam| ^ K))
    (hCosc : 0 ≤ Cosc) {N : ℕ} {y₀ W M₀ : ℝ} (hW : 0 < W) (hWy : 2 * W ≤ y₀) {P : ℕ × ℕ}
    (hPM : pairProd P ≤ M₀) {h k : ℕ} (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
    ‖∫ t, ψ ((t - y₀) / W) * offQuad N P h k t‖ ≤
      |mollAmp N h| * |mollAmp N k| *
        (Cosc * (y₀ + 2 * W) * W * (Real.sqrt 2 * N) ^ K * M₀ ^ ((K : ℝ) / 2) /
          (2 * Real.pi * W ^ K)) * pairProd P ^ (-(3 / 2 : ℝ)) := by
  have hpp : 0 < pairProd P := ZetaNotch.pairProd_pos P
  have hR0 : 0 ≤ |mollAmp N h| * |mollAmp N k| *
      (Cosc * (y₀ + 2 * W) * W * (Real.sqrt 2 * N) ^ K * M₀ ^ ((K : ℝ) / 2) /
        (2 * Real.pi * W ^ K)) * pairProd P ^ (-(3 / 2 : ℝ)) := by
    have hM0 : 0 ≤ M₀ := hpp.le.trans hPM
    have : 0 ≤ M₀ ^ ((K : ℝ) / 2) := Real.rpow_nonneg hM0 _
    have : 0 ≤ y₀ + 2 * W := by linarith
    positivity
  unfold offQuad
  split_ifs with hdiag
  · simpa using hR0
  · set lam := quadFreq P h k with hlam
    have hlamb := inv_le_abs_quadFreq hh hk hdiag
    rw [← hlam] at hlamb
    have hN0 : (0 : ℝ) < N := by
      have := (Finset.mem_Icc.mp hh); exact_mod_cast (by omega : 0 < N)
    have hlam0 : lam ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hlamb
      have : 0 < ((N : ℝ) * Real.sqrt (2 * pairProd P))⁻¹ := by positivity
      linarith
    set c : ℝ := 2 * Real.pi * pairProd P with hc
    have hc0 : 0 < c := by positivity
    have heq : ∫ t, ψ ((t - y₀) / W) * quadPoint N P h k t =
        (quadCoeff N P h k : ℂ) *
          ∫ t, ψ ((t - y₀) / W) * smoothAFECutoff (c / t) * Complex.exp ((lam * t : ℝ) * I) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [quadPoint, hc, hlam]
      rw [mul_comm t (quadFreq P h k)]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := hosc y₀ W hW hWy c hc0 lam hlam0
    have hcoef : |quadCoeff N P h k| = pairAmp P * (|mollAmp N h| * |mollAmp N k|) := by
      unfold quadCoeff
      rw [abs_mul, abs_mul, abs_of_pos (ZetaNotch.pairAmp_pos P)]
      ring
    rw [hcoef, ZetaNotch.pairAmp_eq]
    -- `1/|λ|^K ≤ (N √(2 pp))^K`
    have hlamK : 1 / |lam| ^ K ≤ ((N : ℝ) * Real.sqrt (2 * pairProd P)) ^ K := by
      rw [one_div, ← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ K
      rw [inv_le_comm₀ (abs_pos.mpr hlam0) (by positivity)]
      exact hlamb
    have hsq2 : Real.sqrt (2 * pairProd P) = Real.sqrt 2 * Real.sqrt (pairProd P) :=
      Real.sqrt_mul (by norm_num) _
    have hsqK : Real.sqrt (pairProd P) ^ K = pairProd P ^ ((K : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hpp.le]
      congr 1; ring
    have hsqinv : (Real.sqrt (pairProd P))⁻¹ = pairProd P ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hpp.le]
    have hKM : pairProd P ^ ((K : ℝ) / 2) ≤ M₀ ^ ((K : ℝ) / 2) :=
      Real.rpow_le_rpow hpp.le hPM (by positivity)
    have hpow_eq : pairProd P ^ (-(1 / 2 : ℝ)) * pairProd P ^ ((K : ℝ) / 2) / pairProd P =
        pairProd P ^ ((K : ℝ) / 2) * pairProd P ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_comm (pairProd P ^ (-(1 / 2 : ℝ))),
        mul_assoc, ← Real.rpow_add hpp, show (-(1 / 2 : ℝ)) + -1 = -(3 / 2 : ℝ) by ring]
    have hW0 : 0 < W ^ K := pow_pos hW K
    have hy : 0 ≤ y₀ + 2 * W := by linarith
    calc (Real.sqrt (pairProd P))⁻¹ * (|mollAmp N h| * |mollAmp N k|) *
          ‖∫ t, ψ ((t - y₀) / W) * smoothAFECutoff (c / t) * Complex.exp ((lam * t : ℝ) * I)‖
        ≤ (Real.sqrt (pairProd P))⁻¹ * (|mollAmp N h| * |mollAmp N k|) *
          (Cosc * (y₀ + 2 * W) * W / (c * W ^ K * |lam| ^ K)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = |mollAmp N h| * |mollAmp N k| * (Cosc * (y₀ + 2 * W) * W / (2 * Real.pi * W ^ K)) *
            ((Real.sqrt (pairProd P))⁻¹ / pairProd P * (1 / |lam| ^ K)) := by
          rw [hc]; field_simp
      _ ≤ |mollAmp N h| * |mollAmp N k| * (Cosc * (y₀ + 2 * W) * W / (2 * Real.pi * W ^ K)) *
            ((Real.sqrt (pairProd P))⁻¹ / pairProd P *
              ((N : ℝ) * Real.sqrt (2 * pairProd P)) ^ K) := by
          gcongr
      _ = |mollAmp N h| * |mollAmp N k| * (Cosc * (y₀ + 2 * W) * W / (2 * Real.pi * W ^ K)) *
            (Real.sqrt 2 * N) ^ K *
              (pairProd P ^ (-(1 / 2 : ℝ)) * pairProd P ^ ((K : ℝ) / 2) / pairProd P) := by
          rw [hsq2, hsqinv, mul_pow, mul_pow, hsqK]; ring
      _ ≤ |mollAmp N h| * |mollAmp N k| * (Cosc * (y₀ + 2 * W) * W / (2 * Real.pi * W ^ K)) *
            (Real.sqrt 2 * N) ^ K * (M₀ ^ ((K : ℝ) / 2) * pairProd P ^ (-(3 / 2 : ℝ))) := by
          rw [hpow_eq]
          gcongr
      _ = _ := by ring


/-! ## The tail `mn > M₀` -/

/-- The pairs with `mn ≤ M₀`. -/
def pairBox (M₀ : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊M₀⌋₊ + 1)) ×ˢ (Finset.range (⌊M₀⌋₊ + 1))).filter fun P => pairProd P ≤ M₀

theorem pairProd_le_of_mem_pairBox {M₀ : ℝ} {P : ℕ × ℕ} (hP : P ∈ pairBox M₀) :
    pairProd P ≤ M₀ := (Finset.mem_filter.mp hP).2

theorem lt_pairProd_of_notMem_pairBox {M₀ : ℝ} {P : ℕ × ℕ} (hP : P ∉ pairBox M₀) :
    M₀ < pairProd P := by
  by_contra hle
  push Not at hle
  apply hP
  have h1 : (P.1 : ℝ) + 1 ≤ M₀ := by
    refine le_trans ?_ hle
    unfold pairProd
    have : (1 : ℝ) ≤ (P.2 : ℝ) + 1 := by linarith [(Nat.cast_nonneg P.2 : (0 : ℝ) ≤ P.2)]
    nlinarith [(Nat.cast_nonneg P.1 : (0 : ℝ) ≤ P.1)]
  have h2 : (P.2 : ℝ) + 1 ≤ M₀ := by
    refine le_trans ?_ hle
    unfold pairProd
    have : (1 : ℝ) ≤ (P.1 : ℝ) + 1 := by linarith [(Nat.cast_nonneg P.1 : (0 : ℝ) ≤ P.1)]
    nlinarith [(Nat.cast_nonneg P.2 : (0 : ℝ) ≤ P.2)]
  have hM0 : 0 ≤ M₀ := by linarith [(Nat.cast_nonneg P.1 : (0 : ℝ) ≤ P.1)]
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hle⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (by linarith)))
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (by linarith)))

theorem norm_sum_offQuad_le_of_decay {N : ℕ} {T M₀ A KV : ℝ} (hA : 1 ≤ A) (hKV0 : 0 ≤ KV)
    (hKV : ∀ x : ℝ, 0 < x → ‖smoothAFECutoff x‖ ≤ KV * x ^ (-A)) (hM₀ : 0 < M₀) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ 3 * T) {P : ℕ × ℕ} (hP : M₀ < pairProd P) :
    ‖∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t‖ ≤
      4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) * pairProd P ^ (-(3 / 2 : ℝ)) := by
  have hpp : 0 < pairProd P := hM₀.trans hP
  have hT : 0 < T := by linarith
  have hV : ‖smoothAFECutoff (2 * Real.pi * pairProd P / t)‖ ≤
      KV * (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A) := by
    have hc : 0 < 2 * Real.pi * pairProd P := by positivity
    have h1 : (2 * Real.pi * pairProd P / t) ^ (-A) = (t / (2 * Real.pi * pairProd P)) ^ A := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    have h2 : (t / (2 * Real.pi * pairProd P)) ^ A ≤ (3 * T / (2 * Real.pi * pairProd P)) ^ A :=
      Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right htT hc.le) (by linarith)
    have h3 : (3 * T / (2 * Real.pi * pairProd P)) ^ A =
        (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A) := by
      rw [show 3 * T / (2 * Real.pi * pairProd P) = 3 * T / (2 * Real.pi) / pairProd P by
          field_simp,
        Real.div_rpow (by positivity) hpp.le, Real.rpow_neg hpp.le, div_eq_mul_inv]
    calc ‖smoothAFECutoff (2 * Real.pi * pairProd P / t)‖
        ≤ KV * (2 * Real.pi * pairProd P / t) ^ (-A) := hKV _ (by positivity)
      _ ≤ KV * ((3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A)) := by
          rw [h1, ← h3]; exact mul_le_mul_of_nonneg_left h2 hKV0
      _ = _ := by ring
  have hsum : ‖∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t‖ ≤
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k| *
        (pairAmp P * (KV * (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A))) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (norm_offQuad_le N P h k t).trans ?_
    rw [norm_quadPoint]
    unfold quadCoeff
    rw [abs_mul, abs_mul, abs_of_pos (ZetaNotch.pairAmp_pos P)]
    have hpa := (ZetaNotch.pairAmp_pos P).le
    calc pairAmp P * |mollAmp N h| * |mollAmp N k| * ‖smoothAFECutoff (2 * Real.pi * pairProd P / t)‖
        ≤ pairAmp P * |mollAmp N h| * |mollAmp N k| *
          (KV * (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A)) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = _ := by ring
  refine hsum.trans ?_
  simp_rw [← Finset.sum_mul]
  have h4N := sum_abs_mollAmp_mul_le N
  have hpow : pairAmp P * (KV * (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A)) ≤
      KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A) * pairProd P ^ (-(3 / 2 : ℝ)) := by
    rw [ZetaNotch.pairAmp_eq, Real.sqrt_eq_rpow, ← Real.rpow_neg hpp.le]
    have hsplit : pairProd P ^ (-(1 / 2 : ℝ)) * pairProd P ^ (-A) =
        pairProd P ^ (1 - A) * pairProd P ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hpp, ← Real.rpow_add hpp]; congr 1; ring
    have hle : pairProd P ^ (1 - A) ≤ M₀ ^ (1 - A) :=
      Real.rpow_le_rpow_of_nonpos hM₀ hP.le (by linarith)
    have hc0 : 0 ≤ KV * (3 * T / (2 * Real.pi)) ^ A :=
      mul_nonneg hKV0 (Real.rpow_nonneg (by positivity) _)
    calc pairProd P ^ (-(1 / 2 : ℝ)) * (KV * (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A))
        = KV * (3 * T / (2 * Real.pi)) ^ A *
            (pairProd P ^ (1 - A) * pairProd P ^ (-(3 / 2 : ℝ))) := by rw [← hsplit]; ring
      _ ≤ KV * (3 * T / (2 * Real.pi)) ^ A * (M₀ ^ (1 - A) * pairProd P ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hnn : 0 ≤ pairAmp P * (KV * (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A)) := by
    have := (ZetaNotch.pairAmp_pos P).le
    have : 0 ≤ (3 * T / (2 * Real.pi)) ^ A := Real.rpow_nonneg (by positivity) _
    positivity
  calc (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k|) *
        (pairAmp P * (KV * (3 * T / (2 * Real.pi)) ^ A * pairProd P ^ (-A)))
      ≤ 4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A) *
          pairProd P ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul h4N hpow hnn (by positivity)
    _ = _ := by ring


theorem norm_offTail_le {N : ℕ} {T M₀ A KV : ℝ} (hA : 1 ≤ A) (hKV0 : 0 ≤ KV)
    (hKV : ∀ x : ℝ, 0 < x → ‖smoothAFECutoff x‖ ≤ KV * x ^ (-A)) (hM₀ : 0 < M₀) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ 3 * T) :
    ‖∑' P : ↥((pairBox M₀ : Set (ℕ × ℕ))ᶜ),
        ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N (P : ℕ × ℕ) h k t‖ ≤
      4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) *
        ∑' P : ℕ × ℕ, pairProd P ^ (-(3 / 2 : ℝ)) := by
  have hT : 0 < T := by linarith
  set B : ℝ := 4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ (3 * T / (2 * Real.pi)) ^ A := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ M₀ ^ (1 - A) := Real.rpow_nonneg hM₀.le _
    positivity
  have hZ := ZetaNotch.summable_pairProd_rpow (s := 3 / 2) (by norm_num)
  set sc : Set (ℕ × ℕ) := ((pairBox M₀ : Set (ℕ × ℕ))ᶜ) with hsc
  have hb : ∀ x : sc, ‖∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N (x : ℕ × ℕ) h k t‖ ≤
      B * pairProd (x : ℕ × ℕ) ^ (-(3 / 2 : ℝ)) := fun x =>
    norm_sum_offQuad_le_of_decay hA hKV0 hKV hM₀ ht htT
      (lt_pairProd_of_notMem_pairBox (fun hx => x.2 (Finset.mem_coe.mpr hx)))
  have hbs : Summable fun x : sc => B * pairProd (x : ℕ × ℕ) ^ (-(3 / 2 : ℝ)) :=
    (hZ.subtype sc).mul_left B
  have hns : Summable fun x : sc =>
      ‖∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N (x : ℕ × ℕ) h k t‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hbs
  calc ‖∑' x : sc, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N (x : ℕ × ℕ) h k t‖
      ≤ ∑' x : sc, ‖∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N (x : ℕ × ℕ) h k t‖ :=
        norm_tsum_le_tsum_norm hns
    _ ≤ ∑' x : sc, B * pairProd (x : ℕ × ℕ) ^ (-(3 / 2 : ℝ)) := hns.tsum_le_tsum hb hbs
    _ = B * ∑' x : sc, pairProd (x : ℕ × ℕ) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
    _ ≤ B * ∑' P : ℕ × ℕ, pairProd P ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Summable.tsum_subtype_le (fun P => pairProd P ^ (-(3 / 2 : ℝ)))
          sc (fun P => Real.rpow_nonneg (ZetaNotch.pairProd_pos P).le _) hZ) hB0

/-- **Pointwise decomposition.** `|ζ M_N|² − 2 Σ_{mn ≤ M₀, off-diagonal}` is the AFE error, twice the
ratio form `F(1, 1, t)`, and twice the off-diagonal tail `mn > M₀`. -/
theorem norm_zetaSq_mul_sub_le (N : ℕ) {t CAFE : ℝ} (ht : 0 < t)
    (hAFE : ‖ZetaNotch.zetaSq t - ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        smoothAFECutoff (pairProd p / (t / (2 * Real.pi))) *
        (Complex.exp ((t * pairFreq p : ℝ) * I) + Complex.exp ((t * (-pairFreq p) : ℝ) * I))‖ ≤
      CAFE) (M₀ : ℝ) :
    ‖ZetaNotch.zetaSq t * ((‖linMoll N (critPt t)‖ ^ 2 : ℝ) : ℂ) -
        2 * ∑ P ∈ pairBox M₀, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t‖ ≤
      CAFE * (4 * N) + 2 * ‖ratioForm N 1 1 t‖ +
        2 * ‖∑' P : ↥((pairBox M₀ : Set (ℕ × ℕ))ᶜ),
          ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N (P : ℕ × ℕ) h k t‖ := by
  set A : ℂ := ∑' p : ℕ × ℕ, (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / (t / (2 * Real.pi))) *
    (Complex.exp ((t * pairFreq p : ℝ) * I) + Complex.exp ((t * (-pairFreq p) : ℝ) * I)) with hA
  set M2 : ℂ := ((‖linMoll N (critPt t)‖ ^ 2 : ℝ) : ℂ) with hM2
  have hsum := afeMain_mul_normSq ht N
  rw [← hA, ← hM2] at hsum
  have hq : ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      (quadCoeff N P h k : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
        Complex.exp ((t * quadFreq P h k : ℝ) * I) =
      ratioForm N 1 1 t + ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        offQuad N P h k t := tsum_quadPoint_eq N ht
  rw [hq] at hsum
  have ho : Summable fun P => ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t :=
    summable_sum fun h _ => summable_sum fun k _ => summable_offQuad N ht h k
  have hsplit := ho.sum_add_tsum_compl (s := pairBox M₀)
  set Ob := ∑ P ∈ pairBox M₀, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t
  set Ot := ∑' P : ↥((pairBox M₀ : Set (ℕ × ℕ))ᶜ),
    ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N (P : ℕ × ℕ) h k t
  have hkey : ZetaNotch.zetaSq t * M2 - 2 * Ob =
      (ZetaNotch.zetaSq t - A) * M2 + 2 * ratioForm N 1 1 t + 2 * Ot := by
    have : ZetaNotch.zetaSq t * M2 = (ZetaNotch.zetaSq t - A) * M2 + A * M2 := by ring
    rw [this, hsum, ← hsplit]
    ring
  rw [hkey]
  have hM2n : ‖M2‖ ≤ 4 * N := by
    rw [hM2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact normSq_linMoll_le N t
  calc ‖(ZetaNotch.zetaSq t - A) * M2 + 2 * ratioForm N 1 1 t + 2 * Ot‖
      ≤ ‖(ZetaNotch.zetaSq t - A) * M2‖ + ‖2 * ratioForm N 1 1 t‖ + ‖2 * Ot‖ :=
        norm_add₃_le
    _ ≤ CAFE * (4 * N) + 2 * ‖ratioForm N 1 1 t‖ + 2 * ‖Ot‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
        gcongr
        exact le_trans (norm_nonneg _) hAFE


/-! ## The window bump -/

/-- A smooth bump equal to `1` on `[0, 1]`, supported in `(−1, 2)`. -/
def windowBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 3 / 2, by norm_num, by norm_num⟩

/-- The complexified window bump. -/
def windowBumpC (y : ℝ) : ℂ := ((windowBump y : ℝ) : ℂ)

theorem windowBumpC_support : Function.support windowBumpC ⊆ Icc (-1) 2 := by
  intro y hy
  have hne : (windowBump y : ℝ) ≠ 0 := fun h => hy (by simp [windowBumpC, h])
  have hmem : y ∈ Function.support windowBump := hne
  rw [ContDiffBump.support_eq, Real.ball_eq_Ioo] at hmem
  have h1 : windowBump.rOut = 3 / 2 := rfl
  rw [h1] at hmem
  obtain ⟨h1, h2⟩ := hmem
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

theorem contDiff_windowBumpC (k : ℕ) : ContDiff ℝ k windowBumpC :=
  Complex.ofRealCLM.contDiff.comp (windowBump.contDiff (n := k))

theorem continuous_windowBumpC : Continuous windowBumpC := (contDiff_windowBumpC 0).continuous

theorem windowBump_eq_one {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : windowBump y = 1 := by
  refine windowBump.one_of_mem_closedBall ?_
  rw [Real.closedBall_eq_Icc]
  have h1 : windowBump.rIn = 1 / 2 := rfl
  rw [h1]
  obtain ⟨h0, h1⟩ := hy
  constructor <;> linarith

theorem norm_windowBumpC_le_one (y : ℝ) : ‖windowBumpC y‖ ≤ 1 := by
  rw [windowBumpC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (windowBump.nonneg)]
  exact windowBump.le_one

theorem exists_iteratedDeriv_windowBumpC_bound :
    ∃ Ψ : ℕ → ℝ, ∀ j y, ‖iteratedDeriv j windowBumpC y‖ ≤ Ψ j := by
  have hcs : HasCompactSupport windowBumpC := by
    have h := windowBump.hasCompactSupport
    exact h.comp_left Complex.ofReal_zero
  have hj : ∀ j : ℕ, ∃ C, ∀ y, ‖iteratedDeriv j windowBumpC y‖ ≤ C := by
    intro j
    have hc : Continuous (iteratedDeriv j windowBumpC) :=
      (contDiff_windowBumpC j).continuous_iteratedDeriv j le_rfl
    have hcs' : HasCompactSupport (iteratedDeriv j windowBumpC) := by
      refine (hcs.iteratedFDeriv (𝕜 := ℝ) j).mono fun y hy => ?_
      intro h0
      apply hy
      rw [iteratedDeriv_eq_iteratedFDeriv, h0]
      rfl
    exact hc.bounded_above_of_compact_support hcs'
  choose Ψ hΨ using hj
  exact ⟨Ψ, hΨ⟩


/-! ## The window inequality -/

theorem critPt_ne_one (t : ℝ) : critPt t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [critPt] at this

theorem continuous_linMoll (N : ℕ) : Continuous (linMoll N) := by
  unfold linMoll
  refine continuous_finsetSum _ fun h hh => continuous_const.mul ?_
  have hh0 : (h : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hh).1; exact_mod_cast (by omega : h ≠ 0)
  exact continuous_neg.const_cpow (Or.inl hh0)

theorem continuous_critPt : Continuous critPt := by unfold critPt; fun_prop

theorem continuous_zetaMoll_normSq (N : ℕ) :
    Continuous fun t => ‖riemannZeta (critPt t) * linMoll N (critPt t)‖ ^ 2 := by
  have hz : Continuous fun t => riemannZeta (critPt t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (differentiableAt_riemannZeta (critPt_ne_one t)).continuousAt.comp
        continuous_critPt.continuousAt
  exact ((hz.mul ((continuous_linMoll N).comp continuous_critPt)).norm).pow 2

/-- **The window inequality.**  At one height, with the oscillation, decay, AFE and ratio-form
bounds as inputs. -/
theorem integral_window_meanSquare_le {N : ℕ} {T W y₀ M₀ A KV CAFE BD Cosc : ℝ} {K : ℕ}
    (hT : 64 ≤ T) (hW : 0 < W) (hWT : W ≤ T / 4) (hy₁ : T / 2 ≤ y₀) (hy₂ : y₀ ≤ 2 * T)
    (hM₀ : 0 < M₀) (hA : 1 ≤ A) (hKV0 : 0 ≤ KV)
    (hKV : ∀ x : ℝ, 0 < x → ‖smoothAFECutoff x‖ ≤ KV * x ^ (-A))
    (hCAFE0 : 0 ≤ CAFE)
    (hCAFE : ∀ t : ℝ, 16 ≤ t → ‖ZetaNotch.zetaSq t - ∑' p : ℕ × ℕ, (pairAmp p : ℂ) *
        smoothAFECutoff (pairProd p / (t / (2 * Real.pi))) *
        (Complex.exp ((t * pairFreq p : ℝ) * I) + Complex.exp ((t * (-pairFreq p) : ℝ) * I))‖ ≤
      CAFE * (1 + Real.log t) / Real.sqrt t)
    (hBD : ∀ t ∈ Icc (T / 4) (3 * T), ‖ratioForm N 1 1 t‖ ≤ BD)
    (hCosc0 : 0 ≤ Cosc)
    (hosc : ∀ y₀ W : ℝ, 0 < W → 2 * W ≤ y₀ → ∀ c : ℝ, 0 < c → ∀ lam : ℝ, lam ≠ 0 →
      ‖∫ t, windowBumpC ((t - y₀) / W) * smoothAFECutoff (c / t) *
          Complex.exp ((lam * t : ℝ) * I)‖ ≤
        Cosc * (y₀ + 2 * W) * W / (c * W ^ K * |lam| ^ K)) :
    ∫ t in y₀..(y₀ + W), ‖riemannZeta (critPt t) * linMoll N (critPt t)‖ ^ 2 ≤
      2 * (4 * N * (Cosc * (y₀ + 2 * W) * W * (Real.sqrt 2 * N) ^ K * M₀ ^ ((K : ℝ) / 2) /
          (2 * Real.pi * W ^ K)) * ∑' P : ℕ × ℕ, pairProd P ^ (-(3 / 2 : ℝ))) +
      3 * W * (CAFE * (1 + Real.log (3 * T)) / Real.sqrt (T / 4) * (4 * N) + 2 * BD +
        2 * (4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) *
          ∑' P : ℕ × ℕ, pairProd P ^ (-(3 / 2 : ℝ)))) := by
  set Z : ℝ := ∑' P : ℕ × ℕ, pairProd P ^ (-(3 / 2 : ℝ)) with hZdef
  have hZs := ZetaNotch.summable_pairProd_rpow (s := 3 / 2) (by norm_num)
  have hZ0 : 0 ≤ Z := tsum_nonneg fun P => Real.rpow_nonneg (ZetaNotch.pairProd_pos P).le _
  have hWy : 2 * W ≤ y₀ := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => ‖riemannZeta (critPt t) * linMoll N (critPt t)‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ, b = fun t => windowBump ((t - y₀) / W) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun t => windowBumpC ((t - y₀) / W) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ → ℂ,
      X = fun t => ZetaNotch.zetaSq t * ((‖linMoll N (critPt t)‖ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Ob, hOb⟩ : ∃ Ob : ℝ → ℂ, Ob = fun t =>
      ∑ P ∈ pairBox M₀, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, offQuad N P h k t :=
    ⟨_, rfl⟩
  have hfeq : (fun t => ‖riemannZeta (critPt t) * linMoll N (critPt t)‖ ^ 2) = f := hf.symm
  have hwin : ∀ t, b t ≠ 0 → y₀ - W ≤ t ∧ t ≤ y₀ + 2 * W := by
    intro t ht
    have : windowBumpC ((t - y₀) / W) ≠ 0 := by
      rw [hb] at ht
      simp only [windowBumpC]; exact_mod_cast ht
    exact le_of_window_ne_zero windowBumpC_support hW this
  have hgt : ∀ t, g t = windowBumpC ((t - y₀) / W) := fun t => by rw [hg]
  -- continuity and integrability
  have hfc : Continuous f := hf ▸ continuous_zetaMoll_normSq N
  have hbc : Continuous b := hb ▸ (windowBump.contDiff (n := 0)).continuous.comp
    ((continuous_id.sub continuous_const).div_const W)
  have hbf : Integrable fun t => b t * f t := by
    refine (hbc.mul hfc).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := y₀ - W) (b := y₀ + 2 * W)) fun t ht => ?_)
    have h0 : b t = 0 := by
      by_contra h; exact ht (hwin t h)
    simp [h0]
  -- step 1: the plateau
  have hstep1 : ∫ t in y₀..(y₀ + W), f t ≤ ∫ t, b t * f t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    have heq : ∫ t in Ioc y₀ (y₀ + W), f t = ∫ t in Ioc y₀ (y₀ + W), b t * f t := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have h1 : b t = 1 := by
        rw [hb]
        exact windowBump_eq_one ⟨by
          rw [le_div_iff₀ hW]; linarith [ht.1], by rw [div_le_iff₀ hW]; linarith [ht.2]⟩
      simp [h1]
    rw [heq]
    exact setIntegral_le_integral hbf (Eventually.of_forall fun t => mul_nonneg
      (by rw [hb]; exact windowBump.nonneg) (by rw [hf]; positivity))
  -- step 2: complexify
  have hgX : ∀ t, ((b t * f t : ℝ) : ℂ) = g t * X t := by
    intro t
    rw [hb, hf, hg, hX]
    simp only [windowBumpC, ZetaNotch.zetaSq_eq_normSq]
    rw [norm_mul, mul_pow]
    push_cast
    rfl
  have hstep2 : ∫ t, b t * f t ≤ ‖∫ t, g t * X t‖ := by
    have h : ((∫ t, b t * f t : ℝ) : ℂ) = ∫ t, g t * X t := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall hgX)
    rw [← h, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  -- step 3: split off the box part
  have hint : ∀ P h k, Integrable fun t => g t * offQuad N P h k t := fun P h k => by
    rw [hg]
    exact integrable_window_mul continuous_windowBumpC windowBumpC_support hW hWy
      (continuousOn_offQuad N P h k)
  have hgOb_eq : (fun t => g t * Ob t) = fun t => ∑ P ∈ pairBox M₀, ∑ h ∈ Finset.Icc 1 N,
      ∑ k ∈ Finset.Icc 1 N, g t * offQuad N P h k t := by
    funext t
    rw [hOb]
    simp only [Finset.mul_sum]
  have hgOb_int : Integrable fun t => g t * Ob t := by
    rw [hgOb_eq]
    exact integrable_finsetSum _ fun P _ => integrable_finsetSum _ fun h _ =>
      integrable_finsetSum _ fun k _ => hint P h k
  have hgX_int : Integrable fun t => g t * X t :=
    (hbf.ofReal (𝕜 := ℂ)).congr (Eventually.of_forall hgX)
  have hrest : Integrable fun t => g t * (X t - 2 * Ob t) := by
    have : (fun t => g t * (X t - 2 * Ob t)) = fun t => g t * X t - 2 * (g t * Ob t) := by
      funext t; ring
    rw [this]
    exact hgX_int.sub (hgOb_int.const_mul 2)
  have hsplit : ∫ t, g t * X t = 2 * (∫ t, g t * Ob t) + ∫ t, g t * (X t - 2 * Ob t) := by
    have h1 : (fun t => g t * X t) = fun t => 2 * (g t * Ob t) + g t * (X t - 2 * Ob t) := by
      funext t; ring
    rw [h1, integral_add (hgOb_int.const_mul 2) hrest, integral_const_mul]
  -- step 4: the box part
  set Q₁ : ℝ := Cosc * (y₀ + 2 * W) * W * (Real.sqrt 2 * N) ^ K * M₀ ^ ((K : ℝ) / 2) /
    (2 * Real.pi * W ^ K) with hQ₁
  have hQ₁0 : 0 ≤ Q₁ := by
    have : 0 ≤ M₀ ^ ((K : ℝ) / 2) := Real.rpow_nonneg hM₀.le _
    have : 0 ≤ y₀ + 2 * W := by linarith
    positivity
  have hstep4 : ‖∫ t, g t * Ob t‖ ≤ 4 * N * Q₁ * Z := by
    have hexp : ∫ t, g t * Ob t = ∑ P ∈ pairBox M₀, ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N, ∫ t, g t * offQuad N P h k t := by
      rw [hgOb_eq]
      rw [integral_finsetSum _ fun P _ => integrable_finsetSum _ fun h _ =>
        integrable_finsetSum _ fun k _ => hint P h k]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [integral_finsetSum _ fun h _ => integrable_finsetSum _ fun k _ => hint P h k]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [integral_finsetSum _ fun k _ => hint P h k]
    rw [hexp]
    have hbound : ∀ P ∈ pairBox M₀, ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
        ‖∫ t, g t * offQuad N P h k t‖ ≤
          |mollAmp N h| * |mollAmp N k| * Q₁ * pairProd P ^ (-(3 / 2 : ℝ)) := by
      intro P hP h hh k hk
      have := norm_integral_window_offQuad_le hosc hCosc0 hW hWy (pairProd_le_of_mem_pairBox hP) hh hk
      simp only [hgt]
      exact this
    calc ‖∑ P ∈ pairBox M₀, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          ∫ t, g t * offQuad N P h k t‖
        ≤ ∑ P ∈ pairBox M₀, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            |mollAmp N h| * |mollAmp N k| * Q₁ * pairProd P ^ (-(3 / 2 : ℝ)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P hP => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          exact hbound P hP h hh k hk
      _ = Q₁ * (∑ P ∈ pairBox M₀, pairProd P ^ (-(3 / 2 : ℝ))) *
            (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k|) := by
          have hP : ∀ P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
              |mollAmp N h| * |mollAmp N k| * Q₁ * pairProd P ^ (-(3 / 2 : ℝ)) =
              Q₁ * pairProd P ^ (-(3 / 2 : ℝ)) *
                ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k| := by
            intro P
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
          rw [Finset.sum_congr rfl fun P _ => hP P, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ Q₁ * Z * (4 * N) := by
          have hsZ : ∑ P ∈ pairBox M₀, pairProd P ^ (-(3 / 2 : ℝ)) ≤ Z :=
            hZs.sum_le_tsum _ fun P _ => Real.rpow_nonneg (ZetaNotch.pairProd_pos P).le _
          have hss : 0 ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, |mollAmp N h| * |mollAmp N k| :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hsZ hQ₁0) (sum_abs_mollAmp_mul_le N) hss
            (mul_nonneg hQ₁0 hZ0)
      _ = 4 * N * Q₁ * Z := by ring
  -- step 5: the remainder
  set Bρ : ℝ := CAFE * (1 + Real.log (3 * T)) / Real.sqrt (T / 4) * (4 * N) + 2 * BD +
    2 * (4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) * Z) with hBρ
  have hptw : ∀ t, ‖g t * (X t - 2 * Ob t)‖ ≤ (Icc (y₀ - W) (y₀ + 2 * W)).indicator (fun _ => Bρ) t := by
    intro t
    by_cases ht : t ∈ Icc (y₀ - W) (y₀ + 2 * W)
    · rw [indicator_of_mem ht, norm_mul]
      have htT1 : T / 4 ≤ t := by linarith [ht.1]
      have htT2 : t ≤ 3 * T := by linarith [ht.2]
      have ht16 : 16 ≤ t := by linarith
      have htpos : 0 < t := by linarith
      have hdec := norm_zetaSq_mul_sub_le N htpos (hCAFE t ht16) M₀
      have htail := norm_offTail_le (N := N) hA hKV0 hKV hM₀ htpos htT2
      have hD := hBD t ⟨htT1, htT2⟩
      have hlog : CAFE * (1 + Real.log t) / Real.sqrt t ≤
          CAFE * (1 + Real.log (3 * T)) / Real.sqrt (T / 4) := by
        have hl : Real.log t ≤ Real.log (3 * T) := Real.log_le_log htpos htT2
        have hs : Real.sqrt (T / 4) ≤ Real.sqrt t := Real.sqrt_le_sqrt htT1
        have hs0 : 0 < Real.sqrt (T / 4) := Real.sqrt_pos.mpr (by positivity)
        have hlt : 0 ≤ 1 + Real.log t := by
          have : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
          linarith
        rw [div_le_div_iff₀ (Real.sqrt_pos.mpr htpos) hs0]
        have h1 : CAFE * (1 + Real.log t) ≤ CAFE * (1 + Real.log (3 * T)) :=
          mul_le_mul_of_nonneg_left (by linarith) hCAFE0
        calc CAFE * (1 + Real.log t) * Real.sqrt (T / 4)
            ≤ CAFE * (1 + Real.log (3 * T)) * Real.sqrt t := by
              have : 0 ≤ CAFE * (1 + Real.log t) := mul_nonneg hCAFE0 hlt
              nlinarith
          _ = _ := rfl
      have hgle : ‖g t‖ ≤ 1 := by rw [hgt]; exact norm_windowBumpC_le_one _
      have hX2 : ‖X t - 2 * Ob t‖ ≤ Bρ := by
        rw [hX, hOb]
        refine hdec.trans ?_
        rw [hBρ]
        have h4N : (0 : ℝ) ≤ 4 * N := by positivity
        have := mul_le_mul_of_nonneg_right hlog h4N
        nlinarith
      calc ‖g t‖ * ‖X t - 2 * Ob t‖ ≤ 1 * Bρ :=
            mul_le_mul hgle hX2 (norm_nonneg _) zero_le_one
        _ = Bρ := one_mul _
    · rw [indicator_of_notMem ht]
      have h0 : g t = 0 := by
        rw [hgt]
        by_contra h
        exact ht (le_of_window_ne_zero windowBumpC_support hW h)
      simp [h0]
  have hBρ0 : 0 ≤ Bρ := le_trans (norm_nonneg _) (by
    have := hptw y₀
    rwa [indicator_of_mem (show y₀ ∈ Icc (y₀ - W) (y₀ + 2 * W) from
      ⟨by linarith, by linarith⟩)] at this)
  have hstep5 : ‖∫ t, g t * (X t - 2 * Ob t)‖ ≤ 3 * W * Bρ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
      (Eventually.of_forall hptw)).trans (le_of_eq ?_)
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
      smul_eq_mul]
    ring
  -- combine
  rw [hfeq]
  calc ∫ t in y₀..(y₀ + W), f t ≤ ‖∫ t, g t * X t‖ := hstep1.trans hstep2
    _ = ‖2 * (∫ t, g t * Ob t) + ∫ t, g t * (X t - 2 * Ob t)‖ := by rw [hsplit]
    _ ≤ ‖2 * (∫ t, g t * Ob t)‖ + ‖∫ t, g t * (X t - 2 * Ob t)‖ := norm_add_le _ _
    _ = 2 * ‖∫ t, g t * Ob t‖ + ‖∫ t, g t * (X t - 2 * Ob t)‖ := by
        rw [norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (4 * N * Q₁ * Z) + 3 * W * Bρ := by gcongr
    _ = _ := by rw [hQ₁, hBρ]


/-! ## The theorem -/

theorem eventually_const_mul_rpow_le_one (c : ℝ) {κ : ℝ} (hκ : κ < 0) :
    ∀ᶠ T : ℝ in atTop, c * T ^ κ ≤ 1 := by
  have h := ((tendsto_rpow_neg_atTop (y := -κ) (by linarith)).const_mul c)
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds one_pos)] with T hT
  rw [neg_neg] at hT
  exact hT.le

/-- **The short-window mean square.**  For `θ, η > 0` with `θ + η < ½` there is `C` such that for
all large `T` and all `y₀ ∈ [T/2, 2T]`,
`∫_{y₀}^{y₀+T^{1−η}} |ζ(½ + it) M_N(½ + it)|² dt ≤ C T^{1−η}`, `N = ⌊T^θ⌋`. -/
theorem exists_eventually_shortWindow_meanSquare_le {θ η : ℝ} (hθ0 : 0 < θ) (hη : 0 < η)
    (hθη : θ + η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ y₀ : ℝ, T / 2 ≤ y₀ → y₀ ≤ 2 * T →
      ∫ t in y₀..(y₀ + T ^ (1 - η)),
        ‖riemannZeta (critPt t) * linMoll (molLen θ T) (critPt t)‖ ^ 2 ≤ C * T ^ (1 - η) := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / 2 - θ - η := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (2 + θ) / δ ≤ K := exists_nat_ge _
  have hKδ : 2 + θ ≤ K * δ := by rwa [div_le_iff₀ hδ0] at hK
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 + θ + 2 * ε) / ε := ⟨_, rfl⟩
  have hεA : ε * A = 2 + θ + 2 * ε := by rw [hA]; field_simp
  have hA1 : 1 ≤ A := by rw [hA, le_div_iff₀ hε0]; linarith
  obtain ⟨Ψ, hΨ⟩ := exists_iteratedDeriv_windowBumpC_bound
  obtain ⟨Cosc, hCosc0, hosc⟩ := exists_norm_integral_window_cutoff_cexp_le
    (fun k => contDiff_windowBumpC k) windowBumpC_support hΨ K
  obtain ⟨KV, hKV0, hKV⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (by linarith : (0 : ℝ) < A)
  obtain ⟨CAFE, hCAFE0, hCAFE⟩ := ZetaNotch.exists_norm_zetaSq_sub_symmetricAFE_le
  have hθ : θ < 1 / 2 := by linarith
  have hratio := ratioForm_one_one_uniform hθ0 hθ (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 3) one_pos
  obtain ⟨BD, hBD⟩ : ∃ BD : ℝ, BD = 1 / 2 + 1 / (2 * θ) + 1 := ⟨_, rfl⟩
  have hBD0 : 0 ≤ BD := by rw [hBD]; positivity
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∑' P : ℕ × ℕ, pairProd P ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by
    rw [hZ]; exact tsum_nonneg fun P => Real.rpow_nonneg (ZetaNotch.pairProd_pos P).le _
  obtain ⟨c₄, hc₄⟩ : ∃ c : ℝ, c = 8 * Z * Cosc * 3 * Real.sqrt 2 ^ K / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨c₅, hc₅⟩ : ∃ c : ℝ, c = 24 * KV * Z * (3 / (2 * Real.pi)) ^ A := ⟨_, rfl⟩
  obtain ⟨c₆, hc₆⟩ : ∃ c : ℝ, c = 24 * CAFE := ⟨_, rfl⟩
  refine ⟨3 + 6 * BD, by positivity, ?_⟩
  have he4 := eventually_const_mul_rpow_le_one c₄ (κ := 1 + θ - K * δ) (by linarith)
  have he5 := eventually_const_mul_rpow_le_one c₅ (κ := -1 - ε) (by linarith)
  have he6 : ∀ᶠ T : ℝ in atTop, c₆ * (T ^ θ * (1 + Real.log (3 * T)) / Real.sqrt T) ≤ 1 := by
    have hlim : Tendsto (fun T : ℝ => (1 + Real.log (3 * T)) * T ^ (θ - 1 / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun T : ℝ => Real.log T * T ^ (θ - 1 / 2)) atTop (𝓝 0) := by
        have := (isLittleO_log_rpow_atTop (r := 1 / 2 - θ) (by linarith)).tendsto_div_nhds_zero
        refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with T hT
        rw [div_eq_mul_inv, ← Real.rpow_neg hT.le]; ring_nf
      have h2 : Tendsto (fun T : ℝ => T ^ (θ - 1 / 2)) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := 1 / 2 - θ) (by linarith)
        refine this.congr' (Eventually.of_forall fun T => ?_)
        ring_nf
      have h3 := (h2.const_mul (1 + Real.log 3)).add h1
      rw [mul_zero, zero_add] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      rw [Real.log_mul (by norm_num) hT.ne']; ring
    have := (hlim.const_mul c₆).eventually (gt_mem_nhds (by rw [mul_zero]; exact one_pos))
    filter_upwards [this, eventually_gt_atTop 0] with T hT hT0
    refine le_of_eq_of_le ?_ hT.le
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hT0.le,
      show θ - 1 / 2 = θ + -(1 / 2) by ring, Real.rpow_add hT0]
    ring
  have hW4 : ∀ᶠ T : ℝ in atTop, T ^ (1 - η) ≤ T / 4 := by
    have h := tendsto_rpow_atTop hη
    filter_upwards [h.eventually_ge_atTop 4, eventually_gt_atTop 0] with T hT hT0
    rw [Real.rpow_sub hT0, Real.rpow_one, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  filter_upwards [hratio, he4, he5, he6, hW4, eventually_ge_atTop 64,
    eventually_molLen_ge_one hθ0] with T hratioT he4T he5T he6T hW4T hT64 hN1
  intro y₀ hy₁ hy₂
  have hT0 : 0 < T := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = molLen θ T := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = T ^ (1 - η) := ⟨_, rfl⟩
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = T ^ (1 + ε) := ⟨_, rfl⟩
  rw [← hN, ← hW]
  rw [← hN] at hratioT
  rw [← hW] at hW4T
  have hW0 : 0 < W := by rw [hW]; exact Real.rpow_pos_of_pos hT0 _
  have hM₀0 : 0 < M₀ := by rw [hM₀]; exact Real.rpow_pos_of_pos hT0 _
  have hNT : (N : ℝ) ≤ T ^ θ := by rw [hN]; exact molLen_cast_le_rpow hT0.le
  have hBDT : ∀ t ∈ Icc (T / 4) (3 * T), ‖ratioForm N 1 1 t‖ ≤ BD := by
    intro t ht
    have h := hratioT t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h' := norm_sub_norm_le (ratioForm N 1 1 t) ((1 / 2 + 1 / (2 * θ) : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h'
    rw [hBD]; linarith
  have hmain := integral_window_meanSquare_le (N := N) (K := K) hT64 hW0 hW4T hy₁ hy₂ hM₀0 hA1
    hKV0 (fun x hx => hKV hx) hCAFE0 hCAFE hBDT hCosc0 hosc
  rw [← hZ] at hmain
  refine hmain.trans ?_
  have hyW : y₀ + 2 * W ≤ 3 * T := by linarith
  -- the box term
  have hWK : W ^ K = T ^ ((1 - η) * K) := by
    rw [hW, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
  have hMK : M₀ ^ ((K : ℝ) / 2) = T ^ ((1 + ε) * (K / 2)) := by
    rw [hM₀, ← Real.rpow_mul hT0.le]
  have hNK : (Real.sqrt 2 * N) ^ K ≤ Real.sqrt 2 ^ K * T ^ (θ * K) := by
    rw [mul_pow, Real.rpow_mul hT0.le, Real.rpow_natCast]
    gcongr
  have hexp : T ^ θ * T * T ^ (θ * K) * M₀ ^ ((K : ℝ) / 2) / W ^ K = T ^ (1 + θ - K * δ) := by
    rw [hMK, hWK, div_eq_mul_inv, ← Real.rpow_neg hT0.le,
      show T ^ θ * T = T ^ θ * T ^ (1 : ℝ) by rw [Real.rpow_one], ← Real.rpow_add hT0,
      ← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    congr 1
    rw [hδ, hε]; ring
  have hWKpos : 0 < W ^ K := pow_pos hW0 K
  have hcc : 0 ≤ 8 * Z * Cosc / (2 * Real.pi) := by positivity
  have hbox : 2 * (4 * N * (Cosc * (y₀ + 2 * W) * W * (Real.sqrt 2 * N) ^ K *
      M₀ ^ ((K : ℝ) / 2) / (2 * Real.pi * W ^ K)) * Z) ≤ W := by
    have h1 : (N : ℝ) * (Real.sqrt 2 * N) ^ K ≤ T ^ θ * (Real.sqrt 2 ^ K * T ^ (θ * K)) :=
      mul_le_mul hNT hNK (by positivity) (by positivity)
    have hM0K : 0 ≤ M₀ ^ ((K : ℝ) / 2) := Real.rpow_nonneg hM₀0.le _
    calc 2 * (4 * N * (Cosc * (y₀ + 2 * W) * W * (Real.sqrt 2 * N) ^ K *
          M₀ ^ ((K : ℝ) / 2) / (2 * Real.pi * W ^ K)) * Z)
        = W * (8 * Z * Cosc / (2 * Real.pi)) *
            ((N * (Real.sqrt 2 * N) ^ K) * (y₀ + 2 * W) * M₀ ^ ((K : ℝ) / 2)) / W ^ K := by
          field_simp; ring
      _ ≤ W * (8 * Z * Cosc / (2 * Real.pi)) *
            ((T ^ θ * (Real.sqrt 2 ^ K * T ^ (θ * K))) * (3 * T) * M₀ ^ ((K : ℝ) / 2)) / W ^ K := by
          apply div_le_div_of_nonneg_right _ hWKpos.le
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hW0.le hcc)
          apply mul_le_mul_of_nonneg_right _ hM0K
          exact mul_le_mul h1 hyW (by linarith) (by positivity)
      _ = W * (c₄ * (T ^ θ * T * T ^ (θ * K) * M₀ ^ ((K : ℝ) / 2) / W ^ K)) := by
          rw [hc₄]; field_simp
      _ = W * (c₄ * T ^ (1 + θ - K * δ)) := by rw [hexp]
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left he4T hW0.le
      _ = W := mul_one W
  -- the tail term
  have htail : 3 * W * (2 * (4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) * Z)) ≤
      W := by
    have hpow : (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A) =
        (3 / (2 * Real.pi)) ^ A * T ^ (-1 - ε - θ) := by
      rw [show 3 * T / (2 * Real.pi) = 3 / (2 * Real.pi) * T by ring,
        Real.mul_rpow (by positivity) hT0.le, hM₀, ← Real.rpow_mul hT0.le, mul_assoc,
        ← Real.rpow_add hT0]
      congr 2
      have : (1 + ε) * (1 - A) = 1 + ε - A - ε * A := by ring
      rw [this, hεA]; ring
    have hθT : (N : ℝ) * T ^ (-1 - ε - θ) ≤ T ^ (-1 - ε) := by
      calc (N : ℝ) * T ^ (-1 - ε - θ) ≤ T ^ θ * T ^ (-1 - ε - θ) :=
            mul_le_mul_of_nonneg_right hNT (by positivity)
        _ = T ^ (-1 - ε) := by rw [← Real.rpow_add hT0]; congr 1; ring
    have hc5 : 0 ≤ 24 * KV * Z * (3 / (2 * Real.pi)) ^ A := by
      have : 0 ≤ (3 / (2 * Real.pi)) ^ A := Real.rpow_nonneg (by positivity) _
      positivity
    calc 3 * W * (2 * (4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) * Z))
        = W * (24 * KV * Z * (3 / (2 * Real.pi)) ^ A * (N * T ^ (-1 - ε - θ))) := by
          rw [show KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A) =
            KV * ((3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) by ring, hpow]
          ring
      _ ≤ W * (c₅ * T ^ (-1 - ε)) := by
          rw [hc₅]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hθT hc5) hW0.le
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left he5T hW0.le
      _ = W := mul_one W
  -- the AFE term
  have hafe : 3 * W * (CAFE * (1 + Real.log (3 * T)) / Real.sqrt (T / 4) * (4 * N)) ≤ W := by
    have hs : Real.sqrt (T / 4) = Real.sqrt T / 2 := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
    have hlog : 0 ≤ 1 + Real.log (3 * T) := by
      have : 0 ≤ Real.log (3 * T) := Real.log_nonneg (by linarith)
      linarith
    have hc6 : 0 ≤ c₆ := by rw [hc₆]; positivity
    calc 3 * W * (CAFE * (1 + Real.log (3 * T)) / Real.sqrt (T / 4) * (4 * N))
        = W * (c₆ * (N * (1 + Real.log (3 * T)) / Real.sqrt T)) := by
          rw [hs, hc₆]; field_simp; ring
      _ ≤ W * (c₆ * (T ^ θ * (1 + Real.log (3 * T)) / Real.sqrt T)) := by
          gcongr
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left he6T hW0.le
      _ = W := mul_one W
  have hexpand : 3 * W * (CAFE * (1 + Real.log (3 * T)) / Real.sqrt (T / 4) * (4 * N) + 2 * BD +
      2 * (4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) * Z)) =
      3 * W * (CAFE * (1 + Real.log (3 * T)) / Real.sqrt (T / 4) * (4 * N)) + 6 * BD * W +
        3 * W * (2 * (4 * N * (KV * (3 * T / (2 * Real.pi)) ^ A * M₀ ^ (1 - A)) * Z)) := by ring
  rw [hexpand]
  linarith only [hbox, htail, hafe]

end

end RHTower.VerticalAP
