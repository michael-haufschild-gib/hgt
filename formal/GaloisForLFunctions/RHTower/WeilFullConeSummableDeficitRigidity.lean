import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity
import GaloisForLFunctions.RHTower.WeilPositivitySummablePerturbationRigidity

/-!
# A Weil-positive system with summable deficit below `Λ` is `Λ`

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit`, unconditional). If `lam` is
Weil-positive with the pole term (`WeilPositiveFull`) and its deficit below `Λ` is summable,
`Σ_n (Λ(n) − lam(n))⁺ n^{−1/2} < ∞`, then `lam(n) = Λ(n)` for all `n ≥ 2`. Nothing is assumed about
the excess `(lam − Λ)⁺`.

This contains upward rigidity (`eq_vonMangoldt_of_weilPositiveFull_of_ge`, zero deficit) and
summable rigidity (`eq_vonMangoldt_of_weilPositive_of_summable_sub`). It also gives eventual upward
rigidity (`eq_vonMangoldt_of_weilPositiveFull_of_eventually_ge`): finitely many exceptions below `Λ`
are allowed a priori and cannot occur.

**The test.** The comb `f = Σ_{j<M} Φχ_L(· − j)` of truncated Riemann kernels (`combRiemannKernel`).
- Its transform is `(Σ_j e^{izj}) û(z)`, so on the zeros its zero side is at most
  `(M e^{M/2})²` times the near-radical energy of `Φχ_L`, which tends to `0`.
- Its autocorrelation `k(y) = Σ_{i,j<M} K_L(y + j − i)` (`combAutocorr_eq_sum`) is a discrete triangle:
  - `0 ≤ k ≤ k(0)` (`combAutocorr_le_zero`);
  - `k(0) ≤ 3CM` by a lattice sum (`combAutocorr_zero_le`);
  - `k(y) ≥ (M − ⌊y⌋) m²` for `y ≥ 0`, with `m = min_{[−1,1]} Φ` (`combAutocorr_ge`).

**The argument.** Write `a = (lam − Λ)/√n = a⁺ − a⁻`. Positivity gives `Σ a (k(log n) + k(−log n)) ≤ ‖W‖ ≤ 1`.
- The deficit costs at most `2k(0) Σ a⁻ ≤ 6CM·D`.
- The excess below `N` earns at least `(M/2) m² Σ_{n<N} a⁺(n)` once `M = 2N + 2`.
- Dividing by `M` bounds every partial sum of the excess, so `lam − Λ ∈ ℓ¹(n^{−1/2})`. Summable
  rigidity then forces `lam = Λ`.

**Corollary** (`riemannHypothesis_iff_exists_weilPositiveFull_summable_deficit`). RH holds iff some
full-cone Weil-positive `lam` has summable deficit below `Λ`.

**Consequence for producers.** A Weil-positive system other than `Λ` has infinite deficit below `Λ`
(this module), and it also exceeds `Λ` somewhere (`eq_vonMangoldt_of_weilPositiveFull_of_le`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## A lattice sum -/

theorem exp_neg_two_abs_natCast (n : ℕ) :
    Real.exp (-(2 * |((n : ℤ) : ℝ)|)) = Real.exp (-2) ^ n := by
  rw [← Real.exp_nat_mul]; push_cast; rw [abs_of_nonneg (Nat.cast_nonneg n)]; ring_nf

theorem exp_neg_two_abs_negSucc (n : ℕ) :
    Real.exp (-(2 * |((-((n : ℤ) + 1) : ℤ) : ℝ)|)) = Real.exp (-2) * Real.exp (-2) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast
  rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf

theorem hasSum_int_exp_neg_two_abs :
    HasSum (fun d : ℤ => Real.exp (-(2 * |(d : ℝ)|)))
      ((1 - Real.exp (-2))⁻¹ + Real.exp (-2) * (1 - Real.exp (-2))⁻¹) := by
  have hr0 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h1 : HasSum (fun n : ℕ => Real.exp (-(2 * |((n : ℤ) : ℝ)|))) (1 - Real.exp (-2))⁻¹ :=
    (hasSum_geometric_of_lt_one hr0 hr1).congr_fun fun n => exp_neg_two_abs_natCast n
  have h2 : HasSum (fun n : ℕ => Real.exp (-(2 * |((-((n : ℤ) + 1) : ℤ) : ℝ)|)))
      (Real.exp (-2) * (1 - Real.exp (-2))⁻¹) :=
    ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-2))).congr_fun
      fun n => exp_neg_two_abs_negSucc n
  exact HasSum.of_nat_of_neg_add_one h1 h2

theorem summable_int_exp_neg_two_abs : Summable fun d : ℤ => Real.exp (-(2 * |(d : ℝ)|)) :=
  hasSum_int_exp_neg_two_abs.summable

theorem tsum_int_exp_neg_two_abs_le : ∑' d : ℤ, Real.exp (-(2 * |(d : ℝ)|)) ≤ 3 := by
  rw [hasSum_int_exp_neg_two_abs.tsum_eq]
  have hr1 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hr3 : Real.exp (-2) ≤ 1 / 3 := by
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
  have hden : 0 < 1 - Real.exp (-2) := by linarith
  have hinv : (1 - Real.exp (-2))⁻¹ ≤ 3 / 2 := by
    rw [inv_le_comm₀ hden (by norm_num)]; linarith
  have hinv0 : 0 ≤ (1 - Real.exp (-2))⁻¹ := inv_nonneg.mpr hden.le
  calc (1 - Real.exp (-2))⁻¹ + Real.exp (-2) * (1 - Real.exp (-2))⁻¹
      = (1 + Real.exp (-2)) * (1 - Real.exp (-2))⁻¹ := by ring
    _ ≤ (1 + 1 / 3) * (3 / 2) := mul_le_mul (by linarith) hinv hinv0 (by norm_num)
    _ ≤ 3 := by norm_num

/-- `Σ_{j < M} e^{−2|j − i|} ≤ 3`. -/
theorem sum_range_exp_neg_two_abs_le (i M : ℕ) :
    ∑ j ∈ Finset.range M, Real.exp (-(2 * |(j : ℝ) - i|)) ≤ 3 := by
  have hs := summable_int_exp_neg_two_abs
  have hle := tsum_int_exp_neg_two_abs_le
  set g : ℕ → ℤ := fun j => (j : ℤ) - i with hg
  have hinj : Set.InjOn g ↑(Finset.range M) := by
    intro a _ b _ hab
    simp only [hg] at hab
    exact_mod_cast (sub_left_inj.mp hab)
  have e : ∑ j ∈ Finset.range M, Real.exp (-(2 * |(j : ℝ) - i|)) =
      ∑ d ∈ (Finset.range M).image g, Real.exp (-(2 * |(d : ℝ)|)) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hg]; push_cast; rfl
  rw [e]
  exact (hs.sum_le_tsum _ fun d _ => (Real.exp_pos _).le).trans hle

/-! ## The comb of truncated kernels -/

/-- The comb `Σ_{j < M} Φχ_L(· − j)`. -/
def combRiemannKernel (L : ℝ) (M : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range M, truncatedRiemannKernel L (u - j)

/-- Its real profile. -/
def combRiemannKernelReal (L : ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, truncatedRiemannKernelReal L (u - j)

theorem combRiemannKernel_eq (L : ℝ) (M : ℕ) :
    combRiemannKernel L M = fun u => (combRiemannKernelReal L M u : ℂ) := by
  funext u
  simp only [combRiemannKernel, combRiemannKernelReal, truncatedRiemannKernel_eq]
  push_cast; rfl

theorem contDiff_combRiemannKernel (L : ℝ) (M : ℕ) : ContDiff ℝ 2 (combRiemannKernel L M) := by
  have h := contDiff_nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ))
  exact ContDiff.sum fun j _ => h.comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_combRiemannKernel (L : ℝ) (M : ℕ) :
    HasCompactSupport (combRiemannKernel L M) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -|L|) (b := |L| + M)) fun u hu => ?_
  rw [mem_Icc, not_and_or] at hu
  unfold combRiemannKernel
  refine Finset.sum_eq_zero fun j hj => truncatedRiemannKernel_eq_zero ?_
  have hjM : (j : ℝ) ≤ M := by
    have := Finset.mem_range.mp hj; exact_mod_cast this.le
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rcases hu with hu | hu
  · push Not at hu
    rw [abs_of_neg (by linarith [abs_nonneg L])]
    linarith [le_abs_self L]
  · push Not at hu
    rw [abs_of_pos (by linarith [abs_nonneg L])]
    linarith [le_abs_self L]

theorem continuous_combRiemannKernelReal (L : ℝ) (M : ℕ) :
    Continuous (combRiemannKernelReal L M) :=
  continuous_finsetSum _ fun _ _ =>
    (continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const)

theorem hasCompactSupport_combRiemannKernelReal (L : ℝ) (M : ℕ) :
    HasCompactSupport (combRiemannKernelReal L M) := by
  have h := hasCompactSupport_combRiemannKernel L M
  rw [combRiemannKernel_eq] at h
  exact h.mono' (fun u hu => by
    refine subset_tsupport _ ?_
    intro h0
    exact hu (by simpa using h0))

/-- The transform of the comb: `(Σ_{j<M} e^{izj}) û(z)`. -/
theorem paperFT_combRiemannKernel (L : ℝ) (M : ℕ) (z : ℂ) :
    paperFT (combRiemannKernel L M) z =
      (∑ j ∈ Finset.range M, Complex.exp (I * z * (j : ℝ))) * paperFT (truncatedRiemannKernel L) z := by
  have hint : ∀ j ∈ Finset.range M, Integrable fun u : ℝ =>
      truncatedRiemannKernel L (u - j) * Complex.exp (I * z * u) :=
    fun j _ => integrable_translate_mul_cexp L j z
  unfold paperFT
  have hsplit : (fun u : ℝ => combRiemannKernel L M u * Complex.exp (I * z * u)) =
      fun u : ℝ => ∑ j ∈ Finset.range M, truncatedRiemannKernel L (u - j) * Complex.exp (I * z * u) := by
    funext u; simp only [combRiemannKernel, Finset.sum_mul]
  rw [hsplit, integral_finsetSum _ hint, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e := paperFT_comp_sub (truncatedRiemannKernel L) j z
  unfold paperFT at e
  exact e

theorem norm_combMultiplier_le (M : ℕ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖∑ j ∈ Finset.range M, Complex.exp (I * z * (j : ℝ))‖ ≤ M * Real.exp (M / 2) := by
  calc ‖∑ j ∈ Finset.range M, Complex.exp (I * z * (j : ℝ))‖
      ≤ ∑ j ∈ Finset.range M, ‖Complex.exp (I * z * (j : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range M, Real.exp (M / 2) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hre : (I * z * ((j : ℝ) : ℂ)).re = -(z.im * j) := by simp [Complex.mul_re]
        rw [hre]
        have hjM : (j : ℝ) ≤ M := by
          have := Finset.mem_range.mp hj; exact_mod_cast this.le
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have h1 : |z.im * j| ≤ 1 / 2 * M := by
          rw [abs_mul, abs_of_nonneg hj0]
          exact mul_le_mul hz hjM hj0 (by norm_num)
        have := neg_abs_le (z.im * j)
        linarith
    _ = M * Real.exp (M / 2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The zero side of the comb. -/
theorem norm_W_combRiemannKernel_le (L : ℝ) (M : ℕ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    ‖zetaZeroConfig.W (combRiemannKernel L M) (combRiemannKernel L M)‖ ≤
      (M * Real.exp (M / 2)) ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have hm0 : 0 ≤ (M : ℝ) * Real.exp (M / 2) := by positivity
  have h := norm_W_le_of_zero_bound (f := combRiemannKernel L M)
    (E := (M * Real.exp (M / 2)) * truncatedRiemannTailEnergy L) (by positivity) (fun ρ => ?_)
  · calc _ ≤ (5 / 4) * zetaInvSqSum * ((M * Real.exp (M / 2)) * truncatedRiemannTailEnergy L) ^ 2 := h
      _ = _ := by ring
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hv1, hv2⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
  constructor
  · rw [paperFT_combRiemannKernel, norm_mul]
    have hm := norm_combMultiplier_le M hIm
    calc (1 + |(ρ : ℂ).im|) * (‖∑ j ∈ Finset.range M, Complex.exp (I * gammaOf ρ * (j : ℝ))‖ *
          ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖)
        = ‖∑ j ∈ Finset.range M, Complex.exp (I * gammaOf ρ * (j : ℝ))‖ *
          ((1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖) := by ring
      _ ≤ (M * Real.exp (M / 2)) * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv1 (by positivity) hm0
  · rw [paperFT_combRiemannKernel, norm_mul]
    have hm := norm_combMultiplier_le M hIm'
    calc (1 + |(ρ : ℂ).im|) *
          (‖∑ j ∈ Finset.range M, Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * (j : ℝ))‖ *
          ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖)
        = ‖∑ j ∈ Finset.range M, Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * (j : ℝ))‖ *
          ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖) := by ring
      _ ≤ (M * Real.exp (M / 2)) * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv2 (by positivity) hm0

/-- The autocorrelation of a continuous compactly supported real function is maximal at `0`. -/
theorem autocorr_le_autocorr_zero {F : ℝ → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F)
    (y : ℝ) : (∫ t, F t * F (t - y)) ≤ ∫ t, F t * F t := by
  have hsq : Integrable fun t => F t * F t :=
    (hFc.mul hFc).integrable_of_hasCompactSupport hFs.mul_right
  have hsq' : Integrable fun t => F (t - y) * F (t - y) := hsq.comp_sub_right y
  have hprod : Integrable fun t => F t * F (t - y) :=
    (hFc.mul (hFc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hFs.mul_right
  have hshift : (∫ t, F (t - y) * F (t - y)) = ∫ t, F t * F t :=
    integral_sub_right_eq_self (fun t => F t * F t) y
  have hmono : (∫ t, F t * F (t - y)) ≤ ∫ t, (F t * F t + F (t - y) * F (t - y)) / 2 := by
    refine integral_mono hprod ((hsq.add hsq').div_const 2) fun t => ?_
    nlinarith [sq_nonneg (F t - F (t - y))]
  rw [integral_div, integral_add hsq hsq', hshift] at hmono
  linarith

/-- The autocorrelation `∫ F(t) F(t − y) dt` of the comb profile. -/
def combAutocorr (L : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∫ t, combRiemannKernelReal L M t * combRiemannKernelReal L M (t - y)

theorem combAutocorr_eq_sum (L : ℝ) (M : ℕ) (y : ℝ) :
    combAutocorr L M y = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      truncatedRiemannAutocorr L (y + j - i) := by
  have e := integral_translateComb_autocorr (Finset.range M) (fun _ => (1 : ℝ)) (fun j => (j : ℝ))
    (continuous_truncatedRiemannKernelReal L) (hasCompactSupport_truncatedRiemannKernelReal L) y
  have hk : ∀ v, (∫ t, truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - v)) =
      truncatedRiemannAutocorr L v := fun v => rfl
  simp only [hk, one_mul] at e
  unfold combAutocorr combRiemannKernelReal
  exact e

theorem weilTest_combRiemannKernel_eq (L : ℝ) (M : ℕ) (y : ℝ) :
    EF.weilTest (combRiemannKernel L M) (combRiemannKernel L M) y = (combAutocorr L M y : ℂ) := by
  rw [combRiemannKernel_eq, weilTest_ofReal_eq]; rfl

theorem combAutocorr_nonneg (L : ℝ) (M : ℕ) (y : ℝ) : 0 ≤ combAutocorr L M y := by
  rw [combAutocorr_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => truncatedRiemannAutocorr_nonneg L _

theorem combAutocorr_le_zero (L : ℝ) (M : ℕ) (y : ℝ) : combAutocorr L M y ≤ combAutocorr L M 0 := by
  have h := autocorr_le_autocorr_zero (continuous_combRiemannKernelReal L M)
    (hasCompactSupport_combRiemannKernelReal L M) y
  unfold combAutocorr
  simpa only [sub_zero] using h

/-- `K_L(0)`-mass of the comb is linear in `M`. -/
theorem combAutocorr_zero_le {C : ℝ} (hC : ∀ L y : ℝ, truncatedRiemannAutocorr L y ≤ C * Real.exp (-(2 * |y|)))
    (hC0 : 0 ≤ C) (L : ℝ) (M : ℕ) : combAutocorr L M 0 ≤ 3 * C * M := by
  rw [combAutocorr_eq_sum]
  calc ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, truncatedRiemannAutocorr L (0 + j - i)
      ≤ ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, C * Real.exp (-(2 * |(j : ℝ) - i|)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [zero_add]; exact hC L _
    _ = ∑ i ∈ Finset.range M, C * ∑ j ∈ Finset.range M, Real.exp (-(2 * |(j : ℝ) - i|)) := by
        refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range M, C * 3 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (sum_range_exp_neg_two_abs_le i M) hC0
    _ = 3 * C * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- On `[0, 1]` the truncated autocorrelation is at least `m²`, with `m = min_{[−1,1]} Φ`. -/
theorem exists_truncatedRiemannAutocorr_ge :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℝ, 2 ≤ L → ∀ z ∈ Icc (0 : ℝ) 1, m ^ 2 ≤ truncatedRiemannAutocorr L z := by
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by norm_num, by norm_num⟩ continuous_riemannKernelReal.continuousOn
  refine ⟨riemannKernelReal x₀, riemannKernelReal_pos x₀, fun L hL z hz => ?_⟩
  set m := riemannKernelReal x₀ with hm
  have hm0 : 0 < m := riemannKernelReal_pos x₀
  have hge : ∀ t ∈ Icc (-1 : ℝ) 1, m ≤ riemannKernelReal t := fun t ht => hmin ht
  unfold truncatedRiemannAutocorr
  have hsub := setIntegral_le_integral (s := Ioc (0 : ℝ) 1) (integrable_truncatedRiemannKernel_prod L z)
    (Eventually.of_forall fun t =>
      mul_nonneg (truncatedRiemannKernelReal_nonneg L t) (truncatedRiemannKernelReal_nonneg L _))
  refine le_trans ?_ hsub
  have hcont : Continuous fun t => truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - z) :=
    (continuous_truncatedRiemannKernelReal L).mul
      ((continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const))
  have hint : IntegrableOn (fun t => truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - z))
      (Ioc (0 : ℝ) 1) := hcont.integrableOn_Ioc
  have hconst : ∫ t in Ioc (0 : ℝ) 1, m ^ 2 = m ^ 2 := by
    rw [setIntegral_const]; simp [Measure.real]
  rw [← hconst]
  refine setIntegral_mono_on (integrableOn_const (by simp)) hint measurableSet_Ioc fun t ht => ?_
  have ht1 : |t| ≤ L - 1 := by rw [abs_of_pos ht.1]; linarith [ht.2]
  have ht2 : |t - z| ≤ L - 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hz.1, hz.2]
  have e1 : truncatedRiemannKernelReal L t = riemannKernelReal t := by
    unfold truncatedRiemannKernelReal; rw [bulkCutoff_eq_one ht1, mul_one]
  have e2 : truncatedRiemannKernelReal L (t - z) = riemannKernelReal (t - z) := by
    unfold truncatedRiemannKernelReal; rw [bulkCutoff_eq_one ht2, mul_one]
  rw [e1, e2, sq]
  have g1 := hge t ⟨by linarith [ht.1], ht.2⟩
  have g2 := hge (t - z) ⟨by linarith [ht.1, hz.2], by linarith [ht.2, hz.1]⟩
  exact mul_le_mul g1 g2 hm0.le (riemannKernelReal_pos t).le

/-- **Triangle lower bound.** For `0 ≤ y` with `⌊y⌋ < M` and `L ≥ 2`,
`combAutocorr L M y ≥ (M − ⌊y⌋) m²`. -/
theorem combAutocorr_ge {m : ℝ} (hm : ∀ L : ℝ, 2 ≤ L → ∀ z ∈ Icc (0 : ℝ) 1, m ^ 2 ≤ truncatedRiemannAutocorr L z)
    {L : ℝ} (hL : 2 ≤ L) (M : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ((M : ℝ) - ⌊y⌋₊) * m ^ 2 ≤ combAutocorr L M y ∨ M ≤ ⌊y⌋₊ := by
  rcases le_or_gt M ⌊y⌋₊ with hM | hM
  · exact Or.inr hM
  left
  set d := ⌊y⌋₊ with hd
  have hyd0 : 0 ≤ y - d := by have := Nat.floor_le hy; linarith
  have hyd1 : y - d ≤ 1 := by have := Nat.lt_floor_add_one y; linarith
  have hK := hm L hL (y - d) ⟨hyd0, hyd1⟩
  rw [combAutocorr_eq_sum]
  have hin : ∀ i ∈ Finset.Ico d M, truncatedRiemannAutocorr L (y - d) ≤
      ∑ j ∈ Finset.range M, truncatedRiemannAutocorr L (y + j - i) := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hmem : i - d ∈ Finset.range M := Finset.mem_range.mpr (by omega)
    have e : y + ((i - d : ℕ) : ℝ) - i = y - d := by
      rw [Nat.cast_sub hi'.1]; ring
    have := Finset.single_le_sum (s := Finset.range M) (a := i - d)
      (f := fun j : ℕ => truncatedRiemannAutocorr L (y + j - i))
      (fun j _ => truncatedRiemannAutocorr_nonneg L _) hmem
    rwa [e] at this
  calc ((M : ℝ) - d) * m ^ 2 ≤ ((M : ℝ) - d) * truncatedRiemannAutocorr L (y - d) :=
        mul_le_mul_of_nonneg_left hK (by
          have h : (d : ℝ) < M := (by exact_mod_cast hM)
          linarith)
    _ = ∑ i ∈ Finset.Ico d M, truncatedRiemannAutocorr L (y - d) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hM.le]
    _ ≤ ∑ i ∈ Finset.Ico d M, ∑ j ∈ Finset.range M, truncatedRiemannAutocorr L (y + j - i) :=
        Finset.sum_le_sum hin
    _ ≤ ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, truncatedRiemannAutocorr L (y + j - i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
          Finset.sum_nonneg fun j _ => truncatedRiemannAutocorr_nonneg L _
        intro i hi; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2

/-! ## Summable deficit forces `Λ` -/

/-- **A Weil-positive system with summable deficit below `Λ` is `Λ`.** If `lam` is Weil-positive
with the pole term and `Σ_n (Λ(n) − lam(n))⁺ n^{−1/2} < ∞`, then `lam(n) = Λ(n)` for all `n ≥ 2`.
Unconditional; no condition is placed on the excess `(lam − Λ)⁺`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hdef : Summable fun n =>
      max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set a : ℕ → ℝ := fun n => if 2 ≤ n then
    (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0 with ha
  set ap : ℕ → ℝ := fun n => max (a n) 0 with hap
  set am : ℕ → ℝ := fun n => max (-a n) 0 with ham
  have hap0 : ∀ n, 0 ≤ ap n := fun n => le_max_right _ _
  have ham0 : ∀ n, 0 ≤ am n := fun n => le_max_right _ _
  have hsplit : ∀ n, a n = ap n - am n := fun n => (max_zero_sub_max_neg_zero_eq_self (a n)).symm
  have ham_le : ∀ n, am n ≤ max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n := by
    intro n
    have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    simp only [ham, ha]
    split_ifs with h2
    · rw [show -((lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n) =
          ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) / Real.sqrt n by ring]
      exact max_le (div_le_div_of_nonneg_right (le_max_left _ _) hs)
        (div_nonneg (le_max_right _ _) hs)
    · rw [neg_zero, max_self]; exact div_nonneg (le_max_right _ _) hs
  have ham_sum : Summable am := Summable.of_nonneg_of_le ham0 ham_le hdef
  set D := ∑' n, am n with hD
  have hD0 : 0 ≤ D := tsum_nonneg ham0
  obtain ⟨C, hC0, hC⟩ := exists_truncatedRiemannAutocorr_le
  obtain ⟨m, hm0, hm⟩ := exists_truncatedRiemannAutocorr_ge
  -- every partial sum of the excess is bounded
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, ap n ≤ (1 + 12 * C * D) / m ^ 2 := by
    intro N
    set M : ℕ := 2 * N + 2 with hM
    obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
    set Q : ℝ := ((M : ℝ) * Real.exp (M / 2)) ^ 2 with hQ
    have hQ0 : 0 ≤ Q := sq_nonneg _
    obtain ⟨L₀, hL₀⟩ := exists_nearRadicalEnergy_le (ε := 1 / (Q + 1)) (by positivity)
    set L := max L₀ 2 with hL
    have hL2 : 2 ≤ L := le_max_right _ _
    set f := combRiemannKernel L M with hf
    have hfd : ContDiff ℝ 2 f := contDiff_combRiemannKernel L M
    have hfc : HasCompactSupport f := hasCompactSupport_combRiemannKernel L M
    have hWL : ‖zetaZeroConfig.W f f‖ ≤ 1 := by
      have h1 := norm_W_combRiemannKernel_le L M hΛ'
      have h2 := hL₀ L (le_max_left _ _)
      have h3 : Q * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) ≤ Q * (1 / (Q + 1)) :=
        mul_le_mul_of_nonneg_left h2 hQ0
      have h4 : Q * (1 / (Q + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      calc ‖zetaZeroConfig.W f f‖ ≤ Q * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) :=
            h1
        _ ≤ 1 := h3.trans h4
    set k := EF.weilTest f f with hk
    have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
    set kr : ℝ → ℝ := combAutocorr L M with hkr
    have hkeq : ∀ y, k y = ((kr y : ℝ) : ℂ) := fun y => weilTest_combRiemannKernel_eq L M y
    set T : ℕ → ℝ := fun n => kr (Real.log n) + kr (-Real.log n) with hT
    have hT0 : ∀ n, 0 ≤ T n := fun n =>
      add_nonneg (combAutocorr_nonneg L M _) (combAutocorr_nonneg L M _)
    have hTle : ∀ n, T n ≤ 2 * kr 0 := fun n => by
      have h1 := combAutocorr_le_zero L M (Real.log n)
      have h2 := combAutocorr_le_zero L M (-Real.log n)
      simp only [hT, hkr]; linarith
    -- finitely many atoms are seen
    obtain ⟨N₁, hN₁⟩ := exists_forall_log_eq_zero hkc
    have hTz : ∀ n ∉ Finset.range N₁, T n = 0 := by
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      obtain ⟨h1, h2⟩ := hN₁ n hn
      rw [hkeq] at h1 h2
      have e1 : kr (Real.log n) = 0 := by exact_mod_cast h1
      have e2 : kr (-Real.log n) = 0 := by exact_mod_cast h2
      simp only [hT, e1, e2, add_zero]
    have hsum_ap : Summable fun n => ap n * T n :=
      summable_of_ne_finset_zero (s := Finset.range N₁) fun n hn => by rw [hTz n hn, mul_zero]
    have hsum_am : Summable fun n => am n * T n :=
      summable_of_ne_finset_zero (s := Finset.range N₁) fun n hn => by rw [hTz n hn, mul_zero]
    -- positivity
    have hpos := hW f hfd hfc
    rw [weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt,
      ← zeta_W_eq_weilFullFunctional hfd hfc] at hpos
    have hsum := summable_primeAtoms a hkc
    have hre : ∀ n : ℕ, (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re = a n * T n := by
      intro n
      rw [hkeq, hkeq, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [Complex.sub_re, Complex.re_tsum hsum] at hpos
    have hpos' : ∑' n, a n * T n ≤ 1 := by
      have e : (∑' n : ℕ, (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re) =
          ∑' n, a n * T n := tsum_congr hre
      rw [e] at hpos
      have := Complex.re_le_norm (zetaZeroConfig.W f f)
      linarith
    have hsplit_t : ∑' n, a n * T n = ∑' n, ap n * T n - ∑' n, am n * T n := by
      rw [← Summable.tsum_sub hsum_ap hsum_am]
      exact tsum_congr fun n => by rw [hsplit n]; ring
    have ham_bound : ∑' n, am n * T n ≤ 2 * kr 0 * D := by
      calc ∑' n, am n * T n ≤ ∑' n, am n * (2 * kr 0) :=
            hsum_am.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hTle n) (ham0 n))
              (ham_sum.mul_right _)
        _ = 2 * kr 0 * D := by rw [tsum_mul_right, hD]; ring
    have hkr0 : kr 0 ≤ 3 * C * M := combAutocorr_zero_le hC hC0 L M
    -- the atoms below `N`
    have hlow : ∀ n ∈ Finset.range N, ((N : ℝ) + 1) * m ^ 2 ≤ kr (Real.log n) := by
      intro n hn
      have hnN : n < N := Finset.mem_range.mp hn
      have hy : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have hlogn : Real.log n ≤ N := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rw [h0, Nat.cast_zero, Real.log_zero]; exact Nat.cast_nonneg N
        · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by exact_mod_cast hpos)
          have : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
          linarith
      have hfl : (⌊Real.log n⌋₊ : ℝ) ≤ N := (Nat.floor_le hy).trans hlogn
      rcases combAutocorr_ge hm hL2 M hy with h | h
      · refine le_trans ?_ h
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg m)
        rw [hM]; push_cast; linarith
      · exfalso
        have : (M : ℝ) ≤ ⌊Real.log n⌋₊ := by exact_mod_cast h
        rw [hM] at this; push_cast at this; linarith
    have hfin : ∑ n ∈ Finset.range N, ap n * kr (Real.log n) ≤ ∑' n, ap n * T n := by
      calc ∑ n ∈ Finset.range N, ap n * kr (Real.log n)
          ≤ ∑ n ∈ Finset.range N, ap n * T n :=
            Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
              (by simp only [hT]; linarith [combAutocorr_nonneg L M (-Real.log n)]) (hap0 n)
        _ ≤ ∑' n, ap n * T n :=
            hsum_ap.sum_le_tsum _ fun n _ => mul_nonneg (hap0 n) (hT0 n)
    have hlow_sum : ((N : ℝ) + 1) * m ^ 2 * ∑ n ∈ Finset.range N, ap n ≤
        ∑ n ∈ Finset.range N, ap n * kr (Real.log n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun n hn => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hlow n hn) (hap0 n)
    have htotal : ((N : ℝ) + 1) * m ^ 2 * ∑ n ∈ Finset.range N, ap n ≤ 1 + 6 * C * M * D := by
      have h1 := ham_bound
      have h2 : 2 * kr 0 * D ≤ 2 * (3 * C * M) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkr0 (by norm_num)) hD0
      linarith [hlow_sum.trans hfin]
    have hm2 : 0 < m ^ 2 := by positivity
    have hN1 : (0 : ℝ) < N + 1 := by positivity
    rw [le_div_iff₀ hm2]
    have hMN : (M : ℝ) = 2 * (N + 1) := by rw [hM]; push_cast; ring
    rw [hMN] at htotal
    have hS0 : 0 ≤ ∑ n ∈ Finset.range N, ap n := Finset.sum_nonneg fun n _ => hap0 n
    have key : ((N : ℝ) + 1) * (m ^ 2 * ∑ n ∈ Finset.range N, ap n) ≤
        ((N : ℝ) + 1) * (1 + 12 * C * D) := by
      have hCD : 0 ≤ C * D := mul_nonneg hC0 hD0
      nlinarith
    have := le_of_mul_le_mul_left key hN1
    linarith
  -- the excess is summable, hence the whole deviation
  have hap_sum : Summable ap := summable_of_sum_range_le hap0 hpartial
  have habs : Summable fun n => |lam n - ArithmeticFunction.vonMangoldt n| / Real.sqrt n := by
    rw [← summable_nat_add_iff 2]
    refine (hap_sum.add ham_sum).comp_injective (add_left_injective 2) |>.congr fun n => ?_
    simp only [Function.comp, hap, ham, ha, if_pos (show 2 ≤ n + 2 by omega)]
    have hs : 0 < Real.sqrt ((n + 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    rw [max_zero_add_max_neg_zero_eq_abs_self, abs_div, abs_of_pos hs]
  intro n hn
  exact eq_vonMangoldt_of_weilPositive_of_summable_sub habs (weilPositive_of_weilPositiveFull hW) hn

/-- **Eventually above `Λ` means `Λ`.** A Weil-positive system with `lam(n) ≥ Λ(n)` for all large
`n` equals `Λ`; finitely many exceptions are allowed a priori and do not occur. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_eventually_ge {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {N₀ : ℕ} (hge : ∀ n, N₀ ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit hW ?_
  refine summable_of_ne_finset_zero (s := Finset.range N₀) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [max_eq_right (sub_nonpos.mpr (hge n hn)), zero_div]

/-- **RH as a Weil-positive system with summable deficit.** RH holds iff some full-cone
Weil-positive `lam` has `Σ_n (Λ(n) − lam(n))⁺ n^{−1/2} < ∞`; such a `lam` equals `Λ`. -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_summable_deficit :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      Summable fun n => max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n := by
  constructor
  · intro hRH
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, ?_⟩
    simp only [sub_self, max_self, zero_div]
    exact summable_zero
  · rintro ⟨lam, hW, hdef⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit hW hdef
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

end

end RHTower
