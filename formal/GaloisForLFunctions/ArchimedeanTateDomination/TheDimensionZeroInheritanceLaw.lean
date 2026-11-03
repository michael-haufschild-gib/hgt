import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowFormIsTheDerivativeOfTheJordanCounts
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTangentPrincipleOfTheTateFamily
import GaloisForLFunctions.WindowTowerOfSpecZ.TheJetsOfTheTateFamily

/-!
# Dimension-zero inheritance and the Bombieri–Selberg quadratic envelope

On a window `W_A` (`IsWindowTest A H`), Weil's quadratic form decomposes into the archimedean–polar
functional `archWindowForm H = Ω(0)‖H‖² + J_∞(H) + (½⟨c,H⟩² − ½⟨s,H⟩²)` minus the dimension-zero
derivative of the window point counts `tatePointCount A H k = 2(τ_H(k) − ‖H‖²)`.

* **Jet decomposition and sequential inheritance** (`weilQuad_eq_archWindowForm_sub_deriv_tatePointCount`,
  `weilQuad_nonneg_of_seq_tateDomination`, `riemannHypothesis_of_local_archimedeanTateDomination`):
  if an archimedean family `a` with `a(0) = 0` and `a′(0) = archWindowForm H` dominates
  `tatePointCount A H` along any positive sequence `κ_m ↓ 0` (in particular on any interval `(0, k₀]`),
  dividing by `κ_m` yields `0 ≤ weilQuad H`; across all windows this implies `RiemannHypothesis`.
* **Bombieri–Selberg quadratic envelope** (`jordanTotient_sub_linear_ge_selberg`,
  `jordanTotient_sub_linear_le_sq`): from the exponential generating series
  `J_k(n) = Σ_{j≥0} k^j Λ_j(n) / j!` with `Λ_j ≥ 0`, every `n ≥ 2` satisfies
  `(k² / 2) Λ₂(n) ≤ J_k(n) − k Λ(n)` for all `k ≥ 0` (with `Λ₂(2) = (log 2)² > 0`) and
  `J_k(n) − k Λ(n) ≤ k² (J₁(n) − Λ(n))` for `0 ≤ k ≤ 1`.
* **Coercive window domination** (`linearArchimedeanDomination_of_weilFloor`): on any window `W_A`
  carrying a strict spectral floor `μ ‖H‖² ≤ weilQuad H` (`μ > 0`), the linear archimedean form
  `k · archWindowForm H` dominates `tatePointCount A H k` on the explicit uniform horizon
  `0 ≤ k ≤ min 1 (μ / (coerciveWindowConst A + 1))`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.ArchimedeanTateDomination

open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
open RHTower.WeilMarkovPole ArithmeticDegenerationTheory

/-! ### The archimedean–polar window form and the Tate point counts -/

/-- The critical-line Gamma quadratic form `Ω(0)‖H‖² + J_∞(H)` on a window profile. -/
def archGammaForm (H : ℝ → ℝ) : ℝ :=
  EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H

/-- The rank-two unshifted pole quadratic form `½⟨c,H⟩² − ½⟨s,H⟩²`. -/
def windowPoleForm (H : ℝ → ℝ) : ℝ :=
  coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2

/-- The combined archimedean–polar window form `Ω(0)‖H‖² + J_∞(H) + pole(H)`. -/
def archWindowForm (H : ℝ → ℝ) : ℝ :=
  archGammaForm H + windowPoleForm H

/-- Twice the reduced window Tate point count `2(τ_H(k) − ‖H‖²)` in dimension `k`. -/
def tatePointCount (A : ℝ) (H : ℝ → ℝ) (k : ℝ) : ℝ :=
  2 * (tateFunction A H k - ∫ u, H u ^ 2)

theorem windowPoleForm_eq_exp_prod {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    windowPoleForm H =
      2 * ((∫ u, H u * Real.exp (u / 2)) * ∫ u, H u * Real.exp (-u / 2)) :=
  (pole_eq_pairings H hH.continuous hH.hasCompactSupport).symm

theorem tatePointCount_zero {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    tatePointCount A H 0 = 0 := by
  rw [tatePointCount, tateFunction_zero hH, sub_self, mul_zero]

theorem one_le_windowLevel_of_nonneg {A : ℝ} (hA : 0 ≤ A) : 1 ≤ windowLevel A :=
  (Nat.one_le_floor_iff _).mpr (Real.one_le_exp hA)

/-- On any window of length `A ≥ 0`, `tatePointCount A H k` sums over `2 ≤ n ≤ ⌊e^A⌋`. -/
theorem tatePointCount_eq_sum {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ} (hH : IsWindowTest A H) (k : ℝ) :
    tatePointCount A H k = 2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
      jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) := by
  have h1 : 1 ≤ windowLevel A := one_le_windowLevel_of_nonneg hA
  rw [tatePointCount, tateFunction_eq hH, ← Finset.sum_Ioc_add_eq_sum_Icc h1]
  have hone : jordanTotient k 1 / Real.sqrt (1 : ℕ) * (∫ u, H u * H (u + Real.log (1 : ℕ))) =
      ∫ u, H u ^ 2 := by
    simp [jordanTotient_one_eq, sq]
  rw [hone, add_sub_cancel_right]
  have hset : Finset.Ioc 1 (windowLevel A) = Finset.Icc 2 (windowLevel A) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hset]

theorem hasDerivAt_tatePointCount {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    HasDerivAt (tatePointCount A H)
      (2 * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u) 0 :=
  ((hasDerivAt_tateFunction hH).sub_const (∫ u, H u ^ 2)).const_mul 2

/-- **Dimension-zero jet identity**: Weil's window form is `archWindowForm H` minus the `k = 0`
derivative of `tatePointCount A H`. -/
theorem weilQuad_eq_archWindowForm_sub_deriv_tatePointCount {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) :
    weilQuad H = archWindowForm H - deriv (tatePointCount A H) 0 := by
  rw [weilQuad_eq_tateJet hH, tateFunction_zero hH, (hasDerivAt_tatePointCount hH).deriv,
    (hasDerivAt_tateFunction hH).deriv, archWindowForm, archGammaForm, windowPoleForm]
  ring

theorem weilQuad_eq_archWindowForm_sub_vonMangoldt {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    weilQuad H = archWindowForm H -
      2 * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u := by
  rw [weilQuad_eq_archWindowForm_sub_deriv_tatePointCount hH, (hasDerivAt_tatePointCount hH).deriv]

/-! ### Dimension-zero inheritance -/

/-- **Sequential dimension-zero inheritance**: if `a(0) = 0`, `a′(0) = archWindowForm H`, and
`tatePointCount A H (κ m) ≤ a (κ m)` along any positive sequence `κ m → 0`, then `0 ≤ weilQuad H`. -/
theorem weilQuad_nonneg_of_seq_tateDomination {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {a : ℝ → ℝ} (ha0 : a 0 = 0) (ha : HasDerivAt a (archWindowForm H) 0)
    {κ : ℕ → ℝ} (hκ_pos : ∀ m, 0 < κ m) (hκ_lim : Tendsto κ atTop (𝓝 0))
    (hdom : ∀ m, tatePointCount A H (κ m) ≤ a (κ m)) :
    0 ≤ weilQuad H := by
  have hP : HasDerivAt (fun k => a k - tatePointCount A H k) (weilQuad H) 0 := by
    rw [weilQuad_eq_archWindowForm_sub_vonMangoldt hH]
    exact ha.sub (hasDerivAt_tatePointCount hH)
  have hnhds : Tendsto κ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hκ_lim, Eventually.of_forall hκ_pos⟩
  refine ge_of_tendsto (hP.tendsto_slope_zero_right.comp hnhds) (Eventually.of_forall fun m => ?_)
  simp only [Function.comp_apply, zero_add, ha0, tatePointCount_zero hH, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (hκ_pos m).le) (sub_nonneg.mpr (hdom m))

/-- **Interval dimension-zero inheritance**: domination on `(0, k₀]` implies `0 ≤ weilQuad H`. -/
theorem weilQuad_nonneg_of_local_tateDomination {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {a : ℝ → ℝ} (ha0 : a 0 = 0) (ha : HasDerivAt a (archWindowForm H) 0)
    {k₀ : ℝ} (hk₀ : 0 < k₀) (hdom : ∀ k ∈ Ioc 0 k₀, tatePointCount A H k ≤ a k) :
    0 ≤ weilQuad H := by
  have hP : HasDerivAt (fun k => a k - tatePointCount A H k) (weilQuad H) 0 := by
    rw [weilQuad_eq_archWindowForm_sub_vonMangoldt hH]
    exact ha.sub (hasDerivAt_tatePointCount hH)
  refine ge_of_tendsto hP.tendsto_slope_zero_right ?_
  filter_upwards [Ioo_mem_nhdsGT hk₀] with k hk
  simp only [zero_add, ha0, tatePointCount_zero hH, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hk.1.le) (sub_nonneg.mpr (hdom k ⟨hk.1, hk.2.le⟩))

/-- **Window-local inheritance implies the Riemann Hypothesis**: even with a test-dependent family
and test-dependent horizon `k₀(A, H) > 0`, domination on every window forces `RiemannHypothesis`. -/
theorem riemannHypothesis_of_local_archimedeanTateDomination
    (h : ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      ∃ a : ℝ → ℝ, a 0 = 0 ∧ HasDerivAt a (archWindowForm H) 0 ∧
        ∃ k₀ > 0, ∀ k ∈ Ioc 0 k₀, tatePointCount A H k ≤ a k) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_windowForm_nonneg]
  intro A hA H hH
  obtain ⟨a, ha0, ha, k₀, hk₀, hdom⟩ := h A hA H hH
  exact weilQuad_nonneg_of_local_tateDomination hH ha0 ha hk₀ hdom

/-! ### The Bombieri–Selberg quadratic Taylor envelope -/

private theorem tateJet_head_two {n : ℕ} (hn : 2 ≤ n) (k : ℝ) :
    ∑ j ∈ Finset.range 2, k ^ j * genVonMangoldt j n / (j.factorial : ℝ) =
      k * ArithmeticFunction.vonMangoldt n := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : genVonMangoldt 0 n = 0 := by
    rw [genVonMangoldt_zero, ArithmeticFunction.one_apply, if_neg (by omega)]
  rw [h0, genVonMangoldt_one]
  simp

/-- **Selberg second-jet lower bound**: for `k ≥ 0` and `n ≥ 2`,
`(k² / 2) Λ₂(n) ≤ J_k(n) − k Λ(n)`. -/
theorem jordanTotient_sub_linear_ge_selberg {k : ℝ} (hk : 0 ≤ k) {n : ℕ} (hn : 2 ≤ n) :
    k ^ 2 / 2 * genVonMangoldt 2 n ≤ jordanTotient k n - k * ArithmeticFunction.vonMangoldt n := by
  have hs := hasSum_tateJet n k
  have hle := hs.summable.sum_le_tsum (Finset.range 3) fun j _ =>
    div_nonneg (mul_nonneg (pow_nonneg hk j) (genVonMangoldt_nonneg j n)) (Nat.cast_nonneg _)
  rw [hs.tsum_eq, Finset.sum_range_succ, tateJet_head_two hn k] at hle
  have hfac : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  rw [hfac] at hle
  linarith

/-- Selberg's second generalized von Mangoldt weight at the first prime is `(log 2)²`. -/
theorem genVonMangoldt_two_two : genVonMangoldt 2 2 = Real.log 2 ^ 2 := by
  rw [← tateJet_zero_dim, tateJet]
  have hant : (2 : ℕ).divisorsAntidiagonal = {(1, 2), (2, 1)} := by decide
  rw [hant, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp

theorem genVonMangoldt_two_two_pos : 0 < genVonMangoldt 2 2 := by
  rw [genVonMangoldt_two_two]
  exact sq_pos_of_pos (Real.log_pos (by norm_num))

/-- **Quadratic upper envelope on `[0, 1]`**: for `0 ≤ k ≤ 1` and `n ≥ 2`,
`J_k(n) − k Λ(n) ≤ k² (J₁(n) − Λ(n))`. -/
theorem jordanTotient_sub_linear_le_sq {k : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    jordanTotient k n - k * ArithmeticFunction.vonMangoldt n ≤
      k ^ 2 * (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) := by
  have hsk := (hasSum_nat_add_iff' 2).mpr (hasSum_tateJet n k)
  have hs1 := ((hasSum_nat_add_iff' 2).mpr (hasSum_tateJet n 1)).mul_left (k ^ 2)
  rw [tateJet_head_two hn k] at hsk
  rw [tateJet_head_two hn 1, one_mul] at hs1
  refine hasSum_le (fun j => ?_) hsk hs1
  have hkj : k ^ (j + 2) ≤ k ^ 2 * (1 : ℝ) ^ (j + 2) := by
    rw [one_pow, mul_one, pow_add, mul_comm]
    exact mul_le_of_le_one_right (sq_nonneg k) (pow_le_one₀ hk hk1)
  have hnn : 0 ≤ genVonMangoldt (j + 2) n / ((j + 2).factorial : ℝ) :=
    div_nonneg (genVonMangoldt_nonneg _ _) (Nat.cast_nonneg _)
  calc k ^ (j + 2) * genVonMangoldt (j + 2) n / ((j + 2).factorial : ℝ)
      = k ^ (j + 2) * (genVonMangoldt (j + 2) n / ((j + 2).factorial : ℝ)) := by ring
    _ ≤ (k ^ 2 * (1 : ℝ) ^ (j + 2)) * (genVonMangoldt (j + 2) n / ((j + 2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hkj hnn
    _ = k ^ 2 * ((1 : ℝ) ^ (j + 2) * genVonMangoldt (j + 2) n / ((j + 2).factorial : ℝ)) := by ring

theorem jordanTotient_one_sub_vonMangoldt_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ jordanTotient 1 n - ArithmeticFunction.vonMangoldt n := by
  have h := jordanTotient_ge_tangent zero_le_one n
  rw [if_neg (by omega : n ≠ 1), zero_add, one_mul] at h
  linarith

/-! ### Coercive window domination -/

/-- The quadratic remainder constant `2 Σ_{2 ≤ n ≤ ⌊e^A⌋} (J₁(n) − Λ(n)) / √n` of a window. -/
def coerciveWindowConst (A : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
    (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n

theorem coerciveWindowConst_nonneg (A : ℝ) : 0 ≤ coerciveWindowConst A :=
  mul_nonneg zero_le_two <| Finset.sum_nonneg fun _ hn =>
    div_nonneg (jordanTotient_one_sub_vonMangoldt_nonneg (Finset.mem_Icc.mp hn).1)
      (Real.sqrt_nonneg _)

theorem abs_autocorr_le_norm_sq {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) (ℓ : ℝ) :
    |∫ u, H u * H (u + ℓ)| ≤ ∫ u, H u ^ 2 := by
  have iH : Integrable fun u => H u ^ 2 := integrable_sq hH.continuous hH.hasCompactSupport
  have iH' : Integrable fun u => H (u + ℓ) ^ 2 := iH.comp_add_right ℓ
  have iP : Integrable fun u => H u * H (u + ℓ) :=
    integrable_mul_shift hH.continuous hH.hasCompactSupport ℓ
  have hshift : ∫ u, H (u + ℓ) ^ 2 = ∫ u, H u ^ 2 :=
    integral_add_right_eq_self (fun u => H u ^ 2) ℓ
  rw [abs_le]
  constructor
  · have hm := integral_mono (f := fun u => -(H u ^ 2 + H (u + ℓ) ^ 2) / 2)
      (g := fun u => H u * H (u + ℓ)) ((iH.add iH').neg.div_const 2) iP fun u => by
        dsimp only
        nlinarith only [sq_nonneg (H u + H (u + ℓ))]
    rw [integral_div, integral_neg, integral_add iH iH', hshift] at hm
    linarith
  · have hm := integral_mono (f := fun u => H u * H (u + ℓ))
      (g := fun u => (H u ^ 2 + H (u + ℓ) ^ 2) / 2) iP ((iH.add iH').div_const 2) fun u => by
        dsimp only
        nlinarith only [sq_nonneg (H u - H (u + ℓ))]
    rw [integral_div, integral_add iH iH', hshift] at hm
    linarith

/-- For `0 ≤ k ≤ 1`, the Taylor remainder of `tatePointCount A H k` past its 1-jet is bounded by
`coerciveWindowConst A · k² ‖H‖²`. -/
theorem abs_tatePointCount_sub_jet_le {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1) :
    |tatePointCount A H k -
        2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u| ≤
      coerciveWindowConst A * k ^ 2 * ∫ u, H u ^ 2 := by
  have h1 : 1 ≤ windowLevel A := one_le_windowLevel_of_nonneg hA
  have hset : Finset.Ioc 1 (windowLevel A) = Finset.Icc 2 (windowLevel A) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hvon : ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u =
      ∑ n ∈ Finset.Icc 2 (windowLevel A),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) := by
    rw [integral_windowRep_vonMangoldt_eq_sum hH, ← Finset.sum_Ioc_add_eq_sum_Icc h1]
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul, add_zero, hset]
  have hdiff : tatePointCount A H k -
      2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u =
      2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
        (jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
          ∫ u, H u * H (u + Real.log n) := by
    have hmul : 2 * k * ∑ n ∈ Finset.Icc 2 (windowLevel A),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (∫ u, H u * H (u + Real.log n)) =
        2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
          k * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * ∫ u, H u * H (u + Real.log n)) := by
      rw [mul_assoc, Finset.mul_sum]
    rw [tatePointCount_eq_sum hA hH k, hvon, hmul, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hdiff, abs_mul, abs_of_pos two_pos, coerciveWindowConst, mul_assoc, mul_assoc,
    Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n hn => ?_)) two_pos.le
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hJ0 : 0 ≤ jordanTotient k n - k * ArithmeticFunction.vonMangoldt n := by
    have ht := jordanTotient_ge_tangent hk n
    rw [if_neg (by omega : n ≠ 1), zero_add] at ht
    linarith
  have hJ1 : jordanTotient k n - k * ArithmeticFunction.vonMangoldt n ≤
      k ^ 2 * (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) :=
    jordanTotient_sub_linear_le_sq hk hk1 hn2
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [abs_mul, abs_div, abs_of_nonneg hJ0, abs_of_pos hsq]
  have hcorr := abs_autocorr_le_norm_sq hH (Real.log n)
  have hterm : (jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) *
      |∫ u, H u * H (u + Real.log n)| ≤
      k ^ 2 * (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) * ∫ u, H u ^ 2 :=
    mul_le_mul hJ1 hcorr (abs_nonneg _)
      (mul_nonneg (sq_nonneg k) (jordanTotient_one_sub_vonMangoldt_nonneg hn2))
  calc (jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
        |∫ u, H u * H (u + Real.log n)|
      = ((jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) *
          |∫ u, H u * H (u + Real.log n)|) / Real.sqrt n := by ring
    _ ≤ (k ^ 2 * (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) *
          ∫ u, H u ^ 2) / Real.sqrt n := div_le_div_of_nonneg_right hterm hsq.le
    _ = (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
          (k ^ 2 * ∫ u, H u ^ 2) := by ring

/-- **Coercive window domination**: on any window `W_A` (`A ≥ 0`) with a Weil floor
`μ ‖H‖² ≤ weilQuad H`, the linear archimedean form `k · archWindowForm H` dominates
`tatePointCount A H k` on `0 ≤ k ≤ min 1 (μ / (coerciveWindowConst A + 1))`. -/
theorem linearArchimedeanDomination_of_weilFloor {A μ : ℝ} (hA : 0 ≤ A)
    (hfloor : ∀ H : ℝ → ℝ, IsWindowTest A H → μ * ∫ u, H u ^ 2 ≤ weilQuad H)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) {k : ℝ} (hk : 0 ≤ k)
    (hk_top : k ≤ min 1 (μ / (coerciveWindowConst A + 1))) :
    tatePointCount A H k ≤ k * archWindowForm H := by
  have hk1 : k ≤ 1 := hk_top.trans (min_le_left _ _)
  have hkC : k ≤ μ / (coerciveWindowConst A + 1) := hk_top.trans (min_le_right _ _)
  have hden : 0 < coerciveWindowConst A + 1 := by linarith [coerciveWindowConst_nonneg A]
  have hk_mul : coerciveWindowConst A * k ≤ μ := by
    have h1 := (le_div_iff₀ hden).mp hkC
    nlinarith [hk]
  have hE : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hrem := (le_abs_self _).trans (abs_tatePointCount_sub_jet_le hA hH hk hk1)
  have hQ := mul_le_mul_of_nonneg_left (hfloor H hH) hk
  rw [weilQuad_eq_archWindowForm_sub_vonMangoldt hH] at hQ
  have hck : coerciveWindowConst A * k ^ 2 * ∫ u, H u ^ 2 ≤ k * (μ * ∫ u, H u ^ 2) := by
    have : coerciveWindowConst A * k ^ 2 = k * (coerciveWindowConst A * k) := by ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk_mul hE) hk
  linarith

end GaloisForLFunctions.ArchimedeanTateDomination

#print axioms GaloisForLFunctions.ArchimedeanTateDomination.weilQuad_nonneg_of_seq_tateDomination
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.riemannHypothesis_of_local_archimedeanTateDomination
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.jordanTotient_sub_linear_ge_selberg
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.jordanTotient_sub_linear_le_sq
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.linearArchimedeanDomination_of_weilFloor
