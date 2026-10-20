import GaloisForLFunctions.RHTower.FreeLagSymbolBoundaryLayer
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon

/-!
# The sharp archimedean horizon of the symbol of `ζ`

For a `C²` profile `f` supported in `[−a, a]`, the localized Weil form of `ζ` at height `2πξ` is
the pole terms plus `∫ |h_f(τ + 2πξ)|² (μ(τ) + P_X(τ)) dτ` with `X = e^{2a}` and the prime symbol
`P_X(τ) = −(1/π) Σ_{n ≤ X} Λ(n) n^{−1/2} cos(τ log n)`. Height positivity rests on a lower bound
for `μ + P_X` that is uniform in `τ`.

* **Sharp prime mass** (`exists_sum_vonMangoldt_div_sqrt_le`). By the prime number theorem,
  `Σ_{n ≤ X} Λ(n)/√n = (2 + o(1))√X`. So for every `ε > 0` the sum is at most
  `(2 + ε)√X + C_ε`.
* **Sharp horizon** (`exists_mu_add_PX_ge`).
  `μ + P_X ≥ (log(1 + |τ|/4) − C_ε − (4 + ε)√X)/2π`, so the symbol is nonnegative above
  `|τ| = 4 exp(C_ε + (4 + ε)√X)`. Chebyshev's bound gives the exponent `10 + 68√X`.
* **Optimality** (`not_exists_PX_ge_of_lt_two`). Since `P_X(0) = −(1/π) Σ_{n ≤ X} Λ(n)/√n`, no
  height-uniform bound `P_X ≥ −(c√X + C)/π` holds with `c < 2`. The coefficient `4` of the horizon
  exponent is optimal for height-uniform symbol bounds.
* **Single-height positivity** (`exists_sharp_zetaZeroConfig_re_W_heightShift_ge`). For every
  `C²` profile of aperture `a`,
  `Re W_ζ(S_ξ f, S_ξ f) ≥ (log(1 + π|ξ|/4) − C_ε − (4 + ε)e^a − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`.
  At height `T` the localized forms are therefore positive for prime lengths with
  `√X ≤ (¼ − ε) log T` (`zetaZeroConfig_re_W_heightShift_nonneg_of_horizon`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

theorem sum_Icc_zero_eq_sum_Ioc_vonMangoldt_div_sqrt (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N, (Λ n : ℝ) / Real.sqrt n =
      ∑ n ∈ Finset.Ioc 0 N, (Λ n : ℝ) / Real.sqrt n := by
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
  simp

/-- **Sharp prime mass.** For every `ε > 0` there is `C ≥ 0` with
`Σ_{0 < n ≤ X} Λ(n)/√n ≤ (2 + ε)√X + C` for all `X ≥ 0`. -/
theorem exists_sum_vonMangoldt_div_sqrt_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X →
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n ≤ (2 + ε) * Real.sqrt X + C := by
  have hev := FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt.eventually
    (Iio_mem_nhds (show (2 : ℝ) < 2 + ε by linarith))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop 0))
  refine ⟨34 * Real.sqrt X₀, by positivity, fun X hX => ?_⟩
  have hsX := Real.sqrt_nonneg X
  have hsX₀ := Real.sqrt_nonneg X₀
  rcases le_or_gt X₀ X with h | h
  · obtain ⟨h1, h2⟩ := hX₀ X h
    have h1' := (div_lt_iff₀ (Real.sqrt_pos.mpr h2)).mp h1
    rw [sum_Icc_zero_eq_sum_Ioc_vonMangoldt_div_sqrt] at h1'
    linarith
  · calc _ ≤ 34 * Real.sqrt (⌊X⌋₊ : ℝ) := sum_vonMangoldt_div_sqrt_le _
      _ ≤ 34 * Real.sqrt X₀ := by gcongr; exact (Nat.floor_le hX).trans h.le
      _ ≤ _ := by nlinarith

/-- **Sharp lower bound of the prime symbol**, uniform in height: `P_X ≥ −((2 + ε)√X + C)/π`. -/
theorem exists_PX_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X → ∀ τ : ℝ, -(((2 + ε) * Real.sqrt X + C) / π) ≤ PX X τ := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_vonMangoldt_div_sqrt_le hε
  refine ⟨C, hC0, fun X hX τ => ?_⟩
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n * Real.cos (τ * Real.log n) ≤
      (2 + ε) * Real.sqrt X + C :=
    (Finset.sum_le_sum fun n _ => mul_le_of_le_one_right
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.cos_le_one _)).trans (hC X hX)
  rw [PX, neg_mul, neg_le_neg_iff, one_div, ← div_eq_inv_mul]
  exact (div_le_div_iff_of_pos_right Real.pi_pos).mpr hsum

/-- **The sharp archimedean horizon.** For every `ε > 0` there is `C ≥ 0` with
`μ(τ) + P_X(τ) ≥ (log(1 + |τ|/4) − (C + (4 + ε)√X))/2π`. -/
theorem exists_mu_add_PX_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X → ∀ τ : ℝ,
      (Real.log (1 + |τ| / 4) - (C + (4 + ε) * Real.sqrt X)) / (2 * π) ≤ mu τ + PX X τ := by
  obtain ⟨C, hC0, hC⟩ := exists_PX_ge (half_pos hε)
  refine ⟨10 + 2 * C, by positivity, fun X hX τ => ?_⟩
  have h1 := mu_ge_log τ
  have h2 := hC X hX τ
  have e : (Real.log (1 + |τ| / 4) - (10 + 2 * C + (4 + ε) * Real.sqrt X)) / (2 * π) =
      (Real.log (1 + |τ| / 4) - 10) / (2 * π) - ((2 + ε / 2) * Real.sqrt X + C) / π := by
    field_simp
    ring
  linarith

theorem PX_zero (X : ℝ) :
    PX X 0 = -(1 / π) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n := by
  simp [PX]

/-- **Optimality.** No lower bound `P_X(τ) ≥ −(c√X + C)/π` uniform in `τ` holds with `c < 2`. -/
theorem not_exists_PX_ge_of_lt_two {c : ℝ} (hc : c < 2) :
    ¬ ∃ C : ℝ, ∀ X : ℝ, 0 ≤ X → ∀ τ : ℝ, -((c * Real.sqrt X + C) / π) ≤ PX X τ := by
  rintro ⟨C, hC⟩
  have hev := FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt.eventually
    (Ioi_mem_nhds (show (c + 2) / 2 < 2 by linarith))
  have hev2 : ∀ᶠ X : ℝ in atTop, 2 * |C| / (2 - c) < Real.sqrt X :=
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨X, hX1, hX2, hX3⟩ := (hev.and (hev2.and (eventually_gt_atTop 0))).exists
  have h := hC X hX3.le 0
  rw [PX_zero, neg_mul, neg_le_neg_iff, one_div, ← div_eq_inv_mul,
    div_le_div_iff_of_pos_right Real.pi_pos] at h
  have hge := (lt_div_iff₀ (Real.sqrt_pos.mpr hX3)).mp hX1
  rw [sum_Icc_zero_eq_sum_Ioc_vonMangoldt_div_sqrt] at hge
  have h2 := (div_lt_iff₀ (by linarith : (0 : ℝ) < 2 - c)).mp hX2
  nlinarith [le_abs_self C]

/-- **Single-height lower bound from a symbol bound.** If
`μ + P_{e^{2a}} ≥ (log(1 + |τ|/4) − E)/2π`, then every `C²` profile `f` supported in `[−a, a]`
satisfies `Re W_ζ(S_ξ f, S_ξ f) ≥ (log(1 + π|ξ|/4) − E − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`. -/
theorem zetaZeroConfig_re_W_heightShift_ge_of_symbol {a E : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ)
    (hE : ∀ τ, (Real.log (1 + |τ| / 4) - E) / (2 * π) ≤ mu τ + PX (Real.exp (2 * a)) τ) :
    (Real.log (1 + π * |ξ| / 4) - E - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ f) ⊆ Icc (-a) a :=
    (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hsym : Integrable fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 *
      (mu τ + PX (Real.exp (2 * a)) τ) := by
    refine (integrable_paperFT_mul_mu_add_PX hkd hkc (2 * a)).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have h := re_pole_add_integral_symbol_heightShift_ge ha hf hfs ξ hE hsym
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
      ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)).re =
      ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * (mu τ + PX (Real.exp (2 * a)) τ) := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
        ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)) = fun τ : ℝ =>
        ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * (mu τ + PX (Real.exp (2 * a)) τ) : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [zetaZeroConfig_W_eq_pole_add_integral hg hgs, Complex.add_re, hμre]
  exact h

/-- **Sharp single-height lower bound.** For every `ε > 0` there is `C ≥ 0` such that every `C²`
profile `f` supported in `[−a, a]` satisfies
`Re W_ζ(S_ξ f, S_ξ f) ≥ (log(1 + π|ξ|/4) − (C + (4 + ε)e^a) − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`. -/
theorem exists_sharp_zetaZeroConfig_re_W_heightShift_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 0 ≤ a → ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f →
      tsupport f ⊆ Icc (-a) a → ∀ ξ : ℝ,
        (Real.log (1 + π * |ξ| / 4) - (C + (4 + ε) * Real.exp a) - 2 * pairEnergy (1 / 2) a) *
            (∫ t, ‖f t‖ ^ 2) -
          (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
          (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  obtain ⟨C, hC0, hC⟩ := exists_mu_add_PX_ge hε
  refine ⟨C, hC0, fun {a} ha {f} hf hfs ξ => zetaZeroConfig_re_W_heightShift_ge_of_symbol ha hf hfs
    ξ fun τ => ?_⟩
  have hsq : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
    rw [show 2 * a = a + a by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a).le]
  simpa [hsq] using hC _ (Real.exp_pos (2 * a)).le τ

/-- **The unconditional single-height range.** For every `ε > 0` there is `C` such that
`Re W_ζ(S_ξ f, S_ξ f) ≥ 0` for every `C²` profile `f` supported in `[−a, a]` whenever
`C + (4 + ε)e^a + 2S(a) + 1 ≤ log(1 + π|ξ|/4)` and the spectral tail satisfies
`B_f² ≤ 8(1 + π|ξ|)‖f‖²`. -/
theorem zetaZeroConfig_re_W_heightShift_nonneg_of_horizon {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 0 ≤ a → ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f →
      tsupport f ⊆ Icc (-a) a → ∀ ξ : ℝ,
        C + (4 + ε) * Real.exp a + 2 * pairEnergy (1 / 2) a + 1 ≤ Real.log (1 + π * |ξ| / 4) →
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
          ∫ t, ‖f t‖ ^ 2 →
        0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  obtain ⟨C, hC0, hC⟩ := exists_sharp_zetaZeroConfig_re_W_heightShift_ge hε
  refine ⟨C, hC0, fun {a} ha {f} hf hfs ξ hlog htail => ?_⟩
  have h := hC ha hf hfs ξ
  have hN : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

end GaloisForLFunctions.SquareRootThreshold
