import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheHyperplaneGapIsTheSelectiveMargin
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheSelectiveGardingInequality
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo

/-!
# The selective margin is `2 log 2`

RenormalizedArithmeticPotentialTheory proves that the multiplicative walk has Poincaré constant
`2 log 2`: for every `ε > 0`, eventually in `N`, `(2 log 2 − ε) Var ≤ D_N`, and the prime form is
at most `(log N − γ − 2 log 2 + ε)|x|²` on the harmonic hyperplane. With the conductor-two
excitation (`le_two_mul_log_two_of_hasHyperplaneGap`) this fixes the hyperplane gap of `ζ`, and the
Robin–Euler ceiling fixes that of the Liouville twin.

* **The margin of `ζ` is exactly `2 log 2`** (`isGreatest_zeta_hyperplaneGap`).
* **The margin of the Liouville twin is exactly `0`** (`isGreatest_liouville_hyperplaneGap`): every
  sign gauge `ω² = 1` has gap `0` (`hasHyperplaneGap_zero_of_mul_self_eq_one`), and the Liouville
  twin has no positive one.
* **The selective margin** (`sSup_zeta_sub_sSup_liouville_hyperplaneGap`): the difference of the two
  optimal gaps is `2 log 2`.
* **The sharp selective Poincaré inequality** (`eventually_poleDefect_ge_offPole_sharp`): for every
  `η > 0`, eventually in `N`, `D_N(x) ≥ (2 log 2 − η)(|x|² − ℓ(x)²/H_N)` for all `x`.
* **The sharp selective Gårding inequality** (`eventually_weilQuad_atomicTest_ge_sharp`): on narrow
  atomic tests the Gårding inequality holds with reserve `c₀(2 log 2 − η)`.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticLorentzianGeometry
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- **`ζ` has hyperplane gap `2 log 2`.** -/
theorem zeta_hasHyperplaneGap_two_mul_log_two : HasHyperplaneGap (fun _ => 1) (2 * Real.log 2) :=
  fun ε hε => by
    obtain ⟨N₀, h⟩ := eventually_atomicWeilForm_le_two_log_two hε
    exact ⟨N₀, fun N hN x hx => by simpa only [one_mul] using h N hN x hx⟩

/-- **The hyperplane gap of `ζ` is exactly `2 log 2`.** -/
theorem isGreatest_zeta_hyperplaneGap :
    IsGreatest {g | HasHyperplaneGap (fun _ => 1) g} (2 * Real.log 2) :=
  ⟨zeta_hasHyperplaneGap_two_mul_log_two, fun _ hg => le_two_mul_log_two_of_hasHyperplaneGap hg⟩

/-- **Every sign gauge has gap `0`**: the Robin–Euler ceiling `log N − γ` bounds the prime form of
`ωx` by `|ωx|² = |x|²`. -/
theorem hasHyperplaneGap_zero_of_mul_self_eq_one {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) :
    HasHyperplaneGap ω 0 := fun ε hε => by
  set ε₁ := min ε (1 / 2)
  have hε₁ : 0 < ε₁ := lt_min hε (by norm_num)
  obtain ⟨N₀, h⟩ := eventually_atomicWeilForm_add_poleDefect_le hε₁
  refine ⟨N₀, fun N hN x _ => ?_⟩
  have h1 := h N hN (fun n => ω n * x n)
  have hsq : ∑ n ∈ Icc 1 N, (ω n * x n) ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 :=
    sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
  rw [hsq] at h1
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ (1 - ε₁) * poleDefect N (fun n => ω n * x n) :=
    mul_nonneg (by linarith [min_le_right ε (1 / 2)]) (poleDefect_nonneg N _)
  have hεS : ε₁ * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ ε * ∑ n ∈ Icc 1 N, x n ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hS
  linarith

/-- **The hyperplane gap of the Liouville twin is exactly `0`.** -/
theorem isGreatest_liouville_hyperplaneGap :
    IsGreatest {g | HasHyperplaneGap liouvilleSign g} 0 :=
  ⟨hasHyperplaneGap_zero_of_mul_self_eq_one liouvilleSign_mul_self, fun g hg => by
    by_contra h
    exact not_liouville_hasHyperplaneGap (not_le.mp h) hg⟩

/-- **The selective margin is `2 log 2`**: the optimal hyperplane gaps of `ζ` and of its Liouville
twin differ by `2 log 2`. -/
theorem sSup_zeta_sub_sSup_liouville_hyperplaneGap :
    sSup {g | HasHyperplaneGap (fun _ => 1) g} - sSup {g | HasHyperplaneGap liouvilleSign g} =
      2 * Real.log 2 := by
  rw [isGreatest_zeta_hyperplaneGap.csSup_eq, isGreatest_liouville_hyperplaneGap.csSup_eq, sub_zero]

/-- **The sharp selective Poincaré inequality**: for every `η > 0`, eventually in `N`,
`D_N(x) ≥ (2 log 2 − η)(|x|² − ℓ(x)²/H_N)` for every `x`. -/
theorem eventually_poleDefect_ge_offPole_sharp {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ,
      (2 * Real.log 2 - η) * (∑ n ∈ Icc 1 N, x n ^ 2 - harmonicSum N x ^ 2 / harmonicMass N) ≤
        poleDefect N x := by
  obtain ⟨N₀, h⟩ := eventually_mul_harmonicVar_le_poleDefect hη
  refine ⟨max N₀ 1, fun N hN x => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h1 := h N (le_trans (le_max_left _ _) hN) (poleProj N x)
  rwa [harmonicVar_poleGauge_eq (harmonicSum_poleProj hN1 x), sum_sq_poleProj hN1,
    poleDefect_poleProj] at h1

/-- **The sharp selective Gårding inequality.** For every admissible profile, slack `ε` and loss
`η > 0`, eventually in `N`, every atomic test at width `w ≤ δ_N/2` with nonnegative retained defect
fraction satisfies
`W(f_x) ≥ (φ₀ + c₀(2 log 2 − η))‖f_x‖² − c₀(2 log 2 − η)‖g‖² ℓ(x)²/H_N + 2A(f_x)B(f_x)`. -/
theorem eventually_weilQuad_atomicTest_ge_sharp {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < (∫ u, φ u ^ 2)) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) {η : ℝ}
    (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      w * N ≤ markovOverlapBound → 0 ≤ defectFractionRetained ε w N → ∀ x : ℕ → ℝ,
        (markovFinitePart φ ε w N + defectFractionRetained ε w N * (2 * Real.log 2 - η)) *
            (∫ u, atomicTest N x (atomDilate φ w) u ^ 2) -
          defectFractionRetained ε w N * (2 * Real.log 2 - η) * (∫ u, atomDilate φ w u ^ 2) *
            (harmonicSum N x ^ 2 / harmonicMass N) +
          2 * (∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (-(u / 2))) *
            (∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (u / 2)) ≤
        weilQuad (atomicTest N x (atomDilate φ w)) := by
  obtain ⟨N₁, hgap⟩ := eventually_poleDefect_ge_offPole_sharp hη
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_ge_defect hφ hφsupp hφ0 hK hε hε1
  refine ⟨max (max N₀ N₁) 1, fun N hN w hw0 hw hwN hc₀ x => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN : max N₀ N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hM := hN₀ N (le_trans (le_max_left _ _) hNN) w hw0 hw hwN x
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN1]
  rw [weilQuad_eq_markov_add_pole (contDiff_atomicTest hgc2 N x)
    (hasCompactSupport_atomicTest hgsupp N x)]
  rw [integral_atomicTest_sq hgc2 hgc hgsupp hw' x] at hM ⊢
  unfold markovFinitePart defectFractionRetained at *
  set A := ∫ u, atomDilate φ w u ^ 2
  set c₀ := 1 - ε - 32 * Real.exp 2 * (w * N)
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have h1 : A * c₀ * ((2 * Real.log 2 - η) *
      (∑ n ∈ Icc 1 N, x n ^ 2 - harmonicSum N x ^ 2 / harmonicMass N)) ≤
      A * c₀ * poleDefect N x :=
    mul_le_mul_of_nonneg_left (hgap N (le_trans (le_max_right _ _) hNN) x) (mul_nonneg hA hc₀)
  nlinarith

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
