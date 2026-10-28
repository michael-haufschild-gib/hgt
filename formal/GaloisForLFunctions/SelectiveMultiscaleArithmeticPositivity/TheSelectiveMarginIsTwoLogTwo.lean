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
* **`ζ` has the largest margin among sign gauges** (`isGreatest_signGauge_hyperplaneGap`): the plane
  of the two top eigenvectors of the full prime matrix meets every hyperplane
  (`eventually_forall_exists_orthogonal_atomicWeilForm_ge`), so no gauge with `ω² = 1` has a gap
  above `2 log 2`. Damped weights are excluded: the zero weight has every gap
  (`hasHyperplaneGap_zero_weight`).
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

/-! ### `ζ` has the largest margin among sign gauges -/

section SignGauges

open Filter Matrix

/-- **Every hyperplane meets the top plane.** For every `ε > 0`, eventually in `N`, every linear
condition `Σ_{n ≤ N} x_n c_n = 0` has a nonzero solution with
`P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²`: the eigenvectors of the full prime matrix at
`log N − E_1` and `log N − E_2` span a plane, and a plane meets every hyperplane. -/
theorem eventually_forall_exists_orthogonal_atomicWeilForm_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ, ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n * c n = 0 ∧
      0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
      (Real.log N - Real.eulerMascheroniConstant - 2 * Real.log 2 - ε) *
          ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set δ := min ε (Real.log 2 / 2)
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδl : δ ≤ Real.log 2 / 2 := min_le_right _ _
  filter_upwards [eventually_fullPrimeMatrix_eigenvalue_near one_pos hδ,
    eventually_fullPrimeMatrix_eigenvalue_near two_pos hδ] with N h₁ h₂ c
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  rw [ramanujanAdjunctionEnergy_one] at hi
  rw [ramanujanAdjunctionEnergy_two] at hj
  set lam := (fullPrimeMatrix_isHermitian N).eigenvalues
  set e := (fullPrimeMatrix_isHermitian N).eigenvectorBasis
  have hi' := abs_lt.mp hi
  have hj' := abs_lt.mp hj
  have hij : i ≠ j := fun h => by rw [h] at hi'; linarith
  have hli : Real.log N - Real.eulerMascheroniConstant - 2 * Real.log 2 - ε ≤ lam i := by linarith
  have hlj : Real.log N - Real.eulerMascheroniConstant - 2 * Real.log 2 - ε ≤ lam j := by linarith
  set ℓ : (PrimeHorizonIndex N → ℝ) → ℝ := fun v => ∑ k : PrimeHorizonIndex N, v k * c k
  -- the combination of the two eigenvectors killing the linear condition
  obtain ⟨a, b, hab, hℓ⟩ : ∃ a b : ℝ, 0 < a ^ 2 + b ^ 2 ∧ a * ℓ ⇑(e i) + b * ℓ ⇑(e j) = 0 := by
    by_cases h0 : ℓ ⇑(e i) = 0
    · exact ⟨1, 0, by norm_num, by rw [h0]; ring⟩
    · exact ⟨ℓ ⇑(e j), -ℓ ⇑(e i), by nlinarith [mul_self_pos.mpr h0, sq_nonneg (ℓ ⇑(e j))],
        by ring⟩
  obtain ⟨hQ, hM⟩ := quadratic_eigenvector_plane hij a b
  set v := a • ⇑(e i) + b • ⇑(e j)
  refine ⟨horizonExtend v, ?_, ?_, ?_⟩
  · rw [sum_horizonExtend v (fun n t => t * c n)]
    simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_assoc,
      ← mul_sum]
    exact hℓ
  · rw [sum_horizonExtend v (fun _ t => t ^ 2), hM]
    exact hab
  · rw [sum_horizonExtend v (fun _ t => t ^ 2), hM, atomicWeilForm_horizonExtend, hQ]
    nlinarith [mul_le_mul_of_nonneg_left hli (sq_nonneg a),
      mul_le_mul_of_nonneg_left hlj (sq_nonneg b)]

/-- **Every sign gauge has margin at most `2 log 2`**: if `ω² = 1`, every hyperplane gap of `ω` is
at most `2 log 2`. The substitution `x = ωy` turns `ζ`'s hyperplane into the hyperplane
`Σ y_n ω_n/√n = 0`, which also meets the top plane. -/
theorem le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) {g : ℝ} (hg : HasHyperplaneGap ω g) : g ≤ 2 * Real.log 2 := by
  by_contra hlt
  rw [not_le] at hlt
  set ε := (g - 2 * Real.log 2) / 4
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨N₀, hN₀⟩ := hg ε hε
  obtain ⟨N, hN, hex⟩ := ((eventually_ge_atTop N₀).and
    (eventually_forall_exists_orthogonal_atomicWeilForm_ge hε)).exists
  obtain ⟨y, hy, hmass, hge⟩ := hex (fun n => ω n / Real.sqrt n)
  have hx : ∑ n ∈ Icc 1 N, ω n * y n / Real.sqrt n = 0 := by
    rw [show ∑ n ∈ Icc 1 N, ω n * y n / Real.sqrt n =
      ∑ n ∈ Icc 1 N, y n * (ω n / Real.sqrt n) from sum_congr rfl fun n _ => by ring]
    exact hy
  have hωω : (fun n => ω n * (ω n * y n)) = y := funext fun n => by rw [← mul_assoc, hω, one_mul]
  have hsq : ∑ n ∈ Icc 1 N, (ω n * y n) ^ 2 = ∑ n ∈ Icc 1 N, y n ^ 2 :=
    sum_congr rfl fun n _ => by rw [mul_pow, sq (ω n), hω, one_mul]
  have hle := hN₀ N hN (fun n => ω n * y n) hx
  beta_reduce at hle
  rw [hωω, hsq] at hle
  have h2 := le_of_mul_le_mul_right (hge.trans hle) hmass
  simp only [ε] at h2
  linarith

/-- **`ζ` has the largest margin among sign gauges**: the largest hyperplane gap of a gauge with
`ω² = 1` is `2 log 2`, attained by `ζ`. -/
theorem isGreatest_signGauge_hyperplaneGap :
    IsGreatest {g | ∃ ω : ℕ → ℝ, (∀ n, ω n * ω n = 1) ∧ HasHyperplaneGap ω g}
      (2 * Real.log 2) :=
  ⟨⟨fun _ => 1, fun _ => one_mul 1, zeta_hasHyperplaneGap_two_mul_log_two⟩,
    fun _ ⟨_, hω, hg⟩ => le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one hω hg⟩

/-- **Damping is not selectivity**: the zero weight has every hyperplane gap, so the extremal problem
is posed among sign gauges. -/
theorem hasHyperplaneGap_zero_weight (g : ℝ) : HasHyperplaneGap (fun _ => 0) g := fun ε hε => by
  refine ⟨⌈Real.exp (Real.eulerMascheroniConstant + g)⌉₊, fun N hN x _ => ?_⟩
  have hN' : Real.exp (Real.eulerMascheroniConstant + g) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hlog := Real.log_le_log (Real.exp_pos _) hN'
  rw [Real.log_exp] at hlog
  have h0 : atomicWeilForm N (fun n => 0 * x n) = 0 := by simp [atomicWeilForm]
  rw [h0]
  exact mul_nonneg (by linarith) (sum_nonneg fun _ _ => sq_nonneg _)

end SignGauges

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
