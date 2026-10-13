import GaloisForLFunctions.RHTower.WeilLagPowerGapSampling
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega
import GaloisForLFunctions.HTGeometry.BohrBochnerEquivalence

/-!
# Persistent oscillation of the integer lags

Let `a_n = Φ(log n)` be the integer lags and `a_1 = 2 + γ − log 4π` the sharp ceiling.

**Theorem** (`exists_persistent_integerLag_gt_sub`). For every `ε > 0` and `δ > 0` there are
arbitrarily large `n` with `a_k > a_1 − ε` for every `k ≥ 2` in `[n − n^{1 − δ}, n]`.

**Theorem** (`exists_persistent_integerLag_lt_neg`). There is `η > 0` such that for every `δ > 0`
there are arbitrarily large `n` with `a_k < −η` for every `k ≥ 2` in `[n − n^{1 − δ}, n]`.

Both are unconditional, with a case split on RH.
* Under RH, `Φ` is Bohr almost periodic, hence uniformly continuous
  (`uniformContinuous_weilLagFunctionReal_of_riemannHypothesis`). A power window has
  logarithmic length `O(n^{−δ})` (`exists_log_window_of_power_window`). So one near-extremal value,
  `a_n > a_1 − ε/2` (`frequently_integerLag_gt`) or `a_n ≤ −η`
  (`frequently_integerLag_le_neg_of_riemannHypothesis`), persists over the whole window.
* Without RH, power-gap sampling gives persistent excursions above and below every level
  (`exists_persistent_integerLag_gt_of_not_riemannHypothesis`,
  `exists_persistent_integerLag_lt_of_not_riemannHypothesis`).

The square-root Lipschitz law of `WeilLagTwoSidedMeshSampling` alone gives persistence only over
windows of length `O(√n)`.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- Under RH the real lag function is uniformly continuous. -/
theorem uniformContinuous_weilLagFunctionReal_of_riemannHypothesis (h : RiemannHypothesis) :
    UniformContinuous weilLagFunctionReal := by
  have hU := GaloisForLFunctions.uniformContinuous_of_isBohrAlmostPeriodic
    continuous_weilLagFunction_unconditional (isBohrAlmostPeriodic_weilLagFunction h)
  rw [Metric.uniformContinuous_iff] at hU ⊢
  intro ε hε
  obtain ⟨η, hη, hη'⟩ := hU ε hε
  refine ⟨η, hη, fun {a b} hab => ?_⟩
  have h1 := hη' hab
  rw [dist_eq_norm, weilLagFunction_eq_ofReal, weilLagFunction_eq_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real] at h1
  rwa [dist_eq_norm]

/-- A power window `[n − n^{1 − δ}, n]` has logarithmic length below any `η > 0` for large `n`. -/
theorem exists_log_window_of_power_window {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ, 2 ≤ k → k ≤ n → (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) →
      |Real.log k - Real.log n| < η := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds
    (show (0 : ℝ) < min (η / 2) (1 / 2) by positivity)))
  refine ⟨max N₁ 1, fun n hn k hk2 hkn hgap => ?_⟩
  have hsmall := hN₁ n (le_trans (le_max_left _ _) hn)
  have hs1 : (n : ℝ) ^ (-δ) < η / 2 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hs2 : (n : ℝ) ^ (-δ) < 1 / 2 := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hk0 hkn'
  have hsplit : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
    rw [show (1 : ℝ) - δ = -δ + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  rw [hsplit] at hgap
  have hpos : 0 ≤ (n : ℝ) ^ (-δ) := by positivity
  have hk2n : (n : ℝ) ≤ 2 * k := by nlinarith
  have hlogle : Real.log n - Real.log k ≤ ((n : ℝ) - k) / k := by
    rw [← Real.log_div hn0.ne' hk0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / k by positivity)
    have e : (n : ℝ) / k - 1 = ((n : ℝ) - k) / k := by field_simp
    linarith
  have hratio : ((n : ℝ) - k) / k ≤ 2 * (n : ℝ) ^ (-δ) := by
    rw [div_le_iff₀ hk0]; nlinarith
  have hlog0 : 0 ≤ Real.log n - Real.log k := by
    have := Real.log_le_log hk0 hkn'; linarith
  rw [abs_sub_comm, abs_of_nonneg hlog0]
  linarith

/-- **Persistent near-ceiling values, unconditionally.** For every `ε > 0` and `δ > 0` there are
arbitrarily large `n` with `a_k > a_1 − ε` for every `k ≥ 2` in `[n − n^{1 − δ}, n]`. -/
theorem exists_persistent_integerLag_gt_sub {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ ∀ k : ℕ, 2 ≤ k → k ≤ n → (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) →
      poleSharpConstant - ε < integerLag k := by
  by_cases h : RiemannHypothesis
  · obtain ⟨η, hη, hU⟩ := Metric.uniformContinuous_iff.mp
      (uniformContinuous_weilLagFunctionReal_of_riemannHypothesis h) (ε / 2) (by positivity)
    obtain ⟨N₁, hN₁⟩ := exists_log_window_of_power_window hδ hη
    obtain ⟨n, hn, hgt⟩ := Filter.frequently_atTop.mp
      (frequently_integerLag_gt (ε / 2) (by positivity)) (max N₀ N₁)
    refine ⟨n, le_trans (le_max_left _ _) hn, fun k hk2 hkn hgap => ?_⟩
    have hlog := hN₁ n (le_trans (le_max_right _ _) hn) k hk2 hkn hgap
    have hd := hU (a := Real.log k) (b := Real.log n) (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).1
    unfold integerLag at hgt ⊢
    linarith
  · exact exists_persistent_integerLag_gt_of_not_riemannHypothesis h hδ _ N₀

/-- **Persistent negative values, unconditionally.** There is `η > 0` such that for every `δ > 0`
there are arbitrarily large `n` with `a_k < −η` for every `k ≥ 2` in `[n − n^{1 − δ}, n]`. -/
theorem exists_persistent_integerLag_lt_neg :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n → (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) → integerLag k < -η := by
  by_cases h : RiemannHypothesis
  · obtain ⟨η, hη, hfreq⟩ := frequently_integerLag_le_neg_of_riemannHypothesis h
    refine ⟨η / 2, by positivity, fun δ hδ N₀ => ?_⟩
    obtain ⟨r, hr, hU⟩ := Metric.uniformContinuous_iff.mp
      (uniformContinuous_weilLagFunctionReal_of_riemannHypothesis h) (η / 2) (by positivity)
    obtain ⟨N₁, hN₁⟩ := exists_log_window_of_power_window hδ hr
    obtain ⟨n, hn, hle⟩ := Filter.frequently_atTop.mp hfreq (max N₀ N₁)
    refine ⟨n, le_trans (le_max_left _ _) hn, fun k hk2 hkn hgap => ?_⟩
    have hlog := hN₁ n (le_trans (le_max_right _ _) hn) k hk2 hkn hgap
    have hd := hU (a := Real.log k) (b := Real.log n) (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).2
    unfold integerLag at hle ⊢
    linarith
  · exact ⟨1, one_pos, fun δ hδ N₀ =>
      exists_persistent_integerLag_lt_of_not_riemannHypothesis h hδ (-1) N₀⟩

end

end RHTower
