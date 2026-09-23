import GaloisForLFunctions.RHTower.Sieve.MenonRouteTContourPolynomialFrequency
import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistRate

/-!
# Menon's polynomial-frequency twisted Mobius bound

The sharp twisted Mertens sum retains a super-polylogarithmic saving uniformly through
`|tau| <= N^(24 : ℕ)`, the frequency range used in Menon's Heath--Brown Case IIa.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

set_option maxHeartbeats 2000000 in
/-- The twisted Mertens sum with a super-polylogarithmic saving, uniformly on Menon's literal
polynomial frequency range `|tau| <= N^(24 : ℕ)`. -/
theorem exists_norm_sum_moebiusTwist_le_rate_pow_twentyFour :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℝ in atTop, ∀ tau : ℝ,
      |tau| ≤ N ^ (24 : ℕ) →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist tau n‖
        ≤ K * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) := by
  obtain ⟨A, C, C', M, delta, hC, hC', hM, hdelta, hmain⟩ :=
    exists_norm_sum_moebiusTwist_le_routeTSharp_allHeights
  refine ⟨(162 * Real.exp 7 * C + 108 * Real.exp 1 * C' * (M + 1)
      + (M + 1) * (8 + 54 * C)) / (2 * Real.pi) + 2, by positivity, ?_⟩
  filter_upwards [eventually_rate_growth,
    eventually_routeT_contour_rate_data_pow_twentyFour A delta hdelta,
    eventually_ge_atTop (1 : ℝ)] with N hgrow hdata hN1
  obtain ⟨hN0, hL8, hNbase, hF2, hF3⟩ := hgrow
  intro tau htau
  set L : ℝ := Real.log N with hLdef
  set eps : ℝ := L ^ ((1 : ℝ) / 20) with hepsdef
  have hL0 : (0 : ℝ) < L := by linarith
  have heps0 : (0 : ℝ) < eps := Real.rpow_pos_of_pos hL0 _
  set H : ℝ := N * Real.exp (-(3 * eps)) with hHdef
  set d : ℝ := 1 + 1 / L with hddef
  set S : ℝ := |tau| + N with hSdef
  have hH0 : (0 : ℝ) < H := by rw [hHdef]; positivity
  have hd1 : (1 : ℝ) < d := by
    rw [hddef]
    have : (0 : ℝ) < 1 / L := by positivity
    linarith
  have hd2 : d ≤ 2 := by
    rw [hddef]
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hSbase : routeTInverseBaseHeight ≤ S := by
    rw [hSdef]
    linarith [abs_nonneg tau]
  have hNpow : N ≤ N ^ (24 : ℕ) := by
    calc
      N = N ^ (1 : ℕ) := by ring
      _ ≤ N ^ (24 : ℕ) := pow_le_pow_right₀ hN1 (by omega)
  have hSupper : S ≤ 2 * N ^ (24 : ℕ) := by
    rw [hSdef]
    linarith
  obtain ⟨hshift, hedge, hinv⟩ := hdata S hSbase hSupper
  have hdright : d ≤ routeTContourRight A S := by
    rw [hddef, routeTContourRight]
    linarith
  have hkey := hmain N H tau N d hN0 hH0 hN1 hd1 hd2
    (by rw [← hSdef]; exact hSbase) (by rw [← hSdef]; exact hdright)
  refine le_trans hkey ?_
  exact routeTMoebiusAllHeightsSmoothBound_le_rate hC hC' hM hdelta hN0 hL8 hNbase
    hF2 hF3 hshift hedge

end

end RHTower.Sieve
