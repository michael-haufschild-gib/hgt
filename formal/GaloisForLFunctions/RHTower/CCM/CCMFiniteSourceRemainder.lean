import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanFourierTail
import GaloisForLFunctions.RHTower.CCM.CCMFiniteNeumannFormDecay

open MeasureTheory Set Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Full remainder cancellation is uniform in the admitted source amplitude.
The threshold depends on epsilon, not on the source or its budget. -/
theorem eventually_ccmFiniteNeumannVector_remainder_norm
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
      ‖p‖ ≤ V → CCMFiniteExponentialBudget (p : SoninL2) V →
      ‖ccmRestrictedWeilBoundedRemainder ⟨a, ha⟩
        (ccmFiniteNeumannVector ⟨a, ha⟩ p ⌈a⌉₊)‖ ^ 2 ≤ ε * V ^ 2 := by
  obtain ⟨M, E, hM, _, happ⟩ := eventually_ccmFiniteExponentialSource_neumann_decay
  obtain ⟨D, F, hD, _, hform⟩ := eventually_ccmFiniteExponentialSource_form_decay
  let P := ‖ccmArchimedeanRemainderScalar‖ + 46
  let C := ccmArchimedeanLogComparisonConstant
  let U := (2 * M) ^ 2
  let η := min 1 (ε / (8 * U))
  let K := 8 * P ^ 2 * C * D / ε
  have hP : 0 < P := by dsimp [P]; positivity
  have hC : 0 < C := zero_lt_one.trans_le one_le_ccmArchimedeanLogComparisonConstant
  have hU : 0 < U := by dsimp [U]; positivity
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηpay : η * (8 * U) ≤ ε :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [happ, hform,
    eventually_ccmFullLineRemainder_symbol_small K (2 * η) hK (by positivity)]
    with a haApp haForm haSymbol
  intro ha p V hpNorm hpBudget
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let u := ccmFiniteNeumannVector ap p ⌈a⌉₊
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
  let T := ‖u.1 - fourierCutoff (centralInterval (Real.exp (K * a)))
    (measurableSet_centralInterval (Real.exp (K * a))) u.1‖
  have hT : 0 ≤ T := norm_nonneg _
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have ht2 : (Real.exp a) ^ 2 = Real.exp (2 * a) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hu : Real.exp a * ‖u‖ ≤ 2 * M * V := by
    have huc : ‖u‖ * c ≤ M * V :=
      (le_div_iff₀ hc).1 (haApp ha p V hpNorm hpBudget).1
    have hlower := mul_le_mul_of_nonneg_right
      (exp_aperture_le_twice_suzukiWeilIntervalShift ap) (norm_nonneg u)
    change Real.exp a * ‖u‖ ≤ (2 * c) * ‖u‖ at hlower
    nlinarith only [hlower, huc]
  have hu2 : Real.exp (2 * a) * ‖u‖ ^ 2 ≤ U * V ^ 2 := by
    have hs := mul_self_le_mul_self
      (mul_nonneg (Real.exp_pos a).le (norm_nonneg u)) hu
    rw [← ht2]
    change (Real.exp a) ^ 2 * ‖u‖ ^ 2 ≤ (2 * M) ^ 2 * V ^ 2
    nlinarith only [hs]
  obtain ⟨g, hg, hgNorm, _⟩ := haForm ha p V hpNorm hpBudget
  have hGamma := mul_norm_sq_sub_fourierCutoff_exp_le_ccmArchimedeanFormNorm ap g (K * a)
  dsimp only at hGamma
  rw [hg] at hGamma
  have htail0 : K * a * T ^ 2 ≤ C * (D * a * V ^ 2 * Real.exp (-2 * a)) :=
    hGamma.trans (mul_le_mul_of_nonneg_left hgNorm hC.le)
  have htail : K * (Real.exp (2 * a) * T ^ 2) ≤ C * D * V ^ 2 := by
    apply le_of_mul_le_mul_left (a := a) ?_ ha
    calc
      _ = Real.exp (2 * a) * (K * a * T ^ 2) := by ring
      _ ≤ Real.exp (2 * a) * (C * (D * a * V ^ 2 * Real.exp (-2 * a))) :=
        mul_le_mul_of_nonneg_left htail0 (Real.exp_pos _).le
      _ = a * (C * D * V ^ 2) := by
        rw [show Real.exp (2 * a) * (C * (D * a * V ^ 2 * Real.exp (-2 * a))) =
          (a * (C * D * V ^ 2)) * (Real.exp (2 * a) * Real.exp (-(2 * a))) by ring,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have htailpay : 2 * P ^ 2 * (Real.exp (2 * a) * T ^ 2) ≤ (ε / 4) * V ^ 2 := by
    apply le_of_mul_le_mul_left (a := K) ?_ hK
    calc
      _ = 2 * P ^ 2 * (K * (Real.exp (2 * a) * T ^ 2)) := by ring
      _ ≤ 2 * P ^ 2 * (C * D * V ^ 2) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = K * ((ε / 4) * V ^ 2) := by dsimp [K]; field_simp [hε.ne']; ring
  have hlowpay : 2 * η ^ 2 * (Real.exp (2 * a) * ‖u‖ ^ 2) ≤ (ε / 4) * V ^ 2 := by
    calc
      _ ≤ 2 * η ^ 2 * (U * V ^ 2) := mul_le_mul_of_nonneg_left hu2 (by positivity)
      _ = (2 * η ^ 2 * U) * V ^ 2 := by ring
      _ ≤ (ε / 4) * V ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hηsq : η ^ 2 ≤ η := by nlinarith only [hη, hη1]
        have hm := mul_le_mul_of_nonneg_right hηsq hU.le
        nlinarith only [hm, hηpay]
  have hband : ∀ ξ ∈ centralInterval (Real.exp (K * a)),
      ‖ccmArchimedeanRemainderScalar + (polarPrimeStieltjesSymbol a (-2 * Real.pi * ξ) : ℂ)‖ ≤
        η * Real.exp a := by
    intro ξ hξ
    simpa only [mul_div_cancel_left₀ η (by norm_num : (2 : ℝ) ≠ 0)] using
      haSymbol ξ (abs_le.mpr hξ)
  let X := η * Real.exp a * ‖u‖
  let Y := P * Real.exp a * T
  have hnorm : ‖ccmRestrictedWeilBoundedRemainder ap u‖ ≤ X + Y :=
    norm_ccmRestrictedWeilBoundedRemainder_le_low_add_tail ap
      (Real.exp (K * a)) (η * Real.exp a) (by positivity) hband u
  have hsquare : ‖ccmRestrictedWeilBoundedRemainder ap u‖ ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    have hs := mul_self_le_mul_self (norm_nonneg _) hnorm
    nlinarith only [hs, sq_nonneg (X - Y)]
  calc
    _ ≤ 2 * X ^ 2 + 2 * Y ^ 2 := hsquare
    _ = 2 * η ^ 2 * (Real.exp (2 * a) * ‖u‖ ^ 2) +
        2 * P ^ 2 * (Real.exp (2 * a) * T ^ 2) := by dsimp [X, Y]; rw [← ht2]; ring
    _ ≤ (ε / 4) * V ^ 2 + (ε / 4) * V ^ 2 := add_le_add hlowpay htailpay
    _ ≤ ε * V ^ 2 := by nlinarith only [sq_nonneg V, hε]

end RHTower
end
