import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanFourierTail
import GaloisForLFunctions.RHTower.CCM.CCMFiniteNeumannFormDecay

open MeasureTheory Set Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem neumann_half_scaled_norm :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Real.exp (a / 2) * ‖ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊‖ ≤ M := by
  obtain ⟨M, E, hM, _, happ⟩ := eventually_ccmMatchedOddPoleSource_neumann_decay
  refine ⟨2 * M, by positivity, ?_⟩
  filter_upwards [happ] with a haApp
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
  let t := Real.exp (a / 2)
  have ht : 0 < t := Real.exp_pos _
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have ht2 : t ^ 2 = Real.exp a := by
    dsimp [t]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hu : ‖u‖ * c ≤ M * t := (le_div_iff₀ hc).1 (haApp ha).1
  have hulow := mul_le_mul_of_nonneg_right
    (exp_aperture_le_twice_suzukiWeilIntervalShift ap) (norm_nonneg u)
  apply le_of_mul_le_mul_left (a := t) ?_ ht
  change Real.exp a * ‖u‖ ≤ _ at hulow
  rw [← ht2] at hulow
  change t * (t * ‖u‖) ≤ t * (2 * M)
  nlinarith only [hu, hulow]

/-- The full actual remainder applied to the literal finite odd source
vanishes after the natural norm rescaling. -/
theorem eventually_ccmMatchedOddNeumannVector_scaled_remainder_norm
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Real.exp (-a) * ‖ccmRestrictedWeilBoundedRemainder ⟨a, ha⟩
        (ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊)‖ ^ 2 < ε := by
  obtain ⟨M, hM, hnormU⟩ := neumann_half_scaled_norm
  obtain ⟨D, F, hD, _, hform⟩ := eventually_ccmMatchedOddNeumannVector_form_decay
  let P := ‖ccmArchimedeanRemainderScalar‖ + 46
  let C := ccmArchimedeanLogComparisonConstant
  let U := M ^ 2
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
  filter_upwards [hnormU, hform,
    eventually_ccmFullLineRemainder_symbol_small K (2 * η) hK (by positivity)]
    with a haU haForm haSymbol
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  let T := ‖u.1 - fourierCutoff (centralInterval (Real.exp (K * a)))
    (measurableSet_centralInterval (Real.exp (K * a))) u.1‖
  have hT : 0 ≤ T := norm_nonneg _
  have ht2 : (Real.exp (a / 2)) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hu2 : Real.exp a * ‖u‖ ^ 2 ≤ U := by
    have hs := mul_self_le_mul_self
      (mul_nonneg (Real.exp_pos (a / 2)).le (norm_nonneg u)) (haU ha)
    change (Real.exp (a / 2) * ‖u‖) * (Real.exp (a / 2) * ‖u‖) ≤ M * M at hs
    rw [← ht2]
    change (Real.exp (a / 2)) ^ 2 * ‖u‖ ^ 2 ≤ M ^ 2
    nlinarith only [hs]
  obtain ⟨g, hg, hgNorm, _⟩ := haForm ha
  have hGamma := mul_norm_sq_sub_fourierCutoff_exp_le_ccmArchimedeanFormNorm ap g (K * a)
  dsimp only at hGamma
  rw [hg] at hGamma
  have htail0 : K * a * T ^ 2 ≤ C * (D * a * Real.exp (-a)) :=
    hGamma.trans (mul_le_mul_of_nonneg_left hgNorm hC.le)
  have htail : K * (Real.exp a * T ^ 2) ≤ C * D := by
    apply le_of_mul_le_mul_left (a := a) ?_ ha
    calc
      _ = Real.exp a * (K * a * T ^ 2) := by ring
      _ ≤ Real.exp a * (C * (D * a * Real.exp (-a))) :=
        mul_le_mul_of_nonneg_left htail0 (Real.exp_pos _).le
      _ = a * (C * D) := by
        rw [show Real.exp a * (C * (D * a * Real.exp (-a))) =
          (a * (C * D)) * (Real.exp a * Real.exp (-a)) by ring,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have htailpay : 2 * P ^ 2 * (Real.exp a * T ^ 2) ≤ ε / 4 := by
    apply le_of_mul_le_mul_left (a := K) ?_ hK
    calc
      _ = 2 * P ^ 2 * (K * (Real.exp a * T ^ 2)) := by ring
      _ ≤ 2 * P ^ 2 * (C * D) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = K * (ε / 4) := by dsimp [K]; field_simp [hε.ne']; ring
  have hlowpay : 2 * η ^ 2 * (Real.exp a * ‖u‖ ^ 2) ≤ ε / 4 := by
    calc
      _ ≤ 2 * η ^ 2 * U := mul_le_mul_of_nonneg_left hu2 (by positivity)
      _ ≤ 2 * η * U := mul_le_mul_of_nonneg_right (by nlinarith only [hη, hη1]) hU.le
      _ ≤ ε / 4 := by nlinarith only [hηpay]
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
  have hexp : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ ≤ Real.exp (-a) * (2 * X ^ 2 + 2 * Y ^ 2) :=
      mul_le_mul_of_nonneg_left hsquare (Real.exp_pos _).le
    _ = (Real.exp (-a) * Real.exp a) *
        (2 * η ^ 2 * (Real.exp a * ‖u‖ ^ 2) + 2 * P ^ 2 * (Real.exp a * T ^ 2)) := by
      dsimp [X, Y]
      ring
    _ = 2 * η ^ 2 * (Real.exp a * ‖u‖ ^ 2) + 2 * P ^ 2 * (Real.exp a * T ^ 2) := by
      rw [hexp, one_mul]
    _ ≤ ε / 4 + ε / 4 := add_le_add hlowpay htailpay
    _ < ε := by linarith

theorem tendsto_ccmMatchedOddNeumannVector_scaled_remainder_norm :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-a.1) *
      ‖ccmRestrictedWeilBoundedRemainder a (ccmMatchedOddNeumannVector a ⌈a.1⌉₊)‖ ^ 2)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually
      (eventually_ccmMatchedOddNeumannVector_scaled_remainder_norm ε hε)] with a ha
    exact ha a.2

/-- Complete prime--polar quadratic cancellation follows from the stronger
actual vector estimate and the bounded half-scaled source norm. -/
theorem eventually_ccmMatchedOddNeumannVector_remainder_quadratic
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      let u := ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊
      |(inner ℂ (ccmRestrictedWeilBoundedRemainder ⟨a, ha⟩ u) u).re| < ε := by
  obtain ⟨M, hM, hU⟩ := neumann_half_scaled_norm
  filter_upwards [hU, eventually_ccmMatchedOddNeumannVector_scaled_remainder_norm
    ((ε / M) ^ 2) (by positivity)] with a haU haB
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  let X := Real.exp (-a / 2) * ‖ccmRestrictedWeilBoundedRemainder ap u‖
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have he : (Real.exp (-a / 2)) ^ 2 = Real.exp (-a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hXsq : X ^ 2 < (ε / M) ^ 2 := by
    dsimp [X]
    rw [mul_pow, he]
    exact haB ha
  have hX : X < ε / M := by nlinarith only [hXsq, hX0, div_pos hε hM]
  have hexp : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by
    rw [← Real.exp_add, show -a / 2 + a / 2 = 0 by ring, Real.exp_zero]
  calc
    _ ≤ ‖inner ℂ (ccmRestrictedWeilBoundedRemainder ap u) u‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ccmRestrictedWeilBoundedRemainder ap u‖ * ‖u‖ :=
      norm_inner_le_norm (ccmRestrictedWeilBoundedRemainder ap u) u
    _ = X * (Real.exp (a / 2) * ‖u‖) := by
      change ‖ccmRestrictedWeilBoundedRemainder ap u‖ * ‖u‖ =
        (Real.exp (-a / 2) * ‖ccmRestrictedWeilBoundedRemainder ap u‖) *
          (Real.exp (a / 2) * ‖u‖)
      calc
        _ = (Real.exp (-a / 2) * Real.exp (a / 2)) *
            (‖ccmRestrictedWeilBoundedRemainder ap u‖ * ‖u‖) := by rw [hexp, one_mul]
        _ = _ := by ring
    _ ≤ X * M := mul_le_mul_of_nonneg_left (haU ha) hX0
    _ < ε := (lt_div_iff₀ hM).1 hX

theorem tendsto_ccmMatchedOddNeumannVector_remainder_quadratic :
    Tendsto (fun a : SuzukiPositiveAperture =>
      let u := ccmMatchedOddNeumannVector a ⌈a.1⌉₊
      |(inner ℂ (ccmRestrictedWeilBoundedRemainder a u) u).re|)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le (abs_nonneg _)
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_ccmMatchedOddNeumannVector_remainder_quadratic ε hε)]
      with a ha
    exact ha a.2

end RHTower
end
