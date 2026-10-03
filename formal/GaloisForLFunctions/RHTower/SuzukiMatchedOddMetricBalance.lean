import GaloisForLFunctions.RHTower.SuzukiMatchedOddMetricTransport
import GaloisForLFunctions.RHTower.CCMFiniteNeumannRemainderQuadratic

open Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Actual matched odd energy and prescribed-shift physical mass have
vanishing difference. All source and response estimates are discharged. -/
theorem eventually_suzukiTaMatchedOdd_metric_balance
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      |boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ⟨a, ha⟩) *
          ‖suzukiTaPhysicalEmbedding ⟨a, ha⟩ (suzukiTaRawCoalescingOdd ⟨a, ha⟩ (1 / 2))‖ ^ 2 -
        suzukiTaCoalescingOddEnergy ⟨a, ha⟩ (1 / 2)| < ε := by
  obtain ⟨M, E, hM, hE, happ⟩ := eventually_ccmMatchedOddPoleSource_neumann_decay
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [happ,
    eventually_suzukiTaMatchedOdd_neumann_metric_error δ hδ,
    eventually_ccmMatchedOddNeumannVector_remainder_quadratic δ hδ,
    eventually_suzukiTaMatchedOdd_neumann_relative_error (δ ^ 2) (sq_pos_of_pos hδ),
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (2 * M * E / δ))]
    with a haApp haMetric haQuadratic haError haScale
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let w := suzukiTaRawCoalescingOdd ap (1 / 2)
  let f := ccmArchimedeanFormToAperture ap (suzukiTaToFormCLM ap w)
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  let p := ccmMatchedOddPoleSource ap
  let r := p - ccmShiftedBoundedWeil ap u
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
  let O := suzukiTaCoalescingOddEnergy ap (1 / 2)
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
  have hut : t * ‖u‖ ≤ 2 * M := by
    apply le_of_mul_le_mul_left (a := t) ?_ ht
    change Real.exp a * ‖u‖ ≤ _ at hulow
    rw [← ht2] at hulow
    nlinarith only [hu, hulow]
  have hrt : t * ‖r‖ ≤ E := by
    calc
      _ ≤ t * (E * Real.exp (-7 * a / 2)) :=
        mul_le_mul_of_nonneg_left (haApp ha).2 ht.le
      _ ≤ t * (E * Real.exp (-a / 2)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hE.le) ht.le
      _ = E := by
        rw [show t * (E * Real.exp (-a / 2)) = E * (Real.exp (a / 2) * Real.exp (-a / 2)) by
          dsimp [t]; ring,
          ← Real.exp_add, show a / 2 + -a / 2 = 0 by ring, Real.exp_zero, mul_one]
  have hru : ‖r‖ * ‖u‖ ≤ δ := by
    apply le_of_mul_le_mul_left (a := Real.exp a) ?_ (Real.exp_pos _)
    calc
      _ = (t * ‖r‖) * (t * ‖u‖) := by rw [← ht2]; ring
      _ ≤ E * (2 * M) := mul_le_mul hrt hut (by positivity) hE.le
      _ ≤ Real.exp a * δ := by
        have hs := (div_le_iff₀ hδ).1 haScale
        nlinarith only [hs]
  have herror : t * ‖f - u‖ < δ := by
    have hs : t ^ 2 * ‖f - u‖ ^ 2 < δ ^ 2 := by rw [ht2]; exact haError ha
    nlinarith only [hs, mul_nonneg ht.le (norm_nonneg (f - u)), hδ]
  have hp : |(inner ℂ p (f - u)).re| < δ := by
    calc
      _ ≤ ‖inner ℂ p (f - u)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖p‖ * ‖f - u‖ := norm_inner_le_norm p (f - u)
      _ ≤ t * ‖f - u‖ := mul_le_mul_of_nonneg_right
        (norm_ccmMatchedOddPoleSource_le ap) (norm_nonneg _)
      _ < δ := herror
  have hr : |(inner ℂ r u).re| ≤ δ := by
    calc
      _ ≤ ‖inner ℂ r u‖ := Complex.abs_re_le_norm _
      _ ≤ ‖r‖ * ‖u‖ := norm_inner_le_norm r u
      _ ≤ δ := hru
  have hsource : (inner ℂ p f).re = O := suzukiTaMatchedOdd_source_energy ap
  have hrEq : (inner ℂ r u).re =
      (inner ℂ p u).re - (c * ‖u‖ ^ 2 + (inner ℂ (ccmRestrictedWeilBoundedRemainder ap u) u).re) := by
    dsimp only [r]
    rw [inner_sub_left, Complex.sub_re, ccmShiftedBoundedWeil_re_inner]
  have he : O - c * ‖u‖ ^ 2 =
      (inner ℂ p (f - u)).re + (inner ℂ r u).re +
        (inner ℂ (ccmRestrictedWeilBoundedRemainder ap u) u).re := by
    rw [inner_sub_right, Complex.sub_re]
    linarith only [hsource, hrEq]
  have henergy : |O - c * ‖u‖ ^ 2| < 3 * δ := by
    rw [he]
    have htriangle := (abs_add_le
      ((inner ℂ p (f - u)).re + (inner ℂ r u).re)
      ((inner ℂ (ccmRestrictedWeilBoundedRemainder ap u) u).re)).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    have hq := haQuadratic ha
    change |(inner ℂ (ccmRestrictedWeilBoundedRemainder ap u) u).re| < δ at hq
    linarith only [htriangle, hp, hr, hq]
  have hphys : ‖suzukiTaPhysicalEmbedding ap w‖ = ‖f‖ :=
    (suzukiApertureL2Equiv ap).symm.norm_map f
  change |c * ‖suzukiTaPhysicalEmbedding ap w‖ ^ 2 - O| < ε
  rw [hphys]
  calc
    _ = |c * (‖f‖ ^ 2 - ‖u‖ ^ 2) + -(O - c * ‖u‖ ^ 2)| := congrArg abs (by ring)
    _ ≤ |c * (‖f‖ ^ 2 - ‖u‖ ^ 2)| + |-(O - c * ‖u‖ ^ 2)| := abs_add_le _ _
    _ = c * |‖f‖ ^ 2 - ‖u‖ ^ 2| + |O - c * ‖u‖ ^ 2| := by
      rw [abs_mul, abs_of_pos hc, abs_neg]
    _ < δ + 3 * δ := add_lt_add (haMetric ha) henergy
    _ < ε := by dsimp [δ]; linarith

/-- Unconditional metric balance for the actual odd pole response. -/
theorem tendsto_suzukiTaMatchedOdd_metric_balance :
    Tendsto (fun a : SuzukiPositiveAperture =>
      |boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
          ‖suzukiTaPhysicalEmbedding a (suzukiTaRawCoalescingOdd a (1 / 2))‖ ^ 2 -
        suzukiTaCoalescingOddEnergy a (1 / 2)|)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le (abs_nonneg _)
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_suzukiTaMatchedOdd_metric_balance ε hε)]
      with a ha
    exact ha a.2

end RHTower
end
