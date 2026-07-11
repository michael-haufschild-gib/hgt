/-
# Integer quantization of the modulus-slope field

The enclosed divisor mass is an integer and the slope field is bracketed by it, so the field is
quantized: exact vanishing demands relax to open inequalities, and single samples carry whole-box
information.

* `xi_zeroFree_closedBall_of_modulusSlope_lt_one` — a slope sample below `1` certifies that the
  inner closed ball is ξ-zero-free: an integer in `[0, 1)` is `0`.
* `rh_iff_forall_rightHalf_modulusSlope_lt_one` — RH holds iff the slope field stays strictly
  below `1` on every right-half-contained radius pair.  The flatness criterion's equality is
  never needed; the analytic target is an inequality with a full unit of room.
* `rhLadder_iff_forall_rightHalf_dvd_ballOrderSum` — rung `k` of the multiplicity ladder holds
  iff `2^k` divides the enclosed divisor mass of every right-half-contained closed ball: the
  per-zero divisibility aggregates to box counts and is recovered from them at isolating radii.
* `rhLadder_iff_forall_annulus_modulusSlope_dvd` — the `|ξ|`-readable form: rung `k` holds iff at
  every zero-free annulus over a right-half-contained ball the two-circle slope is an integer
  divisible by `2^k`.  One boundary-modulus reading certifies the rung for the whole enclosed
  box; no germ radii, no per-zero localization, no phase.
* `modulusSlope_eq_zero_of_one_le_sub_re` — past the wall `Re > 1` the field is unconditionally
  flat: the region where flatness is open is exactly the critical strip.
-/
import GaloisForLFunctions.RHTower.ModulusSlopeField
import GaloisForLFunctions.RHTower.RHLadderTheory

open Complex Metric

namespace RHTower

noncomputable section

/-- A ξ-zero in the closed ball forces the enclosed divisor mass to be at least one. -/
theorem one_le_xiBallOrderSum_of_zero {ρ z : ℂ} {r : ℝ} (hz : z ∈ closedBall ρ r)
    (hzero : xi z = 0) : 1 ≤ xiBallOrderSum ρ r := by
  have hT := (MeromorphicOn.divisor xi (closedBall ρ r)).finiteSupport
    (isCompact_closedBall ρ r)
  have hDz : MeromorphicOn.divisor xi (closedBall ρ r) z =
      ((analyticOrderAt xi z).toNat : ℤ) := xi_divisor_closedBall_eq_order_toNat hz
  have horder : (analyticOrderAt xi z).toNat ≠ 0 := fun h0 =>
    ((xi_orderToNat_eq_zero_iff z).mp h0) hzero
  have hzT : z ∈ hT.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support, hDz]
    exact_mod_cast horder
  have hsum : xiBallOrderSum ρ r =
      ∑ u ∈ hT.toFinset, MeromorphicOn.divisor xi (closedBall ρ r) u := by
    rw [xiBallOrderSum]
    exact finsum_eq_sum_of_support_subset _ (by rw [Set.Finite.coe_toFinset])
  have hnn : ∀ u ∈ hT.toFinset, 0 ≤ MeromorphicOn.divisor xi (closedBall ρ r) u := by
    intro u hu
    have hudom : u ∈ closedBall ρ r :=
      (MeromorphicOn.divisor xi (closedBall ρ r)).supportWithinDomain
        (by rwa [Set.Finite.mem_toFinset] at hu)
    rw [xi_divisor_closedBall_eq_order_toNat hudom]
    positivity
  rw [hsum]
  calc (1 : ℤ) ≤ MeromorphicOn.divisor xi (closedBall ρ r) z := by
        rw [hDz]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder
    _ ≤ ∑ u ∈ hT.toFinset, MeromorphicOn.divisor xi (closedBall ρ r) u :=
        Finset.single_le_sum hnn hzT

/-- **Sub-unit slope certifies a zero-free ball.**  The enclosed divisor mass is a nonnegative
integer below the slope; a slope sample below `1` pins it to `0`. -/
theorem xi_zeroFree_closedBall_of_modulusSlope_lt_one {ρ : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hlt : modulusSlope ρ r₁ r₂ < 1) :
    ∀ z ∈ closedBall ρ r₁, xi z ≠ 0 := by
  intro z hz hzero
  have h1 : (1 : ℤ) ≤ xiBallOrderSum ρ r₁ := one_le_xiBallOrderSum_of_zero hz hzero
  have h1R : (1 : ℝ) ≤ ((xiBallOrderSum ρ r₁ : ℤ) : ℝ) := by exact_mod_cast h1
  have hbr := ballOrderSum_le_modulusSlope ρ hr₁ h₁₂
  linarith

/-- **RH as an open inequality.**  RH holds iff the slope field stays strictly below `1` over
every right-half-contained radius pair: quantization converts the exact flatness criterion into
a strict sub-unit bound with a full unit of room. -/
theorem rh_iff_forall_rightHalf_modulusSlope_lt_one :
    RiemannHypothesis ↔
      ∀ (ρ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → 1 / 2 ≤ ρ.re - r₂ →
        modulusSlope ρ r₁ r₂ < 1 := by
  constructor
  · intro hRH ρ r₁ r₂ hr₁ h₁₂ hhalf
    rw [rh_iff_forall_rightHalf_modulusSlope_eq_zero] at hRH
    rw [hRH ρ r₁ r₂ hr₁ h₁₂ hhalf]
    norm_num
  · intro hlt
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hρ hzero
    have hρre : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
    have hs := hlt ρ ((ρ.re - 1 / 2) / 2) (ρ.re - 1 / 2)
      (by linarith) (by linarith) (by linarith)
    exact xi_zeroFree_closedBall_of_modulusSlope_lt_one (by linarith) (by linarith) hs ρ
      (mem_closedBall_self (by linarith)) hzero

/-- Around any point there is a radius inside which the center is the only possible ξ-zero. -/
theorem xi_exists_isolating_radius (ρ : ℂ) :
    ∃ R₀ > 0, ∀ z ∈ ball ρ R₀, z ≠ ρ → xi z ≠ 0 := by
  obtain ⟨R₀, hR₀, h, _hhan, hh0, hfact⟩ := xi_peel_ball ρ
  refine ⟨R₀, hR₀, fun z hz hne => ?_⟩
  rw [hfact z hz]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hne)) (hh0 z hz)

/-- At an isolating radius the enclosed divisor mass is exactly the central vanishing order. -/
theorem xiBallOrderSum_eq_order_of_isolated {ρ : ℂ} {r : ℝ} (hr : 0 < r)
    (hiso : ∀ z ∈ closedBall ρ r, z ≠ ρ → xi z ≠ 0) :
    xiBallOrderSum ρ r = ((analyticOrderAt xi ρ).toNat : ℤ) := by
  have hsingle : ∑ᶠ u, MeromorphicOn.divisor xi (closedBall ρ r) u =
      MeromorphicOn.divisor xi (closedBall ρ r) ρ := by
    apply finsum_eq_single
    intro x hx
    by_cases hxmem : x ∈ closedBall ρ r
    · rw [xi_divisor_closedBall_eq_order_toNat hxmem,
        (xi_orderToNat_eq_zero_iff x).mpr (hiso x hxmem hx)]
      simp
    · exact xi_divisor_closedBall_eq_zero_of_notMem hxmem
  rw [xiBallOrderSum, hsingle,
    xi_divisor_closedBall_eq_order_toNat (mem_closedBall_self hr.le)]

/-- **Rung `k` as a box-count congruence.**  Level `k` of the RH multiplicity ladder holds iff
`2^k` divides the enclosed divisor mass of every right-half-contained closed ball.  Per-zero
divisibility aggregates to box counts; isolating radii recover it. -/
theorem rhLadder_iff_forall_rightHalf_dvd_ballOrderSum (k : ℕ) :
    RHLadder k ↔
      ∀ (ρ : ℂ) (r : ℝ), 0 < r → 1 / 2 < ρ.re - r → (2 ^ k : ℤ) ∣ xiBallOrderSum ρ r := by
  rw [rhLadder_iff_toNat_dvd]
  constructor
  · intro hlad ρ r _hr hhalf
    have hT := (MeromorphicOn.divisor xi (closedBall ρ r)).finiteSupport
      (isCompact_closedBall ρ r)
    have hsum : xiBallOrderSum ρ r =
        ∑ u ∈ hT.toFinset, MeromorphicOn.divisor xi (closedBall ρ r) u := by
      rw [xiBallOrderSum]
      exact finsum_eq_sum_of_support_subset _ (by rw [Set.Finite.coe_toFinset])
    rw [hsum]
    refine Finset.dvd_sum fun u hu => ?_
    have hudom : u ∈ closedBall ρ r :=
      (MeromorphicOn.divisor xi (closedBall ρ r)).supportWithinDomain
        (by rwa [Set.Finite.mem_toFinset] at hu)
    have hun : ‖u - ρ‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hudom
    have humem : u ∈ rightHalf := by
      rw [mem_rightHalf]
      have hre : |(u - ρ).re| ≤ ‖u - ρ‖ := Complex.abs_re_le_norm _
      have : ρ.re - u.re ≤ ‖u - ρ‖ := by
        simp only [Complex.sub_re] at hre
        linarith [abs_le.mp hre]
      linarith
    have huzero : xi u = 0 := by
      by_contra hne
      have hD0 : MeromorphicOn.divisor xi (closedBall ρ r) u = 0 := by
        rw [xi_divisor_closedBall_eq_order_toNat hudom,
          (xi_orderToNat_eq_zero_iff u).mpr hne]
        simp
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
      exact hu hD0
    rw [xi_divisor_closedBall_eq_order_toNat hudom]
    exact_mod_cast hlad u humem huzero
  · intro hdvd ρ hρ hzero
    obtain ⟨R₀, hR₀, hiso⟩ := xi_exists_isolating_radius ρ
    have hρre : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
    have hrpos : 0 < min (R₀ / 2) ((ρ.re - 1 / 2) / 2) :=
      lt_min (by linarith) (by linarith)
    have hriso : ∀ z ∈ closedBall ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2)), z ≠ ρ → xi z ≠ 0 := by
      intro z hz hne
      refine hiso z (mem_ball.mpr ?_) hne
      have h1 : dist z ρ ≤ min (R₀ / 2) ((ρ.re - 1 / 2) / 2) := mem_closedBall.mp hz
      have h2 : min (R₀ / 2) ((ρ.re - 1 / 2) / 2) ≤ R₀ / 2 := min_le_left _ _
      linarith
    have hhalf : 1 / 2 < ρ.re - min (R₀ / 2) ((ρ.re - 1 / 2) / 2) := by
      have : min (R₀ / 2) ((ρ.re - 1 / 2) / 2) ≤ (ρ.re - 1 / 2) / 2 := min_le_right _ _
      linarith
    have hd := hdvd ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2)) hrpos hhalf
    rw [xiBallOrderSum_eq_order_of_isolated hrpos hriso] at hd
    exact_mod_cast hd

/-- **The rung read from `|ξ|` at one annulus.**  Level `k` holds iff at every zero-free annulus
over a right-half-contained ball the two-circle modulus slope is an integer divisible by `2^k`:
a single boundary-modulus reading certifies the rung for the whole enclosed box. -/
theorem rhLadder_iff_forall_annulus_modulusSlope_dvd (k : ℕ) :
    RHLadder k ↔
      ∀ (ρ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → 1 / 2 < ρ.re - r₂ →
        (∀ z : ℂ, r₁ < ‖z - ρ‖ → ‖z - ρ‖ ≤ r₂ → xi z ≠ 0) →
        ∃ n : ℤ, modulusSlope ρ r₁ r₂ = (n : ℝ) ∧ (2 ^ k : ℤ) ∣ n := by
  constructor
  · intro hlad ρ r₁ r₂ hr₁ h₁₂ hhalf hfree
    refine ⟨xiBallOrderSum ρ r₁,
      modulusSlope_eq_ballOrderSum_of_annulus_zeroFree ρ hr₁ h₁₂ hfree, ?_⟩
    exact (rhLadder_iff_forall_rightHalf_dvd_ballOrderSum k).mp hlad ρ r₁ hr₁ (by linarith)
  · intro hann
    rw [rhLadder_iff_toNat_dvd]
    intro ρ hρ hzero
    obtain ⟨R₀, hR₀, hiso⟩ := xi_exists_isolating_radius ρ
    have hρre : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
    have hr₂pos : 0 < min (R₀ / 2) ((ρ.re - 1 / 2) / 2) :=
      lt_min (by linarith) (by linarith)
    have hr₂R₀ : min (R₀ / 2) ((ρ.re - 1 / 2) / 2) < R₀ :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hhalf : 1 / 2 < ρ.re - min (R₀ / 2) ((ρ.re - 1 / 2) / 2) := by
      have : min (R₀ / 2) ((ρ.re - 1 / 2) / 2) ≤ (ρ.re - 1 / 2) / 2 := min_le_right _ _
      linarith
    have hfree : ∀ z : ℂ, min (R₀ / 2) ((ρ.re - 1 / 2) / 2) / 2 < ‖z - ρ‖ →
        ‖z - ρ‖ ≤ min (R₀ / 2) ((ρ.re - 1 / 2) / 2) → xi z ≠ 0 := by
      intro z hlt hle
      refine hiso z (mem_ball.mpr (by rw [dist_eq_norm]; linarith)) ?_
      intro hzρ
      rw [hzρ, sub_self, norm_zero] at hlt
      linarith
    obtain ⟨n, hslope, hdvd⟩ := hann ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2) / 2)
      (min (R₀ / 2) ((ρ.re - 1 / 2) / 2)) (by linarith) (by linarith) hhalf hfree
    have hriso : ∀ z ∈ closedBall ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2) / 2),
        z ≠ ρ → xi z ≠ 0 := by
      intro z hz hne
      refine hiso z (mem_ball.mpr ?_) hne
      have := mem_closedBall.mp hz
      linarith
    have hread : modulusSlope ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2) / 2)
        (min (R₀ / 2) ((ρ.re - 1 / 2) / 2)) =
        ((xiBallOrderSum ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2) / 2) : ℤ) : ℝ) :=
      modulusSlope_eq_ballOrderSum_of_annulus_zeroFree ρ (by linarith) (by linarith) hfree
    have hn : n = xiBallOrderSum ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2) / 2) := by
      have hcast : ((n : ℤ) : ℝ) =
          ((xiBallOrderSum ρ (min (R₀ / 2) ((ρ.re - 1 / 2) / 2) / 2) : ℤ) : ℝ) := by
        rw [← hslope, hread]
      exact_mod_cast hcast
    rw [hn, xiBallOrderSum_eq_order_of_isolated (by linarith) hriso] at hdvd
    exact_mod_cast hdvd

/-- **Past the wall the field is unconditionally flat.**  Any slope sample over a ball beyond
`Re = 1` vanishes, with no zero-location input: the open region of the flatness criterion is
exactly the critical strip. -/
theorem modulusSlope_eq_zero_of_one_le_sub_re {ρ : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hwall : 1 ≤ ρ.re - r₂) :
    modulusSlope ρ r₁ r₂ = 0 := by
  rw [modulusSlope_eq_zero_iff_ball_zeroFree ρ hr₁ h₁₂]
  intro z hz
  refine xi_ne_zero_of_one_lt_re ?_
  have hzn : ‖z - ρ‖ < r₂ := by rwa [mem_ball, dist_eq_norm] at hz
  have hre : |(z - ρ).re| ≤ ‖z - ρ‖ := Complex.abs_re_le_norm _
  have : ρ.re - z.re ≤ ‖z - ρ‖ := by
    simp only [Complex.sub_re] at hre
    linarith [abs_le.mp hre]
  linarith

end

end RHTower
