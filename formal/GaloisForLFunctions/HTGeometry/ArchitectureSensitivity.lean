/-
Sensitivity of the covering architecture's floor, and where it can vanish.

The Section-4 floor is the middle source's demand at the final source's threshold,

    **floor(β, α, x₁) = β + (α - 1/2)·x₁** ,

with the published values `β = 1/32`, `α = 103/128`, `x₁ = 17/42` giving `277/1792`.

Its sensitivities are

    **∂floor/∂β = 1** ,   **∂floor/∂α = x₁ = 17/42** ,

so the middle source's `T`-exponent is `42/17 ≈ 2.47` times as valuable as its `M`-exponent.

Setting `β = 0` — a perfect `T`-exponent — leaves

    (103/128 - 1/2)·(17/42) = **663/5376 = 221/1792 ≈ 0.12333** ,

still positive, and in fact still the dominant part of the published floor: the `T`-exponent
contributes only `1/32 = 56/1792` of `277/1792`.

The floor vanishes **iff `β = 0` and `α ≤ 1/2`** (for `x₁ > 0`) — that is, iff the middle source is
itself a `t`-free bound with square-root cancellation.  So the covering architecture's floor
disappears under exactly the condition that the `t`-free analysis isolates, and the two independent
routes meet at the same place.
-/
import GaloisForLFunctions.HTGeometry.TFreeRequiresCorner

namespace HTGeometry

/-! ### The floor and its sensitivities -/

/-- The Section-4 floor as a function of the middle source's exponents and the threshold. -/
def archFloorAt (β α x₁ : ℚ) : ℚ := β + (α - 1 / 2) * x₁

/-- **It reproduces the published value.** -/
theorem archFloor_published : archFloorAt (1 / 32) (103 / 128) (17 / 42) = 277 / 1792 := by
  unfold archFloorAt; norm_num

/-- And agrees with the demand computed earlier. -/
theorem archFloor_is_huxleyDemand :
    archFloorAt huxleyBeta huxleyAlpha decouplingStart = huxleyDemand := by
  rw [huxleyDemand_eq]
  unfold archFloorAt huxleyBeta huxleyAlpha decouplingStart; norm_num

/-- **Sensitivity to the `T`-exponent is one.** -/
theorem sensitivity_beta (β β' α x₁ : ℚ) :
    archFloorAt β' α x₁ - archFloorAt β α x₁ = β' - β := by
  unfold archFloorAt; ring

/-- **Sensitivity to the `M`-exponent is the threshold.** -/
theorem sensitivity_alpha (β α α' x₁ : ℚ) :
    archFloorAt β α' x₁ - archFloorAt β α x₁ = (α' - α) * x₁ := by
  unfold archFloorAt; ring

/-- **So the `T`-exponent is `42/17` times as valuable at the published threshold.** -/
theorem sensitivity_ratio : (1 : ℚ) / (17 / 42) = 42 / 17 := by norm_num

/-! ### A perfect `T`-exponent is not enough -/

/-- The floor remaining when the `T`-exponent is driven to zero. -/
def residualFloor : ℚ := archFloorAt 0 (103 / 128) (17 / 42)

/-- **It is `221/1792`.** -/
@[simp] theorem residualFloor_eq : residualFloor = 221 / 1792 := by
  unfold residualFloor archFloorAt; norm_num

/-- **It is still positive**, and it is the dominant part of the published floor. -/
theorem residualFloor_dominates :
    0 < residualFloor ∧ residualFloor < 277 / 1792 ∧
      (277 : ℚ) / 1792 - residualFloor = 1 / 32 := by
  rw [residualFloor_eq]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **And it lies below `1/8`**, the threshold identified for the across-class condition. -/
theorem residualFloor_below_eighth : residualFloor < 1 / 8 := by
  rw [residualFloor_eq]; norm_num

/-! ### Where the floor vanishes -/

/-- **The floor vanishes exactly when the middle source is `t`-free with square-root cancellation.** -/
theorem archFloor_zero_iff {β α x₁ : ℚ} (hβ : 0 ≤ β) (hx : 0 < x₁) (hα : 1 / 2 ≤ α) :
    archFloorAt β α x₁ = 0 ↔ β = 0 ∧ α = 1 / 2 := by
  unfold archFloorAt
  constructor
  · intro h
    have h1 : 0 ≤ (α - 1 / 2) * x₁ := mul_nonneg (by linarith) hx.le
    have hβ0 : β = 0 := by linarith
    refine ⟨hβ0, ?_⟩
    rw [hβ0] at h
    have : (α - 1 / 2) * x₁ = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' (ne_of_gt hx)
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

/-- **The same condition the `t`-free analysis isolates.**  A middle source with `β = 0` and
`α = 1/2` is exactly a bound `M^(1/2)` with no power of `T` — the corner. -/
theorem architecture_and_tFree_agree {β α x₁ : ℚ} (hβ : 0 ≤ β) (hx : 0 < x₁) (hα : 1 / 2 ≤ α)
    (h : archFloorAt β α x₁ = 0) : β = 0 ∧ α = 1 / 2 :=
  (archFloor_zero_iff hβ hx hα).mp h

/-- **The published source is far from it**, by `221/1792` in the `M`-exponent's contribution alone. -/
theorem published_far_from_zero :
    archFloorAt huxleyBeta huxleyAlpha decouplingStart = 277 / 1792 ∧
      residualFloor = 221 / 1792 ∧ (277 : ℚ) / 1792 - 221 / 1792 = 1 / 32 := by
  refine ⟨?_, residualFloor_eq, by norm_num⟩
  rw [archFloor_is_huxleyDemand, huxleyDemand_eq]

end HTGeometry
