/-
# A convergent positive factor scales a root limsup

Multiplying a bounded non-negative sequence by a factor converging to a positive constant
multiplies its `limsup` by that constant.  This is the version of the unit-factor law needed when
the convergent group of factors does not tend to one — for a degree-`d` shift lattice the
archimedean group converges to the cusp constant, not to one.

Main result:
* `limsup_mul_eq_of_tendsto` — **`a → κ > 0` and `limsup b = 1` give `limsup (a·b) = κ`**.
-/
import GaloisForLFunctions.HTGeometry.LimsupUnitFactor

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section PositiveFactor

variable {a b : ℕ → ℝ}

theorem limsup_const_mul {κ : ℝ} (hκ : 0 < κ) (c : ℕ → ℝ)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop c) (hcob : IsCoboundedUnder (· ≤ ·) atTop c) :
    limsup (fun k => κ * c k) atTop = κ * limsup c atTop := by
  have hmono : Monotone (fun x : ℝ => κ * x) := fun _ _ h => by nlinarith
  have hcont : ContinuousAt (fun x : ℝ => κ * x) (limsup c atTop) :=
    (continuous_const.mul continuous_id).continuousAt
  exact (hmono.map_limsup_of_continuousAt c hcont hbdd hcob).symm

/-- **A convergent positive factor scales a root `limsup` of one to its own limit.** -/
theorem limsup_mul_eq_of_tendsto {κ : ℝ} (hκ : 0 < κ)
    (ha : Tendsto a atTop (𝓝 κ)) (hbnn : ∀ k, 0 ≤ b k)
    (hbbdd : IsBoundedUnder (· ≤ ·) atTop b) (hb : limsup b atTop = 1) :
    limsup (fun k => a k * b k) atTop = κ := by
  have ha' : Tendsto (fun k => a k / κ) atTop (𝓝 1) := by
    have := ha.div_const κ
    rwa [div_self hκ.ne'] at this
  have hunit := limsup_mul_eq_one_of_tendsto_one ha' hbnn hbbdd hb
  have haev : ∀ᶠ k in atTop, 0 ≤ a k / κ :=
    (ha'.eventually_const_lt (by norm_num : (0 : ℝ) < 1)).mono fun k h => h.le
  have hnn : ∀ᶠ k in atTop, 0 ≤ a k / κ * b k :=
    haev.mono fun k h => mul_nonneg h (hbnn k)
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun k => a k / κ * b k) := by
    refine IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
    rw [Filter.eventually_map]
    exact hnn
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k => a k / κ * b k) := by
    obtain ⟨B, hB⟩ := id hbbdd
    rw [Filter.eventually_map] at hB
    refine ⟨max B 0 * 2, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hB, haev, ha'.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with k hBk hak h2
    calc a k / κ * b k ≤ 2 * max B 0 :=
          mul_le_mul h2.le (le_trans hBk (le_max_left _ _)) (hbnn k) (by norm_num)
      _ = max B 0 * 2 := by ring
  have hscale := limsup_const_mul hκ (fun k => a k / κ * b k) hbdd hcob
  rw [hunit, mul_one] at hscale
  rw [← hscale]
  refine limsup_congr (Filter.Eventually.of_forall fun k => ?_)
  field_simp

end PositiveFactor

end GaloisForLFunctions.HTGeometry
