import GaloisForLFunctions.RHTower.ExteriorGeneralEndpoint
import GaloisForLFunctions.RHTower.ProlateDilatedChannel

/-!
# The dilated channel estimate with a free left endpoint

Over `[L, X]` the dilated exterior estimate gains `1/(L c k)` rather than `1/(c k)`.  For a channel
whose natural range starts at `L = 1` this is the same statement; what it buys is that the range
need not start at `2`, so the whole channel `[1, X]` is covered by one estimate.

The condition is `k L ≥ 2`: the *dilated* argument has to be in the exterior, not the outer
variable.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

theorem abs_dilated_inv_speed_deriv_left {s k t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hk : 1 ≤ k)
    (ht0 : 0 < t) (hkt : 2 ≤ k * t) : |k * xiInvSpeedDeriv s (k * t)| ≤ 1 / t ^ (2 : ℕ) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hbase : |xiInvSpeedDeriv s (k * t)| ≤ 1 / (k * t) ^ (2 : ℕ) :=
    abs_deriv_inv_xiSpeed_le hs0 hs1 hkt
  rw [abs_mul, abs_of_pos hk0]
  have hstep : k * |xiInvSpeedDeriv s (k * t)| ≤ k * (1 / (k * t) ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hbase hk0.le
  refine le_trans hstep ?_
  have hval : k * (1 / (k * t) ^ (2 : ℕ)) = 1 / (k * t ^ (2 : ℕ)) := by
    field_simp
  rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hk, sq_nonneg t, ht0, mul_pos ht0 ht0]

/-- **The dilated exterior estimate over `[L, X]`.**  With `Cr = 1` the constant is
`3 (Ca (3/2 + 1)) = 15 Ca/2`. -/
theorem norm_integral_exterior_dilated_left {L X Ca c k eps s : ℝ} (hL : 1 ≤ L) (hLX : L ≤ X)
    (hkL : 2 ≤ k * L) (hCa : 0 ≤ Ca) (hc : 0 < c) (hk : 1 ≤ k) (heps : |eps| = 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) {a a' : ℝ → ℂ}
    (ha : ∀ x ∈ Set.uIcc L X, HasDerivAt a (a' x) x)
    (hac : ContinuousOn a (Set.uIcc L X))
    (ha'c : ContinuousOn a' (Set.uIcc L X))
    (haB : ∀ x ∈ Set.uIcc L X, ‖a x‖ ≤ Ca / Real.sqrt x)
    (ha'B : ∀ x ∈ Set.uIcc L X, ‖a' x‖ ≤ Ca / (x * Real.sqrt x)) :
    ‖∫ t in L..X, (a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
      ≤ 15 * Ca / (2 * (L * (c * k))) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hck : (0 : ℝ) < c * k := mul_pos hc hk0
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hxL : ∀ x ∈ Set.uIcc L X, L ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hLX] at hx
    exact hx.1
  have hx0 : ∀ x ∈ Set.uIcc L X, (0 : ℝ) < x := fun x hx => lt_of_lt_of_le hL0 (hxL x hx)
  have hkx2 : ∀ x ∈ Set.uIcc L X, (2 : ℝ) ≤ k * x := by
    intro x hx
    have := hxL x hx
    nlinarith [hkL, hk0]
  have hkx : ∀ x ∈ Set.uIcc L X, (1 : ℝ) < k * x := fun x hx => by linarith [hkx2 x hx]
  have hlin : ContinuousOn (fun t : ℝ => k * t) (Set.uIcc L X) :=
    continuousOn_const.mul continuousOn_id
  have hmaps : Set.MapsTo (fun t : ℝ => k * t) (Set.uIcc L X) (Set.Ioi 1) :=
    fun x hx => hkx x hx
  have hmain := _root_.RHTower.norm_integral_exterior_left (Ca := Ca) (Cr := 1)
    hL hLX hCa zero_le_one hck heps
    (fun x hx => hasDerivAt_dilatedPhase hs0 hk (hkx x hx))
    (fun x hx => hasDerivAt_inv_dilatedSpeed (by linarith) (hkx x hx))
    ha hac ha'c
    ((continuousOn_xiSpeed s).comp hlin hmaps)
    ((continuousOn_const.mul ((continuousOn_xiInvSpeedDeriv (by linarith)).comp hlin hmaps)))
    (fun x hx => one_le_xiSpeed (by linarith) (hkx x hx)) haB ha'B
    (fun x hx => by
      refine le_trans (abs_dilated_inv_speed_deriv_left hs0 (by linarith) hk (hx0 x hx)
        (hkx2 x hx)) ?_
      exact le_of_eq (by field_simp))
  refine le_trans hmain (le_of_eq ?_)
  field_simp
  ring

end GaloisForLFunctions.RHTower
