import GaloisForLFunctions.RHTower.SoninChannelHeightSplit
import GaloisForLFunctions.HTGeometry.LogWeightedGeometricSum

/-!
# The outer shells of a tower against a power tail

A shell above a radius sees only what the vector leaves above that radius, so a vector whose mass
outside a ball decays like a power of the radius has geometrically decaying shell masses: the radii
of a tower grow geometrically, so a power of the radius is a geometric sequence in the shell index.

The layer logarithm grows only like the logarithm of the radius, which is linear in the index, and a
logarithm squared is below four times its argument.  One order of the decay therefore pays for the
whole weight and the outer sum is bounded by a single geometric term — in particular by a quantity
that does not grow with the tower's height.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap GaloisForLFunctions.HTGeometry
open scoped InnerProduct InnerProductSpace

/-- **A shell sees only the mass above its inner radius.** -/
theorem norm_evenIndicatorLayer_apply_le_high {s t : ℝ} (hst : s ≤ t) (u : evenSubspace) :
    ‖evenIndicatorLayer s t u‖ ≤ ‖u - evenIndicatorCutoff s u‖ := by
  have hts : evenIndicatorCutoff t (evenIndicatorCutoff s u) = evenIndicatorCutoff s u := by
    have h := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le_rev s t hst) u
    simpa using h
  have hss : evenIndicatorCutoff s (evenIndicatorCutoff s u) = evenIndicatorCutoff s u := by
    have h := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le s s le_rfl) u
    simpa using h
  have hzero : evenIndicatorLayer s t (evenIndicatorCutoff s u) = 0 := by
    rw [evenIndicatorLayer, sub_apply, hts, hss, sub_self]
  have hcomp : evenIndicatorLayer s t (u - evenIndicatorCutoff s u) =
      evenIndicatorLayer s t u := by
    rw [map_sub, hzero, sub_zero]
  rw [← hcomp]
  exact norm_evenIndicatorLayer_apply_le hst _

/-- A tower radius raised to a power is a geometric sequence in the shell index. -/
theorem logShellRadius_pow (a r : ℝ) (p k : ℕ) :
    logShellRadius a r k ^ p = a ^ p * (r ^ p) ^ k := by
  have h1 : ((r : ℝ) ^ k) ^ p = (r ^ p) ^ k := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [logShellRadius, mul_pow, h1]
  ring

/-- **The weighted outer sum against a power tail.**  If the shell masses decay like the inverse
`(p+1)`-st power of the radius, the logarithmically weighted sum over the shells above the cut is
bounded by a single geometric term in the cut index, with no dependence on the tower's height. -/
theorem sum_Ico_logShellRadius_weight_le {a r : ℝ} (ha : 0 < a) (hr : 1 < r) {p : ℕ} (hp : p ≠ 0)
    (K n : ℕ) (u : evenSubspace) {C : ℝ} (hC : 0 ≤ C) (hone : 1 ≤ logShellRadius a r K)
    (hdecay : ∀ k, K ≤ k → ‖evenIndicatorLayer (logShellRadius a r k)
        (logShellRadius a r (k + 1)) u‖ ^ 2 ≤ C / logShellRadius a r k ^ (p + 1)) :
    ∑ k ∈ Finset.Ico K n, |Real.log (logShellRadius a r k)| ^ 2 *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
      4 * C / a ^ p * ((r ^ p)⁻¹ ^ K * (1 - (r ^ p)⁻¹)⁻¹) := by
  classical
  have hrp : (1 : ℝ) < r ^ p := one_lt_pow₀ hr hp
  have hrp0 : (0 : ℝ) < r ^ p := lt_trans zero_lt_one hrp
  have hx0 : (0 : ℝ) ≤ (r ^ p)⁻¹ := le_of_lt (inv_pos.mpr hrp0)
  have hx1 : (r ^ p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hrp
  have hap : (0 : ℝ) < a ^ p := pow_pos ha p
  have hconst : (0 : ℝ) ≤ 4 * C / a ^ p := by positivity
  have hterm : ∀ k ∈ Finset.Ico K n,
      |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
        4 * C / a ^ p * (r ^ p)⁻¹ ^ k := by
    intro k hk
    have hKk : K ≤ k := (Finset.mem_Ico.mp hk).1
    have hρpos : (0 : ℝ) < logShellRadius a r k := logShellRadius_pos ha hr k
    have hρ1 : (1 : ℝ) ≤ logShellRadius a r k :=
      le_trans hone (logShellRadius_mono ha hr hKk)
    have hlogsq : |Real.log (logShellRadius a r k)| ^ 2 ≤ 4 * logShellRadius a r k :=
      sq_abs_log_le_four_mul hρ1
    have hmass := hdecay k hKk
    have hmul : |Real.log (logShellRadius a r k)| ^ 2 *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
        4 * logShellRadius a r k * (C / logShellRadius a r k ^ (p + 1)) :=
      mul_le_mul hlogsq hmass (sq_nonneg _) (by positivity)
    refine le_trans hmul (le_of_eq ?_)
    have hne : logShellRadius a r k ≠ 0 := ne_of_gt hρpos
    have hstep : 4 * logShellRadius a r k * (C / logShellRadius a r k ^ (p + 1)) =
        4 * C / logShellRadius a r k ^ p := by
      rw [pow_succ]
      field_simp
    rw [hstep, logShellRadius_pow a r p k, inv_pow]
    field_simp
  calc ∑ k ∈ Finset.Ico K n, |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2
      ≤ ∑ k ∈ Finset.Ico K n, 4 * C / a ^ p * (r ^ p)⁻¹ ^ k := Finset.sum_le_sum hterm
    _ = 4 * C / a ^ p * ∑ k ∈ Finset.Ico K n, (r ^ p)⁻¹ ^ k := by rw [← Finset.mul_sum]
    _ ≤ 4 * C / a ^ p * ((r ^ p)⁻¹ ^ K * (1 - (r ^ p)⁻¹)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ico_geom_le hx0 hx1 K n) hconst

end RHTower

