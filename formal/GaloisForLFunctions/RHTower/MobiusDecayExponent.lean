import GaloisForLFunctions.RHTower.MobiusHalfDecayFromSubpower

/-!
# Source decay at an arbitrary exponent

The corpus fixes the decay exponent of the Möbius--Laplace source at `1/2`, which is the value that
makes the Mellin transform analytic exactly on the critical half-plane.  The order law needs the
same statements at the exponent `b = (α+1)/(2k)` produced by a subpower coefficient bound, which is
below `1/2` precisely when the bound is strong enough.

Everything is the `1/2`-specific development with the exponent carried as a parameter: the decay
predicate, its asymptotic form, the discharge from a coefficient bound, and analyticity of the
Mellin transform on `Re s > b`.
-/

open Complex Filter Asymptotics
open scoped BigOperators Topology

namespace RHTower

/-- Decay of the Möbius--Laplace source at exponent `b` near the origin. -/
def MobiusDiscreteLaplaceDecay (b : ℝ) : Prop :=
  ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
    ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * x ^ (-b)

/-- The decay statement in filter form. -/
theorem MobiusDiscreteLaplaceDecay.isBigO {b : ℝ} (hdecay : MobiusDiscreteLaplaceDecay b) :
    mobiusDiscreteLaplaceTransform =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
  rcases hdecay with ⟨C, delta, hC, hdelta, hbound⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < delta :=
    (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxd
  have hxpos : 0 < x := hx
  calc ‖mobiusDiscreteLaplaceTransform x‖
      ≤ C * x ^ (-b) := hbound x hxpos hxd
    _ = C * ‖x ^ (-b)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos _)]

/-- **Discharge at the natural exponent.**  A subpower coefficient bound gives source decay at
exponent `(α+1)/(2k)`. -/
theorem mobiusDiscreteLaplaceDecay_of_subpower
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hupper : ∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ C * ((N : ℝ) + 1) ^ α) :
    MobiusDiscreteLaplaceDecay ((α + 1) / (2 * (k : ℝ))) := by
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  refine ⟨(C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹), 1, ?_, one_pos, ?_⟩
  · exact Real.rpow_nonneg (mul_nonneg hC hAbel) _
  · intro x hx hx1
    have hbound := norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower
      hk hα hC hx hx1.le (summable_norm_mobiusCoeff_mul_pow hx) hupper
    rw [mobiusDiscreteLaplaceTransform_eq_tsum]
    refine hbound.trans (le_of_eq ?_)
    congr 1
    rw [one_div x, ← Real.rpow_neg_one x, ← Real.rpow_mul hx.le]
    congr 1
    ring

/-- The half-power decay is the case `b = 1/2`. -/
theorem mobiusDiscreteLaplaceHalfDecay_iff_decay_half :
    MobiusDiscreteLaplaceHalfDecay ↔ MobiusDiscreteLaplaceDecay (1 / 2) := Iff.rfl

/-- The open half-plane to the right of the decay exponent. -/
theorem isOpen_decayHalfPlane (b : ℝ) : IsOpen {s : ℂ | b < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- **Analyticity at the decay exponent.**  Source decay at exponent `b` makes the Mellin transform
analytic on `Re s > b`. -/
theorem analyticOnNhd_mellin_of_mobiusDiscreteLaplaceDecay
    {b : ℝ} (hdecay : MobiusDiscreteLaplaceDecay b) :
    AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) {s : ℂ | b < s.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) (isOpen_decayHalfPlane b)
  exact (mellin_differentiableAt_of_isBigO_rpow_exp
    (a := 1) (b := b) (by norm_num)
    mobiusDiscreteLaplaceTransform_locallyIntegrableOn
    mobiusDiscreteLaplaceTransform_isBigO_exp_neg hdecay.isBigO hs).differentiableWithinAt

end RHTower
