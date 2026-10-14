import GaloisForLFunctions.RHTower.LiClockCenterAverage
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# The critical slope of the averaged Li clock against `ξ'/ξ(3/2)`

The Cauchy slope weights of all zero copies sum to the real number `ξ'/ξ(3/2)`:

`Σ_q Im (a_q − i)⁻¹ = Σ_ρ Re 1/(ρ + ½) = Re ξ'/ξ(3/2)`
(`tsum_centerClockSlopeWeight_eq_re_logDeriv_xi`).

Proof: take the Hadamard partial fractions `ξ'/ξ(s) = Σ_ρ ((ρ − ½)⁻¹ + (s − ρ)⁻¹)` at `s = 3/2`.
Reflection `ρ ↦ 1 − ρ` cancels the centring terms and turns `(3/2 − ρ)⁻¹` into `(ρ + ½)⁻¹`.

With `tendsto_liClockCenterAverage_div` this gives a single-number criterion with both sides
defined without the zeros: **RH ⟺ the small-clock slope of the center-averaged Li clock equals
`ξ'/ξ(3/2)`** (`riemannHypothesis_iff_tendsto_liClockCenterAverage_div`).  The slope never exceeds
`ξ'/ξ(3/2)`.  The deficit is the Cauchy-weighted number of off-line zeros, each weighted by
`Re 1/(ρ + ½) ≍ 1/(1 + γ²)` whatever its depth.
-/

noncomputable section

open Complex Filter Topology

namespace RHTower

private theorem spectralPoint_eq (q : XiZeroCopy) :
    xiSpectralPoint q = ((q.1 : ℂ) - 1 / 2) * (-I) := rfl

/-- The slope weight of a copy is `Re 1/(ρ + ½)`. -/
theorem centerClockSlopeWeight_eq_re_inv (q : XiZeroCopy) :
    centerClockSlopeWeight (xiSpectralPoint q) = (((q.1 : ℂ) + 1 / 2)⁻¹).re := by
  have hρ : (q.1 : ℂ) + 1 / 2 ≠ 0 := by
    intro h
    have := (xi_divisor_support_re_mem_open_unit q.1).1
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hkey : xiSpectralPoint q - I = (-I) * ((q.1 : ℂ) + 1 / 2) := by
    rw [spectralPoint_eq]; ring
  rw [centerClockSlopeWeight, hkey, mul_inv, inv_neg, Complex.inv_I, neg_neg, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]

/-- The reflected copy carries `1 − ρ`. -/
private theorem reflect_val (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := by
  have h := xiSpectralPoint_reflect q
  rw [spectralPoint_eq, spectralPoint_eq] at h
  have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have h2 : ((xiZeroCopyReflectEquiv q).1 : ℂ) - 1 / 2 = -((q.1 : ℂ) - 1 / 2) := by
    apply mul_right_cancel₀ hI
    rw [h]; ring
  linear_combination h2

private theorem re_half_bound (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  rw [abs_le]; constructor <;> linarith

private theorem normSq_sub_half_eq (q : XiZeroCopy) :
    Complex.normSq ((q.1 : ℂ) - 1 / 2) = ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  rw [Complex.normSq_eq_norm_sq, norm_xiSpectralPoint]

private theorem normSq_sub_half_pos (q : XiZeroCopy) :
    0 < Complex.normSq ((q.1 : ℂ) - 1 / 2) := by
  rw [normSq_sub_half_eq]
  exact pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) 2

/-- The centring terms are summable. -/
private theorem summable_re_inv_sub_half :
    Summable fun q : XiZeroCopy => (((q.1 : ℂ) - 1 / 2)⁻¹).re := by
  refine Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left (1 / 2)) fun q => ?_
  rw [Complex.inv_re, Real.norm_eq_abs, abs_div, abs_of_pos (normSq_sub_half_pos q),
    normSq_sub_half_eq, Complex.sub_re]
  have hb := re_half_bound q
  have hpos : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) 2
  have hhalf : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  rw [hhalf, div_le_iff₀ hpos]
  have hx : 1 / 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * ‖xiSpectralPoint q‖ ^ (2 : ℕ) = 1 / 2 := by
    rw [mul_assoc, one_div_mul_cancel hpos.ne', mul_one]
  rw [hx]
  exact hb

/-- The far terms at `3/2` are summable. -/
private theorem summable_re_inv_three_halves_sub :
    Summable fun q : XiZeroCopy => ((3 / 2 - (q.1 : ℂ))⁻¹).re := by
  refine Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left (3 / 2)) fun q => ?_
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hcmp : ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤ Complex.normSq (3 / 2 - (q.1 : ℂ)) := by
    rw [← normSq_sub_half_eq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    norm_num
    nlinarith
  have hpos : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) 2
  have hns : 0 < Complex.normSq (3 / 2 - (q.1 : ℂ)) := lt_of_lt_of_le hpos hcmp
  rw [Complex.inv_re, Real.norm_eq_abs, abs_div, abs_of_pos hns]
  have hre : |(3 / 2 - (q.1 : ℂ)).re| ≤ 3 / 2 := by
    simp only [Complex.sub_re]
    norm_num
    rw [abs_le]; constructor <;> linarith
  calc |(3 / 2 - (q.1 : ℂ)).re| / Complex.normSq (3 / 2 - (q.1 : ℂ))
      ≤ (3 / 2) / Complex.normSq (3 / 2 - (q.1 : ℂ)) := div_le_div_of_nonneg_right hre hns.le
    _ ≤ (3 / 2) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hcmp
    _ = 3 / 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring

/-- **The Hadamard identity at `3/2`.**  `Σ_q Im (a_q − i)⁻¹ = Re ξ'/ξ(3/2)`. -/
theorem tsum_centerClockSlopeWeight_eq_re_logDeriv_xi :
    ∑' q : XiZeroCopy, centerClockSlopeWeight (xiSpectralPoint q) = (logDeriv xi (3 / 2)).re := by
  have hxi : xi (3 / 2 : ℂ) ≠ 0 := xi_ne_zero_of_one_lt_re (by norm_num)
  rw [re_logDeriv_xi_eq_tsum hxi]
  have hsplit : ∀ q : XiZeroCopy, (xiPartialFractionTerm (3 / 2) q).re =
      (((q.1 : ℂ) - 1 / 2)⁻¹).re + ((3 / 2 - (q.1 : ℂ))⁻¹).re := by
    intro q; rw [xiPartialFractionTerm, Complex.add_re]
  simp_rw [hsplit]
  rw [summable_re_inv_sub_half.tsum_add summable_re_inv_three_halves_sub]
  -- the centring terms cancel under reflection
  have hcent : ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹).re = 0 := by
    have hre := (xiZeroCopyReflectEquiv.tsum_eq
      (fun q : XiZeroCopy => (((q.1 : ℂ) - 1 / 2)⁻¹).re)).symm
    have hneg : ∀ q : XiZeroCopy,
        ((((xiZeroCopyReflectEquiv q).1 : ℂ) - 1 / 2)⁻¹).re = -((((q.1 : ℂ) - 1 / 2)⁻¹).re) := by
      intro q
      rw [reflect_val]
      have : (1 - (q.1 : ℂ) - 1 / 2) = -((q.1 : ℂ) - 1 / 2) := by ring
      rw [this, inv_neg, Complex.neg_re]
    simp_rw [hneg, tsum_neg] at hre
    linarith
  -- the far terms are the shifted weights
  have hfar : ∑' q : XiZeroCopy, ((3 / 2 - (q.1 : ℂ))⁻¹).re =
      ∑' q : XiZeroCopy, centerClockSlopeWeight (xiSpectralPoint q) := by
    rw [← xiZeroCopyReflectEquiv.tsum_eq]
    refine tsum_congr fun q => ?_
    rw [reflect_val, centerClockSlopeWeight_eq_re_inv]
    congr 2
    ring
  rw [hcent, zero_add, hfar]

/-- **RH as one number.**  The critical slope of the averaged clock equals `Re ξ'/ξ(3/2)` exactly
under RH. -/
theorem riemannHypothesis_iff_liClockCriticalSlope_eq_logDeriv_xi :
    RiemannHypothesis ↔ liClockCriticalSlope = (logDeriv xi (3 / 2)).re := by
  rw [← tsum_centerClockSlopeWeight_eq_re_logDeriv_xi]
  exact riemannHypothesis_iff_liClockCriticalSlope_eq

/-- **RH as a small-clock slope.**  The center-averaged Li clock satisfies
`A(t)/t → Re ξ'/ξ(3/2)` as `t → 0⁺` iff RH holds. -/
theorem riemannHypothesis_iff_tendsto_liClockCenterAverage_div :
    RiemannHypothesis ↔ Tendsto (fun t : ℝ => liClockCenterAverage t / t) (𝓝[>] 0)
      (𝓝 (logDeriv xi (3 / 2)).re) := by
  rw [riemannHypothesis_iff_liClockCriticalSlope_eq_logDeriv_xi]
  constructor
  · intro h
    rw [← h]
    exact tendsto_liClockCenterAverage_div
  · intro h
    exact tendsto_nhds_unique tendsto_liClockCenterAverage_div h

end RHTower
