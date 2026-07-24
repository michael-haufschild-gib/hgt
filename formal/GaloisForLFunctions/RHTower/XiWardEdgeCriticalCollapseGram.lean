import GaloisForLFunctions.RHTower.XiWardEdgeReChannelDeposit

/-!
# Critical-collapse decoupling of the edge Gram calculus

As a Lorentzian kernel's width collapses (`x₁ → 0⁺`, the near-critical
regime), its self-energy `π/(2x₁)` diverges while its cross mass with any
FIXED kernel stays uniformly bounded by `π/x₂`, independently of the
collapsing width and of both heights.  Partial spectral subtraction is
therefore norm-accessible: removing near-critical kernels changes each
cross channel by a bounded amount even as the removed self-energies
diverge.  The mixed Gram is the quantitative measure of the phase
alignment that raw full-trace subtraction cannot certify. -/

open Complex Filter Topology MeasureTheory Real

namespace RHTower

noncomputable section

/-- **Uniform cross bound**: the cross-Lorentzian mass never exceeds
`π/x₂`, independently of the first width and of both heights. -/
theorem integral_mul_lorentzianHalves_le {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    ∫ t : ℝ, (x₁ / (x₁ ^ 2 + (t + β₁) ^ 2)) *
      (x₂ / (x₂ ^ 2 + (t + β₂) ^ 2)) ≤ π / x₂ := by
  rw [integral_mul_lorentzianHalves_general hx₁ hx₂ β₁ β₂]
  have hs : 0 < x₁ + x₂ := by linarith
  have hD : (0 : ℝ) < (x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2 := by positivity
  calc π * (x₁ + x₂) / ((x₁ + x₂) ^ 2 + (β₁ - β₂) ^ 2)
      ≤ π * (x₁ + x₂) / (x₁ + x₂) ^ 2 :=
        div_le_div₀ (by positivity) le_rfl (by positivity)
          (by nlinarith [sq_nonneg (β₁ - β₂)])
    _ = π / (x₁ + x₂) := by
        field_simp
    _ ≤ π / x₂ :=
        div_le_div₀ pi_pos.le le_rfl hx₂ (by linarith)

/-- **Self-energy divergence**: the squared mass of a collapsing kernel
tends to infinity. -/
theorem tendsto_integral_sq_lorentzianHalf_atTop (β : ℝ) :
    Tendsto (fun x : ℝ => ∫ t : ℝ, (x / (x ^ 2 + (t + β) ^ 2)) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have h1 : Tendsto (fun x : ℝ => x⁻¹) (nhdsWithin 0 (Set.Ioi 0))
      atTop := tendsto_inv_nhdsGT_zero
  have h2 := h1.const_mul_atTop (show (0 : ℝ) < π / 2 by positivity)
  apply Tendsto.congr' _ h2
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [integral_sq_lorentzianHalf hx β]
  ring


/-- Pointwise Harnack kernel transport between widths: the width-`x₁`
Lorentzian half is dominated by four times the width-`x₂` one whenever
`x₁ ≤ 4x₂` and `x₂ ≤ 4x₁`. -/
theorem lorentzianHalf_le_four_mul {x₁ x₂ u : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (h12 : x₁ ≤ 4 * x₂) (h21 : x₂ ≤ 4 * x₁) :
    x₁ / (x₁ ^ 2 + u ^ 2) ≤ 4 * (x₂ / (x₂ ^ 2 + u ^ 2)) := by
  have hD1 : (0 : ℝ) < x₁ ^ 2 + u ^ 2 := by positivity
  have hD2 : (0 : ℝ) < x₂ ^ 2 + u ^ 2 := by positivity
  rw [show 4 * (x₂ / (x₂ ^ 2 + u ^ 2)) = 4 * x₂ / (x₂ ^ 2 + u ^ 2) from by
    ring, div_le_div_iff₀ hD1 hD2]
  nlinarith [sq_nonneg u, mul_pos hx₁ hx₂,
    mul_nonneg (mul_nonneg hx₁.le hx₂.le) (sq_nonneg u),
    mul_nonneg (sq_nonneg u) (sub_nonneg.mpr h12)]

/-- Real part of one Schwarz pair on an arbitrary vertical line. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_line_eq
    (q : XiRightUpperZeroCopy) (σ t : ℝ) :
    (xiAntiCausalWardSchwarzPairResponse q
        (((σ : ℝ) : ℂ) + I * (t : ℂ))).re =
      2 * ((σ + (xiRightCenteredZero q.1).re) /
        ((σ + (xiRightCenteredZero q.1).re) ^ 2 +
          (t + (xiRightCenteredZero q.1).im) ^ 2)) +
      2 * ((σ + (xiRightCenteredZero q.1).re) /
        ((σ + (xiRightCenteredZero q.1).re) ^ 2 +
          (t - (xiRightCenteredZero q.1).im) ^ 2)) := by
  rw [xiAntiCausalWardSchwarzPairResponse, xiRightCenteredZero_conj q.1]
  have h1re : ((((σ : ℝ) : ℂ) + I * (t : ℂ)) +
      xiRightCenteredZero q.1).re =
      σ + (xiRightCenteredZero q.1).re := by
    simp [Complex.add_re, Complex.mul_re]
  have h1im : ((((σ : ℝ) : ℂ) + I * (t : ℂ)) +
      xiRightCenteredZero q.1).im =
      t + (xiRightCenteredZero q.1).im := by
    simp [Complex.add_im, Complex.mul_im]
  have h2re : ((((σ : ℝ) : ℂ) + I * (t : ℂ)) +
      (starRingEnd ℂ) (xiRightCenteredZero q.1)).re =
      σ + (xiRightCenteredZero q.1).re := by
    simp [Complex.add_re, Complex.mul_re]
  have h2im : ((((σ : ℝ) : ℂ) + I * (t : ℂ)) +
      (starRingEnd ℂ) (xiRightCenteredZero q.1)).im =
      t - (xiRightCenteredZero q.1).im := by
    simp [Complex.add_im, Complex.mul_im]
    ring
  rw [Complex.mul_re, Complex.add_re, Complex.inv_re, Complex.inv_re,
    Complex.add_im, Complex.inv_im, Complex.inv_im,
    Complex.normSq_apply, Complex.normSq_apply,
    h1re, h1im, h2re, h2im]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  ring

/-- **Unconditional Harnack transport of the Ward response** from the
critical edge to the interior line `Re w = 2`:
`Re r(½+it) ≤ 4·Re r(2+it)` pointwise. -/
theorem re_continuedXiAntiCausalWardResponse_edge_le_four_mul_interior
    (t : ℝ) :
    (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))).re ≤
      4 * (continuedXiAntiCausalWardResponse
        ((2 : ℂ) + I * (t : ℂ))).re := by
  have hw1 : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hw2 : (0 : ℝ) < ((2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hsum1 := summable_xiAntiCausalWardSchwarzPairResponse hw1
  have hsum2 := summable_xiAntiCausalWardSchwarzPairResponse hw2
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw1,
    continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw2,
    Complex.re_tsum hsum1, Complex.re_tsum hsum2, ← tsum_mul_left]
  apply Summable.tsum_mono (Complex.hasSum_re hsum1.hasSum).summable
    (((Complex.hasSum_re hsum2.hasSum).summable).mul_left 4)
  intro q
  dsimp only
  have hre := xiRightCenteredZero_re_pos q.1
  have hx1 : 0 < (1 / 2 : ℝ) + (xiRightCenteredZero q.1).re := by linarith
  have hx2 : 0 < (2 : ℝ) + (xiRightCenteredZero q.1).re := by linarith
  have hc1 : ((1 / 2 : ℂ) + I * (t : ℂ)) =
      (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) := by norm_num
  have hc2 : ((2 : ℂ) + I * (t : ℂ)) =
      (((2 : ℝ) : ℂ) + I * (t : ℂ)) := by norm_num
  rw [hc1, hc2, re_xiAntiCausalWardSchwarzPairResponse_line_eq,
    re_xiAntiCausalWardSchwarzPairResponse_line_eq]
  have hk1 := lorentzianHalf_le_four_mul
    (u := t + (xiRightCenteredZero q.1).im) hx1 hx2
    (by linarith) (by linarith)
  have hk2 := lorentzianHalf_le_four_mul
    (u := t - (xiRightCenteredZero q.1).im) hx1 hx2
    (by linarith) (by linarith)
  linarith [hk1, hk2]

end

end RHTower
