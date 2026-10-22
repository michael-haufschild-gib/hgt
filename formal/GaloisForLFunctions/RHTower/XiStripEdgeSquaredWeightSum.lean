import GaloisForLFunctions.RHTower.LagExplicitFormula
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPoleUnitStrictTransverseCurvature

/-!
# The strip-edge squared weight sum of the ξ divisor

For a zero `ρ` of `ξ` put `w_ρ = 1/(ρ(1−ρ))`; in the centred spectral coordinate
`a = (ρ − 1/2)(−i)` this is `w = (1/4 + a²)⁻¹`, the resolvent weight of the strip-edge point
`s = 1`.  With `Λ₀ = completedRiemannZeta₀` and multiplicity counted, both

`Σ_ρ w_ρ = 2 Λ₀(1)`   and   `Σ_ρ w_ρ² = 2 (Λ₀(1)² − 2 Λ₀'(1))`

hold with absolutely convergent sums.  The first is the symmetrised partial fraction of `ξ'/ξ`
at `s = 1`.  The second uses the splitting `w² = ρ⁻² + (1−ρ)⁻² + 2w`, the reflection symmetry
`ρ ↦ 1 − ρ` of the divisor, the Hadamard jet `(ξ'/ξ)'(1) = −Σ_ρ ρ⁻²`, and the value
`(ξ'/ξ)'(1) = 2Λ₀(1) + 2Λ₀'(1) − Λ₀(1)²` read off from `ξ(s) = s(s−1)Λ₀(s)/2 + 1/2`.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The second logarithmic derivative of `ξ` at the strip edge -/

/-- The derivative of `ξ = s(s−1)Λ₀(s)/2 + 1/2` at every point. -/
theorem hasDerivAt_xi_completedZeta₀ (s : ℂ) :
    HasDerivAt xi ((2 * s - 1) / 2 * completedRiemannZeta₀ s +
      s * (s - 1) / 2 * deriv completedRiemannZeta₀ s) s := by
  have hp : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) ((2 * s - 1) / 2) s :=
    (((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)).div_const 2).congr_deriv
      (by ring)
  have hz : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ s) s :=
    (differentiable_completedZeta₀ s).hasDerivAt
  have h := (hp.mul hz).add_const (1 / 2 : ℂ)
  exact h

theorem deriv_xi_eq_completedZeta₀ :
    deriv xi = fun s : ℂ => (2 * s - 1) / 2 * completedRiemannZeta₀ s +
      s * (s - 1) / 2 * deriv completedRiemannZeta₀ s :=
  funext fun s => (hasDerivAt_xi_completedZeta₀ s).deriv

/-- `ξ''(1) = Λ₀(1) + Λ₀'(1)`. -/
theorem hasDerivAt_deriv_xi_one :
    HasDerivAt (deriv xi) (completedRiemannZeta₀ 1 + deriv completedRiemannZeta₀ 1) 1 := by
  rw [deriv_xi_eq_completedZeta₀]
  have hz : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ 1) 1 :=
    (differentiable_completedZeta₀ 1).hasDerivAt
  have hz' : HasDerivAt (deriv completedRiemannZeta₀)
      (deriv (deriv completedRiemannZeta₀) 1) 1 :=
    ((differentiable_completedZeta₀.analyticAt 1).deriv).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun s : ℂ => (2 * s - 1) / 2) 1 1 :=
    ((((hasDerivAt_id' (1 : ℂ)).const_mul 2).sub_const 1).div_const 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) ((2 * 1 - 1) / 2) 1 :=
    (((hasDerivAt_id' (1 : ℂ)).mul ((hasDerivAt_id' (1 : ℂ)).sub_const 1)).div_const 2).congr_deriv
      (by ring)
  exact ((h1.mul hz).add (h2.mul hz')).congr_deriv (by ring)

/-- **The strip-edge second logarithmic derivative**:
`(ξ'/ξ)'(1) = 2Λ₀(1) + 2Λ₀'(1) − Λ₀(1)²`. -/
theorem deriv_logDeriv_xi_one_eq_completedZeta₀ :
    deriv (logDeriv xi) 1 =
      2 * completedRiemannZeta₀ 1 + 2 * deriv completedRiemannZeta₀ 1 -
        completedRiemannZeta₀ 1 ^ (2 : ℕ) := by
  have hxi1 : xi 1 ≠ 0 := by rw [xi_one]; norm_num
  have h := hasDerivAt_deriv_xi_one.div (xi_differentiable 1).hasDerivAt hxi1
  rw [show logDeriv xi = deriv xi / xi from rfl, h.deriv, xi_one, hasDerivAt_xi_one.deriv]
  field_simp

/-! ## The strip-edge weight -/

/-- The strip-edge weight `1/(ρ(1−ρ))` of a zero copy. -/
def xiStripEdgeWeight (q : XiZeroCopy) : ℂ := ((q.1 : ℂ) * (1 - (q.1 : ℂ)))⁻¹

/-- In the spectral coordinate the weight is the strip-edge resolvent `(1/4 + a²)⁻¹`. -/
theorem xiStripEdgeWeight_eq_spectral (q : XiZeroCopy) :
    xiStripEdgeWeight q = (1 / 4 + xiSpectralPoint q ^ (2 : ℕ))⁻¹ := by
  rw [xiStripEdgeWeight, xiZeroCopy_eq_half_add q]
  congr 1
  linear_combination (-(xiSpectralPoint q ^ (2 : ℕ))) * Complex.I_mul_I

/-- The weight is dominated by twice the inverse squared spectral height. -/
theorem norm_xiStripEdgeWeight_le (q : XiZeroCopy) :
    ‖xiStripEdgeWeight q‖ ≤ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  have hre := xiSpectral_re_sq_gt_thirtytwo q
  have ha : (xiSpectralPoint q).re ^ 2 ≤ ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (xiSpectralPoint q).im]
  set r := ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hr
  have hr32 : 32 < r := by linarith
  have hlow : r - 1 / 4 ≤ ‖1 / 4 + xiSpectralPoint q ^ (2 : ℕ)‖ := by
    have h := norm_sub_norm_le (xiSpectralPoint q ^ (2 : ℕ)) (-(1 / 4 : ℂ))
    rw [sub_neg_eq_add, add_comm, norm_neg, norm_pow] at h
    rw [hr]
    have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    linarith
  rw [xiStripEdgeWeight_eq_spectral, norm_inv]
  have hpos : 0 < r - 1 / 4 := by linarith
  calc ‖1 / 4 + xiSpectralPoint q ^ (2 : ℕ)‖⁻¹ ≤ (r - 1 / 4)⁻¹ :=
        inv_anti₀ hpos hlow
    _ ≤ 2 * (1 / r) := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        field_simp
        linarith

theorem summable_xiStripEdgeWeight : Summable xiStripEdgeWeight :=
  Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left 2) norm_xiStripEdgeWeight_le

/-- **The first strip-edge sum rule**: `Σ_ρ 1/(ρ(1−ρ)) = 2Λ₀(1)`. -/
theorem hasSum_xiStripEdgeWeight :
    HasSum xiStripEdgeWeight (2 * completedRiemannZeta₀ 1) := by
  have h := summable_xiStripEdgeWeight.hasSum
  have hval : (∑' q, xiStripEdgeWeight q) = 2 * completedRiemannZeta₀ 1 := by
    have h1 := tsum_inv_zero_mul_one_sub_zero
    simp only [one_div] at h1
    rw [show (∑' q, xiStripEdgeWeight q) =
        ∑' q : XiZeroCopy, ((q.1 : ℂ) * (1 - (q.1 : ℂ)))⁻¹ from rfl, h1,
      completedRiemannZeta₀_one, poleSharpConstant]
    push_cast
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
    push_cast
    ring
  rwa [hval] at h

/-- The weight splits into the two reciprocal coordinates of the reflection pair. -/
theorem xiStripEdgeWeight_sq_eq (q : XiZeroCopy) :
    xiStripEdgeWeight q ^ (2 : ℕ) =
      xiRawReciprocalCoordinate q ^ (2 : ℕ) +
        xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ (2 : ℕ) +
          2 * xiStripEdgeWeight q := by
  have h0 := xiZeroCopy_ne_zero q
  have h1 := xiZeroCopy_one_sub_ne_zero q
  have hrefl : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
  rw [xiRawReciprocalCoordinate, xiRawReciprocalCoordinate, hrefl, xiStripEdgeWeight]
  field_simp
  ring

/-- **The second strip-edge sum rule**: `Σ_ρ 1/(ρ(1−ρ))² = 2(Λ₀(1)² − 2Λ₀'(1))`. -/
theorem hasSum_xiStripEdgeWeight_sq :
    HasSum (fun q => xiStripEdgeWeight q ^ (2 : ℕ))
      (2 * (completedRiemannZeta₀ 1 ^ (2 : ℕ) - 2 * deriv completedRiemannZeta₀ 1)) := by
  have htr : HasSum (fun q : XiZeroCopy => xiRawReciprocalCoordinate q ^ (2 : ℕ))
      (xiRawReciprocalPowerTrace 2) := by
    have h := (summable_xiRawReciprocalCoordinate_pow_add_two 0).hasSum
    simpa [xiRawReciprocalPowerTrace] using h
  have htr' : HasSum (fun q : XiZeroCopy =>
      xiRawReciprocalCoordinate (xiZeroCopyReflectEquiv q) ^ (2 : ℕ))
      (xiRawReciprocalPowerTrace 2) :=
    (xiZeroCopyReflectEquiv.hasSum_iff
      (f := fun q : XiZeroCopy => xiRawReciprocalCoordinate q ^ (2 : ℕ))).mpr htr
  have hsum := (htr.add htr').add (hasSum_xiStripEdgeWeight.mul_left 2)
  have htrace : xiRawReciprocalPowerTrace 2 = -deriv (logDeriv xi) 1 := by
    rw [deriv_logDeriv_xi_one_eq_neg_rawReciprocalPowerTrace_two, neg_neg]
  rw [htrace, deriv_logDeriv_xi_one_eq_completedZeta₀] at hsum
  convert hsum using 1
  · funext q
    exact xiStripEdgeWeight_sq_eq q
  · ring

end

end RHTower
