import GaloisForLFunctions.RHTower.ThetaCuspDegreeTwelveFluxCofinal
import GaloisForLFunctions.RHTower.ThetaCuspNativeTwelfthJetLimit
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The Gaussian degree retained by a radius-polynomial center flux

The last odd-four border has Gaussian degree six, while its existing head
has degree at most five. Every fixed polynomial in the physical radius
times the lawful center flux has negligible derivative at degree six.
The exact positive sixth Gaussian moment therefore survives every such
attempt to flatten that border against a fixed head vector.

This excludes exact border flattening in this flux class. It neither
excludes general matrix-flux positivity nor proves the integrated sign.
-/

open Filter Topology Polynomial
namespace RHTower
noncomputable section

private theorem radius_polynomial_div_scale (P : Polynomial ℝ) :
    Tendsto (fun x : ℝ => P.eval (2*x) /
      thetaCuspSingleAtomReflectionScale 1 x) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atTop atTop := by
    simpa only [id_eq, mul_comm] using
      (tendsto_id.atTop_mul_const (show (0 : ℝ) < 2 by norm_num))
  have h := (P.tendsto_div_exp_atTop.comp ht).div_const Real.pi
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  ring

private theorem radius_polynomial_div_scale_pow (P : Polynomial ℝ) (k : ℕ) :
    Tendsto (fun x : ℝ => P.eval (2*x) /
      thetaCuspSingleAtomReflectionScale 1 x^(k+1)) atTop (𝓝 0) := by
  have h := (radius_polynomial_div_scale P).mul
    (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow k)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa only [zero_mul] using h).congr'
  filter_upwards with x
  simp only [pow_succ, inv_pow, div_eq_mul_inv, mul_inv_rev]
  ring

/-- A polynomial in the physical radius multiplying the unchanged center flux. -/
def thetaCuspRadiusPolynomialFlux (P : Polynomial ℝ) (a r : ℝ) : ℝ :=
  P.eval r * thetaCuspCenterCompensationFlux a r

/-- Every radius-polynomial flux derivative is negligible at the actual twelfth-jet scale. -/
theorem thetaCuspRadiusPolynomialFlux_deriv_scaled_six_tendsto_zero
    (P : Polynomial ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => deriv (thetaCuspRadiusPolynomialFlux P a) (2*x) /
      ((2*x)*Real.sinh (a*(2*x))*thetaCuspSourceTerm x 1^(2 : ℕ)*
        thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ))) atTop (𝓝 0) := by
  have hfirst := (radius_polynomial_div_scale_pow (X*P.derivative) 5).mul
    (thetaCuspFullSource_div_firstAtom_tendsto_one.pow 2)
  have hsecond := (radius_polynomial_div_scale P).mul
    (center_flux_deriv_scaled_five_tendsto_zero ha)
  have h := hfirst.add hsecond
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hr : 0 < 2*x := by positivity
  have hs : Real.sinh (a*(2*x)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos ha hr)).ne'
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hder : deriv (thetaCuspRadiusPolynomialFlux P a) (2*x) =
      P.derivative.eval (2*x)*thetaCuspCenterCompensationFlux a (2*x) +
        P.eval (2*x)*deriv (thetaCuspCenterCompensationFlux a) (2*x) := by
    exact ((P.hasDerivAt (2*x)).mul
      (hasDerivAt_thetaCuspCenterCompensationFlux a (2*x))).deriv.trans
        (by rw [(hasDerivAt_thetaCuspCenterCompensationFlux a (2*x)).deriv])
  rw [hder]
  unfold thetaCuspCenterCompensationFlux
  simp only [show 2*x/2 = x by ring]
  field_simp [hr.ne', hs, hf, hq]
  ring

private theorem lower_jet_scaled_six (k : Fin 6) :
    Tendsto (fun x : ℝ =>
      ((-1 : ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) x) /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)))
      atTop (𝓝 0) := by
  have hc : ∃ c : ℝ, Tendsto (thetaCuspNativeScaledEvenJet k.val) atTop (𝓝 c) := by
    fin_cases k
    · exact ⟨1, thetaCuspNativeScaledEvenJet_zero_tendsto⟩
    · exact ⟨8, thetaCuspNativeScaledEvenJet_one_tendsto⟩
    · exact ⟨192, thetaCuspNativeScaledEvenJet_two_tendsto⟩
    · exact ⟨7680, thetaCuspNativeScaledEvenJet_three_tendsto⟩
    · exact ⟨430080, thetaCuspNativeScaledEvenJet_four_tendsto⟩
    · exact ⟨30965760, thetaCuspNativeScaledEvenJet_five_tendsto⟩
  obtain ⟨c, hc⟩ := hc
  have hk : 6-k.val ≠ 0 := by omega
  have hpow : Tendsto (fun x : ℝ =>
      (thetaCuspSingleAtomReflectionScale 1 x)⁻¹^(6-k.val)) atTop (𝓝 0) := by
    simpa only [zero_pow hk] using
      thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow (6-k.val)
  have h := hc.mul hpow
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  have hdegrees : k.val+(6-k.val) = 6 := by omega
  have hscale : thetaCuspSingleAtomReflectionScale 1 x^k.val *
      thetaCuspSingleAtomReflectionScale 1 x^(6-k.val) =
        thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ) := by
    rw [← pow_add, hdegrees]
  unfold thetaCuspNativeScaledEvenJet
  rw [← hscale]
  field_simp [hq, hf]

/-- Actual degree-six border after any fixed lower-jet combination and polynomial center flux. -/
def thetaCuspPolynomialFluxBorderResidual
    (P : Polynomial ℝ) (a : ℝ) (v : Fin 6 → ℝ) (x : ℝ) : ℝ :=
  thetaCuspNativeReflectionJet 12 x -
    ∑ k : Fin 6, v k*((-1 : ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) x) -
    deriv (thetaCuspRadiusPolynomialFlux P a) (2*x) / ((2*x)*Real.sinh (a*(2*x)))

/-- Positive survivor: the complete sixth Gaussian moment is invariant under these changes. -/
theorem thetaCuspPolynomialFluxBorderResidual_scaled_tendsto
    (P : Polynomial ℝ) {a : ℝ} (ha : 0 < a) (v : Fin 6 → ℝ) :
    Tendsto (fun x : ℝ => thetaCuspPolynomialFluxBorderResidual P a v x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)))
      atTop (𝓝 2724986880) := by
  have hsum := tendsto_finsetSum Finset.univ
    (fun k _ => (lower_jet_scaled_six k).const_mul (v k))
  have h := (thetaCuspNativeScaledEvenJet_six_tendsto.sub hsum).sub
    (thetaCuspRadiusPolynomialFlux_deriv_scaled_six_tendsto_zero P ha)
  apply (show Tendsto _ atTop (𝓝 (2724986880 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  simp only [thetaCuspPolynomialFluxBorderResidual, thetaCuspNativeScaledEvenJet,
    sub_div, Finset.sum_div, mul_div_assoc, div_div]
  norm_num
  ring

/-- The retained border is strictly positive on a cofinal physical ray. -/
theorem thetaCuspPolynomialFluxBorderResidual_eventually_pos
    (P : Polynomial ℝ) {a : ℝ} (ha : 0 < a) (v : Fin 6 → ℝ) :
    ∀ᶠ x : ℝ in atTop, 0 < thetaCuspPolynomialFluxBorderResidual P a v x := by
  have hp := (thetaCuspPolynomialFluxBorderResidual_scaled_tendsto P ha v).eventually
    (eventually_gt_nhds (show (0 : ℝ) < 2724986880 by norm_num))
  filter_upwards [hp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hd : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*
      thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ) := by
    have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num : 0 < (1 : ℕ))
    have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    positivity
  exact (div_pos_iff_of_pos_right hd).mp hx

/-- No exact cofinal border flattening is possible using this class of radius-polynomial fluxes. -/
theorem thetaCuspPolynomialFluxBorderResidual_not_eventually_zero
    (P : Polynomial ℝ) {a : ℝ} (ha : 0 < a) (v : Fin 6 → ℝ) :
    ¬ ∀ᶠ x : ℝ in atTop, thetaCuspPolynomialFluxBorderResidual P a v x = 0 := by
  intro hz
  obtain ⟨x, hx, hzero⟩ :=
    ((thetaCuspPolynomialFluxBorderResidual_eventually_pos P ha v).and hz).exists
  exact (ne_of_gt hx) hzero

end
end RHTower
