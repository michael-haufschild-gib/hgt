import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFourierDirichletValue

/-! The original diagonal Fourier source has its exact half four-completion value. -/
open Complex MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
open D4BMGlobalAngularResponse
noncomputable section

private theorem native_archimedean_value (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    8*Complex.Gammaℝ (2*s)*(((2*Real.pi:ℝ):ℂ)^(-s))*nativeBesselMellinFactor q s =
      Complex.Gammaℝ (s+2*center q)*Complex.Gammaℝ s^(2 : ℕ)*Complex.Gammaℝ (s-2*center q) := by
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2pi : ((2:ℂ)*(Real.pi:ℂ))^(-s) = (2:ℂ)^(-s)*(Real.pi:ℂ)^(-s) := by
    simpa using Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) Real.pi_pos.le (-s)
  have h2 : (2:ℂ)^(-s)*(2:ℂ)^(s-3) = 1/8 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),show -s+(s-3)=(-3:ℂ) by ring]
    have h := Complex.cpow_neg_eq_inv_pow_ofReal_pos (a := 2) (by norm_num : (0:ℝ)<2) (3:ℂ)
    norm_num at h ⊢
    exact h
  have hp : (Real.pi:ℂ)^(-s)*(Real.pi:ℂ)^(-s) =
      (Real.pi:ℂ)^(-(s+2*center q)/2)*((Real.pi:ℂ)^(-s/2))^(2 : ℕ)*(Real.pi:ℂ)^(-(s-2*center q)/2) := by
    rw [pow_two]
    repeat' rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  unfold nativeBesselMellinFactor
  rw [Complex.Gammaℝ,Complex.Gammaℝ,Complex.Gammaℝ,Complex.Gammaℝ]
  norm_num
  rw [show -(2*s)/2=-s by ring,show (s+2*center q)/2=s/2+center q by ring,
    show (s-2*center q)/2=s/2-center q by ring,h2pi]
  calc
    _ = (8*((2:ℂ)^(-s)*(2:ℂ)^(s-3)))*
        (((Real.pi:ℂ)^(-s)*(Real.pi:ℂ)^(-s))*
          (Complex.Gamma (s/2+center q)*Complex.Gamma (s/2)^(2 : ℕ)*Complex.Gamma (s/2-center q))) := by
      field_simp [hg]
    _ = ((Real.pi:ℂ)^(-s)*(Real.pi:ℂ)^(-s))*
          (Complex.Gamma (s/2+center q)*Complex.Gamma (s/2)^(2 : ℕ)*Complex.Gamma (s/2-center q)) := by
      rw [h2]
      ring
    _ = _ := by rw [hp]; ring

/-- The original half-square's diagonal Fourier contribution has the derived half four-Lambda value. -/
theorem nativeDiagonalPeriod_fourLambda (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re)
    (s : ℂ) (hs : 2 < s.re) :
    4*reflectedCompletedLambda (2*s)*
      (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))) =
        (reflectedCompletedLambda (s+2*center q)*reflectedCompletedLambda s^(2 : ℕ)*
          reflectedCompletedLambda (s-2*center q))/2 := by
  rw [nativeFourierMellin_lseries q s hs,nativeRamanujan_value q hq s hs]
  have hz : riemannZeta (2*s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  change 4*(Complex.Gammaℝ (2*s)*riemannZeta (2*s))*
    ((((2*Real.pi:ℝ):ℂ)^(-s)*nativeBesselMellinFactor q s)*
      (riemannZeta (s-2*center q)*riemannZeta s^(2 : ℕ)*riemannZeta (s+2*center q)/riemannZeta (2*s))) = _
  calc
    _ = (8*Complex.Gammaℝ (2*s)*(((2*Real.pi:ℝ):ℂ)^(-s))*nativeBesselMellinFactor q s)*
      (riemannZeta (s+2*center q)*riemannZeta s^(2 : ℕ)*riemannZeta (s-2*center q))/2 := by
      field_simp [hz]
      ring
    _ = _ := by
      rw [native_archimedean_value q s hs]
      unfold reflectedCompletedLambda
      ring

end
end RHTower.D4BMCuspProjection
