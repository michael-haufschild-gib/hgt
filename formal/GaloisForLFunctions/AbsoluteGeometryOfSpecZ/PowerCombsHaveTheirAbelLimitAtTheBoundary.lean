import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactDiscreteAbelMean
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanMellinIntegral
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceMellinIntegral
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZeroPairing
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros

/-!
# Power combs retain their Abel limit at the closed zero-width boundary

The exact finite comb identity is preserved by logarithmic Abel averaging.
The contact residue and the convergent nonprime terms then reconstruct
the reflected zero pairing, including parameters with boundary zeros.
-/

noncomputable section

open Complex Finset Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity SelbergClass.DegreeOne

/-- The actual zero width pays subpolynomial growth at its closed boundary. -/
theorem strictGrowth_powerCombTail_of_add_width_le_half
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) :
    _root_.HTGeometry.StrictNaturalPowerGrowth (powerCombTail a) 0 := by
  apply (powerCombTailGrowth_iff_zeroHalfPlane ha ha2 (le_refl (0 : ℝ))).mpr
  intro ρ hρ
  have hb := SquareRootThreshold.xiZeroHalfPlaneBound_zetaZeroWidth ρ hρ
  linarith only [hb, haw]

/-- Every positive logarithmic Abel parameter gives an integrable literal comb. -/
theorem integrableOn_powerCombLogarithmicAbelIntegrand
    {a ε : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) (hε : 0 < ε) :
    IntegrableOn (fun u => stepLaplaceIntegrand (powerCombTail a) 0 u *
      abelKernel 0 (ε : ℂ) u) (Ioi 0) :=
  integrableOn_logarithmicAbelIntegrand
    (strictGrowth_powerCombTail_of_add_width_le_half ha ha2 haw) hε

/-- The literal power comb has its canonical logarithmic Abel limit
throughout the closed zero-width range, whether or not the boundary is attained. -/
theorem tendsto_logarithmicAbelMean_powerCombTail_of_add_width_le_half
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) :
    Tendsto (logarithmicAbelMean (powerCombTail a)) (𝓝[>] 0) (𝓝 (powerTailZeroPairing a)) := by
  let E : ℕ → ℝ := fun N => (N : ℝ) ^ (2 * a - 1) * powerTailArchimedean a N -
    2 * tailRiemannSum (powerTailReferenceProfile a) N + powerTailCombRemainder a N
  let K₀ : ℝ := powerTailArchimedeanRowLimit a / (1 - 2 * a) -
    2 * (∫ t in Ioc (0 : ℝ) 1, powerTailReferenceProfile a t)
  have hE : Tendsto E atTop (𝓝 K₀) := by
    have hh := ((tendsto_normalized_powerTailArchimedean ha ha2).sub
      ((riemannOn_powerTailReferenceProfile ha ha2).2.const_mul 2)).add
        (tendsto_powerTailCombRemainder ha ha2)
    simpa only [add_zero] using hh
  have he (N : ℕ) (hN : 1 ≤ N) :
      powerCombTail a N = E N - 2 * normalizedPowerContacts a N := by
    rw [powerCombTail_eq_mellin_meshes a hN]
    dsimp only [E, normalizedPowerContacts]
    ring
  let B : ℂ := -deriv riemannZeta (1 - (a : ℂ)) / riemannZeta (1 - (a : ℂ)) -
    riemannZeta (1 - (a : ℂ))
  let K : ℂ := (K₀ : ℂ) - 2 * (B / ((1 - 2 * a : ℝ) : ℂ))
  have hmean := (tendsto_logarithmicAbelMean_of_tendsto hE).sub
    ((tendsto_logarithmicAbelMean_normalizedPowerContacts ha ha2 haw).const_mul (2 : ℂ))
  have hT : Tendsto (logarithmicAbelMean (powerCombTail a)) (𝓝[>] 0) (𝓝 K) := by
    apply hmean.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hh := logarithmicAbelMean_congr_pos he ε
    rw [logarithmicAbelMean_sub (strictPowerGrowth_zero_of_tendsto hE)
      ((strictGrowth_normalizedPowerContacts_of_add_width_le_half ha ha2 haw).const_mul 2) hε,
      logarithmicAbelMean_const_mul] at hh
    simpa only [Complex.ofReal_ofNat] using hh.symm
  have ha1 : a < 1 := by linarith only [ha2]
  have hθ : 1 - 2 * (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - 2 * a ≠ 0 by linarith only [ha2])
  have hθ' : 1 - (a : ℂ) * 2 ≠ 0 := by simpa only [mul_comm] using hθ
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hs0 : 1 - (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - a ≠ 0 by linarith only [ha1])
  have hs1 : 1 - (a : ℂ) ≠ 1 := by
    intro h
    exact ha0 (by linear_combination -h)
  have hre : 0 < (1 - (a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [ha1]
  have hζ : riemannZeta (1 - (a : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
        (show 0 < 1 - a by linarith only [ha2]) (show 1 - a < 1 by linarith only [ha])
  have hxi := ArithmeticCorrespondencePositivity.logDeriv_xi_eq_add hre hs1 hζ
  have hpoles : ∀ n : ℕ, (1 - (a : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hh := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hh
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [ha1, hh, hn]
  rw [BohrGeneratorAxis.logDeriv_GammaR _ hpoles] at hxi
  conv_rhs at hxi => rw [logDeriv_apply]
  have href := mul_referencePowerMellinIntegral_eq ha ha2
  have harch := ofReal_powerTailArchimedeanRowLimit ha ha1
  have hsplit : (1 - 2 * (a : ℂ)) * K =
      (powerTailArchimedeanRowLimit a : ℂ) - 2 * B -
        2 * ((1 - 2 * (a : ℂ)) *
          ((∫ t in Ioc (0 : ℝ) 1, powerTailReferenceProfile a t : ℝ) : ℂ)) := by
    dsimp only [K, K₀]
    push_cast
    field_simp [hθ, hθ']
    ring
  rw [href, harch] at hsplit
  have hmain : (1 - 2 * (a : ℂ)) * K =
      2 * logDeriv _root_.RHTower.xi (1 - (a : ℂ)) := by
    rw [hsplit, hxi]
    dsimp only [B]
    have hsub : 1 - (a : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [ha0, hs0, hsub, hζ]
    ring
  have hK : K = powerTailZeroPairing a := by
    apply mul_left_cancel₀ hθ
    rw [powerTailZeroPairing_eq_logDeriv ha2, hmain]
    field_simp [hθ, hθ']
  rwa [hK] at hT

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
