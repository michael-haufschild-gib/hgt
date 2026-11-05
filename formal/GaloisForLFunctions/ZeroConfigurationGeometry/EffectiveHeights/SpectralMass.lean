import GaloisForLFunctions.RHTower.WeilDeletionZeroSide
import GaloisForLFunctions.ZeroConfigurationGeometry.SquareRootInversion.SubSpacingLocalInversion

/-!
# Numerical spectral mass for the actual ζ camera

The certified reciprocal-square zero sum bounds the Lorentzian mass by
`33/100`. Multiplicity transport and extension by zero put the same bound
in the ambient signed-multiplicity interface used by the camera.
-/

open Complex Set Zeta23 RHTower
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry


/-- The total Lorentzian mass of the actual ζ spectrum has a numerical bound. -/
theorem zeta_lorentzian_mass_lt :
    (∑' z : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult z : ℝ) / (1 + Complex.normSq (gammaOf z))) < 33 / 100 := by
  have hs : Summable fun q : XiZeroCopy => 1 / ‖gammaOf (q.1 : ℂ)‖ ^ 2 := by
    simpa only [WeilDeletion.gammaOf_eq_xiSpectralPoint] using xiSpectralPoint_inv_sq_summable
  have h := WeilDeletion.carrier_tsum_le zetaSeam
    (fun z => 1 / ‖gammaOf z‖ ^ 2) (fun _ => by positivity) hs
    (fun z => (zetaZeroConfig.mult z : ℝ) / (1 + Complex.normSq (gammaOf z))) ?_
  · refine h.trans_lt ?_
    simpa only [WeilDeletion.gammaOf_eq_xiSpectralPoint] using
      WeilDeletion.tsum_inv_normSq_spectralPoint_lt
  · intro z
    have hn : 0 < ‖gammaOf (z : ℂ)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (WeilDeletion.gammaOf_ne_zero_of_nontrivialZero z.2))
    rw [Complex.normSq_eq_norm_sq, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le hn (by linarith only [])) (Nat.cast_nonneg _)

/-- The same bound in the ambient signed-multiplicity interface of the camera. -/
theorem zeta_empty_lorentzian_mass_lt :
    (∑' z : ℂ, ‖multDiff zetaZeroConfig emptyZeroConfig z‖ /
      (1 + Complex.normSq (gammaOf z))) < 33 / 100 := by
  classical
  have hterm (z : ℂ) : ‖multDiff zetaZeroConfig emptyZeroConfig z‖ /
      (1 + Complex.normSq (gammaOf z)) = zetaZeroConfig.carrier.indicator
        (fun w => (zetaZeroConfig.mult w : ℝ) / (1 + Complex.normSq (gammaOf w))) z := by
    rw [multDiff_emptyZeroConfig]
    by_cases hz : z ∈ zetaZeroConfig.carrier
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Complex.norm_natCast]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero, zero_div]
  simp_rw [hterm]
  rw [← tsum_subtype]
  exact zeta_lorentzian_mass_lt

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_lorentzian_mass_lt
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_empty_lorentzian_mass_lt
