import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactAbelIntegrability
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactAbelMean
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.HolomorphicContactSymbolsExcludeInteriorZeros

/-!
# Absolute critical-comb Abel integrability detects RH

Under RH the literal critical comb has every positive power bound, hence
every positively damped logarithmic integral converges absolutely.
Conversely, these integrals produce a holomorphic contact transform on
the right half-plane. An off-line zero reflected rightward would give it
a nonzero interior pole.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity

/-- A right-hand zero prevents the critical comb's absolute logarithmic
Abel integrals from existing for all positive damping parameters. -/
theorem not_logarithmicAbelIntegrable_criticalPowerComb_of_right_zero
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) :
    ¬ LogarithmicAbelIntegrable (powerCombTail (1 / 2)) := by
  intro hc
  apply holomorphic_contact_symbol_excludes_interior_zero
    (a := 1 / 2) (by norm_num) (by norm_num)
    (F := oneSidedStepMellin (powerContactPrefix (1 / 2)))
    (by simpa using differentiableOn_criticalContactIntegral_of_abelIntegrable hc)
    (fun s hs => by simpa [criticalPowerContactFactor] using
      oneSidedStepMellin_criticalPowerContacts_initial hs) hzero
  simpa using hre

/-- Every positive absolute logarithmic Abel integral of the critical
literal comb exists exactly under RH. -/
theorem logarithmicAbelIntegrable_criticalPowerComb_iff_rh :
    LogarithmicAbelIntegrable (powerCombTail (1 / 2)) ↔ RiemannHypothesis := by
  constructor
  · intro hc
    apply SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
    apply le_antisymm _ SquareRootThreshold.zetaZeroWidth_nonneg
    apply (SquareRootThreshold.zetaZeroWidth_le_iff_re_le (le_refl (0 : ℝ))).mpr
    intro ρ hρ
    have hzero : riemannZeta ρ = 0 := hρ.1
    by_contra hle
    have hgt : 1 / 2 < ρ.re := by simpa only [add_zero] using not_le.mp hle
    exact not_logarithmicAbelIntegrable_criticalPowerComb_of_right_zero hzero hgt hc
  · intro hRH
    exact logarithmicAbelIntegrable_of_strictGrowth
      (strictGrowth_criticalPowerCombTail_iff_rh.mpr hRH)

/-- The elementary finite part minus twice the regularized contact value. -/
def criticalPowerCombAbelLimit : ℂ :=
  (criticalPowerCombElementaryLimit : ℂ) - 2 * deriv criticalPowerContactFactor 0

/-- Under RH, the critical comb has a finite logarithmic Abel limit even
though its ordinary limit does not exist. -/
theorem tendsto_logarithmicAbelMean_criticalPowerComb_of_rh
    (hRH : RiemannHypothesis) :
    Tendsto (logarithmicAbelMean (powerCombTail (1 / 2)))
      (𝓝[>] 0) (𝓝 criticalPowerCombAbelLimit) := by
  have hE := strictPowerGrowth_zero_of_tendsto tendsto_criticalPowerCombElementaryRemainder
  have hg := strictGrowth_criticalHarmonicContacts_iff_rh.mpr hRH
  have hlim := (tendsto_logarithmicAbelMean_of_tendsto
    tendsto_criticalPowerCombElementaryRemainder).sub
      ((tendsto_logarithmicAbelMean_criticalHarmonicContacts_of_rh hRH).const_mul (2 : ℂ))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [logarithmicAbelMean_congr_pos
    (fun N hN => powerCombTail_half_eq_elementary_sub_contacts hN) ε,
    logarithmicAbelMean_sub hE (hg.const_mul 2) hε,
    logarithmicAbelMean_const_mul]
  norm_num only [ofReal_ofNat]

/-- Whenever every positive absolute logarithmic Abel integral exists,
its limit is forced to the same explicit finite part. -/
theorem tendsto_logarithmicAbelMean_criticalPowerComb_of_integrable
    (hI : LogarithmicAbelIntegrable (powerCombTail (1 / 2))) :
    Tendsto (logarithmicAbelMean (powerCombTail (1 / 2)))
      (𝓝[>] 0) (𝓝 criticalPowerCombAbelLimit) :=
  tendsto_logarithmicAbelMean_criticalPowerComb_of_rh
    (logarithmicAbelIntegrable_criticalPowerComb_iff_rh.mp hI)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
