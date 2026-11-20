import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheOrderOfAbsoluteMertensMass
import Mathlib.Analysis.SpecificLimits.FloorPow

/-!
# Location of the reciprocal absolute Mertens mass

Put weight |M(k)|/k at index k and normalize by the total mass through
N. A power cutoff N^θ has probability N^(-(1-θ)Θ+o(1)). Thus on the
logarithmic position scale the mass concentrates at the upper endpoint,
even though the weights need not grow monotonically.
-/
noncomputable section
open Filter Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open _root_.RHTower

private theorem cutoff_tends_to_infinity : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

private theorem mass_tends_to_infinity : Tendsto mertensAbelMass atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hz := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  simpa only [Real.rpow_zero,mul_one] using (eventually_large_mertens_abel_mass le_rfl hz C).mono
    (fun _ h => h.le)

/-- Ordinary exponent of the unshifted mass, suitable for probability
ratios. Its strict positivity holds eventually by the power lower law. -/
theorem log_mertens_mass_order :
    Tendsto (fun N : ℕ => Real.log (mertensAbelMass N)/Real.log ((N:ℝ)+1))
      atTop (𝓝 zetaZeroAbscissa) := by
  have hc : Tendsto (fun N : ℕ => Real.log 2/Real.log ((N:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp cutoff_tends_to_infinity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto _ _ (𝓝 zetaZeroAbscissa) by simpa only [sub_zero] using mertens_abel_mass_log_order.sub hc)
    mertens_abel_mass_log_order
  · filter_upwards [mass_tends_to_infinity.eventually_ge_atTop 1,eventually_ge_atTop 1] with N h hN
    have hp := zero_lt_one.trans_le h
    have hX : 1<(N:ℝ)+1 := by linarith only [(Nat.one_le_cast (α:=ℝ)).mpr hN]
    have hl := Real.log_le_log (by positivity : 0<1+mertensAbelMass N)
      (show 1+mertensAbelMass N≤2*mertensAbelMass N by linarith only [h])
    rw [Real.log_mul (by norm_num) hp.ne'] at hl
    rw [←sub_div]
    exact div_le_div_of_nonneg_right (by linarith only [hl]) (Real.log_pos hX).le
  · filter_upwards [mass_tends_to_infinity.eventually_ge_atTop 1,eventually_ge_atTop 1] with N h hN
    apply div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le h) (le_add_of_nonneg_left zero_le_one))
    exact Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N))

/-- Any diverging sequence of inner cutoffs with a limiting logarithmic
position θ has exact lower-tail exponent (θ−1)Θ. -/
theorem relative_mertens_mass_exponent (K : ℕ → ℕ) (hK : Tendsto K atTop atTop) {θ : ℝ}
    (hk : Tendsto (fun N : ℕ => Real.log ((K N:ℝ)+1)/Real.log ((N:ℝ)+1)) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => Real.log (mertensAbelMass (K N)/mertensAbelMass N) /
      Real.log ((N:ℝ)+1)) atTop (𝓝 ((θ-1)*zetaZeroAbscissa)) := by
  have h := ((log_mertens_mass_order.comp hK).mul hk).sub log_mertens_mass_order
  rw [show zetaZeroAbscissa*θ-zetaZeroAbscissa = (θ-1)*zetaZeroAbscissa by ring] at h
  apply h.congr'
  filter_upwards [(mass_tends_to_infinity.comp hK).eventually_gt_atTop 0,
    mass_tends_to_infinity.eventually_gt_atTop 0,hK.eventually_ge_atTop 1,eventually_ge_atTop 1]
    with N hM hN hK1 hN1
  have hklog : 0<Real.log ((K N:ℝ)+1) := Real.log_pos
    (lt_add_of_pos_left 1 (Nat.cast_pos.mpr hK1))
  have hnlog : 0<Real.log ((N:ℝ)+1) := Real.log_pos
    (lt_add_of_pos_left 1 (Nat.cast_pos.mpr hN1))
  simp only [Function.comp_apply] at hM ⊢
  rw [Real.log_div hM.ne' hN.ne']
  change _ / Real.log ((K N:ℝ)+1) * (_ / Real.log ((N:ℝ)+1)) - _ / Real.log ((N:ℝ)+1) = _
  field_simp [hklog.ne',hnlog.ne']

/-- Logarithmic position of the natural integer power cutoff. -/
theorem log_position_of_power_cutoff {θ : ℝ} (hθ : 0<θ) :
    Tendsto (fun N : ℕ => Real.log ((⌊((N:ℝ)+1)^θ⌋₊:ℝ)+1) / Real.log ((N:ℝ)+1)) atTop (𝓝 θ) := by
  have hc : Tendsto (fun N : ℕ => Real.log 2/Real.log ((N:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp cutoff_tends_to_infinity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun N : ℕ => θ+Real.log 2/Real.log ((N:ℝ)+1)) atTop (𝓝 θ) by
      simpa only [add_zero] using hc.const_add θ)
  · filter_upwards [eventually_ge_atTop 1] with N hn
    have hx := lt_add_of_pos_left 1 (Nat.cast_pos.mpr hn : 0<(N:ℝ))
    have hp := zero_lt_one.trans hx
    have h := Real.log_le_log (Real.rpow_pos_of_pos hp θ) (Nat.lt_floor_add_one (((N:ℝ)+1)^θ)).le
    rw [Real.log_rpow hp] at h
    exact (le_div_iff₀ (Real.log_pos hx)).mpr (by linarith only [h])
  · filter_upwards [eventually_ge_atTop 1] with N hn
    have hx := lt_add_of_pos_left 1 (Nat.cast_pos.mpr hn : 0<(N:ℝ))
    have hp := zero_lt_one.trans hx
    let Y := ((N:ℝ)+1)^θ
    have hy : 1≤Y := Real.one_le_rpow hx.le hθ.le
    have h := Real.log_le_log (show 0<(⌊Y⌋₊:ℝ)+1 by positivity)
      (show (⌊Y⌋₊:ℝ)+1≤2*Y by linarith only [hy,Nat.floor_le (zero_le_one.trans hy)])
    rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hy).ne'] at h
    dsimp only [Y] at h
    rw [Real.log_rpow hp] at h
    apply (div_le_iff₀ (Real.log_pos hx)).mpr
    rw [add_mul,div_mul_cancel₀ _ (Real.log_pos hx).ne']
    linarith only [h]

/-- The mass proportion at position θ has logarithmic decay rate
(1−θ)Θ, including when only critical-line zeros exist. -/
theorem power_cutoff_mertens_mass_exponent {θ : ℝ} (hθ : 0<θ) :
    Tendsto (fun N : ℕ => Real.log (mertensAbelMass ⌊((N:ℝ)+1)^θ⌋₊/mertensAbelMass N) /
      Real.log ((N:ℝ)+1)) atTop (𝓝 ((θ-1)*zetaZeroAbscissa)) :=
  relative_mertens_mass_exponent _ (tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hθ).comp cutoff_tends_to_infinity)) (log_position_of_power_cutoff hθ)

/-- Every fixed proper fraction of the logarithmic index range carries
asymptotically zero of the normalized absolute mass. -/
theorem power_cutoff_mertens_mass_vanishes {θ : ℝ} (hθ : 0<θ) (hl : θ<1) :
    Tendsto (fun N : ℕ => mertensAbelMass ⌊((N:ℝ)+1)^θ⌋₊/mertensAbelMass N) atTop (𝓝 0) := by
  let c := (1-θ)*zetaZeroAbscissa/2
  have hΘ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  have hc : 0<c := half_pos (mul_pos (sub_pos.mpr hl) hΘ)
  have hc' : (θ-1)*zetaZeroAbscissa < -c := by dsimp only [c] at hc ⊢; linarith only [hc]
  have hK := tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hθ).comp cutoff_tends_to_infinity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_rpow_neg_atTop hc).comp cutoff_tends_to_infinity)
  · exact .of_forall fun N => div_nonneg (mertens_abel_mass_nonneg _) (mertens_abel_mass_nonneg _)
  · filter_upwards [(power_cutoff_mertens_mass_exponent hθ).eventually_lt_const hc',
      (mass_tends_to_infinity.comp hK).eventually_gt_atTop 0,
      mass_tends_to_infinity.eventually_gt_atTop 0,eventually_ge_atTop 1] with N h hM hN hn
    have hx := lt_add_of_pos_left 1 (Nat.cast_pos.mpr hn : 0<(N:ℝ))
    have hy := Real.rpow_pos_of_pos (zero_lt_one.trans hx) (-c)
    apply le_of_lt
    apply (Real.log_lt_log_iff (div_pos hM hN) hy).mp
    rw [Real.log_rpow (zero_lt_one.trans hx)]
    exact (div_lt_iff₀ (Real.log_pos hx)).mp h

#print axioms relative_mertens_mass_exponent
#print axioms power_cutoff_mertens_mass_exponent
#print axioms power_cutoff_mertens_mass_vanishes
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
