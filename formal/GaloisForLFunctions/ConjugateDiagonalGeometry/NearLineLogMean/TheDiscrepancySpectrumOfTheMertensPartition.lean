import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ThePowerSpectrumOfReciprocalMertensMass
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.IntegralMomentsOfTheEndpointDistribution

/-!
# Discrepancy of the cumulative Mertens partition

Put every normalized reciprocal Mertens weight at its cumulative right
endpoint. The uniform discrepancy is the first jump divided by total
mass. All finite integrated powers of the discrepancy are exactly the
next normalized moment divided by its order.
-/

noncomputable section
open Filter Topology Finset MeasureTheory
open scoped Interval
open _root_.RHTower GaloisForLFunctions.CumulativeQuadrature
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem mass_zero : mertensAbelMass 0=0 := by simp [mertensAbelMass]

private theorem mass_one : mertensAbelMass 1=1 := by
  simp [mertensAbelMass,←sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum,mobCoeff_one]

private theorem mass_positive {n : ℕ} (hn : 1≤n) : 0 < mertensAbelMass n := by
  have h := mertens_abel_mass_mono hn
  rw [mass_one] at h
  exact zero_lt_one.trans_le h

private theorem mass_step (j : ℕ) :
    mertensAbelMass (j+1)-mertensAbelMass j = reciprocalMertensWeight (j+1) := by
  simp only [mertensAbelMass,Finset.sum_range_succ,add_sub_cancel_left,
    reciprocalMertensWeight,Nat.cast_succ]

private theorem weight_le_one (k : ℕ) : reciprocalMertensWeight k≤1 := by
  rcases Nat.eq_zero_or_pos k with rfl|hk
  · simp [reciprocalMertensWeight]
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hk : 0<(k:ℝ))).mpr
    rw [one_mul,←sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum]
    exact (norm_sum_le _ _).trans ((sum_le_sum (s:=range k) (fun i _ => norm_mobCoeff_le (i+1))).trans_eq
      (by simp))

/-- Endpoint lag of every Mertens cell lies in [0,1]. The first cell
approaches the upper bound, independent of the integer cutoff. -/
theorem mertens_endpoint_lag_bounds {N : ℕ} {y : ℝ} (h0 : 0≤y) (hN : y ≤ mertensAbelMass N) :
    0≤endpointLag mertensAbelMass N y ∧ endpointLag mertensAbelMass N y≤1 := by
  rcases hN.eq_or_lt with he|hlt
  · subst y
    have hsum : rightSum mertensAbelMass (fun z => if z ≤ mertensAbelMass N then 1 else 0) N =
        mertensAbelMass N - mertensAbelMass 0 := by
      rw [rightSum,←Finset.sum_range_sub mertensAbelMass N]
      refine sum_congr rfl fun j hj => ?_
      rw [if_pos (mertens_abel_mass_mono (mem_range.mp hj)),mul_one]
    simp only [endpointLag,hsum,sub_self,le_refl,zero_le_one,and_self]
  · have exists_larger : ∃ k : ℕ, y < mertensAbelMass k := ⟨N,hlt⟩
    let k := Nat.find exists_larger
    have hk : y < mertensAbelMass k := Nat.find_spec exists_larger
    have hkN : k≤N := Nat.find_min' exists_larger hlt
    have hkpos : 0<k := by
      by_contra! he
      rw [Nat.eq_zero_of_le_zero he,mass_zero] at hk
      exact hk.not_ge h0
    let j := k-1
    have hsucc : j+1=k := by dsimp only [j]; omega
    have hjk : j<k := by omega
    have hj := le_of_not_gt (Nat.find_min exists_larger hjk)
    have hnext : y < mertensAbelMass (j+1) := hsucc.symm ▸ hk
    rw [endpointLag_on_cell mertens_abel_mass_mono (hjk.trans_le hkN) hj hnext]
    refine ⟨sub_nonneg.mpr hj,?_⟩
    exact (sub_le_sub_right hnext.le _).trans ((mass_step j).le.trans (weight_le_one _))

/-- The least uniform bound on the normalized CDF error is exactly
the reciprocal of the unnormalized total mass. -/
theorem exact_uniform_mertens_cdf_error {N : ℕ} (hn : 1≤N) (B : ℝ) :
    (∀ y ∈ Set.Icc 0 (mertensAbelMass N), endpointLag mertensAbelMass N y/mertensAbelMass N≤B) ↔
      1/mertensAbelMass N≤B := by
  have hp := mass_positive hn
  have hge := mertens_abel_mass_mono hn
  rw [mass_one] at hge
  constructor
  · intro h
    apply (div_le_iff₀ hp).mpr
    by_contra! hB
    obtain ⟨t,ht,ht1⟩ := exists_between (max_lt zero_lt_one hB)
    have ht0 := (le_max_left 0 _).trans ht.le
    have htB := (le_max_right 0 _).trans_lt ht
    have hg := (div_le_iff₀ hp).mp (h t ⟨ht0,ht1.le.trans hge⟩)
    have he := endpointLag_on_cell mertens_abel_mass_mono (i:=0) hn
      (by rwa [mass_zero] : mertensAbelMass 0≤t) (by simpa only [zero_add,mass_one] using ht1)
    rw [he,mass_zero,sub_zero] at hg
    exact htB.not_ge hg
  · intro h y hy
    exact (div_le_div_of_nonneg_right (mertens_endpoint_lag_bounds hy.1 hy.2).2 hp.le).trans h

/-- Kolmogorov distance from the uniform law in cumulative mass coordinates. -/
def uniformMertensEndpointError (N : ℕ) : ℝ :=
  sSup ((fun y => endpointLag mertensAbelMass N y/mertensAbelMass N) ''
    Set.Icc 0 (mertensAbelMass N))

theorem uniform_mertens_endpoint_error_eq {N : ℕ} (hn : 1≤N) :
    uniformMertensEndpointError N=1/mertensAbelMass N := by
  let S := (fun y => endpointLag mertensAbelMass N y/mertensAbelMass N) ''
    Set.Icc 0 (mertensAbelMass N)
  have ne : S.Nonempty := (Set.nonempty_Icc.mpr (mertens_abel_mass_nonneg N)).image _
  have hi : ∀ x ∈ S, x≤1/mertensAbelMass N := by
    rintro x ⟨y,hy,rfl⟩
    exact ((exact_uniform_mertens_cdf_error hn _).mpr le_rfl) y hy
  have hb : BddAbove S := ⟨_,hi⟩
  apply le_antisymm (csSup_le ne hi)
  apply (exact_uniform_mertens_cdf_error hn _).mp
  exact fun y hy => le_csSup hb ⟨y,hy,rfl⟩

/-- Ordinary exponent of the uniform discrepancy, including at the
critical-line boundary. -/
theorem uniform_mertens_endpoint_error_log_order :
    Tendsto (fun N : ℕ => Real.log (uniformMertensEndpointError N)/Real.log ((N:ℝ)+1)) atTop
      (𝓝 (-zetaZeroAbscissa)) := by
  have h := reciprocal_mertens_moment_log_order (q:=1) zero_lt_one
  have hΘ : 0≤zetaZeroAbscissa := (by norm_num : (0:ℝ)≤1/2).trans half_le_zetaZeroAbscissa
  rw [show 1+1*(zetaZeroAbscissa-1)=zetaZeroAbscissa by ring,max_eq_right hΘ] at h
  apply h.neg.congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [reciprocal_mertens_first_moment,uniform_mertens_endpoint_error_eq hn,one_div,Real.log_inv,neg_div]

/-- Integrated p-th power on the unit mass interval (before taking
the p-th root). -/
def normalizedMertensLagMoment (p : ℝ) (N : ℕ) :=
  (∫ y in 0..mertensAbelMass N, (endpointLag mertensAbelMass N y)^p)/(mertensAbelMass N)^(p+1)

theorem normalized_mertens_lag_eq_power_sum {p : ℝ} (hp : 0<p) (N : ℕ) :
    normalizedMertensLagMoment p N =
      (reciprocalMertensMoment (p+1) N/(mertensAbelMass N)^(p+1))/(p+1) := by
  have h := integral_endpoint_lag_rpow mertens_abel_mass_mono N hp
  rw [mass_zero] at h
  simp only [mass_step] at h
  rw [normalizedMertensLagMoment,h,reciprocalMertensMoment,_root_.RHTower.sum_Icc_eq_sum_range_shift]
  ring

/-- Ordinary decay exponent of every integrated CDF discrepancy. At
p=1 the rate is always N^(-1+o(1)), while p>1 can detect a zero
strictly to the right of the critical line. -/
theorem mertens_endpoint_error_log_spectrum {p : ℝ} (hp : 0<p) :
    Tendsto (fun N : ℕ => Real.log (normalizedMertensLagMoment p N)/Real.log ((N:ℝ)+1))
      atTop (𝓝 (max (-p) (-(p+1)*zetaZeroAbscissa))) := by
  have hq : 0<p+1 := by linarith only [hp]
  have h := normalized_reciprocal_mertens_moment_order hq
  rw [show 1-(p+1)= -p by ring] at h
  have hX : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log (p+1)/Real.log ((N:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hX)
  have hl := h.sub hc
  rw [sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  have hsum := zero_lt_one.trans_le (reciprocal_mertens_moment_one_le (p+1) hn)
  rw [normalized_mertens_lag_eq_power_sum hp,Real.log_div
    (div_pos hsum (Real.rpow_pos_of_pos (mass_positive hn) _)).ne' hq.ne',sub_div]

#print axioms uniform_mertens_endpoint_error_log_order
#print axioms exact_uniform_mertens_cdf_error
#print axioms normalized_mertens_lag_eq_power_sum
#print axioms mertens_endpoint_error_log_spectrum
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
