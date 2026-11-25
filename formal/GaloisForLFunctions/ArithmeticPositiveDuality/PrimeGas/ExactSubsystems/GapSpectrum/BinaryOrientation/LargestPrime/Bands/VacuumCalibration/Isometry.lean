import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.VacuumCalibration.Tilt

/-! # Isometric composition detected by an unscaled band vacuum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.VacuumCalibration

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

private theorem shifted (a : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => 1+a*h.val) criticalApproach (𝓝 1) := by
  have H : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have ht := (tendsto_const_nhds (x := (1:ℝ))).add ((H.mono_right nhdsWithin_le_nhds).const_mul a)
  simpa only [mul_zero,add_zero] using ht

/-- Below unit inverse temperature the escaping band is occupied with probability tending to one. -/
theorem below {c d s : ℝ} (hc : 0 < c) (hcd : c < d) (hs : s < 1) :
    Tendsto (fun h => vacuum c d h s) criticalApproach (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro y hy
    exact Eventually.of_forall fun h => hy.trans_le (vacuum_mem c d h s).1
  · intro y hy
    obtain ⟨a,ha⟩ := ((response_atBot hc hcd).eventually_lt_const hy).exists
    filter_upwards [(shifted a).eventually_const_lt hs,(drift_limit hc hcd a).eventually_lt_const ha] with h h1 h2
    exact ((vacuum_mono c d h) h1.le).trans_lt h2

/-- Above unit inverse temperature the escaping band is empty with probability tending to one. -/
theorem above {c d s : ℝ} (hc : 0 < c) (hcd : c < d) (hs : 1 < s) :
    Tendsto (fun h => vacuum c d h s) criticalApproach (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro y hy
    obtain ⟨a,ha⟩ := ((response_atTop hc hcd).eventually_const_lt hy).exists
    filter_upwards [(shifted a).eventually_lt_const hs,(drift_limit hc hcd a).eventually_const_lt ha] with h h1 h2
    exact h2.trans_le ((vacuum_mono c d h) h1.le)
  · intro y hy
    exact Eventually.of_forall fun h => ((vacuum_mem c d h s).2).trans_lt hy

theorem at_one {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun h => vacuum c d h 1) criticalApproach (𝓝 (c/d)) := by
  simpa only [zero_mul,add_zero,response_zero hc hcd.le] using drift_limit hc hcd 0

/-- A single normalized band vacancy has an interior limit precisely at isometric divisor splitting. -/
theorem split_isometric_iff_interior_vacuum {c d : ℝ} (hc : 0 < c) (hcd : c < d) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ∃ r ∈ Ioo (0:ℝ) 1, Tendsto (fun h => vacuum c d h (2*s.re)) criticalApproach (𝓝 r) := by
  letI := criticalApproach_neBot
  rw [split_isometric_iff]
  constructor
  · intro hs
    refine ⟨c/d,⟨div_pos hc (hc.trans hcd),(div_lt_one (hc.trans hcd)).mpr hcd⟩,?_⟩
    rw [show 2*s.re = 1 by rw [hs]; ring]
    exact at_one hc hcd
  · rintro ⟨r,hr,ht⟩
    rcases lt_trichotomy s.re (1/2) with hl | he | hg
    · have H := below hc hcd (show 2*s.re < 1 by linarith only [hl])
      exact False.elim (hr.1.ne' (tendsto_nhds_unique ht H))
    · exact he
    · have H := above hc hcd (show 1 < 2*s.re by linarith only [hg])
      exact False.elim (hr.2.ne (tendsto_nhds_unique ht H))

/-- Doubling the log-energy cutoff gives a fair empty/occupied bit exactly at isometric splitting. -/
theorem split_isometric_iff_half_vacuum {c : ℝ} (hc : 0 < c) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      Tendsto (fun h => vacuum c (2*c) h (2*s.re)) criticalApproach (𝓝 (1/2)) := by
  have hd : c < 2*c := by simpa only [two_mul] using lt_add_of_pos_right c hc
  constructor
  · intro h
    have hs := (split_isometric_iff s).mp h
    have he : c/(2*c) = 1/2 := by field_simp [hc.ne']
    rw [show 2*s.re = 1 by rw [hs]; ring,← he]
    exact at_one hc hd
  · intro h
    exact (split_isometric_iff_interior_vacuum hc hd s).mpr
      ⟨1/2,⟨half_pos zero_lt_one,half_lt_self zero_lt_one⟩,h⟩

#print axioms below
#print axioms above
#print axioms at_one
#print axioms split_isometric_iff_interior_vacuum
#print axioms split_isometric_iff_half_vacuum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.VacuumCalibration
