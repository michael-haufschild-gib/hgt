import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheOrderOfAbsoluteMertensMass
import GaloisForLFunctions.RHTower.ChronologicalMobiusHalfPrefixMoments
import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# First passage of the absolute Mertens mass

The least index at which the cumulative reciprocal Mertens mass reaches a
prescribed real level has logarithmic order 1/Θ. The overshoot tends to
zero in absolute size because the individual jumps tend to zero by the
prime number theorem.
-/

noncomputable section
open Filter Finset Topology
open _root_.RHTower
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem mass_reaches_level (t : ℝ) : ∃ N, t ≤ mertensAbelMass N := by
  have hz := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  obtain ⟨N,hN⟩ := (eventually_large_mertens_abel_mass (b:=0) le_rfl hz t).exists
  exact ⟨N,by simpa only [Real.rpow_zero,mul_one] using hN.le⟩

/-- First index at which the cumulative absolute mass reaches a level. -/
def mertensFirstPassage (t : ℝ) : ℕ := Nat.find (mass_reaches_level t)

theorem mertens_first_passage_le_iff (t : ℝ) (N : ℕ) :
    mertensFirstPassage t ≤ N ↔ t ≤ mertensAbelMass N :=
  ⟨fun h => (Nat.find_spec (mass_reaches_level t)).trans (mertens_abel_mass_mono h),
    fun h => Nat.find_min' (mass_reaches_level t) h⟩

theorem tendsto_mertens_first_passage : Tendsto mertensFirstPassage atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_gt_atTop (mertensAbelMass N)] with t ht
  exact (lt_of_not_ge (fun h => ht.not_ge ((mertens_first_passage_le_iff t N).mp h))).le

/-- The prime number theorem makes each reciprocal-mass jump vanish. -/
theorem mertens_mass_jump_vanishes :
    Tendsto (fun n : ℕ => ‖mobiusMertensPartialSum n‖/(n:ℝ)) atTop (𝓝 0) := by
  apply tendsto_abs_sum_moebius_div.congr
  intro n
  rw [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal,shiftedMertensReal_eq]
  have hI : Ioc 0 n = Icc 1 n := by
    ext k; simp only [mem_Ioc,mem_Icc]; omega
  rw [hI]

/-- First passage hits every large target with vanishing absolute overshoot. -/
theorem mertens_first_passage_overshoot :
    Tendsto (fun t : ℝ => mertensAbelMass (mertensFirstPassage t)-t) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (mertens_mass_jump_vanishes.comp tendsto_mertens_first_passage)
  · exact .of_forall fun t => sub_nonneg.mpr ((mertens_first_passage_le_iff _ _).mp le_rfl)
  · filter_upwards [tendsto_mertens_first_passage.eventually_ge_atTop 1] with t ht
    change mertensAbelMass (mertensFirstPassage t)-t ≤
      ‖mobiusMertensPartialSum (mertensFirstPassage t)‖/(mertensFirstPassage t:ℝ)
    cases h : mertensFirstPassage t with
    | zero => omega
    | succ n =>
      have hprev : mertensAbelMass n < t := lt_of_not_ge fun hle => by
        have hle' := (mertens_first_passage_le_iff t n).mpr hle
        omega
      simp only [mertensAbelMass,Finset.sum_range_succ,Nat.cast_succ]
      change mertensAbelMass n + _ - t ≤ _
      linarith only [hprev]

/-- Ordinary inverse exponent of the first-passage index on the real level scale. -/
theorem mertens_first_passage_log_order :
    Tendsto (fun t : ℝ => Real.log ((mertensFirstPassage t:ℝ)+1)/Real.log t)
      atTop (𝓝 (1/zetaZeroAbscissa)) := by
  have hΘ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  have herr : Tendsto (fun t : ℝ => Real.log 2/Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have htarg : Tendsto (fun t : ℝ => Real.log (1+mertensAbelMass (mertensFirstPassage t))/Real.log t)
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun t : ℝ => 1+Real.log 2/Real.log t) atTop (𝓝 1) by
        simpa only [add_zero] using herr.const_add 1)
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with t h
      have hreach := (mertens_first_passage_le_iff t _).mp le_rfl
      apply (le_div_iff₀ (Real.log_pos h)).mpr
      rw [one_mul]
      exact Real.log_le_log (zero_lt_one.trans h) (by linarith only [hreach])
    · filter_upwards [eventually_gt_atTop (2:ℝ),
        mertens_first_passage_overshoot.eventually_lt_const (by norm_num : (0:ℝ)<1)] with t h he
      have hlog := Real.log_pos (lt_trans (by norm_num : (1:ℝ)<2) h)
      have hle := Real.log_le_log (add_pos_of_pos_of_nonneg zero_lt_one (mertens_abel_mass_nonneg _))
        (show 1+mertensAbelMass (mertensFirstPassage t) ≤ 2*t by linarith only [he,h])
      rw [Real.log_mul (by norm_num) (by linarith only [h] : t≠0)] at hle
      apply (div_le_iff₀ hlog).mpr
      rw [add_mul,one_mul,div_mul_cancel₀ _ hlog.ne']
      linarith only [hle]
  have h := htarg.div (mertens_abel_mass_log_order.comp tendsto_mertens_first_passage) hΘ.ne'
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),tendsto_mertens_first_passage.eventually_ge_atTop 1] with t ht hn
  have hreach := (mertens_first_passage_le_iff t _).mp le_rfl
  have hM := Real.log_pos (show 1<1+mertensAbelMass (mertensFirstPassage t) by linarith only [ht,hreach])
  have hN := Real.log_pos (lt_add_of_pos_left 1 (Nat.cast_pos.mpr hn : 0<(mertensFirstPassage t:ℝ)))
  change (_/Real.log t)/(_/Real.log ((mertensFirstPassage t:ℝ)+1)) = _
  field_simp [hM.ne',hN.ne',(Real.log_pos ht).ne']

/-- Sampling the inverse at any prescribed sequence of levels tending
to infinity suffices to test the square-root boundary. -/
theorem rh_iff_mertens_first_passage_has_quadratic_order (u : ℕ → ℝ)
    (hu : Tendsto u atTop atTop) :
    RiemannHypothesis ↔ Tendsto (fun n =>
      Real.log ((mertensFirstPassage (u n):ℝ)+1)/Real.log (u n)) atTop (𝓝 2) := by
  rw [←zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  have h := mertens_first_passage_log_order.comp hu
  constructor
  · intro he
    rw [he] at h
    norm_num at h
    exact h
  · intro h₂
    have hΘ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
    have he := (div_eq_iff hΘ.ne').mp (tendsto_nhds_unique h h₂)
    linarith only [he]

#print axioms rh_iff_mertens_first_passage_has_quadratic_order
#print axioms mertens_mass_jump_vanishes
#print axioms mertens_first_passage_overshoot
#print axioms mertens_first_passage_log_order
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
