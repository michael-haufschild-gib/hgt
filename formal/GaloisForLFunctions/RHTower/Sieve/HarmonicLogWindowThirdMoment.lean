import GaloisForLFunctions.RHTower.Sieve.HarmonicLogMomentAsymptotics

open Finset MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

theorem three_le_log_of_sixtyFour_le {x : ℝ} (hx : 64 ≤ x) :
    3 ≤ Real.log x := by
  have hlog8 : 2 ≤ Real.log (8 : ℝ) := RHTower.two_le_log_of_eight_le (by norm_num)
  have hlog64 : Real.log (64 : ℝ) = Real.log 8 + Real.log 8 := by
    rw [show (64 : ℝ) = 8 * 8 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hmono : Real.log (64 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  linarith

theorem antitoneOn_logPowDivId_three :
    AntitoneOn (RHTower.logPowDivId 3) (Set.Ici 64) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (64 : ℝ))
  · intro x hx
    have hx64 : (64 : ℝ) ≤ x := hx
    exact (RHTower.hasDerivAt_logPowDivId 3 (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx64 : (64 : ℝ) < x := hx
    exact (RHTower.hasDerivAt_logPowDivId 3 (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx64 : (64 : ℝ) ≤ x := le_of_lt hx
    have hlog : 3 ≤ Real.log x := three_le_log_of_sixtyFour_le hx64
    rw [(RHTower.hasDerivAt_logPowDivId 3 (by linarith)).deriv]
    rw [RHTower.derivLogPowDivId]
    norm_num
    have hnum : 3 * Real.log x ^ 2 - Real.log x ^ 3 ≤ 0 := by
      have hsquare : 0 ≤ Real.log x ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hsquare (sub_nonneg.mpr hlog)]
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg x)

theorem abs_harmonicLogWindowMoment_three_sub_integral_le
    {A B : ℕ} (hA : 64 ≤ A) (hAB : A ≤ B) :
    |harmonicLogWindowMoment 3 A B -
        ∫ x in (A + 1 : ℕ)..(B + 1 : ℕ), RHTower.logPowDivId 3 x| ≤
      RHTower.logPowDivId 3 (A + 1 : ℕ) -
        RHTower.logPowDivId 3 (B + 1 : ℕ) := by
  have hanti : AntitoneOn (RHTower.logPowDivId 3)
      (Set.Icc ((A + 1 : ℕ) : ℝ) (((A + 1 : ℕ) : ℝ) + (B - A : ℕ))) :=
    antitoneOn_logPowDivId_three.mono (fun x hx => by
      show (64 : ℝ) ≤ x
      have hAreal : (64 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      push_cast at hx
      exact hAreal.trans (by linarith [hx.1]))
  have h := HTGeometry.abs_sum_sub_integral_le_of_antitoneOn hanti
  rw [harmonicLogWindowMoment, Finset.Ioc_eq_Ico,
    Finset.sum_Ico_eq_sum_range]
  have hsubNat : B + 1 - (A + 1) = B - A := by omega
  rw [hsubNat]
  have hend : (((A + 1 : ℕ) : ℝ) + ((B - A : ℕ) : ℝ)) = ((B + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hAB]
    push_cast
    ring
  rw [← hend]
  simpa only [RHTower.logPowDivId, Nat.cast_add, Nat.cast_one] using h

/-- Quartic-log main term for the third harmonic logarithmic window moment. -/
theorem abs_harmonicLogWindowMoment_three_sub_quartic_le
    {A B : ℕ} (hA : 64 ≤ A) (hAB : A ≤ B) :
    |harmonicLogWindowMoment 3 A B -
        (Real.log (B + 1 : ℕ) ^ 4 / 4 - Real.log (A + 1 : ℕ) ^ 4 / 4)| ≤
      RHTower.logPowDivId 3 (A + 1 : ℕ) -
        RHTower.logPowDivId 3 (B + 1 : ℕ) := by
  have hab : (((A + 1 : ℕ) : ℝ)) ≤ (((B + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hAB 1
  have hprim :
      Real.log (B + 1 : ℕ) ^ 4 / 4 - Real.log (A + 1 : ℕ) ^ 4 / 4 =
        harmonicLogMomentPrimitive 3 (B + 1 : ℕ) -
          harmonicLogMomentPrimitive 3 (A + 1 : ℕ) := by
    norm_num [harmonicLogMomentPrimitive]
  rw [hprim]
  rw [← intervalIntegral_logPowDivId 3 (by positivity) hab]
  exact abs_harmonicLogWindowMoment_three_sub_integral_le hA hAB

/-- The third harmonic logarithmic prefix differs from its quartic main term by one fixed
constant beyond the monotonicity threshold. -/
theorem exists_abs_harmonicLogWindowMoment_three_zero_sub_quartic_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 64 ≤ N →
      |harmonicLogWindowMoment 3 0 N - Real.log (N + 1 : ℕ) ^ 4 / 4| ≤ C := by
  let C : ℝ :=
    |harmonicLogWindowMoment 3 0 64 - Real.log (65 : ℕ) ^ 4 / 4| +
      RHTower.logPowDivId 3 65
  refine ⟨C, by
    dsimp [C]
    exact add_nonneg (abs_nonneg _) (by
      rw [RHTower.logPowDivId]
      positivity), ?_⟩
  intro N hN
  have hsplit := harmonicLogWindowMoment_add 3 (A := 0) (B := 64) (C := N)
    (by norm_num) hN
  have htail := abs_harmonicLogWindowMoment_three_sub_quartic_le
    (A := 64) (B := N) (by norm_num) hN
  have hendNonneg : 0 ≤ RHTower.logPowDivId 3 (N + 1 : ℕ) := by
    rw [RHTower.logPowDivId]
    positivity
  have htail' :
      |harmonicLogWindowMoment 3 64 N -
          (Real.log (N + 1 : ℕ) ^ 4 / 4 - Real.log (65 : ℕ) ^ 4 / 4)| ≤
        RHTower.logPowDivId 3 65 :=
    htail.trans (sub_le_self _ hendNonneg)
  calc
    |harmonicLogWindowMoment 3 0 N - Real.log (N + 1 : ℕ) ^ 4 / 4| =
        |(harmonicLogWindowMoment 3 0 64 - Real.log (65 : ℕ) ^ 4 / 4) +
          (harmonicLogWindowMoment 3 64 N -
            (Real.log (N + 1 : ℕ) ^ 4 / 4 - Real.log (65 : ℕ) ^ 4 / 4))| := by
      rw [← hsplit]
      ring_nf
    _ ≤ |harmonicLogWindowMoment 3 0 64 - Real.log (65 : ℕ) ^ 4 / 4| +
        |harmonicLogWindowMoment 3 64 N -
          (Real.log (N + 1 : ℕ) ^ 4 / 4 - Real.log (65 : ℕ) ^ 4 / 4)| :=
      abs_add_le _ _
    _ ≤ C := by
      dsimp [C]
      exact add_le_add le_rfl htail'

/-- Third harmonic logarithmic moment at a fixed dilation has coefficient `1/4`. -/
theorem tendsto_harmonicLogWindowMoment_three_natDiv_div_log_fourth_quarter
    {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      harmonicLogWindowMoment 3 0 (N / c) / Real.log N ^ 4)
      atTop (𝓝 (1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_abs_harmonicLogWindowMoment_three_zero_sub_quartic_le
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (n := 4) (by norm_num)).comp hlog
  have herr : Tendsto (fun N : ℕ =>
      (harmonicLogWindowMoment 3 0 (N / c) -
        Real.log (N / c + 1 : ℕ) ^ 4 / 4) / Real.log N ^ 4)
      atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ => C / Real.log N ^ 4)
        atTop (𝓝 0) := hscale.const_div_atTop C
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (64 * c), eventually_ge_atTop 2] with N hNc hN2
    have hdiv : 64 ≤ N / c := (Nat.le_div_iff_mul_le hc).mpr hNc
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlogpos 4)]
    exact div_le_div_of_nonneg_right (hbound (N / c) hdiv)
      (pow_nonneg hlogpos.le 4)
  have hratio := tendsto_log_natDiv_add_one_div_log_one hc
  have hmain : Tendsto (fun N : ℕ =>
      (Real.log (N / c + 1 : ℕ) ^ 4 / 4) / Real.log N ^ 4)
      atTop (𝓝 (1 / 4 : ℝ)) := by
    have h := (hratio.pow 4).const_mul (1 / 4 : ℝ)
    simpa only [one_pow, mul_one] using h.congr' (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlogN : Real.log (N : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hN)).ne'
      field_simp [hlogN])
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlogN]
  ring

end


end RHTower.Sieve
