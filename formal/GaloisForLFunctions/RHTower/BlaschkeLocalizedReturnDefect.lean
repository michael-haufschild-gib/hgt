import GaloisForLFunctions.RHTower.BlaschkeLocalizedUpperReturnClock

/-!
# Target calibration for the Blaschke return clock

The exact constructive defect is bounded by a linear prefactor times
`exp (-L)`. This proves that changing from water level to physical
coherence accuracy shifts logarithmic depth only sublinearly.
-/

noncomputable section

namespace RHTower

/-- Linear prefactor controlling the exact active-water defect. -/
def blaschkeReturnDefectLinearConstant (a : ℝ) : ℝ :=
  1 +
    (1 + |blaschkeSpectralOffset a|) /
      blaschkeSpectralSlope a +
    2 / (1 - a ^ (2 : ℕ))

theorem blaschkeActiveWaterTail_le_exp_neg_div
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ} (hLtail : blaschkeSpectralOffset a ≤ L) :
    (1 - a ^ (2 : ℕ)) *
        (a ^ (2 : ℕ)) ^ (blaschkeActiveTailRadius a L + 1) ≤
      Real.exp (-L) / (1 - a ^ (2 : ℕ)) := by
  let R := blaschkeActiveTailRadius a L
  have hbase : 0 < 1 - a ^ (2 : ℕ) := by nlinarith
  have hpositive :
      0 < blaschkeLocalizedWeight a ((R + 1) + 1) :=
    blaschkeLocalizedWeight_succ_pos a ha0 ha1 (R + 1)
  have hdepth :
      L < blaschkeSpectralDepth a (R + 1) := by
    have hnot :
        ¬ blaschkeSpectralDepth a (R + 1) ≤ L := by
      rw [blaschkeSpectralDepth_le_iff_le_activeTailRadius
        a ha0 ha1 hLtail]
      dsimp only [R]
      omega
    exact lt_of_not_ge hnot
  have hfirst :
      blaschkeLocalizedWeight a ((R + 1) + 1) <
        Real.exp (-L) := by
    calc
      blaschkeLocalizedWeight a ((R + 1) + 1) =
          Real.exp
            (-blaschkeSpectralDepth a (R + 1)) := by
        rw [blaschkeSpectralDepth, neg_neg,
          Real.exp_log hpositive]
      _ < Real.exp (-L) := by
        exact Real.exp_lt_exp.mpr (by linarith)
  have htailIdentity :
      (1 - a ^ (2 : ℕ)) * (a ^ (2 : ℕ)) ^ (R + 1) =
        blaschkeLocalizedWeight a ((R + 1) + 1) /
          (1 - a ^ (2 : ℕ)) := by
    rw [blaschkeLocalizedWeight_succ]
    field_simp [hbase.ne']
  rw [htailIdentity]
  exact (div_lt_div_iff_of_pos_right hbase).2 hfirst |>.le

theorem blaschkeActiveWaterReturnDefect_linear_exp_bound
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ}
    (hLtail : blaschkeSpectralOffset a ≤ L)
    (hLnonneg : 0 ≤ L) :
    blaschkeActiveWaterReturnDefect a L ≤
      blaschkeReturnDefectLinearConstant a *
        (1 + L) * Real.exp (-L) := by
  let rho := blaschkeSpectralSlope a
  let c := blaschkeSpectralOffset a
  let R : ℝ := (blaschkeActiveTailRadius a L : ℝ)
  have hrho : 0 < rho := by
    simpa only [rho] using blaschkeSpectralSlope_pos a ha0 ha1
  have hbase : 0 < 1 - a ^ (2 : ℕ) := by nlinarith
  have hR :=
    (blaschkeActiveTailRadius_bracket
      a ha0 ha1 hLtail).1
  have hRle : R ≤ (L - c) / rho := by
    apply (le_div_iff₀ hrho).2
    simpa only [R, rho, c, mul_comm] using hR
  have habs : -c ≤ |c| := neg_le_abs c
  have hactiveCoeff :
      R + 1 ≤
        (1 + (1 + |c|) / rho) * (1 + L) := by
    have hA : 0 ≤ (1 + |c|) / rho := by positivity
    have hAL : 0 ≤ ((1 + |c|) / rho) * L :=
      mul_nonneg hA hLnonneg
    have hinv : 0 < 1 / rho := by positivity
    have hmid :
        (L - c) / rho ≤ (L + |c|) / rho := by
      apply (div_le_div_iff_of_pos_right hrho).2
      linarith
    have hRmid : R + 1 ≤ (L + |c|) / rho + 1 := by
      simpa only [add_comm] using
        add_le_add_right (hRle.trans hmid) 1
    have hgap :
        0 ≤ L + 1 / rho + (|c| / rho) * L := by
      have habsDiv : 0 ≤ |c| / rho := by positivity
      positivity
    calc
      R + 1 ≤ (L + |c|) / rho + 1 := hRmid
      _ ≤ (1 + (1 + |c|) / rho) * (1 + L) := by
        have heq :
            (1 + (1 + |c|) / rho) * (1 + L) -
                ((L + |c|) / rho + 1) =
              L + 1 / rho + (|c| / rho) * L := by
          ring
        linarith
  have hactive :
      (R + 1) * Real.exp (-L) ≤
        (1 + (1 + |c|) / rho) * (1 + L) *
          Real.exp (-L) :=
    mul_le_mul_of_nonneg_right hactiveCoeff (Real.exp_pos _).le
  have htail :=
    blaschkeActiveWaterTail_le_exp_neg_div
      a ha0 ha1 hLtail
  have htailScaled :
      2 * ((1 - a ^ (2 : ℕ)) *
          (a ^ (2 : ℕ)) ^ (blaschkeActiveTailRadius a L + 1)) ≤
        (2 / (1 - a ^ (2 : ℕ))) * (1 + L) *
          Real.exp (-L) := by
    have htwo := mul_le_mul_of_nonneg_left htail
      (by norm_num : (0 : ℝ) ≤ 2)
    have hone : 1 ≤ 1 + L := by linarith
    calc
      2 * ((1 - a ^ (2 : ℕ)) *
          (a ^ (2 : ℕ)) ^ (blaschkeActiveTailRadius a L + 1)) ≤
          2 * (Real.exp (-L) / (1 - a ^ (2 : ℕ))) := htwo
      _ ≤ (2 / (1 - a ^ (2 : ℕ))) * (1 + L) *
          Real.exp (-L) := by
        have hcoef : 0 ≤ 2 / (1 - a ^ (2 : ℕ)) := by positivity
        have hfactor :=
          mul_le_mul_of_nonneg_left hone hcoef
        calc
          2 * (Real.exp (-L) / (1 - a ^ (2 : ℕ))) =
              (2 / (1 - a ^ (2 : ℕ))) * 1 * Real.exp (-L) := by
            ring
          _ ≤ (2 / (1 - a ^ (2 : ℕ))) * (1 + L) *
              Real.exp (-L) :=
            mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
  have hactive' :
      (((blaschkeActiveTailRadius a L + 1 : ℕ) : ℝ)) *
          Real.exp (-L) ≤
        (1 + (1 + |blaschkeSpectralOffset a|) /
            blaschkeSpectralSlope a) * (1 + L) *
          Real.exp (-L) := by
    simpa only [R, Nat.cast_add, Nat.cast_one, rho, c] using hactive
  rw [blaschkeActiveWaterReturnDefect]
  rw [blaschkeReturnDefectLinearConstant]
  calc
    (((blaschkeActiveTailRadius a L + 1 : ℕ) : ℝ)) *
        Real.exp (-L) +
        2 * ((1 - a ^ (2 : ℕ)) *
          (a ^ (2 : ℕ)) ^ (blaschkeActiveTailRadius a L + 1)) ≤
      (1 + (1 + |blaschkeSpectralOffset a|) /
          blaschkeSpectralSlope a) * (1 + L) *
          Real.exp (-L) +
        (2 / (1 - a ^ (2 : ℕ))) * (1 + L) *
          Real.exp (-L) :=
      add_le_add hactive' htailScaled
    _ =
      (1 + (1 + |blaschkeSpectralOffset a|) /
          blaschkeSpectralSlope a +
        2 / (1 - a ^ (2 : ℕ))) *
          (1 + L) * Real.exp (-L) := by ring

end RHTower
