import GaloisForLFunctions.RHTower.ThetaCuspModularEnergyTube

/-! # Coupled compact coordinates for the actual even rank-four comparison -/
namespace RHTower
noncomputable section
open Set

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear

/-- The actual modular gap is trapped between two quadratic functions of the same drift. -/
theorem thetaCuspModularGapAmplitude_drift_tube {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    191/10-(12/5)*u x^2 ≤ a x ∧ a x ≤ 96/5-(4/3)*u x^2 := by
  have hl := thetaCuspModularGapAmplitude_energy_lower hx
  have hinit := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have hu := thetaCuspModularMassDrift_energy_lower hx
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 39/4) hx.1) hu 2
  have he := thetaCuspModularStrongEnergy_lt hx.1
  constructor <;> nlinarith [sq_nonneg x]

/-- Exact physical drift, gap and relative shear occupy one coupled algebraic tube. -/
theorem thetaCuspModularState_coupled_even_tube {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    0 ≤ u x ∧ u x ≤ 1 ∧
      191/10-(12/5)*u x^2 ≤ a x ∧ a x ≤ 96/5-(4/3)*u x^2 ∧
      u x ≤ w x ∧ w x ≤ (5/4)*u x := by
  have hb := thetaCuspModularState_energy_box hx
  have ha := thetaCuspModularGapAmplitude_drift_tube hx
  exact ⟨hb.1, hb.2.1, ha.1, ha.2, thetaCuspModularMassDrift_le_shear hx.1,
    thetaCuspModularTransverseShear_le_fiveFourths_drift hx⟩

/-- A unit-cube parametrization retains the correlation forced by the complete source orbit. -/
theorem exists_thetaCuspModularState_even_unit_coordinates {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    ∃ t v : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ v ∈ Icc (0 : ℝ) 1 ∧
      a x = 191/10-(12/5)*u x^2+t*(1/10+(16/15)*u x^2) ∧
      w x = u x*(1+v/4) := by
  obtain ⟨hu0, _, ha0, ha1, hw0, hw1⟩ := thetaCuspModularState_coupled_even_tube hx
  let t := (a x-(191/10-(12/5)*u x^2))/(1/10+(16/15)*u x^2)
  have hd : 0 < 1/10+(16/15)*u x^2 := by positivity
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr ha0) hd.le
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    linarith only [ha1]
  have hat : a x = 191/10-(12/5)*u x^2+t*(1/10+(16/15)*u x^2) := by
    dsimp [t]
    field_simp
    ring
  by_cases hz : u x = 0
  · refine ⟨t, 0, ⟨ht0, ht1⟩, by norm_num, hat, ?_⟩
    rw [hz]
    linarith only [hw0, hw1, hz]
  · have hup : 0 < u x := lt_of_le_of_ne hu0 (Ne.symm hz)
    let v := 4*(w x-u x)/u x
    have hv0 : 0 ≤ v := div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hw0)) hup.le
    have hv1 : v ≤ 1 := by
      apply (div_le_iff₀ hup).mpr
      linarith only [hw1]
    refine ⟨t, v, ⟨ht0, ht1⟩, ⟨hv0, hv1⟩, hat, ?_⟩
    dsimp [v]
    field_simp
    ring

end
end RHTower
