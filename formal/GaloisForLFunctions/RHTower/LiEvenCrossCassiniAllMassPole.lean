import GaloisForLFunctions.RHTower.LiEvenCrossCassiniLogMassPole
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# Retained Cassini poles at every positive mass

Hardy's unbounded real Xi zeros provide squared nodes beyond any prescribed mass scale.
At such a node, logarithmic reflection lies in the zero-free source disk, so the actual
even Cassini current retains its exact cubic pole.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Positive logarithmic mass, with no interior-window restriction. -/
abbrev LiEvenCrossPositiveMass := {v : ℝ // 0 < v}

/-- Actual squared Xi nodes have unbounded norm, unconditionally. -/
theorem exists_xiSquaredNode_norm_gt (B : ℝ) :
    ∃ q : XiZeroCopy, B < ‖xiSquaredNode q‖ := by
  obtain ⟨t, ht, hz⟩ := exists_Xi_zero_gt (max B 1)
  have hBt : B < t := lt_of_le_of_lt (le_max_left B 1) ht
  have h1t : 1 < t := lt_of_le_of_lt (le_max_right B 1) ht
  have htpos : 0 < t := lt_trans zero_lt_one h1t
  have hXi : XiC (t : ℂ) = 0 := by rw [XiC_ofReal, hz, Complex.ofReal_zero]
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp hXi
  refine ⟨q, ?_⟩
  rw [xiSquaredNode, hq, norm_pow, Complex.norm_real, Real.norm_of_nonneg htpos.le]
  nlinarith

/-- Logarithmic coordinate of an actual squared node at a positive mass. -/
def liEvenCrossCassiniPositiveLogMassPole (v : LiEvenCrossPositiveMass)
    (q : XiZeroCopy) : ℂ :=
  Complex.log (-xiSquaredNode q / (v.val : ℂ))

theorem liEvenCrossCassiniPositiveLogMassPole_direct_mass
    (v : LiEvenCrossPositiveMass) (q : XiZeroCopy) :
    (v.val : ℂ) * Complex.exp (liEvenCrossCassiniPositiveLogMassPole v q) =
      -xiSquaredNode q := by
  have hvne : (v.val : ℂ) ≠ 0 := by exact_mod_cast v.property.ne'
  rw [liEvenCrossCassiniPositiveLogMassPole, Complex.exp_log
    (div_ne_zero (neg_ne_zero.mpr (xiSquaredNode_ne_zero q)) hvne)]
  field_simp

theorem liEvenCrossCassiniPositiveLogMassPole_reflected_mass
    (v : LiEvenCrossPositiveMass) (q : XiZeroCopy) :
    (v.val : ℂ) * Complex.exp (-liEvenCrossCassiniPositiveLogMassPole v q) =
      -(v.val : ℂ) ^ 2 / xiSquaredNode q := by
  have hvne : (v.val : ℂ) ≠ 0 := by exact_mod_cast v.property.ne'
  rw [Complex.exp_neg, liEvenCrossCassiniPositiveLogMassPole, Complex.exp_log
    (div_ne_zero (neg_ne_zero.mpr (xiSquaredNode_ne_zero q)) hvne)]
  field_simp

private theorem cassiniSource_one_sub_small_ne_zero_allMass {z : ℂ}
    (hz : ‖z‖ < 1) : xiSquaredSeamCassiniSource (1 - z) ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ := (xiSquaredSeamCassiniSource_eq_zero_iff_exists_zeroCopy _).mp hzero
  have hnode : xiSquaredNode q = -z := by
    unfold xiSquaredSeamCassiniZero at hq
    unfold xiSquaredNode
    linear_combination hq
  have hbig := liEvenCross_squaredNode_norm_lower q
  rw [hnode, norm_neg] at hbig
  linarith

/-- Reflection of a node beyond the squared mass scale is regular. -/
theorem analyticAt_liEvenCrossCassiniLogMassCurrent_positive_reflected_exp
    (v : LiEvenCrossPositiveMass) (q : XiZeroCopy)
    (hq : v.val ^ 2 < ‖xiSquaredNode q‖) :
    AnalyticAt ℂ
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp (-t)))
      (liEvenCrossCassiniPositiveLogMassPole v q) := by
  have hnorm : 0 < ‖xiSquaredNode q‖ := norm_pos_iff.mpr (xiSquaredNode_ne_zero q)
  have hsmall : ‖(v.val : ℂ) * Complex.exp (-liEvenCrossCassiniPositiveLogMassPole v q)‖ < 1 := by
    rw [liEvenCrossCassiniPositiveLogMassPole_reflected_mass, norm_div, norm_neg, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg v.property.le]
    exact (div_lt_one hnorm).mpr hq
  have hz := cassiniSource_one_sub_small_ne_zero_allMass hsmall
  exact (analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero hz).comp
    (f := fun t : ℂ => (v.val : ℂ) * Complex.exp (-t))
    (x := liEvenCrossCassiniPositiveLogMassPole v q) (by fun_prop)

/-- Every sufficiently large actual node retains cubic order after even reflection. -/
theorem meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_positive_pole
    (v : LiEvenCrossPositiveMass) (q : XiZeroCopy)
    (hq : v.val ^ 2 < ‖xiSquaredNode q‖) :
    meromorphicOrderAt (liEvenCrossCassiniEvenLogMassGerm v.val)
      (liEvenCrossCassiniPositiveLogMassPole v q) = ((-3 : ℤ) : WithTop ℤ) := by
  have he := liEvenCrossCassiniPositiveLogMassPole_direct_mass v q
  have hd : deriv (fun t : ℂ => (v.val : ℂ) * Complex.exp t)
      (liEvenCrossCassiniPositiveLogMassPole v q) ≠ 0 := by
    rw [((Complex.hasDerivAt_exp _).const_mul (v.val : ℂ)).deriv, he]
    exact neg_ne_zero.mpr (xiSquaredNode_ne_zero q)
  have hD : meromorphicOrderAt
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp t))
      (liEvenCrossCassiniPositiveLogMassPole v q) = ((-3 : ℤ) : WithTop ℤ) := by
    rw [← Function.comp_def, meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) hd, he]
    exact meromorphicOrderAt_liEvenCrossCassiniLogMassCurrent_node q
  have hR := analyticAt_liEvenCrossCassiniLogMassCurrent_positive_reflected_exp v q hq
  have hlt : meromorphicOrderAt
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp t))
      (liEvenCrossCassiniPositiveLogMassPole v q) < meromorphicOrderAt
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp (-t)))
      (liEvenCrossCassiniPositiveLogMassPole v q) := by
    rw [hD]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-3 : ℤ) < 0 by norm_num)) hR.meromorphicOrderAt_nonneg
  change meromorphicOrderAt
    ((fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp t)) +
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp (-t))))
    (liEvenCrossCassiniPositiveLogMassPole v q) = _
  rw [meromorphicOrderAt_add_eq_left_of_lt hR.meromorphicAt hlt]
  exact hD

/-- Every positive mass has a genuine cubic pole of the actual even Cassini current. -/
theorem exists_liEvenCrossCassiniEvenLogMassGerm_cubic_pole_positive
    (v : LiEvenCrossPositiveMass) :
    ∃ t : ℂ, meromorphicOrderAt (liEvenCrossCassiniEvenLogMassGerm v.val) t =
      ((-3 : ℤ) : WithTop ℤ) := by
  obtain ⟨q, hq⟩ := exists_xiSquaredNode_norm_gt (v.val ^ 2)
  exact ⟨liEvenCrossCassiniPositiveLogMassPole v q,
    meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_positive_pole v q hq⟩

end

end RHTower
