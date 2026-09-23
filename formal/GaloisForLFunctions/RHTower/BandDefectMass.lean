import GaloisForLFunctions.RHTower.BandComparisonDefect

/-!
# The Liouville mass of the band comparison defect

The exponential factor of a Volterra comparison estimate is the total mass of the defect against the
Liouville measure `dy/|Xi'|`.  On the band that measure vanishes like `sqrt(1-y)` at the endpoint,
because `1/|Xi'| = sqrt((1-y²)/(y²-s))`, so a simple pole has finite mass while a double pole would
not.  This is the whole point of the cancellation proved in `BandComparisonDefect`.

The bound is uniform: on every closed subinterval of the collar `[1/2, 1)` the mass is at most `500`,
with no dependence on the aperture and none on the separation parameter beyond `s ≤ 1/8`.  The
majorant is `200 sqrt 2 / sqrt(1-y²)`, whose exact primitive is `arcsin`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The integrand of the Liouville mass of the band defect. -/
def bandDefectMassIntegrand (s y : ℝ) : ℝ :=
  |bandComparisonDefect s y| / prolateWKBProfile s y

section

variable {s y A B : ℝ}

theorem continuousOn_prolateWKBProfile_Ioo (s : ℝ) :
    ContinuousOn (prolateWKBProfile s) (Ioo (-1 : ℝ) 1) := by
  have hfun : prolateWKBProfile s
      = fun t : ℝ => Real.sqrt ((t ^ (2 : ℕ) - s) / (1 - t ^ (2 : ℕ))) := by
    funext t
    rw [prolateWKBProfile]
  rw [hfun]
  refine Real.continuous_sqrt.comp_continuousOn (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
  intro t ht
  have h1 : -1 < t := ht.1
  have h2 : t < 1 := ht.2
  have : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
  exact this.ne'

theorem continuousOn_bandEndpointPhase (hs : s ≤ 1 / 4) :
    ContinuousOn (bandEndpointPhase s) (Ioo (1 / 2 : ℝ) 1) := by
  intro y hy
  have h1 : (1 : ℝ) / 2 < y := hy.1
  have hsy : s ≤ y ^ (2 : ℕ) := by nlinarith
  exact ((hasDerivAt_bandEndpointPhase (by linarith) hy.2 hsy).continuousAt).continuousWithinAt

theorem continuousOn_bandPhaseLogDefect (hs1 : s ≤ 1 / 8) :
    ContinuousOn (bandPhaseLogDefect s) (Ioo (1 / 2 : ℝ) 1) := by
  have hsub : Ioo (1 / 2 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hfun : bandPhaseLogDefect s
      = fun t : ℝ => -(prolateWKBProfile s t) / bandEndpointPhase s t + t / (1 - t ^ (2 : ℕ)) := by
    funext t
    rw [bandPhaseLogDefect]
  rw [hfun]
  refine ContinuousOn.add (ContinuousOn.div
    ((continuousOn_prolateWKBProfile_Ioo s).mono hsub).neg
    (continuousOn_bandEndpointPhase (by linarith)) ?_)
    (ContinuousOn.div continuousOn_id (by fun_prop) ?_)
  · intro t ht
    have h1 : (1 : ℝ) / 2 < t := ht.1
    have hsy : s < t ^ (2 : ℕ) := by nlinarith
    exact (bandEndpointPhase_pos ht.2 hsy (by linarith)).ne'
  · intro t ht
    have h1 : (1 : ℝ) / 2 < t := ht.1
    have : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith [ht.2]
    exact this.ne'

theorem continuousOn_bandDefectAlg (hs1 : s ≤ 1 / 8) :
    ContinuousOn (bandDefectAlg s) (Ioo (1 / 2 : ℝ) 1) := by
  have hfun : bandDefectAlg s
      = fun t : ℝ => (t ^ (4 : ℕ) + (3 - 8 * s) * t ^ (2 : ℕ) + 2 * s ^ (2 : ℕ) + 2 * s)
          / (4 * (1 - t ^ (2 : ℕ)) * (t ^ (2 : ℕ) - s) ^ (2 : ℕ)) := by
    funext t
    rw [bandDefectAlg]
  rw [hfun]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro t ht
  have h1 : (1 : ℝ) / 2 < t := ht.1
  have h2 : t < 1 := ht.2
  have hd : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
  have hs : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  positivity

theorem continuousOn_bandComparisonDefect (hs1 : s ≤ 1 / 8) :
    ContinuousOn (bandComparisonDefect s) (Ioo (1 / 2 : ℝ) 1) := by
  have hL := continuousOn_bandPhaseLogDefect hs1
  have hA := continuousOn_bandDefectAlg hs1
  have hcont : ContinuousOn
      (fun t : ℝ => bandDefectAlg s t + t * bandPhaseLogDefect s t / (2 * (1 - t ^ (2 : ℕ)))
        - bandPhaseLogDefect s t ^ (2 : ℕ) / 4) (Ioo (1 / 2 : ℝ) 1) := by
    refine (hA.add (ContinuousOn.div (continuousOn_id.mul hL) (by fun_prop) ?_)).sub
      ((hL.pow 2).div_const 4)
    intro t ht
    have h1 : (1 : ℝ) / 2 < t := ht.1
    have : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith [ht.2]
    positivity
  refine hcont.congr ?_
  intro t ht
  have h1 : (1 : ℝ) / 2 < t := ht.1
  have h2 : t < 1 := ht.2
  have hd : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
  have hs : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  exact bandComparisonDefect_eq hd.ne' hs.ne'
    (bandEndpointPhase_pos h2 (by linarith) (by linarith)).ne'

theorem continuousOn_bandDefectMassIntegrand (hs1 : s ≤ 1 / 8) :
    ContinuousOn (bandDefectMassIntegrand s) (Ioo (1 / 2 : ℝ) 1) := by
  have hsub : Ioo (1 / 2 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hfun : bandDefectMassIntegrand s
      = fun t : ℝ => |bandComparisonDefect s t| / prolateWKBProfile s t := by
    funext t
    rw [bandDefectMassIntegrand]
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_bandComparisonDefect hs1).abs)
    ((continuousOn_prolateWKBProfile_Ioo s).mono hsub) ?_
  intro t ht
  have h1 : (1 : ℝ) / 2 < t := ht.1
  have h2 : t < 1 := ht.2
  have hd : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
  have hs : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  rw [prolateWKBProfile]
  exact (Real.sqrt_pos.2 (div_pos hs hd)).ne'

/-- **The pointwise majorant.**  The Liouville measure turns the simple pole into an inverse square
root, which is integrable at the endpoint. -/
theorem bandDefectMassIntegrand_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 ≤ y)
    (hy1 : y < 1) :
    bandDefectMassIntegrand s y ≤ 200 * Real.sqrt 2 * (1 / Real.sqrt (1 - y ^ (2 : ℕ))) := by
  have hy2 : y ^ (2 : ℕ) < 1 := by nlinarith
  have h1y2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
  have hsy : (1 : ℝ) / 8 ≤ y ^ (2 : ℕ) - s := by nlinarith
  have hspos : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
  set u := Real.sqrt (1 - y ^ (2 : ℕ)) with hudef
  set z := Real.sqrt (y ^ (2 : ℕ) - s) with hzdef
  have hu : 0 < u := Real.sqrt_pos.2 h1y2
  have hz : 0 < z := Real.sqrt_pos.2 hspos
  have hu2 : u ^ (2 : ℕ) = 1 - y ^ (2 : ℕ) := Real.sq_sqrt h1y2.le
  have hz2 : z ^ (2 : ℕ) = y ^ (2 : ℕ) - s := Real.sq_sqrt hspos.le
  have hr2 : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have hr : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hzlow : 1 ≤ 2 * Real.sqrt 2 * z := by nlinarith [hz2, hsy, hr2, hr, hz]
  have hdiv : bandDefectMassIntegrand s y = |bandComparisonDefect s y| * u / z := by
    rw [bandDefectMassIntegrand, prolateWKBProfile_eq_div (by linarith), ← hudef, ← hzdef,
      div_div_eq_mul_div]
  have ha : |bandComparisonDefect s y| * (1 - y ^ (2 : ℕ)) ≤ 100 :=
    (le_div_iff₀ h1y2).mp (abs_bandComparisonDefect_le hs0 hs1 hy0 hy1)
  have hgoal : |bandComparisonDefect s y| * u / z ≤ 200 * Real.sqrt 2 / u := by
    rw [div_le_div_iff₀ hz hu]
    have hstep : |bandComparisonDefect s y| * u * u = |bandComparisonDefect s y| * (1 - y ^ (2 : ℕ)) := by
      nlinarith [hu2]
    rw [hstep]
    nlinarith [ha, hzlow, hr]
  rw [hdiv, mul_one_div]
  exact hgoal

theorem intervalIntegrable_bandDefectMassIntegrand (hs1 : s ≤ 1 / 8)
    (hA : 1 / 2 < A) (hAB : A ≤ B) (hB : B < 1) :
    IntervalIntegrable (bandDefectMassIntegrand s) MeasureTheory.volume A B := by
  have hsub : uIcc A B ⊆ Ioo (1 / 2 : ℝ) 1 := by
    rw [uIcc_of_le hAB]
    intro t ht
    exact ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hB⟩
  exact ((continuousOn_bandDefectMassIntegrand hs1).mono hsub).intervalIntegrable

/-- **The mass bound.**  The total Liouville mass of the band defect on the endpoint collar is at
most `500`, uniformly in the aperture and in the separation parameter. -/
theorem integral_bandDefectMass_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8)
    (hA : 1 / 2 < A) (hAB : A ≤ B) (hB : B < 1) :
    (∫ y in A..B, bandDefectMassIntegrand s y) ≤ 500 := by
  have hsub : uIcc A B ⊆ Ioo (1 / 2 : ℝ) 1 := by
    rw [uIcc_of_le hAB]
    intro t ht
    exact ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hB⟩
  have hmaj : ContinuousOn (fun t : ℝ => 200 * Real.sqrt 2 * (1 / Real.sqrt (1 - t ^ (2 : ℕ))))
      (Ioo (1 / 2 : ℝ) 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
    · intro t ht
      have h1 : (1 : ℝ) / 2 < t := ht.1
      have hd : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith [ht.2]
      exact (Real.sqrt_pos.2 hd).ne'
  have hgint : IntervalIntegrable (fun t : ℝ => 200 * Real.sqrt 2 * (1 / Real.sqrt (1 - t ^ (2 : ℕ))))
      MeasureTheory.volume A B := (hmaj.mono hsub).intervalIntegrable
  have hmono : (∫ y in A..B, bandDefectMassIntegrand s y)
      ≤ ∫ t in A..B, 200 * Real.sqrt 2 * (1 / Real.sqrt (1 - t ^ (2 : ℕ))) := by
    refine intervalIntegral.integral_mono_on hAB
      (intervalIntegrable_bandDefectMassIntegrand hs1 hA hAB hB) hgint fun t ht => ?_
    exact bandDefectMassIntegrand_le hs0 hs1 (le_of_lt (lt_of_lt_of_le hA ht.1))
      (lt_of_le_of_lt ht.2 hB)
  have hFTC : (∫ t in A..B, 200 * Real.sqrt 2 * (1 / Real.sqrt (1 - t ^ (2 : ℕ))))
      = 200 * Real.sqrt 2 * Real.arcsin B - 200 * Real.sqrt 2 * Real.arcsin A := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => 200 * Real.sqrt 2 * Real.arcsin t) (fun t ht => ?_) hgint
    have hmem := hsub ht
    have h1 : (1 : ℝ) / 2 < t := hmem.1
    exact (Real.hasDerivAt_arcsin (by linarith) (by linarith [hmem.2])).const_mul _
  have harcB : Real.arcsin B ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two B
  have harcA : 0 ≤ Real.arcsin A := Real.arcsin_nonneg.2 (by linarith)
  have hpi : Real.pi ≤ 32 / 10 := by linarith [Real.pi_lt_d2]
  have hr2 : Real.sqrt 2 ≤ 15 / 10 := by
    rw [show (15 : ℝ) / 10 = Real.sqrt ((15 / 10) ^ (2 : ℕ)) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hrpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hfin : 200 * Real.sqrt 2 * Real.arcsin B - 200 * Real.sqrt 2 * Real.arcsin A ≤ 500 := by
    nlinarith [harcB, harcA, hpi, hr2, hrpos]
  linarith [hmono, hFTC.le, hFTC.ge, hfin]

end

end GaloisForLFunctions.RHTower

end
