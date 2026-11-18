import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Buchstab's delay equation by the method of steps

On the interval starting at `n+1`, the mass `u ω(u)` is the primitive of
the preceding profile, with its integration constant fixed by continuity.
This is the defining equation in Weingartner, arXiv:2607.21883, §1.
-/

namespace RHTower.Sieve.Buchstab
noncomputable section
open MeasureTheory Set Filter Topology

/-- Weighted mass on successive unit intervals. Clipping the denominator outside
the interval makes each primitive a continuous real function. -/
def intervalMass : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, x => intervalMass n 1 +
      ∫ y in (0:ℝ)..x, intervalMass n y / ((n:ℝ) + 1 + max y 0)

/-- The Buchstab profile at `u = n+1+x` for `0 ≤ x ≤ 1`. -/
def profile (n : ℕ) (x : ℝ) : ℝ :=
  intervalMass n x / ((n:ℝ) + 1 + max x 0)

private theorem denom_pos (n : ℕ) (x : ℝ) : 0 < (n:ℝ) + 1 + max x 0 :=
  add_pos_of_pos_of_nonneg (by positivity) (le_max_right _ _)

private theorem primitive_deriv {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun z => ∫ y in (0:ℝ)..z, f y) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

theorem intervalMass_continuous (n : ℕ) : Continuous (intervalMass n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (profile n) := ih.div (by fun_prop) (fun x => (denom_pos n x).ne')
    exact continuous_const.add (continuous_iff_continuousAt.mpr fun x =>
      (primitive_deriv hc x).continuousAt)

theorem profile_continuous (n : ℕ) : Continuous (profile n) :=
  (intervalMass_continuous n).div (by fun_prop) (fun x => (denom_pos n x).ne')

/-- Differentiating each weighted interval recovers the preceding one. -/
theorem hasDerivAt_intervalMass_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (intervalMass (n+1)) (profile n x) x :=
  (primitive_deriv (profile_continuous n) x).const_add _

/-- Adjacent pieces agree at every integer junction. -/
theorem profile_glue (n : ℕ) : profile (n+1) 0 = profile n 1 := by
  simp [profile, intervalMass, Nat.cast_succ, add_assoc]

/-- The integrated delay equation between any two arguments in a cell. -/
theorem intervalMass_increment (n : ℕ) (x y : ℝ) :
    intervalMass (n+1) y - intervalMass (n+1) x = ∫ z in x..y, profile n z := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => hasDerivAt_intervalMass_succ n z) ((profile_continuous n).intervalIntegrable _ _)

/-- Exact weighted mean of the preceding endpoint and the mass added in this cell. -/
theorem profile_succ_mean (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    profile (n+1) x = (((n:ℝ)+2) * profile n 1 + ∫ y in (0:ℝ)..x, profile n y) /
      ((n:ℝ)+2+x) := by
  change (intervalMass n 1 + ∫ y in (0:ℝ)..x, profile n y) / (((n+1:ℕ):ℝ)+1+max x 0) = _
  have he : ((n:ℝ) + 2) * profile n 1 = intervalMass n 1 := by
    rw [profile, max_eq_left zero_le_one]
    field_simp
    ring
  rw [he, max_eq_left hx, Nat.cast_succ, show (n:ℝ)+1+1 = (n:ℝ)+2 by ring]

/-- The second unit cell is the logarithmic branch of the Buchstab function. -/
theorem profile_one_formula (x : Set.Ici (0:ℝ)) :
    profile 1 x = (1 + Real.log (1 + x.val)) / (2 + x.val) := by
  have hint : ∫ y in (0:ℝ)..x.val, profile 0 y = Real.log (1+x.val) := by
    have hh (y : ℝ) (hy : y ∈ uIcc 0 x.val) :
        HasDerivAt (fun v : ℝ => Real.log (1+v)) (profile 0 y) y := by
      rw [uIcc_of_le x.property] at hy
      have hpos : 0 < 1+y := by linarith [hy.1]
      simpa [profile, intervalMass, max_eq_left hy.1, one_div] using
        ((hasDerivAt_id y).const_add 1).log hpos.ne'
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hh
      ((profile_continuous 0).intervalIntegrable 0 x.val)
  rw [profile_succ_mean 0 x.property, hint]
  norm_num [profile, intervalMass]

/-- The derivative of the unweighted profile is the delayed difference divided by the argument. -/
theorem hasDerivAt_profile_succ (n : ℕ) (x : Set.Ioi (0:ℝ)) :
    HasDerivAt (profile (n+1)) ((profile n x - profile (n+1) x) / ((n:ℝ)+2+x)) x.val := by
  have hx : 0 < x.val := x.property
  let d := (n:ℝ)+2+x.val
  have hd : d ≠ 0 := by dsimp [d]; positivity
  have hn : ((n+1 : ℕ) : ℝ) + 1 = (n:ℝ)+2 := by push_cast; ring
  have he : profile (n+1) x = intervalMass (n+1) x / d := by
    simp only [profile, d, max_eq_left hx.le, hn]
  have hf : profile (n+1) =ᶠ[𝓝 x.val] fun z => intervalMass (n+1) z / ((n:ℝ)+2+z) := by
    filter_upwards [lt_mem_nhds hx] with z hz
    simp only [profile, max_eq_left hz.le, hn]
  have hh : HasDerivAt (fun z : ℝ => intervalMass (n+1) z / ((n:ℝ)+2+z))
      ((profile n x * d - intervalMass (n+1) x * 1) / d^2) x.val :=
    (hasDerivAt_intervalMass_succ n x).div ((hasDerivAt_id x.val).const_add ((n:ℝ)+2)) hd
  have hval : (profile n x * d - intervalMass (n+1) x * 1) / d^2 =
      (profile n x - profile (n+1) x) / d := by
    rw [he]
    field_simp [hd]
  rw [hval] at hh
  exact hh.congr_of_eventuallyEq hf

#print axioms intervalMass_increment
#print axioms profile_glue
#print axioms profile_one_formula
#print axioms hasDerivAt_profile_succ

end
end RHTower.Sieve.Buchstab
