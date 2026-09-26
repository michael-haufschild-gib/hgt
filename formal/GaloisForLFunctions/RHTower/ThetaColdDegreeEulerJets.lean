import GaloisForLFunctions.RHTower.SourceFallingEulerMomentShift
import GaloisForLFunctions.RHTower.ThetaColdDegreeCornerLogJet

/-!
# Literal theta falling Euler jets

The first three normalized Gaussian moment differences are exact averages of bounded
ordinary theta-source jets. The same jets identify the signed square-coordinate logarithmic
profile. All source smoothness and boundedness inputs are discharged from the literal
theta source and its global Schwartz bounds.
-/

open Real Set Filter Topology MeasureTheory
namespace RHTower.ThetaColdCorner
open ColdGamma
noncomputable section

def eulerJetOne (x : ℝ) : ℝ := x*iteratedDeriv 1 thetaCuspFullSource x/2
def eulerJetTwo (x : ℝ) : ℝ :=
  (x^2*iteratedDeriv 2 thetaCuspFullSource x-x*iteratedDeriv 1 thetaCuspFullSource x)/4
def eulerJetThree (x : ℝ) : ℝ :=
  (x^3*iteratedDeriv 3 thetaCuspFullSource x-3*x^2*iteratedDeriv 2 thetaCuspFullSource x+
    3*x*iteratedDeriv 1 thetaCuspFullSource x)/8

private theorem continuous_source_deriv (m : ℕ) : Continuous (iteratedDeriv m thetaCuspFullSource) :=
  contDiff_thetaCuspFullSource.continuous_iteratedDeriv m (by exact_mod_cast ((ENat.coe_lt_top m).le))

private theorem hasDerivAt_source_iterated (m : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m thetaCuspFullSource)
      (iteratedDeriv (m+1) thetaCuspFullSource x) x := by
  simpa only [iteratedDeriv_succ] using
    (contDiff_thetaCuspFullSource.differentiable_iteratedDeriv m
      (by exact_mod_cast (ENat.coe_lt_top m))).differentiableAt.hasDerivAt (x := x)

theorem continuous_eulerJetOne : Continuous eulerJetOne := by
  exact (continuous_id.mul (continuous_source_deriv 1)).div_const 2

theorem continuous_eulerJetTwo : Continuous eulerJetTwo := by
  exact (((continuous_id.pow 2).mul (continuous_source_deriv 2)).sub
    (continuous_id.mul (continuous_source_deriv 1))).div_const 4

theorem continuous_eulerJetThree : Continuous eulerJetThree := by
  exact ((((continuous_id.pow 3).mul (continuous_source_deriv 3)).sub
    (((continuous_id.pow 2).const_mul 3).mul (continuous_source_deriv 2))).add
    ((continuous_id.const_mul 3).mul (continuous_source_deriv 1))).div_const 8

private theorem bounded_weighted_deriv (k m : ℕ) :
    ∃ B : ℝ, ∀ x : ℝ, |x^k*iteratedDeriv m thetaCuspFullSource x| ≤ B := by
  refine ⟨thetaCuspDerivativeExpConstant m * (Nat.factorial k : ℝ), fun x => ?_⟩
  simpa only [abs_mul, abs_pow, Real.norm_eq_abs] using
    weighted_iteratedDeriv_thetaCuspFullSource_le k m x

theorem bounded_source : ∃ B : ℝ, ∀ x : ℝ, |thetaCuspFullSource x| ≤ B := by
  simpa only [pow_zero, one_mul, iteratedDeriv_zero] using bounded_weighted_deriv 0 0

theorem bounded_eulerJetOne : ∃ B : ℝ, ∀ x : ℝ, |eulerJetOne x| ≤ B := by
  obtain ⟨B, hB⟩ := bounded_weighted_deriv 1 1
  refine ⟨B/2, fun x => ?_⟩
  simpa only [eulerJetOne, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), pow_one] using div_le_div_of_nonneg_right (hB x) (by norm_num : (0:ℝ) ≤ 2)

theorem bounded_eulerJetTwo : ∃ B : ℝ, ∀ x : ℝ, |eulerJetTwo x| ≤ B := by
  obtain ⟨B, hB⟩ := bounded_weighted_deriv 2 2
  obtain ⟨C, hC⟩ := bounded_weighted_deriv 1 1
  refine ⟨(B+C)/4, fun x => ?_⟩
  unfold eulerJetTwo
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 4)
  exact (abs_sub _ _).trans (by simpa only [pow_one] using add_le_add (hB x) (hC x))

theorem bounded_eulerJetThree : ∃ B : ℝ, ∀ x : ℝ, |eulerJetThree x| ≤ B := by
  obtain ⟨B, hB⟩ := bounded_weighted_deriv 3 3
  obtain ⟨C, hC⟩ := bounded_weighted_deriv 2 2
  obtain ⟨D, hD⟩ := bounded_weighted_deriv 1 1
  refine ⟨(B+3*C+3*D)/8, fun x => ?_⟩
  unfold eulerJetThree
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8)]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 8)
  have h := (abs_add_le (x^3*iteratedDeriv 3 thetaCuspFullSource x-
    3*x^2*iteratedDeriv 2 thetaCuspFullSource x) (3*x*iteratedDeriv 1 thetaCuspFullSource x)).trans
    (add_le_add (abs_sub _ _) le_rfl)
  simp only [mul_assoc, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] at h
  have hc := hC x
  have hd := hD x
  simp only [abs_mul, pow_one] at hc hd
  have hb := hB x
  simp only [abs_mul] at hb
  have hh : |x^3| * |iteratedDeriv 3 thetaCuspFullSource x| +
      3*(|x^2| * |iteratedDeriv 2 thetaCuspFullSource x|) +
      3*(|x| * |iteratedDeriv 1 thetaCuspFullSource x|) ≤ B+3*C+3*D := by linarith
  simpa only [mul_assoc] using h.trans hh

private theorem bounded_add {F H : ℝ → ℝ} (hf : ∃ B, ∀ x, |F x| ≤ B)
    (hh : ∃ C, ∀ x, |H x| ≤ C) : ∃ D, ∀ x, |F x+H x| ≤ D := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hh
  exact ⟨B+C, fun x => (abs_add_le _ _).trans (add_le_add (hB x) (hC x))⟩

private theorem bounded_mul (c : ℝ) {H : ℝ → ℝ} (hh : ∃ C, ∀ x, |H x| ≤ C) :
    ∃ D, ∀ x, |c*H x| ≤ D := by
  obtain ⟨C, hC⟩ := hh
  refine ⟨|c| * C, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

theorem source_difference_one {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspGaussianApertureGammaShape j *
      (sourceAverage L (j+1) thetaCuspFullSource-sourceAverage L j thetaCuspFullSource) =
      sourceAverage L j eulerJetOne := by
  obtain ⟨B, hB⟩ := bounded_source
  obtain ⟨C, hC⟩ := bounded_eulerJetOne
  apply sourceAverage_euler_shift hL j contDiff_thetaCuspFullSource.continuous continuous_eulerJetOne hB hC
  intro x hx
  refine ⟨iteratedDeriv 1 thetaCuspFullSource x, ?_, ?_⟩
  · simpa only [iteratedDeriv_zero] using hasDerivAt_source_iterated 0 x
  · unfold eulerJetOne; ring

private theorem eulerJetOne_shift {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspGaussianApertureGammaShape j *
      (sourceAverage L (j+1) eulerJetOne-sourceAverage L j eulerJetOne) =
      sourceAverage L j eulerJetTwo+sourceAverage L j eulerJetOne := by
  obtain ⟨B, hB⟩ := bounded_eulerJetOne
  obtain ⟨C, hC⟩ := bounded_eulerJetTwo
  obtain ⟨D, hD⟩ := bounded_add bounded_eulerJetTwo bounded_eulerJetOne
  rw [← sourceAverage_add hL j continuous_eulerJetTwo continuous_eulerJetOne hC hB]
  apply sourceAverage_euler_shift hL j continuous_eulerJetOne
    (continuous_eulerJetTwo.add continuous_eulerJetOne) hB hD
  intro x hx
  refine ⟨(iteratedDeriv 1 thetaCuspFullSource x+x*iteratedDeriv 2 thetaCuspFullSource x)/2, ?_, ?_⟩
  · convert! ((hasDerivAt_id x).mul (hasDerivAt_source_iterated 1 x)).div_const 2 using 1
    simp only [id_eq, one_mul]
  · simp only [Pi.add_apply, eulerJetOne, eulerJetTwo]; ring

private theorem eulerJetTwo_shift {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspGaussianApertureGammaShape j *
      (sourceAverage L (j+1) eulerJetTwo-sourceAverage L j eulerJetTwo) =
      sourceAverage L j eulerJetThree+2*sourceAverage L j eulerJetTwo := by
  obtain ⟨B, hB⟩ := bounded_eulerJetTwo
  obtain ⟨C, hC⟩ := bounded_eulerJetThree
  obtain ⟨D, hD⟩ := bounded_add bounded_eulerJetThree (bounded_mul 2 bounded_eulerJetTwo)
  obtain ⟨E, hE⟩ := bounded_mul 2 bounded_eulerJetTwo
  rw [← sourceAverage_const_mul L j 2 eulerJetTwo,
    ← sourceAverage_add hL j continuous_eulerJetThree (continuous_eulerJetTwo.const_mul 2) hC hE]
  apply sourceAverage_euler_shift hL j continuous_eulerJetTwo
    (continuous_eulerJetThree.add (continuous_eulerJetTwo.const_mul 2)) hB hD
  intro x hx
  refine ⟨(x*iteratedDeriv 2 thetaCuspFullSource x+x^2*iteratedDeriv 3 thetaCuspFullSource x-
    iteratedDeriv 1 thetaCuspFullSource x)/4, ?_, ?_⟩
  · convert! ((((hasDerivAt_id x).pow 2).mul (hasDerivAt_source_iterated 2 x)).sub
      ((hasDerivAt_id x).mul (hasDerivAt_source_iterated 1 x))).div_const 4 using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one, one_mul, Pi.pow_apply]
    ring
  · simp only [Pi.add_apply, eulerJetTwo, eulerJetThree]; ring

/-- Literal-source second shape difference, with its exact Gamma factor. -/
theorem source_difference_two {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspGaussianApertureGammaShape j*(thetaCuspGaussianApertureGammaShape j+1)*
      (sourceAverage L (j+2) thetaCuspFullSource-2*sourceAverage L (j+1) thetaCuspFullSource+
        sourceAverage L j thetaCuspFullSource) = sourceAverage L j eulerJetTwo := by
  have h1 := source_difference_one hL (j+1)
  simp only [thetaCuspGaussianApertureGammaShape_add, Nat.cast_one, Nat.add_assoc] at h1
  exact falling_euler_difference_two _ _ _ _ _ _ _ (source_difference_one hL j) h1 (eulerJetOne_shift hL j)

/-- Literal-source third shape difference; the incoming corner is an ordinary Schwartz average. -/
theorem source_difference_three {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspGaussianApertureGammaShape j*(thetaCuspGaussianApertureGammaShape j+1)*
      (thetaCuspGaussianApertureGammaShape j+2)*
      (sourceAverage L (j+3) thetaCuspFullSource-3*sourceAverage L (j+2) thetaCuspFullSource+
        3*sourceAverage L (j+1) thetaCuspFullSource-sourceAverage L j thetaCuspFullSource) =
      sourceAverage L j eulerJetThree := by
  have h1 := source_difference_two hL (j+1)
  simp only [thetaCuspGaussianApertureGammaShape_add, Nat.cast_one, Nat.add_assoc] at h1
  apply falling_euler_difference_three (thetaCuspGaussianApertureGammaShape j)
    (sourceAverage L j thetaCuspFullSource) (sourceAverage L (j+1) thetaCuspFullSource)
    (sourceAverage L (j+2) thetaCuspFullSource) (sourceAverage L (j+3) thetaCuspFullSource)
    (sourceAverage L j eulerJetTwo) (sourceAverage L (j+1) eulerJetTwo)
    (sourceAverage L j eulerJetThree) (source_difference_two hL j) _ (eulerJetTwo_shift hL j)
  convert! h1 using 1
  ring

/-- Exact third source logarithmic derivative in ordinary source jets. -/
theorem logSource_third_eq (x : ℝ) :
    iteratedDeriv 3 thetaCuspLogSource x =
      (thetaCuspFullSource x^2*iteratedDeriv 3 thetaCuspFullSource x-
        3*thetaCuspFullSource x*iteratedDeriv 1 thetaCuspFullSource x*iteratedDeriv 2 thetaCuspFullSource x+
        2*(iteratedDeriv 1 thetaCuspFullSource x)^3)/thetaCuspFullSource x^3 := by
  have h0 : HasDerivAt thetaCuspFullSource (iteratedDeriv 1 thetaCuspFullSource x) x := by
    simpa only [iteratedDeriv_zero] using hasDerivAt_source_iterated 0 x
  have h1 := hasDerivAt_source_iterated 1 x
  have h2 := hasDerivAt_source_iterated 2 x
  have hn := (h2.mul h0).sub (h1.pow 2)
  have hq := hn.div (h0.pow 2) (pow_ne_zero 2 (thetaCuspFullSource_pos_all x).ne')
  have heq : iteratedDeriv 2 thetaCuspLogSource =ᶠ[𝓝 x]
      (fun z => (iteratedDeriv 2 thetaCuspFullSource z*thetaCuspFullSource z-
        (iteratedDeriv 1 thetaCuspFullSource z)^2)/thetaCuspFullSource z^2) :=
    Eventually.of_forall fun z => iteratedDeriv_two_thetaCuspLogSource_eq z
  rw [show 3=2+1 by rfl, iteratedDeriv_succ, (hq.congr_of_eventuallyEq heq).deriv]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
  field_simp [(thetaCuspFullSource_pos_all x).ne']
  ring

/-- The signed Euler-jet quotient is the literal square-coordinate logarithmic jet. -/
theorem euler_profile_eq_log_third {u : ℝ} (hu : 0 < u) :
    (thetaCuspFullSource (Real.sqrt u)^2*eulerJetThree (Real.sqrt u)-
      3*thetaCuspFullSource (Real.sqrt u)*eulerJetOne (Real.sqrt u)*eulerJetTwo (Real.sqrt u)+
      2*(eulerJetOne (Real.sqrt u))^3)/(u^3*thetaCuspFullSource (Real.sqrt u)^3) =
      iteratedDeriv 3 squareLog u := by
  rw [iteratedDeriv_three_squareLog hu,
    logSource_third_eq, iteratedDeriv_two_thetaCuspLogSource_eq]
  have hone : iteratedDeriv 1 thetaCuspLogSource (Real.sqrt u) =
      iteratedDeriv 1 thetaCuspFullSource (Real.sqrt u)/thetaCuspFullSource (Real.sqrt u) := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource (Real.sqrt u)).deriv
  rw [hone]
  simp only [eulerJetOne, eulerJetTwo, eulerJetThree, thetaCuspLogConcavityNumerator]
  have hx : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hphi := (thetaCuspFullSource_pos_all (Real.sqrt u)).ne'
  have hs : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  generalize hxdef : Real.sqrt u = x at *
  rw [← hs]
  field_simp
  ring

end
end RHTower.ThetaColdCorner
