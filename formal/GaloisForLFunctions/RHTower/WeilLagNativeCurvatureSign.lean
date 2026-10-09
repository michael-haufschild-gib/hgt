import GaloisForLFunctions.RHTower.WeilLagQuadraticInterpolation
import GaloisForLFunctions.RHTower.ChebyshevLagWindow
import GaloisForLFunctions.RHTower.WeilLagDiscretePrimeCurvature

/-!
# Native sign of discrete integer-lag curvature

For the centered second difference `D(n)` of `sqrt(n) * integerLag(n)`, the
normalized arithmetic error `n * D(n) - Λ(n) + 1` tends to zero with an explicit
bound. The logarithmic and complete trivial-zero corrections are retained.
Consequently, at every sufficiently large integer, native curvature is positive
exactly at odd prime powers and negative at every other integer.
-/

open Real Set
namespace RHTower.IntegerLagCurvature

private theorem convexOn_log_sub_quadratic {R : ℝ} (hR : 2 ≤ R) :
    ConvexOn ℝ (Icc 2 R) (fun x : ℝ => x * Real.log x - x ^ 2 / (2 * R)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun x => Real.log x + 1 - x / R)
    (f'' := fun x => x⁻¹ - 1 / R) (convex_Icc 2 R)
  · exact (continuous_id.mul_log.sub ((continuous_id.pow 2).div_const (2 * R))).continuousOn
  · intro x hx
    have hxI : x ∈ Icc 2 R := interior_subset hx
    have hx0 : 0 < x := by linarith [hxI.1]
    have hd := (Real.hasDerivAt_mul_log hx0.ne').sub
      (((hasDerivAt_id' x).pow 2).div_const (2 * R))
    convert! hd.hasDerivWithinAt using 1
    field_simp
    ring
  · intro x hx
    have hxI : x ∈ Icc 2 R := interior_subset hx
    have hx0 : 0 < x := by linarith [hxI.1]
    simpa only [one_div, Pi.sub_apply] using!
      ((Real.hasDerivAt_log hx0.ne').add_const 1).sub
        ((hasDerivAt_id' x).div_const R) |>.hasDerivWithinAt
  · intro x hx
    have hxI : x ∈ Icc 2 R := interior_subset hx
    have hx0 : 0 < x := by linarith [hxI.1]
    have h := one_div_le_one_div_of_le hx0 hxI.2
    simpa only [one_div, sub_nonneg] using h

/-- Centered logarithmic second difference at the integer `n + 3`. -/
noncomputable def logCurvature (n : ℕ) : ℝ :=
  (n + 4 : ℝ) * Real.log (n + 4) - 2 * ((n + 3) * Real.log (n + 3)) +
    (n + 2) * Real.log (n + 2)

/-- The logarithmic curvature lies between the two endpoint reciprocal scales. -/
theorem logCurvature_bounds (n : ℕ) :
    1 / (n + 4 : ℝ) ≤ logCurvature n ∧ logCurvature n ≤ 1 / (n + 2 : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlo := (convexOn_log_sub_quadratic (R := (n : ℝ) + 4) (by linarith)).2
    (show (n : ℝ) + 2 ∈ Icc 2 ((n : ℝ) + 4) from ⟨by linarith, by linarith⟩)
    (show (n : ℝ) + 4 ∈ Icc 2 ((n : ℝ) + 4) from ⟨by linarith, le_rfl⟩)
    (show 0 ≤ (1 / 2 : ℝ) by positivity) (show 0 ≤ (1 / 2 : ℝ) by positivity)
    (by ring)
  have hup := mul_log_chord_defect_le_of_lower_bound
    (r := (n : ℝ) + 2) (a := (n : ℝ) + 2) (b := (n : ℝ) + 4)
    (x := (n : ℝ) + 3) (u := (1 / 2 : ℝ)) (v := (1 / 2 : ℝ))
    (by positivity) le_rfl (by linarith) (by positivity) (by positivity) (by ring) (by ring)
  simp only [smul_eq_mul] at hlo
  rw [show (1 / 2 : ℝ) * (n + 2) + (1 / 2 : ℝ) * (n + 4) = n + 3 by ring] at hlo
  constructor
  · dsimp [logCurvature]
    have hR : (n : ℝ) + 4 ≠ 0 := by positivity
    field_simp [hR] at hlo ⊢
    nlinarith only [hlo]
  · dsimp [logCurvature]
    have hr : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hr] at hup ⊢
    nlinarith only [hup]
end RHTower.IntegerLagCurvature

namespace RHTower.IntegerLagCurvature
open Real Set

/-- Centered second difference of the complete trivial-zero correction. -/
noncomputable def trivialCurvature (n : ℕ) : ℝ :=
  trivialZeroSeriesReal (n + 4 : ℝ) - 2 * trivialZeroSeriesReal (n + 3 : ℝ) +
    trivialZeroSeriesReal (n + 2 : ℝ)

/-- Trivial-zero curvature is nonnegative and bounded by a quadratic reciprocal. -/
theorem trivialCurvature_bounds (n : ℕ) :
    0 ≤ trivialCurvature n ∧ trivialCurvature n ≤ 4 / (n + 2 : ℝ) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc := trivialZeroSeriesReal_chord (a := (n : ℝ) + 2) (b := (n : ℝ) + 4)
    (u := (1 / 2 : ℝ)) (v := (1 / 2 : ℝ))
    (by linarith) (by linarith) (by positivity) (by positivity) (by ring)
  rw [show (1 / 2 : ℝ) * (n + 2) + (1 / 2 : ℝ) * (n + 4) = n + 3 by ring] at hc
  have hm := trivialZeroSeriesReal_nonneg (X := (n : ℝ) + 3) (by linarith)
  have ha := trivialZeroSeriesReal_anti (X := (n : ℝ) + 2) (Y := (n : ℝ) + 4)
    (by linarith) (by linarith)
  have hb := trivialZeroSeriesReal_le_two_div_sq (X := (n : ℝ) + 2) (by linarith)
  dsimp [trivialCurvature]
  constructor
  · linarith only [hc]
  · calc
      _ ≤ 2 * trivialZeroSeriesReal (n + 2 : ℝ) := by linarith only [hm, ha]
      _ ≤ 2 * (2 / (n + 2 : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring

end RHTower.IntegerLagCurvature

namespace RHTower.IntegerLagCurvature
open Real Set

/-- Native centered curvature of the scaled lag at the integer `n + 3`. -/
noncomputable def scaledCurvature (n : ℕ) : ℝ :=
  Real.sqrt (n + 4 : ℕ) * integerLag (n + 4) -
    2 * (Real.sqrt (n + 3 : ℕ) * integerLag (n + 3)) +
    Real.sqrt (n + 2 : ℕ) * integerLag (n + 2)

/-- Exact native decomposition into the arithmetic atom and both archimedean terms. -/
theorem scaledCurvature_eq (n : ℕ) :
    scaledCurvature n = ArithmeticFunction.vonMangoldt (n + 3) / (n + 3 : ℝ) -
      logCurvature n + trivialCurvature n := by
  rw [scaledCurvature, scaled_second_difference]
  simp only [logCurvature, trivialCurvature, Nat.cast_add, Nat.cast_ofNat]

/-- Two-sided native curvature bounds with the actual Mangoldt weight retained. -/
theorem scaledCurvature_bounds (n : ℕ) :
    ArithmeticFunction.vonMangoldt (n + 3) / (n + 3 : ℝ) - 1 / (n + 2 : ℝ) ≤
        scaledCurvature n ∧
    scaledCurvature n ≤ ArithmeticFunction.vonMangoldt (n + 3) / (n + 3 : ℝ) -
        1 / (n + 4 : ℝ) + 4 / (n + 2 : ℝ) ^ 2 := by
  have hE := logCurvature_bounds n
  have hT := trivialCurvature_bounds n
  rw [scaledCurvature_eq]
  constructor <;> linarith

/-- Uniform arithmetic curvature error with an explicit vanishing reciprocal bound. -/
theorem scaledCurvature_error (n : ℕ) :
    |(n + 3 : ℝ) * scaledCurvature n - ArithmeticFunction.vonMangoldt (n + 3) + 1| ≤
      9 / (n + 2 : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 < (n : ℝ) + 2 := by positivity
  have hc : 0 < (n : ℝ) + 3 := by positivity
  have hR : 0 < (n : ℝ) + 4 := by positivity
  have h := scaledCurvature_bounds n
  have hlo : -1 / (n + 2 : ℝ) ≤
      (n + 3 : ℝ) * scaledCurvature n - ArithmeticFunction.vonMangoldt (n + 3) + 1 := by
    calc
      _ = (n + 3 : ℝ) *
          (ArithmeticFunction.vonMangoldt (n + 3) / (n + 3 : ℝ) - 1 / (n + 2 : ℝ)) -
          ArithmeticFunction.vonMangoldt (n + 3) + 1 := by field_simp; ring
      _ ≤ _ := by gcongr; exact h.1
  have hup :
      (n + 3 : ℝ) * scaledCurvature n - ArithmeticFunction.vonMangoldt (n + 3) + 1 ≤
        1 / (n + 4 : ℝ) + 4 * (n + 3 : ℝ) / (n + 2 : ℝ) ^ 2 := by
    calc
      _ ≤ (n + 3 : ℝ) *
          (ArithmeticFunction.vonMangoldt (n + 3) / (n + 3 : ℝ) - 1 / (n + 4 : ℝ) +
            4 / (n + 2 : ℝ) ^ 2) - ArithmeticFunction.vonMangoldt (n + 3) + 1 := by
        gcongr
        exact h.2
      _ = _ := by field_simp; ring
  have hi : 1 / (n + 4 : ℝ) ≤ 1 / (n + 2 : ℝ) :=
    one_div_le_one_div_of_le hr (by linarith)
  have hf : 4 * (n + 3 : ℝ) / (n + 2 : ℝ) ^ 2 ≤ 8 / (n + 2 : ℝ) := by
    calc
      _ ≤ (8 * (n + 2 : ℝ)) / (n + 2 : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith only [hn]) (sq_nonneg _)
      _ = _ := by field_simp
  apply abs_le.mpr
  constructor
  · calc
      -(9 / (n + 2 : ℝ)) ≤ -1 / (n + 2 : ℝ) := by
        simpa only [neg_div] using
          neg_le_neg (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 9) hr.le)
      _ ≤ _ := hlo
  · have hs : 1 / (n + 2 : ℝ) + 8 / (n + 2 : ℝ) = 9 / (n + 2 : ℝ) := by ring
    linarith only [hup, hi, hf, hs]
end RHTower.IntegerLagCurvature
namespace RHTower.IntegerLagCurvature
open Real Set

private theorem eventually_scaledCurvature_sign :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (0 < scaledCurvature n ↔ IsPrimePow (n + 3) ∧ (n + 3).minFac ≠ 2) ∧
      (scaledCurvature n < 0 ↔ ¬ (IsPrimePow (n + 3) ∧ (n + 3).minFac ≠ 2)) := by
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.strictMonoOn_log
      (by norm_num : (2 : ℝ) ∈ Ioi 0)
      (show Real.exp 1 ∈ Ioi 0 from Real.exp_pos _) Real.exp_one_gt_two
    simpa only [Real.log_exp] using h
  have hlog3 : 1 < Real.log 3 := by
    have h := Real.strictMonoOn_log
      (show Real.exp 1 ∈ Ioi 0 from Real.exp_pos _)
      (by norm_num : (3 : ℝ) ∈ Ioi 0) Real.exp_one_lt_three
    simpa only [Real.log_exp] using h
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let δ : ℝ := min (1 - Real.log 2) (Real.log 3 - 1) / 2
  have hδ : 0 < δ := div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hδ2 : δ < 1 - Real.log 2 := by
    have h := min_le_left (1 - Real.log 2) (Real.log 3 - 1)
    dsimp [δ]
    linarith
  have hδ3 : δ < Real.log 3 - 1 := by
    have h := min_le_right (1 - Real.log 2) (Real.log 3 - 1)
    dsimp [δ]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (9 / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 < (n : ℝ) + 2 := by positivity
  have hc : 0 < (n : ℝ) + 3 := by positivity
  have hsmall : 9 / (n + 2 : ℝ) < δ := by
    have hN9 := (div_lt_iff₀ hδ).mp hN
    apply (div_lt_iff₀ hr).mpr
    nlinarith
  have he := abs_lt.mp ((scaledCurvature_error n).trans_lt hsmall)
  by_cases hp : IsPrimePow (n + 3) ∧ (n + 3).minFac ≠ 2
  · have hfac := (Nat.minFac_prime (by omega : n + 3 ≠ 1)).two_le
    have hfac3 : 3 ≤ (n + 3).minFac := by omega
    have hweight : Real.log 3 ≤ ArithmeticFunction.vonMangoldt (n + 3) := by
      rw [ArithmeticFunction.vonMangoldt_apply, if_pos hp.1]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hfac3)
    have hD : 0 < scaledCurvature n := by
      by_contra h
      have hprod := mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt h)
      linarith [he.1]
    exact ⟨iff_of_true hD hp, iff_of_false (not_lt.mpr hD.le) (not_not.mpr hp)⟩
  · have hweight : ArithmeticFunction.vonMangoldt (n + 3) ≤ Real.log 2 := by
      by_cases hpp : IsPrimePow (n + 3)
      · have hfac : (n + 3).minFac = 2 := by
          by_contra h
          exact hp ⟨hpp, h⟩
        rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp, hfac]
        norm_num
      · rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp]
        exact hlog2pos.le
    have hD : scaledCurvature n < 0 := by
      by_contra h
      have hprod := mul_nonneg hc.le (le_of_not_gt h)
      linarith [he.2]
    exact ⟨iff_of_false (not_lt.mpr hD.le) hp, iff_of_true hD hp⟩

end RHTower.IntegerLagCurvature

namespace RHTower.IntegerLagCurvature

/-- Native curvature eventually detects exactly odd prime powers, with strict negative
curvature at every remaining integer. -/
theorem eventually_scaledCurvature_odd_prime_power_sign :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (0 < scaledCurvature n ↔ IsPrimePow (n + 3) ∧ ¬ 2 ∣ n + 3) ∧
      (scaledCurvature n < 0 ↔ ¬ (IsPrimePow (n + 3) ∧ ¬ 2 ∣ n + 3)) := by
  simpa only [ne_eq, Nat.minFac_eq_two_iff] using eventually_scaledCurvature_sign

end RHTower.IntegerLagCurvature
