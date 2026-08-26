import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovKernelMoments
import GaloisForLFunctions.RHTower.PrimeHigherMertens
import GaloisForLFunctions.RHTower.ZetaNearOneLineBound
import GaloisForLFunctions.HTGeometry.MonotoneRiemannSum

/-!
# Harmonic logarithmic window moments

This file supplies the unconditional degree-two sum--integral estimate needed by
the differentiated Barban--Vehov kernels.  The estimate is uniform even when the
lower endpoint is small: the finite prefix through eight is bounded explicitly,
and the tail is controlled by monotonicity of `(log x)^2 / x`.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Primitive for the harmonic logarithmic moment density. -/
def harmonicLogMomentPrimitive (m : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ (m + 1) / ((m : ℝ) + 1)

theorem hasDerivAt_harmonicLogMomentPrimitive
    (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (harmonicLogMomentPrimitive m) (RHTower.logPowDivId m x) x := by
  have h := (Real.hasDerivAt_log hx.ne').pow (m + 1) |>.div_const ((m : ℝ) + 1)
  refine h.congr_deriv ?_
  rw [RHTower.logPowDivId]
  simp only [Nat.cast_add, Nat.cast_one]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm, hx.ne']
  congr 1

theorem intervalIntegral_logPowDivId
    (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, RHTower.logPowDivId m x) =
      harmonicLogMomentPrimitive m b - harmonicLogMomentPrimitive m a := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (harmonicLogMomentPrimitive m) (RHTower.logPowDivId m x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_harmonicLogMomentPrimitive m (ha.trans_le hx.1)
  have hint : IntervalIntegrable (RHTower.logPowDivId m) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (RHTower.hasDerivAt_logPowDivId m
      (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem antitoneOn_logPowDivId_two :
    AntitoneOn (RHTower.logPowDivId 2) (Set.Ici 8) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (8 : ℝ))
  · intro x hx
    have hx8 : (8 : ℝ) ≤ x := hx
    exact (RHTower.hasDerivAt_logPowDivId 2 (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    exact (RHTower.hasDerivAt_logPowDivId 2 (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8' : (8 : ℝ) < x := hx
    have hx8 : 8 ≤ x := le_of_lt hx8'
    have hlog : 2 ≤ Real.log x := RHTower.two_le_log_of_eight_le hx8
    rw [(RHTower.hasDerivAt_logPowDivId 2 (by linarith)).deriv]
    rw [RHTower.derivLogPowDivId]
    norm_num
    have hnum : 2 * Real.log x - Real.log x ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (le_trans (by norm_num) hlog) (sub_nonneg.mpr hlog)]
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg x)

theorem abs_harmonicLogWindowMoment_two_sub_integral_le
    {A B : ℕ} (hA : 8 ≤ A) (hAB : A ≤ B) :
    |harmonicLogWindowMoment 2 A B -
        ∫ x in (A + 1 : ℕ)..(B + 1 : ℕ), RHTower.logPowDivId 2 x| ≤
      RHTower.logPowDivId 2 (A + 1 : ℕ) -
        RHTower.logPowDivId 2 (B + 1 : ℕ) := by
  have hanti : AntitoneOn (RHTower.logPowDivId 2)
      (Set.Icc ((A + 1 : ℕ) : ℝ) (((A + 1 : ℕ) : ℝ) + (B - A : ℕ))) :=
    antitoneOn_logPowDivId_two.mono (fun x hx => by
      show (8 : ℝ) ≤ x
      have hAreal : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
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

/-- Cubic-log main term for the second harmonic logarithmic window moment, with endpoint error. -/
theorem abs_harmonicLogWindowMoment_two_sub_cubic_le
    {A B : ℕ} (hA : 8 ≤ A) (hAB : A ≤ B) :
    |harmonicLogWindowMoment 2 A B -
        (Real.log (B + 1 : ℕ) ^ 3 / 3 - Real.log (A + 1 : ℕ) ^ 3 / 3)| ≤
      RHTower.logPowDivId 2 (A + 1 : ℕ) -
        RHTower.logPowDivId 2 (B + 1 : ℕ) := by
  have hab : (((A + 1 : ℕ) : ℝ)) ≤ (((B + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_le_add_right hAB 1
  have hprim :
      Real.log (B + 1 : ℕ) ^ 3 / 3 - Real.log (A + 1 : ℕ) ^ 3 / 3 =
        harmonicLogMomentPrimitive 2 (B + 1 : ℕ) -
          harmonicLogMomentPrimitive 2 (A + 1 : ℕ) := by
    norm_num [harmonicLogMomentPrimitive]
  rw [hprim]
  rw [← intervalIntegral_logPowDivId 2 (by positivity) hab]
  exact abs_harmonicLogWindowMoment_two_sub_integral_le hA hAB

theorem harmonicLogWindowMoment_nonneg (m A B : ℕ) :
    0 ≤ harmonicLogWindowMoment m A B := by
  rw [harmonicLogWindowMoment]
  exact Finset.sum_nonneg fun j hj => by
    have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le A) (Finset.mem_Ioc.mp hj).1
    have hjone : 1 ≤ j := hjpos
    exact div_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hjone)) m)
      (Nat.cast_nonneg j)

theorem harmonicLogWindowMoment_two_zero_eight_le :
    harmonicLogWindowMoment 2 0 8 ≤ 392 := by
  rw [harmonicLogWindowMoment]
  calc
    (∑ j ∈ Finset.Ioc (0 : ℕ) 8, Real.log (j : ℝ) ^ 2 / (j : ℝ)) ≤
        ∑ _j ∈ Finset.Ioc (0 : ℕ) 8, (49 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjdata := Finset.mem_Ioc.mp hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjdata.1
      have hjone : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjdata.1
      have hlog0 : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg hjone
      have hlogle : Real.log (j : ℝ) ≤ 7 := by
        have h := Real.log_le_sub_one_of_pos hjpos
        have hjle : (j : ℝ) ≤ 8 := by exact_mod_cast hjdata.2
        linarith
      have hsq : Real.log (j : ℝ) ^ 2 ≤ 49 := by nlinarith
      rw [div_le_iff₀ hjpos]
      nlinarith
    _ = 392 := by norm_num

theorem harmonicLogMomentPrimitive_two_nat_succ_le
    {N : ℕ} (hN : N ≤ 8) : harmonicLogMomentPrimitive 2 (N + 1 : ℕ) ≤ 512 := by
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 1))
  have hlogle : Real.log ((N + 1 : ℕ) : ℝ) ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos hpos
    have hcast : (((N + 1 : ℕ) : ℝ)) ≤ 9 := by exact_mod_cast Nat.add_le_add_right hN 1
    linarith
  have hcub : Real.log ((N + 1 : ℕ) : ℝ) ^ 3 ≤ 512 := by
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlogle),
      mul_nonneg (sq_nonneg (Real.log ((N + 1 : ℕ) : ℝ)))
        (sub_nonneg.mpr hlogle)]
  rw [harmonicLogMomentPrimitive]
  norm_num [Nat.cast_add, Nat.cast_one] at hcub ⊢
  linarith

theorem logPowDivId_two_nine_le : RHTower.logPowDivId 2 9 ≤ 64 := by
  have hlog0 : 0 ≤ Real.log (9 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogle : Real.log (9 : ℝ) ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    norm_num at h
    exact h
  rw [RHTower.logPowDivId]
  have hsq : Real.log (9 : ℝ) ^ 2 ≤ 64 := by nlinarith
  linarith

theorem harmonicLogWindowMoment_add (m : ℕ) {A B C : ℕ}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    harmonicLogWindowMoment m A B + harmonicLogWindowMoment m B C =
      harmonicLogWindowMoment m A C := by
  rw [harmonicLogWindowMoment, harmonicLogWindowMoment, harmonicLogWindowMoment]
  have hdisj : Disjoint (Finset.Ioc A B) (Finset.Ioc B C) := by
    rw [Finset.disjoint_left]
    intro j hjAB hjBC
    rw [Finset.mem_Ioc] at hjAB hjBC
    omega
  rw [← Finset.sum_union hdisj,
    Finset.Ioc_union_Ioc_eq_Ioc hAB hBC]

private theorem harmonicLogMomentPrimitive_two_nat_succ_nonneg (N : ℕ) :
    0 ≤ harmonicLogMomentPrimitive 2 (N + 1 : ℕ) := by
  rw [harmonicLogMomentPrimitive]
  exact div_nonneg (pow_nonneg (Real.log_nonneg (by
    exact_mod_cast (by omega : 1 ≤ N + 1))) 3) (by norm_num)

private theorem abs_harmonicLogWindowMoment_two_zero_sub_cubic_le_of_le_eight
    {N : ℕ} (hN : N ≤ 8) :
    |harmonicLogWindowMoment 2 0 N - Real.log (N + 1 : ℕ) ^ 3 / 3| ≤ 1000 := by
  have hsplit := harmonicLogWindowMoment_add 2 (A := 0) (B := N) (C := 8)
    (Nat.zero_le N) hN
  have hwindowLe : harmonicLogWindowMoment 2 0 N ≤
      harmonicLogWindowMoment 2 0 8 := by
    have htail := harmonicLogWindowMoment_nonneg 2 N 8
    linarith
  have hmainLe : Real.log (N + 1 : ℕ) ^ 3 / 3 ≤ 512 := by
    have h := harmonicLogMomentPrimitive_two_nat_succ_le hN
    norm_num [harmonicLogMomentPrimitive, Nat.cast_add, Nat.cast_one] at h ⊢
    exact h
  have hwindowNonneg := harmonicLogWindowMoment_nonneg 2 0 N
  have hmainNonneg : 0 ≤ Real.log (N + 1 : ℕ) ^ 3 / 3 := by
    have h := harmonicLogMomentPrimitive_two_nat_succ_nonneg N
    norm_num [harmonicLogMomentPrimitive, Nat.cast_add, Nat.cast_one] at h ⊢
    exact h
  calc
    |harmonicLogWindowMoment 2 0 N - Real.log (N + 1 : ℕ) ^ 3 / 3| ≤
        |harmonicLogWindowMoment 2 0 N| + |-(Real.log (N + 1 : ℕ) ^ 3 / 3)| := by
          simpa [sub_eq_add_neg] using
            (abs_add_le (harmonicLogWindowMoment 2 0 N)
              (-(Real.log (N + 1 : ℕ) ^ 3 / 3)))
    _ = harmonicLogWindowMoment 2 0 N + Real.log (N + 1 : ℕ) ^ 3 / 3 := by
      rw [abs_of_nonneg hwindowNonneg, abs_neg, abs_of_nonneg hmainNonneg]
    _ ≤ 392 + 512 := add_le_add
      (hwindowLe.trans harmonicLogWindowMoment_two_zero_eight_le) hmainLe
    _ ≤ 1000 := by norm_num

private theorem abs_harmonicLogWindowMoment_two_zero_sub_cubic_le_of_eight_le
    {N : ℕ} (hN : 8 ≤ N) :
    |harmonicLogWindowMoment 2 0 N - Real.log (N + 1 : ℕ) ^ 3 / 3| ≤ 1000 := by
  have hsplit := harmonicLogWindowMoment_add 2 (A := 0) (B := 8) (C := N)
    (by norm_num) hN
  have hheadMainNonneg : 0 ≤ Real.log (9 : ℕ) ^ 3 / 3 := by
    have h := harmonicLogMomentPrimitive_two_nat_succ_nonneg 8
    norm_num [harmonicLogMomentPrimitive] at h ⊢
    exact h
  have hheadMainLe : Real.log (9 : ℕ) ^ 3 / 3 ≤ 512 := by
    have h := harmonicLogMomentPrimitive_two_nat_succ_le (N := 8) (by norm_num)
    norm_num [harmonicLogMomentPrimitive] at h ⊢
    exact h
  have hheadNonneg := harmonicLogWindowMoment_nonneg 2 0 8
  have hheadAbs :
      |harmonicLogWindowMoment 2 0 8 - Real.log (9 : ℕ) ^ 3 / 3| ≤ 904 := by
    calc
      |harmonicLogWindowMoment 2 0 8 - Real.log (9 : ℕ) ^ 3 / 3| ≤
          |harmonicLogWindowMoment 2 0 8| + |-(Real.log (9 : ℕ) ^ 3 / 3)| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le (harmonicLogWindowMoment 2 0 8)
                (-(Real.log (9 : ℕ) ^ 3 / 3)))
      _ = harmonicLogWindowMoment 2 0 8 + Real.log (9 : ℕ) ^ 3 / 3 := by
        rw [abs_of_nonneg hheadNonneg, abs_neg, abs_of_nonneg hheadMainNonneg]
      _ ≤ 392 + 512 := add_le_add harmonicLogWindowMoment_two_zero_eight_le hheadMainLe
      _ = 904 := by norm_num
  have htail := abs_harmonicLogWindowMoment_two_sub_cubic_le
    (A := 8) (B := N) (by norm_num) hN
  have hendNonneg : 0 ≤ RHTower.logPowDivId 2 (N + 1 : ℕ) := by
    rw [RHTower.logPowDivId]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have htailAbs :
      |harmonicLogWindowMoment 2 8 N -
          (Real.log (N + 1 : ℕ) ^ 3 / 3 - Real.log (9 : ℕ) ^ 3 / 3)| ≤ 64 :=
    htail.trans ((sub_le_self _ hendNonneg).trans logPowDivId_two_nine_le)
  calc
    |harmonicLogWindowMoment 2 0 N - Real.log (N + 1 : ℕ) ^ 3 / 3| =
        |(harmonicLogWindowMoment 2 0 8 - Real.log (9 : ℕ) ^ 3 / 3) +
          (harmonicLogWindowMoment 2 8 N -
            (Real.log (N + 1 : ℕ) ^ 3 / 3 - Real.log (9 : ℕ) ^ 3 / 3))| := by
              rw [← hsplit]
              ring_nf
    _ ≤ |harmonicLogWindowMoment 2 0 8 - Real.log (9 : ℕ) ^ 3 / 3| +
        |harmonicLogWindowMoment 2 8 N -
          (Real.log (N + 1 : ℕ) ^ 3 / 3 - Real.log (9 : ℕ) ^ 3 / 3)| := abs_add_le _ _
    _ ≤ 904 + 64 := add_le_add hheadAbs htailAbs
    _ ≤ 1000 := by norm_num

/-- Uniform cubic-log estimate for the second harmonic logarithmic prefix. -/
theorem abs_harmonicLogWindowMoment_two_zero_sub_cubic_le (N : ℕ) :
    |harmonicLogWindowMoment 2 0 N - Real.log (N + 1 : ℕ) ^ 3 / 3| ≤ 1000 := by
  by_cases hN : N ≤ 8
  · exact abs_harmonicLogWindowMoment_two_zero_sub_cubic_le_of_le_eight hN
  · exact abs_harmonicLogWindowMoment_two_zero_sub_cubic_le_of_eight_le (by omega)

/-- Uniform cubic-log estimate for every second harmonic logarithmic window. -/
theorem abs_harmonicLogWindowMoment_two_sub_cubic_uniform_le
    {A B : ℕ} (hAB : A ≤ B) :
    |harmonicLogWindowMoment 2 A B -
        (Real.log (B + 1 : ℕ) ^ 3 / 3 - Real.log (A + 1 : ℕ) ^ 3 / 3)| ≤ 2000 := by
  have hsplit := harmonicLogWindowMoment_add 2 (A := 0) (B := A) (C := B)
    (Nat.zero_le A) hAB
  have hA := abs_harmonicLogWindowMoment_two_zero_sub_cubic_le A
  have hB := abs_harmonicLogWindowMoment_two_zero_sub_cubic_le B
  calc
    |harmonicLogWindowMoment 2 A B -
        (Real.log (B + 1 : ℕ) ^ 3 / 3 - Real.log (A + 1 : ℕ) ^ 3 / 3)| =
      |(harmonicLogWindowMoment 2 0 B - Real.log (B + 1 : ℕ) ^ 3 / 3) -
        (harmonicLogWindowMoment 2 0 A - Real.log (A + 1 : ℕ) ^ 3 / 3)| := by
          rw [← hsplit]
          ring_nf
    _ ≤ |harmonicLogWindowMoment 2 0 B - Real.log (B + 1 : ℕ) ^ 3 / 3| +
        |harmonicLogWindowMoment 2 0 A - Real.log (A + 1 : ℕ) ^ 3 / 3| := by
          have htri := abs_sub_le
            (harmonicLogWindowMoment 2 0 B - Real.log (B + 1 : ℕ) ^ 3 / 3) 0
            (harmonicLogWindowMoment 2 0 A - Real.log (A + 1 : ℕ) ^ 3 / 3)
          rw [sub_zero, zero_sub, abs_neg] at htri
          exact htri
    _ ≤ 1000 + 1000 := add_le_add hB hA
    _ = 2000 := by norm_num

end

end RHTower.Sieve
