import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowMoments

/-!
# Low harmonic logarithmic window moments

The harmonic logarithmic moments `H_m(A, B) = ∑_{A < j ≤ B} (log j)^m / j` are compared with their
integrals. For an antitone weight `(log t)^m / t` the sum differs from the integral over
`[A+1, B+1]` by at most the drop of the weight across the window; the weights for `m = 0, 1` are
antitone on `[8, ∞)`. Together with explicit bounds on the initial segment `j ≤ 8`, this gives
uniform estimates `|H_0(A, B) - (log(B+1) - log(A+1))| ≤ 40` and
`|H_1(A, B) - ((log(B+1))²/2 - (log(A+1))²/2)| ≤ 200` for all `A ≤ B`.

## Main results

- `abs_harmonicLogWindowMoment_sub_integral_le`: sum-integral comparison for an antitone weight.
- `antitoneOn_logPowDivId_zero`, `antitoneOn_logPowDivId_one`: `1/t` and `log t / t` are antitone
  on `[8, ∞)`.
- `abs_harmonicLogWindowMoment_zero_sub_log_le`, `abs_harmonicLogWindowMoment_one_sub_logSquare_le`:
  windowed comparisons for `8 ≤ A ≤ B`.
- `abs_harmonicLogWindowMoment_zero_zero_sub_log_le`: `|H_0(0, N) - log(N+1)| ≤ 20`.
- `abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le`: `|H_1(0, N) - (log(N+1))²/2| ≤ 100`.
- `abs_harmonicLogWindowMoment_zero_sub_log_uniform_le`,
  `abs_harmonicLogWindowMoment_one_sub_logSquare_uniform_le`: uniform window bounds `40` and `200`.

## Hypotheses

All main results are unconditional. The general sum-integral comparison takes antitonicity of the
weight on `[A+1, ∞)` as an argument; it is proved for `m = 0, 1` on `[8, ∞)` and used only there.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Assuming the weight `(log t)^m / t` is antitone on `[A+1, ∞)`, `H_m(A, B)` differs from
`∫_{A+1}^{B+1} (log t)^m / t dt` by at most the weight at `A+1` minus the weight at `B+1`. -/
theorem abs_harmonicLogWindowMoment_sub_integral_le
    (m : ℕ) {A B : ℕ} (hAB : A ≤ B)
    (hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici ((A + 1 : ℕ) : ℝ))) :
    |harmonicLogWindowMoment m A B -
        ∫ x in (A + 1 : ℕ)..(B + 1 : ℕ), RHTower.logPowDivId m x| ≤
      RHTower.logPowDivId m (A + 1 : ℕ) -
        RHTower.logPowDivId m (B + 1 : ℕ) := by
  have hanti' : AntitoneOn (RHTower.logPowDivId m)
      (Set.Icc ((A + 1 : ℕ) : ℝ) (((A + 1 : ℕ) : ℝ) + (B - A : ℕ))) :=
    hanti.mono (fun x hx => hx.1)
  have h := HTGeometry.abs_sum_sub_integral_le_of_antitoneOn hanti'
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

/-- `t ↦ 1/t` is antitone on `[8, ∞)`. -/
theorem antitoneOn_logPowDivId_zero :
    AntitoneOn (RHTower.logPowDivId 0) (Set.Ici 8) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (8 : ℝ))
  · intro x hx
    have hx8 : (8 : ℝ) ≤ x := hx
    exact (RHTower.hasDerivAt_logPowDivId 0 (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    exact (RHTower.hasDerivAt_logPowDivId 0 (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    rw [(RHTower.hasDerivAt_logPowDivId 0 (by linarith)).deriv]
    rw [RHTower.derivLogPowDivId]
    norm_num
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg x)

/-- `t ↦ log t / t` is antitone on `[8, ∞)`. -/
theorem antitoneOn_logPowDivId_one :
    AntitoneOn (RHTower.logPowDivId 1) (Set.Ici 8) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (8 : ℝ))
  · intro x hx
    have hx8 : (8 : ℝ) ≤ x := hx
    exact (RHTower.hasDerivAt_logPowDivId 1 (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    exact (RHTower.hasDerivAt_logPowDivId 1 (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) ≤ x := le_of_lt hx
    have hlog : 2 ≤ Real.log x := RHTower.two_le_log_of_eight_le hx8
    rw [(RHTower.hasDerivAt_logPowDivId 1 (by linarith)).deriv]
    rw [RHTower.derivLogPowDivId]
    norm_num
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x)

/-- For `8 ≤ A ≤ B`, `|H_0(A, B) - (log(B+1) - log(A+1))| ≤ 1/(A+1) - 1/(B+1)`. -/
theorem abs_harmonicLogWindowMoment_zero_sub_log_le
    {A B : ℕ} (hA : 8 ≤ A) (hAB : A ≤ B) :
    |harmonicLogWindowMoment 0 A B -
        (Real.log (B + 1 : ℕ) - Real.log (A + 1 : ℕ))| ≤
      RHTower.logPowDivId 0 (A + 1 : ℕ) -
        RHTower.logPowDivId 0 (B + 1 : ℕ) := by
  have hanti : AntitoneOn (RHTower.logPowDivId 0)
      (Set.Ici ((A + 1 : ℕ) : ℝ)) :=
    antitoneOn_logPowDivId_zero.mono (fun x hx => by
    have hAreal : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hxA : ((A + 1 : ℕ) : ℝ) ≤ x := hx
    push_cast at hxA
    exact hAreal.trans (by linarith))
  have h := abs_harmonicLogWindowMoment_sub_integral_le 0 hAB hanti
  rw [intervalIntegral_logPowDivId 0 (by positivity) (by exact_mod_cast Nat.add_le_add_right hAB 1)] at h
  norm_num [harmonicLogMomentPrimitive] at h ⊢
  exact h

/-- For `8 ≤ A ≤ B`, `H_1(A, B)` is within `log(A+1)/(A+1) - log(B+1)/(B+1)` of
`(log(B+1))²/2 - (log(A+1))²/2`. -/
theorem abs_harmonicLogWindowMoment_one_sub_logSquare_le
    {A B : ℕ} (hA : 8 ≤ A) (hAB : A ≤ B) :
    |harmonicLogWindowMoment 1 A B -
        (Real.log (B + 1 : ℕ) ^ (2 : ℕ) / 2 - Real.log (A + 1 : ℕ) ^ (2 : ℕ) / 2)| ≤
      RHTower.logPowDivId 1 (A + 1 : ℕ) -
        RHTower.logPowDivId 1 (B + 1 : ℕ) := by
  have hanti : AntitoneOn (RHTower.logPowDivId 1)
      (Set.Ici ((A + 1 : ℕ) : ℝ)) :=
    antitoneOn_logPowDivId_one.mono (fun x hx => by
    have hAreal : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hxA : ((A + 1 : ℕ) : ℝ) ≤ x := hx
    push_cast at hxA
    exact hAreal.trans (by linarith))
  have h := abs_harmonicLogWindowMoment_sub_integral_le 1 hAB hanti
  rw [intervalIntegral_logPowDivId 1 (by positivity) (by exact_mod_cast Nat.add_le_add_right hAB 1)] at h
  norm_num [harmonicLogMomentPrimitive] at h ⊢
  exact h

/-- `∑_{j ≤ 8} 1/j ≤ 8`. -/
theorem harmonicLogWindowMoment_zero_zero_eight_le :
    harmonicLogWindowMoment 0 0 8 ≤ 8 := by
  rw [harmonicLogWindowMoment]
  calc
    (∑ j ∈ Finset.Ioc (0 : ℕ) 8, Real.log (j : ℝ) ^ (0 : ℕ) / (j : ℝ)) ≤
        ∑ _j ∈ Finset.Ioc (0 : ℕ) 8, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [pow_zero]
      have hjpos : (0 : ℝ) < (j : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp hj).1
      rw [div_le_one hjpos]
      exact_mod_cast (Finset.mem_Ioc.mp hj).1
    _ = 8 := by norm_num

/-- `∑_{j ≤ 8} log j / j ≤ 56`. -/
theorem harmonicLogWindowMoment_one_zero_eight_le :
    harmonicLogWindowMoment 1 0 8 ≤ 56 := by
  rw [harmonicLogWindowMoment]
  calc
    (∑ j ∈ Finset.Ioc (0 : ℕ) 8, Real.log (j : ℝ) ^ (1 : ℕ) / (j : ℝ)) ≤
        ∑ _j ∈ Finset.Ioc (0 : ℕ) 8, (7 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [pow_one]
      have hjdata := Finset.mem_Ioc.mp hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjdata.1
      have hlogle : Real.log (j : ℝ) ≤ 7 := by
        have h := Real.log_le_sub_one_of_pos hjpos
        have hjle : (j : ℝ) ≤ 8 := by exact_mod_cast hjdata.2
        linarith
      rw [div_le_iff₀ hjpos]
      nlinarith [show (1 : ℝ) ≤ j by exact_mod_cast hjdata.1]
    _ = 56 := by norm_num

theorem harmonicLogMomentPrimitive_nat_succ_nonneg (m N : ℕ) :
    0 ≤ harmonicLogMomentPrimitive m (N + 1 : ℕ) := by
  rw [harmonicLogMomentPrimitive]
  exact div_nonneg (pow_nonneg (Real.log_nonneg (by
    exact_mod_cast (by omega : 1 ≤ N + 1))) (m + 1)) (by positivity)

theorem harmonicLogMomentPrimitive_zero_nat_succ_le
    {N : ℕ} (hN : N ≤ 8) : harmonicLogMomentPrimitive 0 (N + 1 : ℕ) ≤ 8 := by
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlogle : Real.log ((N + 1 : ℕ) : ℝ) ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos hpos
    have hcast : (((N + 1 : ℕ) : ℝ)) ≤ 9 := by exact_mod_cast Nat.add_le_add_right hN 1
    linarith
  norm_num [harmonicLogMomentPrimitive, Nat.cast_add, Nat.cast_one] at hlogle ⊢
  exact hlogle

theorem harmonicLogMomentPrimitive_one_nat_succ_le
    {N : ℕ} (hN : N ≤ 8) : harmonicLogMomentPrimitive 1 (N + 1 : ℕ) ≤ 32 := by
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 1))
  have hlogle : Real.log ((N + 1 : ℕ) : ℝ) ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos hpos
    have hcast : (((N + 1 : ℕ) : ℝ)) ≤ 9 := by exact_mod_cast Nat.add_le_add_right hN 1
    linarith
  have hsq : Real.log ((N + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ 64 := by nlinarith
  norm_num [harmonicLogMomentPrimitive, Nat.cast_add, Nat.cast_one] at hsq ⊢
  linarith

theorem logPowDivId_zero_nine_le : RHTower.logPowDivId 0 9 ≤ 1 := by
  norm_num [RHTower.logPowDivId]

theorem logPowDivId_one_nine_le : RHTower.logPowDivId 1 9 ≤ 1 := by
  have hlogle : Real.log (9 : ℝ) ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    norm_num at h
    exact h
  norm_num [RHTower.logPowDivId]
  linarith

private theorem abs_harmonicLogWindowMoment_zero_zero_sub_log_le_of_le_eight
    {N : ℕ} (hN : N ≤ 8) :
    |harmonicLogWindowMoment 0 0 N - Real.log (N + 1 : ℕ)| ≤ 20 := by
  have hsplit := harmonicLogWindowMoment_add 0 (A := 0) (B := N) (C := 8)
    (Nat.zero_le N) hN
  have hwindowLe : harmonicLogWindowMoment 0 0 N ≤
      harmonicLogWindowMoment 0 0 8 := by
    have htail := harmonicLogWindowMoment_nonneg 0 N 8
    linarith
  have hmainLe : Real.log (N + 1 : ℕ) ≤ 8 := by
    have h := harmonicLogMomentPrimitive_zero_nat_succ_le hN
    norm_num [harmonicLogMomentPrimitive, Nat.cast_add, Nat.cast_one] at h ⊢
    exact h
  have hwindowNonneg := harmonicLogWindowMoment_nonneg 0 0 N
  have hmainNonneg : 0 ≤ Real.log (N + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 1))
  calc
    |harmonicLogWindowMoment 0 0 N - Real.log (N + 1 : ℕ)| ≤
        |harmonicLogWindowMoment 0 0 N| + |-Real.log (N + 1 : ℕ)| := by
          simpa [sub_eq_add_neg] using
            abs_add_le (harmonicLogWindowMoment 0 0 N) (-Real.log (N + 1 : ℕ))
    _ = harmonicLogWindowMoment 0 0 N + Real.log (N + 1 : ℕ) := by
      rw [abs_of_nonneg hwindowNonneg, abs_neg, abs_of_nonneg hmainNonneg]
    _ ≤ 8 + 8 := add_le_add
      (hwindowLe.trans harmonicLogWindowMoment_zero_zero_eight_le) hmainLe
    _ ≤ 20 := by norm_num

private theorem abs_harmonicLogWindowMoment_zero_zero_sub_log_le_of_eight_le
    {N : ℕ} (hN : 8 ≤ N) :
    |harmonicLogWindowMoment 0 0 N - Real.log (N + 1 : ℕ)| ≤ 20 := by
  have hsplit := harmonicLogWindowMoment_add 0 (A := 0) (B := 8) (C := N)
    (by norm_num) hN
  have hheadMainNonneg : 0 ≤ Real.log (9 : ℕ) := Real.log_nonneg (by norm_num)
  have hheadMainLe : Real.log (9 : ℕ) ≤ 8 := by
    have h := harmonicLogMomentPrimitive_zero_nat_succ_le (N := 8) (by norm_num)
    norm_num [harmonicLogMomentPrimitive] at h ⊢
    exact h
  have hheadNonneg := harmonicLogWindowMoment_nonneg 0 0 8
  have hheadAbs : |harmonicLogWindowMoment 0 0 8 - Real.log (9 : ℕ)| ≤ 16 := by
    calc
      |harmonicLogWindowMoment 0 0 8 - Real.log (9 : ℕ)| ≤
          |harmonicLogWindowMoment 0 0 8| + |-Real.log (9 : ℕ)| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (harmonicLogWindowMoment 0 0 8) (-Real.log (9 : ℕ))
      _ = harmonicLogWindowMoment 0 0 8 + Real.log (9 : ℕ) := by
        rw [abs_of_nonneg hheadNonneg, abs_neg, abs_of_nonneg hheadMainNonneg]
      _ ≤ 8 + 8 := add_le_add harmonicLogWindowMoment_zero_zero_eight_le hheadMainLe
      _ = 16 := by norm_num
  have htail := abs_harmonicLogWindowMoment_zero_sub_log_le
    (A := 8) (B := N) (by norm_num) hN
  have hendNonneg : 0 ≤ RHTower.logPowDivId 0 (N + 1 : ℕ) := by
    norm_num [RHTower.logPowDivId]
    positivity
  have htailAbs :
      |harmonicLogWindowMoment 0 8 N -
          (Real.log (N + 1 : ℕ) - Real.log (9 : ℕ))| ≤ 1 :=
    htail.trans ((sub_le_self _ hendNonneg).trans logPowDivId_zero_nine_le)
  calc
    |harmonicLogWindowMoment 0 0 N - Real.log (N + 1 : ℕ)| =
        |(harmonicLogWindowMoment 0 0 8 - Real.log (9 : ℕ)) +
          (harmonicLogWindowMoment 0 8 N -
            (Real.log (N + 1 : ℕ) - Real.log (9 : ℕ)))| := by
              rw [← hsplit]
              ring_nf
    _ ≤ |harmonicLogWindowMoment 0 0 8 - Real.log (9 : ℕ)| +
        |harmonicLogWindowMoment 0 8 N -
          (Real.log (N + 1 : ℕ) - Real.log (9 : ℕ))| := abs_add_le _ _
    _ ≤ 16 + 1 := add_le_add hheadAbs htailAbs
    _ ≤ 20 := by norm_num

/-- For every `N`, `|∑_{j ≤ N} 1/j - log(N+1)| ≤ 20`. -/
theorem abs_harmonicLogWindowMoment_zero_zero_sub_log_le (N : ℕ) :
    |harmonicLogWindowMoment 0 0 N - Real.log (N + 1 : ℕ)| ≤ 20 := by
  by_cases hN : N ≤ 8
  · exact abs_harmonicLogWindowMoment_zero_zero_sub_log_le_of_le_eight hN
  · exact abs_harmonicLogWindowMoment_zero_zero_sub_log_le_of_eight_le (by omega)

/-- For all `A ≤ B`, `|∑_{A < j ≤ B} 1/j - (log(B+1) - log(A+1))| ≤ 40`. -/
theorem abs_harmonicLogWindowMoment_zero_sub_log_uniform_le
    {A B : ℕ} (hAB : A ≤ B) :
    |harmonicLogWindowMoment 0 A B -
        (Real.log (B + 1 : ℕ) - Real.log (A + 1 : ℕ))| ≤ 40 := by
  have hsplit := harmonicLogWindowMoment_add 0 (A := 0) (B := A) (C := B)
    (Nat.zero_le A) hAB
  have hA := abs_harmonicLogWindowMoment_zero_zero_sub_log_le A
  have hB := abs_harmonicLogWindowMoment_zero_zero_sub_log_le B
  calc
    |harmonicLogWindowMoment 0 A B -
        (Real.log (B + 1 : ℕ) - Real.log (A + 1 : ℕ))| =
      |(harmonicLogWindowMoment 0 0 B - Real.log (B + 1 : ℕ)) -
        (harmonicLogWindowMoment 0 0 A - Real.log (A + 1 : ℕ))| := by
          rw [← hsplit]
          ring_nf
    _ ≤ |harmonicLogWindowMoment 0 0 B - Real.log (B + 1 : ℕ)| +
        |harmonicLogWindowMoment 0 0 A - Real.log (A + 1 : ℕ)| := by
          have htri := abs_sub_le
            (harmonicLogWindowMoment 0 0 B - Real.log (B + 1 : ℕ)) 0
            (harmonicLogWindowMoment 0 0 A - Real.log (A + 1 : ℕ))
          rw [sub_zero, zero_sub, abs_neg] at htri
          exact htri
    _ ≤ 20 + 20 := add_le_add hB hA
    _ = 40 := by norm_num

private theorem abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le_of_le_eight
    {N : ℕ} (hN : N ≤ 8) :
    |harmonicLogWindowMoment 1 0 N - Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2| ≤ 100 := by
  have hsplit := harmonicLogWindowMoment_add 1 (A := 0) (B := N) (C := 8)
    (Nat.zero_le N) hN
  have hwindowLe : harmonicLogWindowMoment 1 0 N ≤
      harmonicLogWindowMoment 1 0 8 := by
    have htail := harmonicLogWindowMoment_nonneg 1 N 8
    linarith
  have hmainLe : Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2 ≤ 32 := by
    have h := harmonicLogMomentPrimitive_one_nat_succ_le hN
    norm_num [harmonicLogMomentPrimitive, Nat.cast_add, Nat.cast_one] at h ⊢
    exact h
  have hwindowNonneg := harmonicLogWindowMoment_nonneg 1 0 N
  have hmainNonneg : 0 ≤ Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2 := by positivity
  calc
    |harmonicLogWindowMoment 1 0 N - Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2| ≤
        |harmonicLogWindowMoment 1 0 N| + |-(Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2)| := by
          simpa [sub_eq_add_neg] using
            abs_add_le (harmonicLogWindowMoment 1 0 N)
              (-(Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2))
    _ = harmonicLogWindowMoment 1 0 N + Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2 := by
      rw [abs_of_nonneg hwindowNonneg, abs_neg, abs_of_nonneg hmainNonneg]
    _ ≤ 56 + 32 := add_le_add
      (hwindowLe.trans harmonicLogWindowMoment_one_zero_eight_le) hmainLe
    _ ≤ 100 := by norm_num

private theorem abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le_of_eight_le
    {N : ℕ} (hN : 8 ≤ N) :
    |harmonicLogWindowMoment 1 0 N - Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2| ≤ 100 := by
  have hsplit := harmonicLogWindowMoment_add 1 (A := 0) (B := 8) (C := N)
    (by norm_num) hN
  have hheadMainNonneg : 0 ≤ Real.log (9 : ℕ) ^ (2 : ℕ) / 2 := by positivity
  have hheadMainLe : Real.log (9 : ℕ) ^ (2 : ℕ) / 2 ≤ 32 := by
    have h := harmonicLogMomentPrimitive_one_nat_succ_le (N := 8) (by norm_num)
    norm_num [harmonicLogMomentPrimitive] at h ⊢
    exact h
  have hheadNonneg := harmonicLogWindowMoment_nonneg 1 0 8
  have hheadAbs : |harmonicLogWindowMoment 1 0 8 - Real.log (9 : ℕ) ^ (2 : ℕ) / 2| ≤ 88 := by
    calc
      |harmonicLogWindowMoment 1 0 8 - Real.log (9 : ℕ) ^ (2 : ℕ) / 2| ≤
          |harmonicLogWindowMoment 1 0 8| + |-(Real.log (9 : ℕ) ^ (2 : ℕ) / 2)| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (harmonicLogWindowMoment 1 0 8)
                (-(Real.log (9 : ℕ) ^ (2 : ℕ) / 2))
      _ = harmonicLogWindowMoment 1 0 8 + Real.log (9 : ℕ) ^ (2 : ℕ) / 2 := by
        rw [abs_of_nonneg hheadNonneg, abs_neg, abs_of_nonneg hheadMainNonneg]
      _ ≤ 56 + 32 := add_le_add harmonicLogWindowMoment_one_zero_eight_le hheadMainLe
      _ = 88 := by norm_num
  have htail := abs_harmonicLogWindowMoment_one_sub_logSquare_le
    (A := 8) (B := N) (by norm_num) hN
  have hendNonneg : 0 ≤ RHTower.logPowDivId 1 (N + 1 : ℕ) := by
    rw [RHTower.logPowDivId]
    have hOne : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ N + 1)
    exact div_nonneg (pow_nonneg (Real.log_nonneg hOne) 1) (by positivity)
  have htailAbs :
      |harmonicLogWindowMoment 1 8 N -
          (Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2 - Real.log (9 : ℕ) ^ (2 : ℕ) / 2)| ≤ 1 :=
    htail.trans ((sub_le_self _ hendNonneg).trans logPowDivId_one_nine_le)
  calc
    |harmonicLogWindowMoment 1 0 N - Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2| =
        |(harmonicLogWindowMoment 1 0 8 - Real.log (9 : ℕ) ^ (2 : ℕ) / 2) +
          (harmonicLogWindowMoment 1 8 N -
            (Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2 - Real.log (9 : ℕ) ^ (2 : ℕ) / 2))| := by
              rw [← hsplit]
              ring_nf
    _ ≤ |harmonicLogWindowMoment 1 0 8 - Real.log (9 : ℕ) ^ (2 : ℕ) / 2| +
        |harmonicLogWindowMoment 1 8 N -
          (Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2 - Real.log (9 : ℕ) ^ (2 : ℕ) / 2)| := abs_add_le _ _
    _ ≤ 88 + 1 := add_le_add hheadAbs htailAbs
    _ ≤ 100 := by norm_num

/-- For every `N`, `|∑_{j ≤ N} log j / j - (log(N+1))²/2| ≤ 100`. -/
theorem abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le (N : ℕ) :
    |harmonicLogWindowMoment 1 0 N - Real.log (N + 1 : ℕ) ^ (2 : ℕ) / 2| ≤ 100 := by
  by_cases hN : N ≤ 8
  · exact abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le_of_le_eight hN
  · exact abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le_of_eight_le (by omega)

/-- For all `A ≤ B`, `|∑_{A < j ≤ B} log j / j - ((log(B+1))²/2 - (log(A+1))²/2)| ≤ 200`. -/
theorem abs_harmonicLogWindowMoment_one_sub_logSquare_uniform_le
    {A B : ℕ} (hAB : A ≤ B) :
    |harmonicLogWindowMoment 1 A B -
        (Real.log (B + 1 : ℕ) ^ (2 : ℕ) / 2 - Real.log (A + 1 : ℕ) ^ (2 : ℕ) / 2)| ≤ 200 := by
  have hsplit := harmonicLogWindowMoment_add 1 (A := 0) (B := A) (C := B)
    (Nat.zero_le A) hAB
  have hA := abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le A
  have hB := abs_harmonicLogWindowMoment_one_zero_sub_logSquare_le B
  calc
    |harmonicLogWindowMoment 1 A B -
        (Real.log (B + 1 : ℕ) ^ (2 : ℕ) / 2 - Real.log (A + 1 : ℕ) ^ (2 : ℕ) / 2)| =
      |(harmonicLogWindowMoment 1 0 B - Real.log (B + 1 : ℕ) ^ (2 : ℕ) / 2) -
        (harmonicLogWindowMoment 1 0 A - Real.log (A + 1 : ℕ) ^ (2 : ℕ) / 2)| := by
          rw [← hsplit]
          ring_nf
    _ ≤ |harmonicLogWindowMoment 1 0 B - Real.log (B + 1 : ℕ) ^ (2 : ℕ) / 2| +
        |harmonicLogWindowMoment 1 0 A - Real.log (A + 1 : ℕ) ^ (2 : ℕ) / 2| := by
          have htri := abs_sub_le
            (harmonicLogWindowMoment 1 0 B - Real.log (B + 1 : ℕ) ^ (2 : ℕ) / 2) 0
            (harmonicLogWindowMoment 1 0 A - Real.log (A + 1 : ℕ) ^ (2 : ℕ) / 2)
          rw [sub_zero, zero_sub, abs_neg] at htri
          exact htri
    _ ≤ 100 + 100 := add_le_add hB hA
    _ = 200 := by norm_num

end

end RHTower.Sieve
