import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction
import GaloisForLFunctions.RHTower.Sieve.HeathBrownIdentity

/-!
# Exact reconstruction from short Möbius coefficients

The square of the truncated inversion defect starts beyond the square
of its support threshold. Below that threshold the inverse is exactly
twice its truncation minus the truncation, zeta, truncation composition.
Logarithmic delay profiles inherit this finite identity with every sign
and cutoff retained.
-/

noncomputable section
open scoped BigOperators
open ArithmeticFunction

namespace RHTower

/-- The short inverse, retaining the terminal cutoff of the profile. -/
def logarithmicShortMobiusInverse (U : ℕ) (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation (Sieve.truncatedMoebius U) f T

theorem moebius_eq_short_square_correction (U n : ℕ) (hn : n < (U + 1) ^ 2) :
    (moebius n : ℝ) = 2 * Sieve.truncatedMoebius U n -
      (Sieve.truncatedMoebius U *
        (Sieve.truncatedMoebius U * (zeta : ArithmeticFunction ℝ))) n := by
  let M := Sieve.truncatedMoebius U
  let E := Sieve.moebiusZetaDefect U
  let Z : ArithmeticFunction ℝ := zeta
  let mu : ArithmeticFunction ℝ := moebius
  have hmz : mu * Z = 1 := coe_moebius_mul_coe_zeta
  have he : mu * E = mu - M := by
    dsimp only [E, Sieve.moebiusZetaDefect]
    change mu * (1 - M * Z) = mu - M
    rw [mul_sub, mul_one, mul_comm M Z, ← mul_assoc, hmz, one_mul]
  have halg : mu = M + M - M * (M * Z) + mu * E ^ 2 := by
    calc
      _ = M + M - M * (M * Z) + (mu - M) * E := by
        rw [sub_mul, he]
        dsimp only [E, Sieve.moebiusZetaDefect]
        change mu = M + M - M * (M * Z) + (mu - M - M * (1 - M * Z))
        ring
      _ = _ := by
        congr 1
        rw [pow_two, ← mul_assoc, he]
  have hmu : Sieve.VanishesBelow mu 1 := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact ArithmeticFunction.map_zero
  have hzero : (mu * E ^ 2) n = 0 := by
    apply Sieve.vanishesBelow_mul hmu (Sieve.moebiusZetaDefect_pow_vanishesBelow U 2) n
    simpa only [one_mul] using hn
  have h := congrArg (fun a : ArithmeticFunction ℝ => a n) halg
  change (moebius n : ℝ) = M n + M n - (M * (M * Z)) n + (mu * E ^ 2) n at h
  rw [hzero, add_zero] at h
  change (moebius n : ℝ) = 2 * M n - (M * (M * Z)) n
  linarith only [h]

private theorem dilation_arithmetic_mul (a b : ArithmeticFunction ℝ) (f : ℝ → ℝ) :
    logarithmicWeightedDilation (a * b) f =
      logarithmicWeightedDilation a (logarithmicWeightedDilation b f) := by
  funext T
  exact (logarithmicWeightedDilation_comp a b f T).symm

private theorem dilation_arithmetic_zeta (f : ℝ → ℝ) :
    logarithmicDilationSum f = logarithmicWeightedDilation (zeta : ArithmeticFunction ℝ) f := by
  funext T
  unfold logarithmicDilationSum logarithmicWeightedDilation
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg hn0, Nat.cast_one]

/-- The full inverse is recovered using only coefficients at most `U`
when the squared truncation defect lies beyond the terminal cutoff. -/
theorem logarithmicMobiusInverse_eq_short_correction (U : ℕ) (f : ℝ → ℝ) {T : ℝ}
    (hU : ⌊Real.exp T⌋₊ < (U + 1) ^ 2) :
    logarithmicMobiusInverse f T = 2 * logarithmicShortMobiusInverse U f T -
      logarithmicShortMobiusInverse U
        (logarithmicShortMobiusInverse U (logarithmicDilationSum f)) T := by
  change logarithmicMobiusInverse f T =
    2 * logarithmicWeightedDilation (Sieve.truncatedMoebius U) f T -
      logarithmicWeightedDilation (Sieve.truncatedMoebius U)
        (logarithmicWeightedDilation (Sieve.truncatedMoebius U) (logarithmicDilationSum f)) T
  rw [dilation_arithmetic_zeta]
  simp only [← dilation_arithmetic_mul]
  unfold logarithmicMobiusInverse logarithmicWeightedDilation
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [moebius_eq_short_square_correction U n ((Finset.mem_Icc.mp hn).2.trans_lt hU)]
  ring

theorem floor_exp_lt_succ_floor_exp_half_sq (T : ℝ) :
    ⌊Real.exp T⌋₊ < (⌊Real.exp (T / 2)⌋₊ + 1) ^ 2 := by
  have he : Real.exp T = Real.exp (T / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp T < ((⌊Real.exp (T / 2)⌋₊ : ℝ) + 1) ^ 2 := by
    rw [he]
    exact (sq_lt_sq₀ (Real.exp_pos (T / 2)).le
      (by positivity : (0 : ℝ) ≤ (⌊Real.exp (T / 2)⌋₊ : ℝ) + 1)).2 (Nat.lt_floor_add_one _)
  have h := (Nat.floor_le (Real.exp_pos T).le).trans_lt hs
  exact_mod_cast h

theorem logarithmicMobiusInverse_eq_half_correction (f : ℝ → ℝ) (T : ℝ) :
    logarithmicMobiusInverse f T =
      2 * logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ f T -
        logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊
          (logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ (logarithmicDilationSum f)) T :=
  logarithmicMobiusInverse_eq_short_correction _ f (floor_exp_lt_succ_floor_exp_half_sq T)

theorem logarithmicShortMobiusInverse_eq_prefix (U : ℕ) (f : ℝ → ℝ) {T : ℝ}
    (hU : U ≤ ⌊Real.exp T⌋₊) :
    logarithmicShortMobiusInverse U f T =
      ∑ n ∈ Finset.Icc 1 U, (moebius n : ℝ) * f (T - Real.log n) := by
  have hs : Finset.Icc 1 U ⊆ Finset.Icc 1 ⌊Real.exp T⌋₊ :=
    fun n hn => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hU⟩
  unfold logarithmicShortMobiusInverse logarithmicWeightedDilation
  calc
    _ = ∑ n ∈ Finset.Icc 1 U, Sieve.truncatedMoebius U n * f (T - Real.log n) := by
      symm
      apply Finset.sum_subset hs
      intro n hn hnU
      have hn' : ¬ n ≤ U := by
        intro h
        exact hnU (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, h⟩)
      simp only [Sieve.truncatedMoebius_apply, if_neg hn', zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Sieve.truncatedMoebius_apply, if_pos (Finset.mem_Icc.mp hn).2]

/-- At the half cutoff both short inverse factors range independently
over the same full interval. No product-boundary terms are omitted. -/
theorem logarithmicShortMobiusInverse_twice_eq_square (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊
      (logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ f) T =
      ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
          (moebius a : ℝ) * (moebius b : ℝ) * f (T - Real.log (a * b : ℕ)) := by
  let U := ⌊Real.exp (T / 2)⌋₊
  have hU : U ≤ ⌊Real.exp T⌋₊ := Nat.floor_mono
    (Real.exp_le_exp.mpr (by linarith only [hT]))
  have hsq : (U : ℝ) ^ 2 ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (T / 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.exp_pos _).le) 2
      _ = _ := by rw [sq, ← Real.exp_add]; congr 1; ring
  rw [logarithmicShortMobiusInverse_eq_prefix U _ hU]
  apply Finset.sum_congr rfl
  intro a ha
  have hapos : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have haU : (a : ℝ) ≤ U := by exact_mod_cast (Finset.mem_Icc.mp ha).2
  have hshift : U ≤ ⌊Real.exp (T - Real.log a)⌋₊ := by
    rw [Nat.le_floor_iff (Real.exp_pos _).le, Real.exp_sub, Real.exp_log hapos,
      le_div_iff₀ hapos]
    exact (mul_le_mul_of_nonneg_left haU (Nat.cast_nonneg U)).trans (by simpa only [sq] using hsq)
  rw [logarithmicShortMobiusInverse_eq_prefix U _ hshift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
  rw [Nat.cast_mul, Real.log_mul hapos.ne' hbpos.ne', sub_sub]
  ring

end RHTower
