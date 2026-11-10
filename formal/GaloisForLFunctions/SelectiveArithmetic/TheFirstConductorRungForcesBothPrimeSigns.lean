import GaloisForLFunctions.SelectiveArithmetic.TheSignIsSquareRootCancellationOfTheRieszMean
import GaloisForLFunctions.SelectiveArithmetic.BoundedShapesDoNotDecideFeasibility
import GaloisForLFunctions.RHTower.VonMangoldtNonPrimeSqrtSum

/-!
# The first conductor rung forces both prime signs

Missing one prime sign makes a real character's Riesz mean equal, up to ramified
primes and proper prime powers, to a signed untwisted Riesz mean. Ramified primes
cost at most `2a log q`; proper powers cost `O(a² exp a)`.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-- A prime at which a Dirichlet character vanishes divides its modulus. -/
theorem prime_dvd_of_character_eq_zero {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hzero : χ (p : ZMod q) = 0) : p ∣ q := by
  by_contra hn
  have hu := (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hn)
  exact (hu.map χ.toMonoidHom).ne_zero hzero

/-- The total von Mangoldt mass of ramified primes is at most `log q`. -/
theorem sum_ramified_prime_mass_le {q N : ℕ} (hq : q ≠ 0) :
    ∑ p ∈ (Icc 2 N).filter (fun p => p.Prime ∧ p ∣ q), (Λ p : ℝ) ≤ Real.log q := by
  rw [← ArithmeticFunction.vonMangoldt_sum]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hp).2.2, hq⟩
  · intro p _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- When every unramified prime has sign `s`, only ramification and proper powers
separate the character Riesz mean from the signed prime main term. -/
theorem riesz_twist_error_le {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    {a s : ℝ} (ha : 0 ≤ a) (hs : |s| = 1)
    (hprime : ∀ p : ℕ, p.Prime → p ≤ ⌊Real.exp (2 * a)⌋₊ →
      χ (p : ZMod q) = 0 ∨ χ (p : ZMod q) = (s : ℂ)) :
    |(∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n * (2 * a - Real.log n)) -
      s * ∑ n ∈ Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n)| ≤
      2 * a * Real.log q +
        4 * a * ∑ n ∈ (Icc 2 ⌊Real.exp (2 * a)⌋₊).filter (fun n => ¬ n.Prime), (Λ n : ℝ) := by
  classical
  let N := ⌊Real.exp (2 * a)⌋₊
  have hpoint (n : ℕ) (hn : n ∈ Icc 2 N) :
      |(twistWeight χ n - s * (Λ n : ℝ)) * (2 * a - Real.log n)| ≤
        2 * a * (if n.Prime ∧ n ∣ q then (Λ n : ℝ) else 0) +
          4 * a * (if ¬ n.Prime then (Λ n : ℝ) else 0) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := (mem_Icc.mp hn).1; omega : 0 < n)
    have hnE : (n : ℝ) ≤ Real.exp (2 * a) :=
      (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ N).trans
        (Nat.floor_le (Real.exp_pos _).le)
    have hlog : Real.log n ≤ 2 * a := by
      simpa only [Real.log_exp] using Real.log_le_log hn0 hnE
    have hw : 0 ≤ 2 * a - Real.log n := sub_nonneg.mpr hlog
    have hw' : 2 * a - Real.log n ≤ 2 * a := by
      linarith only [Real.log_natCast_nonneg n]
    have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    by_cases hp : n.Prime
    · rcases hprime n hp (mem_Icc.mp hn).2 with hz | hz
      · have hd := prime_dvd_of_character_eq_zero χ hp hz
        simp only [twistWeight, hz, Complex.zero_re, mul_zero, zero_sub,
          abs_mul, abs_neg, hs, one_mul, abs_of_nonneg hΛ, abs_of_nonneg hw,
          if_pos (And.intro hp hd), if_false, not_true_eq_false, hp, add_zero]
        nlinarith only [mul_le_mul_of_nonneg_left hw' hΛ]
      · have he : twistWeight χ n - s * (Λ n : ℝ) = 0 := by
          simp only [twistWeight, hz, Complex.ofReal_re]
          ring
        rw [he, zero_mul, abs_zero]
        positivity
    · have he : |twistWeight χ n - s * (Λ n : ℝ)| ≤ 2 * (Λ n : ℝ) := by
        have htw := dominated_twistWeight χ n
        have hsm : |s * (Λ n : ℝ)| = Λ n := by rw [abs_mul, hs, one_mul, abs_of_nonneg hΛ]
        have htri := abs_sub (twistWeight χ n) (s * (Λ n : ℝ))
        rw [hsm] at htri
        linarith only [htri, htw]
      simp only [hp, false_and, if_false, not_false_eq_true, if_true, mul_zero, zero_add]
      rw [abs_mul, abs_of_nonneg hw]
      have hm := mul_le_mul he hw' hw (by positivity : (0 : ℝ) ≤ 2 * Λ n)
      nlinarith only [hm]
  have he : (∑ n ∈ Icc 2 N, twistWeight χ n * (2 * a - Real.log n)) -
      s * ∑ n ∈ Icc 2 N, (Λ n : ℝ) * (2 * a - Real.log n) =
      ∑ n ∈ Icc 2 N, (twistWeight χ n - s * (Λ n : ℝ)) * (2 * a - Real.log n) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  change |_ - s * _| ≤ _
  rw [he]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpoint).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter, ← sum_filter]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (sum_ramified_prime_mass_le hq) (by positivity)) _

/-- Proper prime powers up to `exp(2a)` have von Mangoldt mass `O(a exp a)`. -/
theorem sum_nonprime_mass_le_exp {a : ℝ} (ha : 0 ≤ a) :
    ∑ n ∈ (Icc 2 ⌊Real.exp (2 * a)⌋₊).filter (fun n => ¬ n.Prime), (Λ n : ℝ) ≤
      Real.exp a * (4 * a + 4 * Real.log 4 + 16) := by
  classical
  let N := ⌊Real.exp (2 * a)⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa only [Nat.cast_one] using Real.one_le_exp (by linarith : 0 ≤ 2 * a))
  have hNE : (N : ℝ) ≤ Real.exp (2 * a) := Nat.floor_le (Real.exp_pos _).le
  have hlog : Real.log N ≤ 2 * a := by
    simpa only [Real.log_exp] using Real.log_le_log
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNE
  have hsqrt (n : ℕ) (hn : n ∈ Icc 2 N) : Real.sqrt n ≤ Real.exp a := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have he : Real.exp a ^ 2 = Real.exp (2 * a) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    exact (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ N).trans hNE
  have hsum : ∑ n ∈ (Icc 2 N).filter (fun n => ¬ n.Prime), (Λ n : ℝ) ≤
      Real.exp a * ∑ n ∈ (Ioc 0 N).filter (fun n => ¬ n.Prime), (Λ n : ℝ) / Real.sqrt n := by
    calc
      _ ≤ Real.exp a * ∑ n ∈ (Icc 2 N).filter (fun n => ¬ n.Prime), (Λ n : ℝ) / Real.sqrt n := by
        rw [mul_sum]
        apply sum_le_sum
        intro n hn
        have hn0 : (0 : ℝ) < n := by
          exact_mod_cast (by have := (mem_Icc.mp (mem_filter.mp hn).1).1; omega : 0 < n)
        have hsp := Real.sqrt_pos.mpr hn0
        rw [mul_div_assoc, le_div_iff₀ hsp]
        nlinarith only [mul_le_mul_of_nonneg_left (hsqrt n (mem_filter.mp hn).1)
          (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (by
          intro n hn
          obtain ⟨hn, hp⟩ := mem_filter.mp hn
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := (mem_Icc.mp hn).1; omega,
            (mem_Icc.mp hn).2⟩, hp⟩) (fun n _ _ => by positivity)) (Real.exp_pos _).le
  refine hsum.trans ((mul_le_mul_of_nonneg_left
    (_root_.RHTower.sum_nonprime_vonMangoldt_div_sqrt_le hN) (Real.exp_pos _).le).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith only [hlog]

end GaloisForLFunctions.SelectiveArithmetic
