import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeSquarefreeStepAndMultiOctaveL2Energy
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusLimit
import GaloisForLFunctions.RHTower.Sieve.MoebiusSharpLittleO
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Coprime Möbius cancellation and odd dilation means

Restricting the Möbius function to integers coprime to any fixed natural
modulus preserves its mean-zero limit. The prime-deletion recurrence is a
bounded dilation contraction, with the unconditional Mertens limit as its
base. Repeated prime factors leave the coprimality condition unchanged;
the zero modulus is supported only at the unit.

Every finite product of Möbius dilations factors through a single common
Möbius power with a coprimality restriction. For an odd number of factors,
that power reduces to the Möbius function itself. Consequently every fixed
odd multiplicative dilation product has mean zero, without pairwise
coprimality or squarefreeness assumptions on its multipliers.
-/

open Finset Filter
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The Möbius function restricted to integers coprime to Q. -/
def coprimeMoebiusIndicator (Q n : ℕ) : ℝ :=
  if Nat.Coprime Q n then ((μ n : ℤ) : ℝ) else 0

/-- The finite prefix sum of the coprime-restricted Möbius function. -/
def coprimeMoebiusSum (Q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, coprimeMoebiusIndicator Q n

/-- The coprime-restricted Möbius prefix at the natural floor of x, normalized by x. -/
def coprimeMoebiusMean (Q : ℕ) (x : ℝ) : ℝ :=
  coprimeMoebiusSum Q ⌊x⌋₊ / x

/-- Every coprime-restricted Möbius value has modulus at most one. -/
theorem abs_coprimeMoebiusIndicator_le_one (Q n : ℕ) :
    |coprimeMoebiusIndicator Q n| ≤ 1 := by
  unfold coprimeMoebiusIndicator
  split_ifs
  · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · norm_num

/-- The modulus of the restricted prefix is at most its length. -/
theorem abs_coprimeMoebiusSum_le (Q N : ℕ) : |coprimeMoebiusSum Q N| ≤ (N : ℝ) := by
  unfold coprimeMoebiusSum
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, |coprimeMoebiusIndicator Q n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => abs_coprimeMoebiusIndicator_le_one Q n
    _ = _ := by simp

/-- The normalized restricted mean is bounded by one on the whole real line. -/
theorem abs_coprimeMoebiusMean_le_one (Q : ℕ) (x : ℝ) :
    |coprimeMoebiusMean Q x| ≤ 1 := by
  by_cases hx : x ≤ 0
  · simp [coprimeMoebiusMean, Nat.floor_of_nonpos hx, coprimeMoebiusSum]
  · have hx0 : 0 < x := lt_of_not_ge hx
    rw [coprimeMoebiusMean, abs_div, abs_of_pos hx0]
    exact (div_le_one hx0).mpr ((abs_coprimeMoebiusSum_le _ _).trans (Nat.floor_le hx0.le))

/-- Repeating a prime factor, or any divisor of the modulus, leaves its indicator unchanged. -/
theorem coprimeMoebiusIndicator_mul_of_dvd {p Q : ℕ} (hpQ : p ∣ Q) (n : ℕ) :
    coprimeMoebiusIndicator (p * Q) n = coprimeMoebiusIndicator Q n := by
  have hc : Nat.Coprime (p * Q) n ↔ Nat.Coprime Q n :=
    ⟨fun h => (Nat.coprime_mul_iff_left.mp h).2,
      fun h => Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.of_dvd_left hpQ h, h⟩⟩
  unfold coprimeMoebiusIndicator
  by_cases hQn : Nat.Coprime Q n
  · rw [if_pos hQn, if_pos (hc.mpr hQn)]
  · rw [if_neg hQn, if_neg (fun h => hQn (hc.mp h))]

/-- Multiplying the modulus by one of its divisors leaves the normalized mean unchanged. -/
theorem coprimeMoebiusMean_mul_of_dvd {p Q : ℕ} (hpQ : p ∣ Q) (x : ℝ) :
    coprimeMoebiusMean (p * Q) x = coprimeMoebiusMean Q x := by
  unfold coprimeMoebiusMean coprimeMoebiusSum
  simp_rw [coprimeMoebiusIndicator_mul_of_dvd hpQ]

/-- Exact prime deletion for the coprime-restricted Möbius indicator. -/
theorem coprimeMoebiusIndicator_prime_relation {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) (n : ℕ) :
    coprimeMoebiusIndicator Q n = coprimeMoebiusIndicator (p * Q) n -
      if p ∣ n then coprimeMoebiusIndicator (p * Q) (n / p) else 0 := by
  have hQp : Nat.Coprime Q p := (hp.coprime_iff_not_dvd.mpr hPQ).symm
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hQpm : Nat.Coprime Q (p * m) ↔ Nat.Coprime Q m :=
      ⟨fun h => (Nat.coprime_mul_iff_right.mp h).2,
        fun h => Nat.coprime_mul_iff_right.mpr ⟨hQp, h⟩⟩
    have hbad : ¬ Nat.Coprime (p * Q) (p * m) := fun h =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_left.mp h).1) (dvd_mul_right p m)
    have hpmul : p ∣ p * m := dvd_mul_right p m
    unfold coprimeMoebiusIndicator
    rw [if_neg hbad, if_pos hpmul, Nat.mul_div_cancel_left m hp.pos, zero_sub]
    by_cases hQm : Nat.Coprime Q m
    · rw [if_pos (hQpm.mpr hQm)]
      by_cases hpm : p ∣ m
      · have hnot : ¬ Nat.Coprime p m := fun h => (hp.coprime_iff_not_dvd.mp h) hpm
        have hz : μ (p * m) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree
          (fun h => hnot (Nat.coprime_of_squarefree_mul h))
        have hbadm : ¬ Nat.Coprime (p * Q) m := fun h => hnot (Nat.coprime_mul_iff_left.mp h).1
        rw [if_neg hbadm, hz, Int.cast_zero, neg_zero]
      · have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
        have hgoodm : Nat.Coprime (p * Q) m := Nat.coprime_mul_iff_left.mpr ⟨hcop, hQm⟩
        rw [if_pos hgoodm, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
          ArithmeticFunction.moebius_apply_prime hp]
        simp
    · rw [if_neg (fun h => hQm (hQpm.mp h)),
        if_neg (fun h => hQm (Nat.coprime_mul_iff_left.mp h).2), neg_zero]
  · unfold coprimeMoebiusIndicator
    rw [if_neg hpn, sub_zero]
    by_cases hQn : Nat.Coprime Q n
    · have hgood : Nat.Coprime (p * Q) n :=
        Nat.coprime_mul_iff_left.mpr ⟨hp.coprime_iff_not_dvd.mpr hpn, hQn⟩
      rw [if_pos hQn, if_pos hgood]
    · rw [if_neg hQn, if_neg (fun h => hQn (Nat.coprime_mul_iff_left.mp h).2)]

/-- Exact prime deletion for the finite restricted prefix. -/
theorem coprimeMoebiusSum_prime_relation {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) (N : ℕ) :
    coprimeMoebiusSum Q N = coprimeMoebiusSum (p * Q) N -
      coprimeMoebiusSum (p * Q) (N / p) := by
  classical
  unfold coprimeMoebiusSum
  simp_rw [coprimeMoebiusIndicator_prime_relation hp hPQ]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter,
    sum_Icc_filter_dvd_eq_sum_Icc_div hp.pos]
  simp only [Nat.mul_div_cancel_left _ hp.pos]

/-- Prime deletion gives a minus dilation recurrence for the normalized mean. -/
theorem coprimeMoebiusMean_prime_relation {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q) (x : ℝ) :
    coprimeMoebiusMean Q x = coprimeMoebiusMean (p * Q) x -
      (1 / (p : ℝ)) * coprimeMoebiusMean (p * Q) (x / p) := by
  unfold coprimeMoebiusMean
  rw [Nat.floor_div_natCast, coprimeMoebiusSum_prime_relation hp hPQ]
  by_cases hx : x = 0
  · simp [hx]
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp

/-- Deleting one new prime preserves a zero limit through the bounded contraction theorem. -/
theorem tendsto_coprimeMoebiusMean_prime_step {p Q : ℕ}
    (hp : p.Prime) (hPQ : ¬ p ∣ Q)
    (hlim : Tendsto (coprimeMoebiusMean Q) atTop (𝓝 0)) :
    Tendsto (coprimeMoebiusMean (p * Q)) atTop (𝓝 0) := by
  have h := tendsto_of_div_contraction (p : ℝ) (by exact_mod_cast hp.one_lt)
    (coprimeMoebiusMean (p * Q)) (coprimeMoebiusMean Q) 0 1 (by norm_num)
    (abs_coprimeMoebiusMean_le_one (p * Q)) hlim (coprimeMoebiusMean_prime_relation hp hPQ)
  simpa only [mul_zero] using h

/-- The modulus-one restricted mean tends to zero by the unconditional Mertens limit. -/
theorem tendsto_coprimeMoebiusMean_one : Tendsto (coprimeMoebiusMean 1) atTop (𝓝 0) := by
  have hcount (N : ℕ) : coprimeMoebiusSum 1 N =
      ∑ n ∈ Finset.range (N + 1), ((μ n : ℤ) : ℝ) := by
    unfold coprimeMoebiusSum
    simp only [coprimeMoebiusIndicator, Nat.coprime_one_left_eq_true, if_true]
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by rfl,
      Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ N + 1)]
    simp
  have hnorm (N : ℕ) :
      ‖∑ n ∈ Finset.range (N + 1), (μ n : ℂ)‖ = |coprimeMoebiusSum 1 N| := by
    rw [hcount]
    have hcast : (∑ n ∈ Finset.range (N + 1), (μ n : ℂ)) =
        ((∑ n ∈ Finset.range (N + 1), ((μ n : ℤ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hkey : Tendsto (fun x : ℝ => |coprimeMoebiusMean 1 x|) atTop (𝓝 0) := by
    apply tendsto_norm_sum_moebius_div.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    rw [coprimeMoebiusMean, abs_div, abs_of_pos hx0, hnorm]
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hkey

/-- The zero-modulus restricted mean tends to zero because only the unit contributes. -/
theorem tendsto_coprimeMoebiusMean_zero : Tendsto (coprimeMoebiusMean 0) atTop (𝓝 0) := by
  have hcount (N : ℕ) : coprimeMoebiusSum 0 N = if 1 ≤ N then 1 else 0 := by
    simp [coprimeMoebiusSum, coprimeMoebiusIndicator, Nat.coprime_zero_left]
  have hbound (N : ℕ) : |coprimeMoebiusSum 0 N| ≤ 1 := by
    rw [hcount]
    split_ifs <;> norm_num
  have hkey : Tendsto (fun x : ℝ => |coprimeMoebiusMean 0 x|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _
      (show Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) by simpa only [one_div] using tendsto_inv_atTop_zero)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    rw [coprimeMoebiusMean, abs_div, abs_of_pos hx0]
    exact div_le_div_of_nonneg_right (hbound _) hx0.le
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hkey

/-- For every fixed natural modulus, the coprime-restricted Möbius mean tends to zero. -/
theorem tendsto_coprimeMoebiusMean : ∀ Q : ℕ,
    Tendsto (coprimeMoebiusMean Q) atTop (𝓝 0) := by
  intro Q
  induction Q using Nat.strong_induction_on with
  | _ Q ih =>
    rcases eq_or_ne Q 0 with rfl | hQ0
    · exact tendsto_coprimeMoebiusMean_zero
    rcases eq_or_ne Q 1 with rfl | hQ1
    · exact tendsto_coprimeMoebiusMean_one
    let p := Q.minFac
    let R := Q / p
    have hp : p.Prime := Nat.minFac_prime hQ1
    have hpd : p ∣ Q := Nat.minFac_dvd Q
    have hmul : p * R = Q := Nat.mul_div_cancel' hpd
    have hRlt : R < Q := Nat.div_lt_self (Nat.pos_of_ne_zero hQ0) hp.one_lt
    have hlim := ih R hRlt
    rw [← hmul]
    by_cases hpR : p ∣ R
    · have heq : coprimeMoebiusMean (p * R) = coprimeMoebiusMean R :=
        funext (coprimeMoebiusMean_mul_of_dvd hpR)
      rwa [heq]
    · exact tendsto_coprimeMoebiusMean_prime_step hp hpR hlim

/-- Every positive odd power of a Möbius value equals that value. -/
theorem moebius_real_odd_pow (n r : ℕ) :
    ((μ n : ℤ) : ℝ) ^ (2 * r + 1) = ((μ n : ℤ) : ℝ) := by
  have h := (abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := n)))
  have ht : μ n = 0 ∨ μ n = 1 ∨ μ n = -1 := by omega
  rcases ht with h | h | h <;> rw [h] <;> simp [pow_add, pow_mul]

/-- A finite product of Möbius dilations factors through one common Möbius power and one coprimality test. -/
theorem moebius_dilation_product_eq_coprime_power {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (n : ℕ) :
    (∏ i, ((μ (a i * n) : ℤ) : ℝ)) =
      (∏ i, ((μ (a i) : ℤ) : ℝ)) *
        (if Nat.Coprime (∏ i, a i) n then ((μ n : ℤ) : ℝ) ^ Fintype.card ι else 0) := by
  classical
  by_cases hc : Nat.Coprime (∏ i, a i) n
  · rw [if_pos hc]
    have hcop := Nat.coprime_fintype_prod_left_iff.mp hc
    calc
      _ = ∏ i, (((μ (a i) : ℤ) : ℝ) * ((μ n : ℤ) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hcop i), Int.cast_mul]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  · have hnot : ¬ ∀ i, Nat.Coprime (a i) n :=
      fun h => hc (Nat.coprime_fintype_prod_left_iff.mpr h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hz : μ (a i * n) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (fun h => hi (Nat.coprime_of_squarefree_mul h))
    have hprod : (∏ i, ((μ (a i * n) : ℤ) : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz, Int.cast_zero])
    rw [hprod, if_neg hc, mul_zero]

/-- An odd product of Möbius dilations is a constant times one coprime-restricted Möbius value. -/
theorem moebius_odd_dilation_product_eq (r : ℕ) (a : Fin (2 * r + 1) → ℕ) (n : ℕ) :
    (∏ i, ((μ (a i * n) : ℤ) : ℝ)) =
      (∏ i, ((μ (a i) : ℤ) : ℝ)) * coprimeMoebiusIndicator (∏ i, a i) n := by
  simpa only [Fintype.card_fin, moebius_real_odd_pow, coprimeMoebiusIndicator] using
    moebius_dilation_product_eq_coprime_power a n

/-- Every fixed odd product of Möbius dilations has arithmetic mean zero. -/
theorem tendsto_moebius_odd_dilation_product_mean (r : ℕ) (a : Fin (2 * r + 1) → ℕ) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∏ i, ((μ (a i * n) : ℤ) : ℝ)) / x)
      atTop (𝓝 0) := by
  have heq (x : ℝ) :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∏ i, ((μ (a i * n) : ℤ) : ℝ)) / x =
        (∏ i, ((μ (a i) : ℤ) : ℝ)) * coprimeMoebiusMean (∏ i, a i) x := by
    simp_rw [moebius_odd_dilation_product_eq]
    rw [← Finset.mul_sum]
    unfold coprimeMoebiusMean coprimeMoebiusSum
    ring
  simp_rw [heq]
  simpa only [mul_zero] using
    (tendsto_coprimeMoebiusMean (∏ i, a i)).const_mul (∏ i, ((μ (a i) : ℤ) : ℝ))
end
end GaloisForLFunctions.BezoutValuationIncidence
