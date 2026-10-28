import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal
import GaloisForLFunctions.HTGeometry.ShiftPartialSummation
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Quantitative Gram control for actual Ramanujan pole profiles

Complete-period orthogonality bounds the harmonic discrepancy uniformly in the
integer horizon, with explicit dependence on the conductor. All vectors are the
literal Ramanujan profiles in the prime matrix.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open RenormalizedArithmeticPotentialTheory RenormalizedBiarithmeticGeometry

private theorem harmonic_increment_sum (N : ℕ) :
    1 / ((N : ℝ) + 1) +
      ∑ j ∈ range N, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) = 1 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have h₁ : (N : ℝ) + 1 ≠ 0 := by positivity
    have h₂ : (N : ℝ) + 2 ≠ 0 := by positivity
    have he : 1 / ((N : ℝ) + 2) +
        1 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) = 1 / ((N : ℝ) + 1) := by
      field_simp
      ring
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    linarith only [ih, he]

private theorem harmonic_sum_le_partial_sum_bound {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n : ℕ, |∑ i ∈ range n, f i| ≤ B) (N : ℕ) :
    |∑ i ∈ range N, f i / ((i : ℝ) + 1)| ≤ B := by
  have hS (j : ℕ) : |_root_.HTGeometry.partialSum f j| ≤ B * (j : ℝ) ^ (0 : ℝ) := by
    simpa only [_root_.HTGeometry.partialSum, Real.rpow_zero, mul_one] using hf j
  have h := _root_.HTGeometry.abel_bound_of_partialSum_le hS N
  simp only [Real.rpow_zero, mul_one] at h
  have he : B * (1 / ((N : ℝ) + 1)) +
      ∑ j ∈ range N, B * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) = B := by
    rw [← mul_sum, ← mul_add, harmonic_increment_sum, mul_one]
  simpa only [div_eq_mul_inv, one_mul] using h.trans_eq he

private theorem periodic_harmonic_discrepancy {p : ℕ → ℝ} {q : ℕ}
    (hq : 0 < q) (hper : Function.Periodic p q) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, p n / (n : ℝ)) -
        periodMean p q * (∑ n ∈ Icc 1 N, 1 / (n : ℝ))| ≤
      ∑ i ∈ range q, |p (i + 1) - periodMean p q| := by
  let b : ℕ → ℝ := fun n => p (n + 1) - periodMean p q
  have hbper : Function.Periodic b q := by
    intro n
    dsimp only [b]
    rw [show n + q + 1 = (n + 1) + q by omega, hper]
  have hshift : (∑ i ∈ range q, p (i + 1)) = ∑ i ∈ range q, p i := by
    simpa only [Nat.add_comm] using sum_range_shift_of_periodic hper 1
  have hbzero : (∑ i ∈ range q, b i) = 0 := by
    simp only [b, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hshift, periodMean]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    ring
  have hb := harmonic_sum_le_partial_sum_bound
    (fun n => abs_sum_range_le_of_periodic hq hbper hbzero n) N
  have he : (∑ n ∈ Icc 1 N, p n / (n : ℝ)) -
        periodMean p q * (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) =
      ∑ i ∈ range N, b i / ((i : ℝ) + 1) := by
    rw [_root_.RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range,
      _root_.RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range,
      mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [b, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    ring
  rw [he]
  exact hb

private theorem normalized_square_shift_sum {m q : ℕ} (hm : 0 < m)
    (hmq : m ∣ q) (hq : 0 < q) (hper : Function.Periodic (normalizedRamanujanMode m) q) :
    (∑ i ∈ range q, normalizedRamanujanMode m (i + 1) ^ 2) = q := by
  have hmean := periodMean_normalizedRamanujanMode_mul hm hm hmq hmq hq
  simp only [ite_true, periodMean] at hmean
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsum := congrArg (fun x : ℝ => x * (q : ℝ)) hmean
  rw [div_mul_cancel₀ _ hq0, one_mul] at hsum
  have hsquare : (∑ i ∈ range q, normalizedRamanujanMode m i ^ 2) = q := by
    simpa only [pow_two] using hsum
  have hperSq : Function.Periodic (fun n => normalizedRamanujanMode m n ^ 2) q :=
    fun n => congrArg (fun x : ℝ => x ^ 2) (hper n)
  have hshift := sum_range_shift_of_periodic
    (p := fun n => normalizedRamanujanMode m n ^ 2) (q := q) hperSq 1
  calc
    _ = ∑ i ∈ range q, normalizedRamanujanMode m i ^ 2 := by
      simpa only [Nat.add_comm] using hshift
    _ = _ := hsquare

private theorem abs_product_le_half_squares (a b : ℝ) :
    |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith only [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

private theorem normalized_product_period_variation {m l q : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmq : m ∣ q) (hlq : l ∣ q) (hq : 0 < q)
    (hpm : Function.Periodic (normalizedRamanujanMode m) q)
    (hpl : Function.Periodic (normalizedRamanujanMode l) q) :
    (∑ i ∈ range q, |normalizedRamanujanMode m (i + 1) *
      normalizedRamanujanMode l (i + 1) - (if m = l then 1 else 0)|) ≤ 2 * (q : ℝ) := by
  let δ : ℝ := if m = l then 1 else 0
  have hδ : 0 ≤ δ ∧ δ ≤ 1 := by dsimp [δ]; split_ifs <;> norm_num
  have hpoint (i : ℕ) :
      |normalizedRamanujanMode m (i + 1) * normalizedRamanujanMode l (i + 1) - δ| ≤
        (normalizedRamanujanMode m (i + 1) ^ 2 +
          normalizedRamanujanMode l (i + 1) ^ 2) / 2 + δ := by
    calc
      _ ≤ |normalizedRamanujanMode m (i + 1) * normalizedRamanujanMode l (i + 1)| + |δ| :=
        abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg hδ.1]
        exact add_le_add (abs_product_le_half_squares _ _) le_rfl
  calc
    _ ≤ ∑ i ∈ range q, ((normalizedRamanujanMode m (i + 1) ^ 2 +
        normalizedRamanujanMode l (i + 1) ^ 2) / 2 + δ) :=
      sum_le_sum fun i _ => hpoint i
    _ = ((q : ℝ) + (q : ℝ)) / 2 + (q : ℝ) * δ := by
      rw [sum_add_distrib, ← sum_div, sum_add_distrib,
        normalized_square_shift_sum hm hmq hq hpm,
        normalized_square_shift_sum hl hlq hq hpl]
      simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ 2 * (q : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hδ.2 (Nat.cast_nonneg q)
      linarith only [h]

private theorem ramanujanPoleProfile_gram_error_le_nat {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
        (if m = l then 1 else 0) * (∑ n ∈ Icc 1 N, 1 / (n : ℝ))| ≤
      2 * (m : ℝ) * (l : ℝ) := by
  have hpm : Function.Periodic (normalizedRamanujanMode m) (m * l) := by
    intro n
    simpa only [Nat.cast_id, Nat.mul_comm] using
      ((normalizedRamanujanMode_periodic hm).nat_mul l) n
  have hpl : Function.Periodic (normalizedRamanujanMode l) (m * l) := by
    intro n
    simpa only [Nat.cast_id] using
      ((normalizedRamanujanMode_periodic hl).nat_mul m) n
  have hper : Function.Periodic
      (fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n)
      (m * l) := fun n => congrArg₂ (· * ·) (hpm n) (hpl n)
  have hq := Nat.mul_pos hm hl
  have h := periodic_harmonic_discrepancy hq hper N
  rw [periodMean_normalizedRamanujanMode_mul (q := m * l) hm hl
    (dvd_mul_right m l) (dvd_mul_left l m) hq] at h
  have hb := h.trans (normalized_product_period_variation (q := m * l) hm hl
    (dvd_mul_right m l) (dvd_mul_left l m) hq hpm hpl)
  have he : (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) =
      ∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ) := by
    apply sum_congr rfl
    intro n _
    rw [ramanujanPoleProfile, ramanujanPoleProfile, div_mul_div_comm, ← sq,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [he]
  simpa only [Nat.cast_mul, mul_assoc] using hb

/-- Every literal Ramanujan Gram entry has a conductor-explicit, horizon-uniform error. -/
theorem ramanujanPoleProfile_gram_error_le (m l : ℕ+) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
        (if m = l then 1 else 0) * (∑ n ∈ Icc 1 N, 1 / (n : ℝ))| ≤
      2 * (m : ℝ) * (l : ℝ) := by
  have h := ramanujanPoleProfile_gram_error_le_nat
    (m := (m : ℕ)) (l := (l : ℕ)) m.property l.property N
  have hδ : (if (m : ℕ) = (l : ℕ) then (1 : ℝ) else 0) =
      (if m = l then 1 else 0) := by
    by_cases hml : m = l
    · subst l
      simp
    · have hval : (m : ℕ) ≠ (l : ℕ) := fun he => hml (Subtype.ext he)
      rw [if_neg hval, if_neg hml]
  rw [hδ] at h
  exact h

private theorem ramanujan_family_gram_expansion (S : Finset ℕ+)
    (c : ℕ+ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) =
      ∑ m ∈ S, ∑ l ∈ S, c m * c l *
        (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ m ∈ S, ∑ l ∈ S,
        c m * c l * (ramanujanPoleProfile m n * ramanujanPoleProfile l n) := by
      apply sum_congr rfl
      intro n _
      rw [pow_two, sum_mul]
      apply sum_congr rfl
      intro m _
      rw [mul_sum]
      apply sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [sum_comm]
      apply sum_congr rfl
      intro l _
      rw [mul_sum]

/-- One quadratic budget controls every coefficient vector in any finite conductor family. -/
theorem ramanujanPoleProfile_family_gram_error_le (S : Finset ℕ+)
    (c : ℕ+ → ℝ) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) -
        (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) * (∑ m ∈ S, c m ^ 2)| ≤
      2 * (∑ m ∈ S, (m : ℝ) ^ 2) * (∑ m ∈ S, c m ^ 2) := by
  let H : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)
  let G (m l : ℕ+) : ℝ :=
    ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n
  have hdiag : (∑ m ∈ S, ∑ l ∈ S,
      c m * c l * ((if m = l then 1 else 0) * H)) = H * (∑ m ∈ S, c m ^ 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single m]
    · simp only [ite_true, one_mul]
      ring
    · intro l _ hl
      rw [if_neg (Ne.symm hl), zero_mul, mul_zero]
    · exact fun h => (h hm).elim
  have herr : (∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) -
      H * (∑ m ∈ S, c m ^ 2) =
        ∑ m ∈ S, ∑ l ∈ S, c m * c l * (G m l - (if m = l then 1 else 0) * H) := by
    rw [ramanujan_family_gram_expansion, ← hdiag, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro l _
    dsimp only [G]
    ring
  have hfactor : (∑ m ∈ S, ∑ l ∈ S, |c m| * |c l| * (2 * (m : ℝ) * (l : ℝ))) =
      2 * (∑ m ∈ S, (m : ℝ) * |c m|) ^ 2 := by
    simp_rw [pow_two, sum_mul, mul_sum]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro l _
    ring
  have hcs : (∑ m ∈ S, (m : ℝ) * |c m|) ^ 2 ≤
      (∑ m ∈ S, (m : ℝ) ^ 2) * (∑ m ∈ S, c m ^ 2) := by
    simpa only [sq_abs] using
      sum_mul_sq_le_sq_mul_sq S (fun m : ℕ+ => (m : ℝ)) (fun m => |c m|)
  change |(∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) -
    H * (∑ m ∈ S, c m ^ 2)| ≤ _
  rw [herr]
  calc
    _ ≤ ∑ m ∈ S, ∑ l ∈ S,
        |c m * c l * (G m l - (if m = l then 1 else 0) * H)| := by
      exact (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun m _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ m ∈ S, ∑ l ∈ S, |c m| * |c l| * (2 * (m : ℝ) * (l : ℝ)) := by
      apply sum_le_sum
      intro m _
      apply sum_le_sum
      intro l _
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (ramanujanPoleProfile_gram_error_le m l N)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = 2 * (∑ m ∈ S, (m : ℝ) * |c m|) ^ 2 := hfactor
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 2)


private theorem harmonic_log_error_le (N : ℕ) :
    |(∑ n ∈ Icc 1 N, 1 / (n : ℝ)) - Real.log N| ≤ 1 := by
  have hlo : Real.log N ≤ (harmonic N : ℝ) := by
    simpa only [Nat.floor_natCast] using log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
  have hup := harmonic_le_one_add_log N
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlo hup
  simp only [← one_div] at hlo hup
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith only [hup]

/-- Explicit conductor cost for logarithmically normalized, growing Ramanujan families. -/
theorem ramanujanPoleProfile_family_log_gram_error_le (S : Finset ℕ+)
    (c : ℕ+ → ℝ) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2) -
        Real.log N * (∑ m ∈ S, c m ^ 2)| ≤
      (1 + 2 * (∑ m ∈ S, (m : ℝ) ^ 2)) * (∑ m ∈ S, c m ^ 2) := by
  let A : ℝ := ∑ n ∈ Icc 1 N, (∑ m ∈ S, c m * ramanujanPoleProfile m n) ^ 2
  let C : ℝ := ∑ m ∈ S, c m ^ 2
  let H : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)
  have hC : 0 ≤ C := sum_nonneg fun m _ => sq_nonneg (c m)
  have hgram := ramanujanPoleProfile_family_gram_error_le S c N
  have hlog : |(H - Real.log N) * C| ≤ C := by
    rw [abs_mul, abs_of_nonneg hC]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (harmonic_log_error_le N) hC
  change |A - Real.log N * C| ≤ _
  calc
    _ = |(A - H * C) + (H - Real.log N) * C| := by congr 1; ring
    _ ≤ |A - H * C| + |(H - Real.log N) * C| := abs_add_le _ _
    _ ≤ 2 * (∑ m ∈ S, (m : ℝ) ^ 2) * C + C := add_le_add hgram hlog
    _ = _ := by ring

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanPoleProfile_gram_error_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanPoleProfile_family_gram_error_le

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanPoleProfile_family_log_gram_error_le
