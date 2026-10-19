import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiValuationSamplingAndPronicObservability
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Field

/-!
# Valuation depth and finite-window Fermi stability

The horizon forces dyadic sieve saturation after finitely many levels.
Selected boundary readings then recover every even sieve value by a finite
weighted sum. The pronic energy of an initial window is controlled by a
larger selected window with a quadratic valuation-depth factor.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem dvd_dyadic_stable (L : ℕ) :
    ∀ (d n : ℕ), 0 < d → d < 2 ^ L →
      (d ∣ 2 ^ (L + 1) * n ↔ d ∣ 2 ^ L * n) := by
  induction L with
  | zero =>
    intro d n hd hcap
    norm_num at hcap
    omega
  | succ L ih =>
    intro d n hd hcap
    have hpow (j : ℕ) : 2 ^ (j + 1) * n = 2 * (2 ^ j * n) := by
      rw [pow_succ]
      ring
    by_cases hd2 : 2 ∣ d
    · obtain ⟨e, rfl⟩ := hd2
      have he : 0 < e := by omega
      have hbound : e < 2 ^ L := by
        rw [pow_succ] at hcap
        omega
      have hleft : (2 * e ∣ 2 ^ (L + 1 + 1) * n) ↔ e ∣ 2 ^ (L + 1) * n := by
        rw [hpow (L + 1), Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)]
      have hright : (2 * e ∣ 2 ^ (L + 1) * n) ↔ e ∣ 2 ^ L * n := by
        rw [hpow L, Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)]
      exact hleft.trans ((ih e n he hbound).trans hright.symm)
    · have hc : Nat.Coprime d 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hd2).symm
      rw [hpow (L + 1)]
      constructor
      · exact hc.dvd_of_dvd_mul_left
      · intro h
        exact dvd_mul_of_dvd_right h 2

private theorem terminal_weighted_sum (L : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range L, f j) + 2 * f L =
      ∑ j ∈ Finset.range (L + 1), (if j = L then 2 else 1) * f j := by
  rw [Finset.sum_range_succ]
  rw [if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hne : j ≠ L := by have := Finset.mem_range.mp hj; omega
  rw [if_neg hne]
  ring

private theorem terminal_cauchy_bound (L : ℕ) (f : ℕ → ℝ) :
    ((∑ j ∈ Finset.range L, f j) + 2 * f L) ^ 2 ≤
      ((L : ℝ) + 4) * ∑ j ∈ Finset.range (L + 1), f j ^ 2 := by
  have hw : (∑ j ∈ Finset.range (L + 1), (if j = L then (2 : ℝ) else 1) ^ 2) =
      (L : ℝ) + 4 := by
    rw [Finset.sum_range_succ]
    have hsum : (∑ j ∈ Finset.range L, (if j = L then (2 : ℝ) else 1) ^ 2) = L := by
      calc
        _ = ∑ j ∈ Finset.range L, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hne : j ≠ L := by have := Finset.mem_range.mp hj; omega
          rw [if_neg hne]
          norm_num
        _ = L := by simp
    rw [hsum]
    norm_num
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (L + 1))
    (fun j => if j = L then (2 : ℝ) else 1) f
  rw [hw] at h
  have heq := terminal_weighted_sum L f
  rw [← heq] at h
  exact h

private theorem pronic_dilation_compare {a n y : ℝ} (ha : 1 ≤ a) (hn : 0 < n) :
    (y / a) ^ 2 / (n * (n + 1)) ≤ y ^ 2 / ((a * n) * (a * n + 1)) := by
  have ha0 : 0 < a := by linarith
  have hleft : 0 < a ^ 2 * (n * (n + 1)) := by positivity
  have hright : 0 < (a * n) * (a * n + 1) := by positivity
  have hden : (a * n) * (a * n + 1) ≤ a ^ 2 * (n * (n + 1)) := by
    nlinarith [mul_nonneg (show 0 ≤ a * n by positivity) (show 0 ≤ a - 1 by linarith)]
  have h := div_le_div_of_nonneg_left (sq_nonneg y) hright hden
  simpa only [div_pow, div_div] using h

private theorem dyadic_telescope (f : ℕ → ℝ) (L : ℕ) :
    f 0 = (∑ j ∈ Finset.range L, (2 * f j - f (j + 1)) / (2 : ℝ) ^ (j + 1)) +
      f L / (2 : ℝ) ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, pow_succ]
    rw [ih]
    have hp : (2 : ℝ) ^ L ≠ 0 := by positivity
    field_simp
    ring

private def dyadicPairIndex (j m : ℕ) : ℕ := 2 ^ j * (m + 1) - 1

private theorem dyadic_pair_boundary (j m : ℕ) :
    4 * dyadicPairIndex j m + 4 = 2 ^ (j + 1) * (2 * m + 2) := by
  have hp : 0 < (2 : ℕ) ^ j * (m + 1) := by positivity
  have he : 2 ^ (j + 1) * (2 * m + 2) = 4 * (2 ^ j * (m + 1)) := by
    rw [pow_succ]
    ring
  unfold dyadicPairIndex
  omega

private theorem dyadic_pair_sum_le {L j M : ℕ} (hj : j ≤ L)
    (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) :
    (∑ m ∈ Finset.range M, f (dyadicPairIndex j m)) ≤
      ∑ m ∈ Finset.range (2 ^ L * M), f m := by
  have hi : Function.Injective (dyadicPairIndex j) := by
    intro a b hab
    have hpa : 0 < (2 : ℕ) ^ j * (a + 1) := by positivity
    have hpb : 0 < (2 : ℕ) ^ j * (b + 1) := by positivity
    have he : 2 ^ j * (a + 1) = 2 ^ j * (b + 1) := by
      unfold dyadicPairIndex at hab
      omega
    have he' := Nat.mul_left_cancel (by positivity : 0 < (2 : ℕ) ^ j) he
    omega
  have hs : (Finset.range M).image (dyadicPairIndex j) ⊆ Finset.range (2 ^ L * M) := by
    intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
    have hmM : m + 1 ≤ M := by have := Finset.mem_range.mp hm; omega
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hj
    have hprod := Nat.mul_le_mul hp hmM
    have hpos : 0 < (2 : ℕ) ^ j * (m + 1) := by positivity
    apply Finset.mem_range.mpr
    unfold dyadicPairIndex
    omega
  calc
    _ = ∑ m ∈ (Finset.range M).image (dyadicPairIndex j), f m := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hi hab
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => hf m)

private theorem even_pronic_stability (L M : ℕ) (s J : ℕ → ℝ)
    (hrec : ∀ m : ℕ, s (2 * m + 2) =
      (∑ j ∈ Finset.range L, J (2 ^ (j + 1) * (2 * m + 2)) / (2 : ℝ) ^ (j + 1)) +
        2 * (J (2 ^ (L + 1) * (2 * m + 2)) / (2 : ℝ) ^ (L + 1))) :
    (∑ m ∈ Finset.range M, s (2 * m + 2) ^ 2 /
      (((2 * m + 2 : ℕ) : ℝ) * (((2 * m + 2 : ℕ) : ℝ) + 1))) ≤
      (((L : ℝ) + 4) * ((L : ℝ) + 1)) *
        ∑ m ∈ Finset.range (2 ^ L * M), J (4 * m + 4) ^ 2 /
          (((4 * m + 4 : ℕ) : ℝ) * (((4 * m + 4 : ℕ) : ℝ) + 1)) := by
  let E : ℕ → ℝ := fun m => J (4 * m + 4) ^ 2 /
    (((4 * m + 4 : ℕ) : ℝ) * (((4 * m + 4 : ℕ) : ℝ) + 1))
  have hE (m : ℕ) : 0 ≤ E m := by dsimp [E]; positivity
  have hA : 0 ≤ (L : ℝ) + 4 := by positivity
  have hpoint (m : ℕ) : s (2 * m + 2) ^ 2 /
      (((2 * m + 2 : ℕ) : ℝ) * (((2 * m + 2 : ℕ) : ℝ) + 1)) ≤
      ((L : ℝ) + 4) * ∑ j ∈ Finset.range (L + 1), E (dyadicPairIndex j m) := by
    let f : ℕ → ℝ := fun j => J (2 ^ (j + 1) * (2 * m + 2)) / (2 : ℝ) ^ (j + 1)
    have hc := terminal_cauchy_bound L f
    change ((∑ j ∈ Finset.range L, f j) + 2 * f L) ^ 2 ≤ _ at hc
    have hr : s (2 * m + 2) = (∑ j ∈ Finset.range L, f j) + 2 * f L := hrec m
    rw [← hr] at hc
    have hn : 0 < ((2 * m + 2 : ℕ) : ℝ) := by positivity
    have hd : 0 ≤ (((2 * m + 2 : ℕ) : ℝ) * (((2 * m + 2 : ℕ) : ℝ) + 1)) := by positivity
    have hdiv := div_le_div_of_nonneg_right hc hd
    rw [mul_div_assoc, Finset.sum_div] at hdiv
    refine hdiv.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) hA)
    intro j _
    have hpNat : 1 ≤ (2 : ℕ) ^ (j + 1) := by
      have hp : 0 < (2 : ℕ) ^ (j + 1) := by positivity
      omega
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast hpNat
    have h := pronic_dilation_compare (y := J (2 ^ (j + 1) * (2 * m + 2))) hp hn
    dsimp [f, E]
    rw [dyadic_pair_boundary]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hsum := Finset.sum_le_sum (fun m (_ : m ∈ Finset.range M) => hpoint m)
  rw [← Finset.mul_sum, Finset.sum_comm] at hsum
  have hbound : (∑ j ∈ Finset.range (L + 1),
      ∑ m ∈ Finset.range M, E (dyadicPairIndex j m)) ≤
      ((L : ℝ) + 1) * ∑ m ∈ Finset.range (2 ^ L * M), E m := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (L + 1), ∑ m ∈ Finset.range (2 ^ L * M), E m := by
        apply Finset.sum_le_sum
        intro j hj
        exact dyadic_pair_sum_le (by have := Finset.mem_range.mp hj; omega) E hE
      _ = _ := by simp
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left hbound hA)
  simpa only [mul_assoc] using hfinal

private theorem sieve_dyadic_stable (N : ℕ) (c : ℕ → ℝ) (L n : ℕ)
    (hN : N < 2 ^ L) :
    sieveSeq N c (2 ^ (L + 1) * n) = sieveSeq N c (2 ^ L * n) := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hb := Finset.mem_Icc.mp hd
  simp only [dvd_dyadic_stable L d n (by omega) (by omega)]

/-- Every finite horizon saturates on a dyadic chain after its logarithmic cutoff. -/
theorem sieveSeq_dyadic_depth_saturation (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    sieveSeq N c (2 ^ (Nat.log 2 N + 2) * n) =
      sieveSeq N c (2 ^ (Nat.log 2 N + 1) * n) := by
  have hN : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by omega) N
  simpa [Nat.add_assoc] using sieve_dyadic_stable N c (Nat.log 2 N + 1) n hN

private theorem boundary_double (N : ℕ) (c : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    fermiBoundaryJump N c (2 * n) = 2 * sieveSeq N c n - sieveSeq N c (2 * n) := by
  have h := fermiBoundaryJump_even N c (n - 1)
  rw [show 2 * (n - 1) + 2 = 2 * n by omega,
    show n - 1 + 1 = n by omega] at h
  exact h

private theorem even_depth_recovery (N : ℕ) (c : ℕ → ℝ) (L m : ℕ)
    (hN : N < 2 ^ L) :
    sieveSeq N c (2 * m + 2) =
      (∑ j ∈ Finset.range L,
        fermiBoundaryJump N c (2 ^ (j + 1) * (2 * m + 2)) / (2 : ℝ) ^ (j + 1)) +
      2 * (fermiBoundaryJump N c (2 ^ (L + 1) * (2 * m + 2)) /
        (2 : ℝ) ^ (L + 1)) := by
  have hj (j : ℕ) : fermiBoundaryJump N c (2 ^ (j + 1) * (2 * m + 2)) =
      2 * sieveSeq N c (2 ^ j * (2 * m + 2)) -
        sieveSeq N c (2 ^ (j + 1) * (2 * m + 2)) := by
    have h := boundary_double N c (2 ^ j * (2 * m + 2)) (by positivity)
    rw [show 2 * (2 ^ j * (2 * m + 2)) = 2 ^ (j + 1) * (2 * m + 2) by
      rw [pow_succ]; ring] at h
    exact h
  have ht : fermiBoundaryJump N c (2 ^ (L + 1) * (2 * m + 2)) =
      sieveSeq N c (2 ^ L * (2 * m + 2)) := by
    rw [hj L, sieve_dyadic_stable N c L (2 * m + 2) hN]
    ring
  have htel := dyadic_telescope (fun j => sieveSeq N c (2 ^ j * (2 * m + 2))) L
  simp only [pow_zero, one_mul] at htel
  calc
    _ = (∑ j ∈ Finset.range L,
        (2 * sieveSeq N c (2 ^ j * (2 * m + 2)) -
          sieveSeq N c (2 ^ (j + 1) * (2 * m + 2))) / (2 : ℝ) ^ (j + 1)) +
        sieveSeq N c (2 ^ L * (2 * m + 2)) / (2 : ℝ) ^ L := htel
    _ = (∑ j ∈ Finset.range L,
        fermiBoundaryJump N c (2 ^ (j + 1) * (2 * m + 2)) / (2 : ℝ) ^ (j + 1)) +
        sieveSeq N c (2 ^ L * (2 * m + 2)) / (2 : ℝ) ^ L := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hj j]
    _ = _ := by
      rw [ht, pow_succ]
      congr 1
      field_simp

/-- Selected even boundaries recover an even sieve value through a finite dyadic window. -/
theorem fermiBoundaryJump_even_depth_recovery (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    let L := Nat.log 2 N + 1
    sieveSeq N c (2 * m + 2) =
      (∑ j ∈ Finset.range L,
        fermiBoundaryJump N c (2 ^ (j + 1) * (2 * m + 2)) / (2 : ℝ) ^ (j + 1)) +
      2 * (fermiBoundaryJump N c (2 ^ (L + 1) * (2 * m + 2)) /
        (2 : ℝ) ^ (L + 1)) := by
  exact even_depth_recovery N c (Nat.log 2 N + 1) m
    (Nat.lt_pow_succ_log_self (by omega) N)

/-- Unrestricted coefficients admit a quadratic-depth inverse bound in the pronic reading norm. -/
theorem sievePairedPronicEnergy_le_depth_selected_window (N M : ℕ) (c : ℕ → ℝ) :
    let L := Nat.log 2 N + 1
    sievePairedPronicEnergy N c (Finset.range M) ≤
      (((L : ℝ) + 4) * ((L : ℝ) + 1)) *
        fermiSelectedPronicEnergy N c (Finset.range (2 ^ L * M)) := by
  let L := Nat.log 2 N + 1
  change sievePairedPronicEnergy N c (Finset.range M) ≤
    (((L : ℝ) + 4) * ((L : ℝ) + 1)) *
      fermiSelectedPronicEnergy N c (Finset.range (2 ^ L * M))
  have heven := even_pronic_stability L M (sieveSeq N c) (fermiBoundaryJump N c)
    (fun m => even_depth_recovery N c L m (Nat.lt_pow_succ_log_self (by omega) N))
  have heven' : (∑ m ∈ Finset.range M,
      sieveSeq N c (2 * m + 2) ^ 2 / (pronicSeq (2 * m + 2) : ℝ)) ≤
      (((L : ℝ) + 4) * ((L : ℝ) + 1)) *
        ∑ m ∈ Finset.range (2 ^ L * M),
          fermiBoundaryJump N c (4 * m + 4) ^ 2 / (pronicSeq (4 * m + 4) : ℝ) := by
    simpa only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using heven
  let O : ℕ → ℝ := fun m =>
    fermiBoundaryJump N c (2 * m + 1) ^ 2 / (pronicSeq (2 * m + 1) : ℝ)
  have hO (m : ℕ) : 0 ≤ O m := by dsimp [O]; positivity
  have hp : 1 ≤ (2 : ℕ) ^ L := by
    have hp0 : 0 < (2 : ℕ) ^ L := by positivity
    omega
  have hM : M ≤ 2 ^ L * M := by nlinarith
  have hsub : Finset.range M ⊆ Finset.range (2 ^ L * M) := by
    intro m hm
    apply Finset.mem_range.mpr
    have hmM := Finset.mem_range.mp hm
    omega
  have hodd : (∑ m ∈ Finset.range M, O m) ≤
      ∑ m ∈ Finset.range (2 ^ L * M), O m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hO m)
  have hC : 1 ≤ ((L : ℝ) + 4) * ((L : ℝ) + 1) := by
    have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    nlinarith
  have hodd' := hodd.trans (show (∑ m ∈ Finset.range (2 ^ L * M), O m) ≤
      (((L : ℝ) + 4) * ((L : ℝ) + 1)) *
        ∑ m ∈ Finset.range (2 ^ L * M), O m from by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg (fun m _ => hO m)))
  have ho : (∑ m ∈ Finset.range M,
      sieveSeq N c (2 * m + 1) ^ 2 / (pronicSeq (2 * m + 1) : ℝ)) =
      ∑ m ∈ Finset.range M, O m := by
    apply Finset.sum_congr rfl
    intro m _
    simp only [O, fermiBoundaryJump_odd, neg_sq]
  unfold sievePairedPronicEnergy fermiSelectedPronicEnergy
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ho, mul_add]
  exact add_le_add hodd' heven'

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
