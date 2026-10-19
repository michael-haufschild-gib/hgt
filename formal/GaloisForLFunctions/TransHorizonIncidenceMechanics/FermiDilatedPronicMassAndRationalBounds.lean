import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiCompleteTraceValuationStability

/-!
# Dilated pronic masses and exact rational bounds

The masses `E_d = ∑' n, 1 / pronicSeq (d*n)` describe the physical energies
of divisor indicators. They converge for every positive dilation and agree
with the corresponding sampled divisibility sums. Parity splitting uses
mathlib's `tsum_even_add_odd`.

Termwise rational comparisons and the existing telescoping pronic tail give
`(10/3) E_4 ≤ E_2 ≤ (100/27) E_4`, `(26/7) E_12 ≤ E_6`, and `2 E_6 ≤ E_3`.
No numerical approximation or value of a transcendental series is used.
These are supporting estimates for the finite-horizon physical cone gap.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

set_option autoImplicit false

open BezoutValuationIncidence
open scoped BigOperators

/-- Reciprocal-pronic mass on all multiples of a dilation; the zero-index summand is zero. -/
noncomputable def fermiDilatedPronicMass (d : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / (pronicSeq (d * n) : ℝ)

theorem fermiDilatedPronicMass_summable {d : ℕ} (hd : 0 < d) :
    Summable (fun n : ℕ => (1 : ℝ) / (pronicSeq (d * n) : ℝ)) := by
  have h := summable_div_pronicSeq_of_bounded (g := fun _ => (1 : ℝ))
    (B := 1) (by intro n; norm_num)
  exact h.comp_injective (i := fun n => d * n)
    (by intro a b heq; exact Nat.mul_left_cancel hd heq)

theorem fermiDilatedPronicMass_pos {d : ℕ} (hd : 0 < d) :
    0 < fermiDilatedPronicMass d := by
  have h := (fermiDilatedPronicMass_summable hd).le_tsum 1 (fun n _ => by positivity)
  have hpr : 0 < (pronicSeq d : ℝ) := by
    exact_mod_cast (show 0 < pronicSeq d by unfold pronicSeq; positivity)
  have h' : (1 : ℝ) / (pronicSeq d : ℝ) ≤ fermiDilatedPronicMass d := by
    simpa only [Nat.mul_one, fermiDilatedPronicMass] using h
  exact lt_of_lt_of_le (one_div_pos.mpr hpr) h'

theorem fermiDilatedPronicMass_eq_divisor_sum {d : ℕ} (hd : 0 < d) :
    fermiDilatedPronicMass d =
      ∑' n : ℕ, (if d ∣ n then (1 : ℝ) else 0) / (pronicSeq n : ℝ) := by
  have hi : Function.Injective (fun n : ℕ => d * n) :=
    fun a b h => Nat.mul_left_cancel hd h
  have h := hi.tsum_eq
    (f := fun n : ℕ => (if d ∣ n then (1 : ℝ) else 0) / (pronicSeq n : ℝ))
    (by
      intro n hn
      have hdn : d ∣ n := by
        by_contra hh
        exact hn (by simp [hh])
      obtain ⟨k, hk⟩ := hdn
      exact ⟨k, hk.symm⟩)
  simpa only [dvd_mul_right, if_true, fermiDilatedPronicMass] using h

theorem fermiDilatedPronicMass_eq_sampled_divisor_sum (a : ℕ) {d : ℕ} (hd : 0 < d) :
    fermiDilatedPronicMass (a * d) =
      ∑' n : ℕ, (if d ∣ n then (1 : ℝ) else 0) / (pronicSeq (a * n) : ℝ) := by
  have hi : Function.Injective (fun n : ℕ => d * n) :=
    fun p q h => Nat.mul_left_cancel hd h
  have h := hi.tsum_eq
    (f := fun n : ℕ => (if d ∣ n then (1 : ℝ) else 0) / (pronicSeq (a * n) : ℝ))
    (by
      intro n hn
      have hdn : d ∣ n := by
        by_contra hh
        exact hn (by simp [hh])
      obtain ⟨k, hk⟩ := hdn
      exact ⟨k, hk.symm⟩)
  simpa only [dvd_mul_right, if_true, fermiDilatedPronicMass, Nat.mul_assoc] using h

theorem fermiDilatedPronicMass_odd_split {d : ℕ} (hd : 0 < d) :
    (∑' m : ℕ, (1 : ℝ) / (pronicSeq (d * (2 * m + 1)) : ℝ)) =
      fermiDilatedPronicMass d - fermiDilatedPronicMass (2 * d) := by
  have hs := fermiDilatedPronicMass_summable hd
  have he := hs.comp_injective (i := fun m => 2 * m)
    (by intro a b h; change 2 * a = 2 * b at h; omega)
  have ho := hs.comp_injective (i := fun m => 2 * m + 1)
    (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hsplit := tsum_even_add_odd
    (f := fun n : ℕ => (1 : ℝ) / (pronicSeq (d * n) : ℝ)) he ho
  have heq : (∑' m : ℕ, (1 : ℝ) / (pronicSeq (d * (2 * m)) : ℝ)) =
      fermiDilatedPronicMass (2 * d) := by
    unfold fermiDilatedPronicMass
    apply tsum_congr
    intro m
    congr 3
    ring
  change _ + _ = fermiDilatedPronicMass d at hsplit
  rw [heq] at hsplit
  linarith

private theorem double_reciprocal_identity {x : ℝ} (hx : 0 < x) :
    1 / (x * (x + 1)) =
      (4 - 2 / (x + 1)) * (1 / ((2 * x) * (2 * x + 1))) := by
  field_simp
  ring

private theorem dilated_term_double_lower {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (4 - 2 / ((d : ℝ) + 1)) * (1 / (pronicSeq ((2 * d) * n) : ℝ)) ≤
      1 / (pronicSeq (d * n) : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [pronicSeq]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 < (d : ℝ) * n := mul_pos hdR (by linarith)
  have hdx : (d : ℝ) ≤ d * n := by nlinarith
  have hfrac : 2 / ((d : ℝ) * n + 1) ≤ 2 / ((d : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  simp only [cast_pronicSeq_eq, Nat.cast_mul, Nat.cast_ofNat]
  rw [double_reciprocal_identity hx]
  have hmul := mul_le_mul_of_nonneg_right (show
    4 - 2 / ((d : ℝ) + 1) ≤ 4 - 2 / ((d : ℝ) * n + 1) by linarith)
    (show 0 ≤ 1 / ((2 * ((d : ℝ) * n)) * (2 * ((d : ℝ) * n) + 1)) by positivity)
  simpa only [mul_assoc] using hmul

theorem fermiDilatedPronicMass_double_lower {d : ℕ} (hd : 0 < d) :
    (4 - 2 / ((d : ℝ) + 1)) * fermiDilatedPronicMass (2 * d) ≤
      fermiDilatedPronicMass d := by
  have h := ((fermiDilatedPronicMass_summable (show 0 < 2 * d by omega)).mul_left
    (4 - 2 / ((d : ℝ) + 1))).tsum_le_tsum (dilated_term_double_lower hd)
      (fermiDilatedPronicMass_summable hd)
  simpa only [tsum_mul_left, fermiDilatedPronicMass] using h

private theorem four_tail_term_bound (n : ℕ) :
    (1 : ℝ) / (pronicSeq (4 * (n + 2)) : ℝ) ≤
      (1 / 16) * (1 / (pronicSeq (n + 1) : ℝ)) := by
  simp only [cast_pronicSeq_eq, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one, mul_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem fermiDilatedPronicMass_four_upper : fermiDilatedPronicMass 4 ≤ 9 / 80 := by
  have hs := fermiDilatedPronicMass_summable (by norm_num : 0 < 4)
  have htail : Summable (fun n : ℕ => (1 : ℝ) / (pronicSeq (4 * (n + 2)) : ℝ)) :=
    hs.comp_injective (by intro a b h; change a + 2 = b + 2 at h; omega)
  have hpr : HasSum (fun n : ℕ => (1 : ℝ) / (pronicSeq (n + 1) : ℝ)) 1 := by
    simpa only [Nat.zero_add, Nat.add_comm, Nat.cast_zero, zero_add, div_one] using
      hasSum_one_div_pronicSeq_shift 0
  have htailbound := htail.tsum_le_tsum four_tail_term_bound (hpr.summable.mul_left (1 / 16))
  rw [tsum_mul_left, hpr.tsum_eq, mul_one] at htailbound
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hfirst : (∑ i ∈ Finset.range 2, (1 : ℝ) / (pronicSeq (4 * i) : ℝ)) =
      1 / 20 := by norm_num [Finset.sum_range_succ, pronicSeq]
  rw [hfirst] at hsplit
  have hsplit' : (1 / 20 : ℝ) +
      (∑' n : ℕ, (1 : ℝ) / (pronicSeq (4 * (n + 2)) : ℝ)) =
      fermiDilatedPronicMass 4 := by
    exact hsplit
  linarith

private theorem four_two_term_defect_nonneg (n : ℕ) :
    0 ≤ 4 * ((1 : ℝ) / (pronicSeq (4 * n) : ℝ)) -
      1 / (pronicSeq (2 * n) : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [pronicSeq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [cast_pronicSeq_eq, Nat.cast_mul, Nat.cast_ofNat, mul_one_div]
  rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem fermiDilatedPronicMass_four_two_defect :
    (1 / 30 : ℝ) ≤ 4 * fermiDilatedPronicMass 4 - fermiDilatedPronicMass 2 := by
  have hs := ((fermiDilatedPronicMass_summable (by norm_num : 0 < 4)).mul_left 4).sub
    (fermiDilatedPronicMass_summable (by norm_num : 0 < 2))
  have h := hs.le_tsum 1 (fun n _ => four_two_term_defect_nonneg n)
  rw [((fermiDilatedPronicMass_summable (by norm_num : 0 < 4)).mul_left 4).tsum_sub
    (fermiDilatedPronicMass_summable (by norm_num : 0 < 2)), tsum_mul_left] at h
  have hterm : 4 * ((1 : ℝ) / (pronicSeq (4 * 1) : ℝ)) -
      1 / (pronicSeq (2 * 1) : ℝ) = 1 / 30 := by norm_num [pronicSeq]
  rw [hterm] at h
  exact h

theorem fermiDilatedPronicMass_two_four_bounds :
    (10 / 3 : ℝ) * fermiDilatedPronicMass 4 ≤ fermiDilatedPronicMass 2 ∧
      fermiDilatedPronicMass 2 ≤ (100 / 27 : ℝ) * fermiDilatedPronicMass 4 := by
  constructor
  · have h := fermiDilatedPronicMass_double_lower (by norm_num : 0 < 2)
    norm_num at h
    exact h
  · have hdef := fermiDilatedPronicMass_four_two_defect
    have h4 := fermiDilatedPronicMass_four_upper
    linarith

theorem fermiDilatedPronicMass_six_twelve_bound :
    (26 / 7 : ℝ) * fermiDilatedPronicMass 12 ≤ fermiDilatedPronicMass 6 := by
  have h := fermiDilatedPronicMass_double_lower (by norm_num : 0 < 6)
  norm_num at h
  exact h

theorem fermiDilatedPronicMass_three_six_bound :
    2 * fermiDilatedPronicMass 6 ≤ fermiDilatedPronicMass 3 := by
  have h := fermiDilatedPronicMass_double_lower (by norm_num : 0 < 3)
  have h6 := fermiDilatedPronicMass_pos (by norm_num : 0 < 6)
  norm_num at h
  linarith

end GaloisForLFunctions.TransHorizonIncidenceMechanics
