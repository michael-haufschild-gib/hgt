/-
# Exact two-adic quadratic correlations

The quadratic factors at conductors `4` and `8` have correlations much
sharper than their cardinality envelopes.  This module proves their complete
finite correlation bounds in the exact integer-shift gcd shape needed by the
Dirichlet-character second-moment argument.  Every residue calculation is a
closed symbolic equality checked by Lean.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicQuadratic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

noncomputable section

namespace RHTower

private theorem quadraticCharacterFour_translate (k d : ZMod 4) :
    ∑ x : ZMod 4,
      quadraticCharacterFour (x + k) * quadraticCharacterFour (x + (k + d)) =
      ∑ x : ZMod 4,
        quadraticCharacterFour x * quadraticCharacterFour (x + d) := by
  simpa only [Equiv.coe_addRight, add_assoc] using
    (Equiv.sum_comp (Equiv.addRight k) (fun x : ZMod 4 =>
      quadraticCharacterFour x * quadraticCharacterFour (x + d)))

private theorem quadraticCharacterEight_translate
    (γ : ZMod 8 → ℂ) (k d : ZMod 8) :
    ∑ x : ZMod 8, γ (x + k) * γ (x + (k + d)) =
      ∑ x : ZMod 8, γ x * γ (x + d) := by
  simpa only [Equiv.coe_addRight, add_assoc] using
    (Equiv.sum_comp (Equiv.addRight k) (fun x : ZMod 8 => γ x * γ (x + d)))

private theorem quadraticCharacterFour_apply_val (x : ZMod 4) :
    quadraticCharacterFour x =
      if x.val % 2 = 0 then 0 else if x.val % 4 = 1 then 1 else -1 := by
  fin_cases x <;>
    norm_num [ZMod.val, quadraticCharacterFour, ZMod.χ₄, ZMod.val_natCast]

private theorem quadraticCharacterEight_apply_val (x : ZMod 8) :
    quadraticCharacterEight x =
      if x.val % 2 = 0 then 0 else
        if x.val % 8 = 1 ∨ x.val % 8 = 7 then 1 else -1 := by
  fin_cases x <;>
    norm_num [ZMod.val, quadraticCharacterEight, ZMod.χ₈, ZMod.val_natCast]

private theorem quadraticCharacterEightPrime_apply_val (x : ZMod 8) :
    quadraticCharacterEightPrime x =
      if x.val % 2 = 0 then 0 else
        if x.val % 8 = 1 ∨ x.val % 8 = 3 then 1 else -1 := by
  fin_cases x <;>
    norm_num [ZMod.val, quadraticCharacterEightPrime, ZMod.χ₈', ZMod.val_natCast]

private theorem quadraticCharacterFour_correlation_pattern (k d : ZMod 4) :
    ‖∑ x : ZMod 4,
      quadraticCharacterFour (x + k) * quadraticCharacterFour (x + (k + d))‖ ≤
      if d.val = 0 then 4 else if d.val = 2 then 2 else 0 := by
  calc
    _ = ‖∑ x : ZMod 4,
      quadraticCharacterFour x * quadraticCharacterFour (x + d)‖ :=
      congrArg norm (quadraticCharacterFour_translate k d)
    _ ≤ _ := by
      classical
      let f : ZMod 4 → ℂ := fun x =>
        quadraticCharacterFour x * quadraticCharacterFour (x + d)
      change ‖∑ x : ZMod 4, f x‖ ≤ _
      have hsum : (∑ x : ZMod 4, f x) = ∑ i ∈ Finset.range 4, f (i : ZMod 4) := by
        rw [← Fin.sum_univ_eq_sum_range fun i => f (i : ZMod 4)]
        rfl
      rw [hsum]
      simp only [f]
      simp_rw [quadraticCharacterFour_apply_val, ZMod.val_add]
      fin_cases d <;>
        simp +decide [Finset.sum_range_succ, ZMod.val] <;> norm_num [ZMod]

private theorem quadraticCharacterEight_correlation_pattern (k d : ZMod 8) :
    ‖∑ x : ZMod 8,
      quadraticCharacterEight (x + k) * quadraticCharacterEight (x + (k + d))‖ ≤
      if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
  calc
    _ = ‖∑ x : ZMod 8,
      quadraticCharacterEight x * quadraticCharacterEight (x + d)‖ :=
      congrArg norm (quadraticCharacterEight_translate quadraticCharacterEight k d)
    _ ≤ _ := by
      classical
      let f : ZMod 8 → ℂ := fun x =>
        quadraticCharacterEight x * quadraticCharacterEight (x + d)
      change ‖∑ x : ZMod 8, f x‖ ≤ _
      have hsum : (∑ x : ZMod 8, f x) = ∑ i ∈ Finset.range 8, f (i : ZMod 8) := by
        rw [← Fin.sum_univ_eq_sum_range fun i => f (i : ZMod 8)]
        rfl
      rw [hsum]
      simp only [f]
      simp_rw [quadraticCharacterEight_apply_val, ZMod.val_add]
      fin_cases d <;>
        simp +decide [Finset.sum_range_succ, ZMod.val] <;> norm_num [ZMod]

private theorem quadraticCharacterEightPrime_correlation_pattern (k d : ZMod 8) :
    ‖∑ x : ZMod 8,
      quadraticCharacterEightPrime (x + k) * quadraticCharacterEightPrime (x + (k + d))‖ ≤
      if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
  calc
    _ = ‖∑ x : ZMod 8,
      quadraticCharacterEightPrime x * quadraticCharacterEightPrime (x + d)‖ :=
      congrArg norm (quadraticCharacterEight_translate quadraticCharacterEightPrime k d)
    _ ≤ _ := by
      classical
      let f : ZMod 8 → ℂ := fun x =>
        quadraticCharacterEightPrime x * quadraticCharacterEightPrime (x + d)
      change ‖∑ x : ZMod 8, f x‖ ≤ _
      have hsum : (∑ x : ZMod 8, f x) = ∑ i ∈ Finset.range 8, f (i : ZMod 8) := by
        rw [← Fin.sum_univ_eq_sum_range fun i => f (i : ZMod 8)]
        rfl
      rw [hsum]
      simp only [f]
      simp_rw [quadraticCharacterEightPrime_apply_val, ZMod.val_add]
      fin_cases d <;>
        simp +decide [Finset.sum_range_succ, ZMod.val] <;> norm_num [ZMod]

/-- The conductor-four local quadratic correlation has the exact gcd majorant. -/
theorem quadraticCharacterFour_shiftCorrelation_norm_le_gcd (k l : ℤ) :
    ‖∑ x : ZMod 4,
      quadraticCharacterFour (x + (k : ZMod 4)) *
        quadraticCharacterFour (x + (l : ZMod 4))‖ ≤
      (Nat.gcd 4 (l - k).natAbs : ℝ) := by
  let d : ZMod 4 := ((l - k : ℤ) : ZMod 4)
  have hshift : (l : ZMod 4) = (k : ZMod 4) + d := by
    dsimp [d]
    push_cast
    ring
  rw [hshift]
  by_cases hzero : d.val = 0
  · have hdzero : ((l - k : ℤ) : ZMod 4) = 0 := by
      change d = 0
      exact (ZMod.val_eq_zero d).mp hzero
    have hdivInt : (4 : ℤ) ∣ l - k :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (l - k) 4).mp hdzero
    have hdiv : 4 ∣ (l - k).natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdivInt)
    calc
      _ ≤ if d.val = 0 then 4 else if d.val = 2 then 2 else 0 := by
        exact quadraticCharacterFour_correlation_pattern (k : ZMod 4) d
      _ = (4 : ℝ) := by simp [hzero]
      _ ≤ (Nat.gcd 4 (l - k).natAbs : ℝ) := by
        exact_mod_cast Nat.le_of_dvd
          (Nat.gcd_pos_of_pos_left (l - k).natAbs (by norm_num))
          (Nat.dvd_gcd dvd_rfl hdiv)
  · by_cases htwo : d.val = 2
    · have hdTwo : ((l - k : ℤ) : ZMod 4) = (2 : ZMod 4) := by
        change d = (2 : ZMod 4)
        rw [← ZMod.natCast_zmod_val d]
        simp [htwo]
      have hfour : (4 : ℤ) ∣ 2 - (l - k) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (l - k) 2 4).mp hdTwo
      have htwoInt : (2 : ℤ) ∣ l - k := by
        have h : (2 : ℤ) ∣ 2 - (2 - (l - k)) :=
          Int.dvd_sub (by norm_num) (dvd_trans (by norm_num) hfour)
        simpa using h
      have hdiv : 2 ∣ (l - k).natAbs :=
        Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr htwoInt)
      calc
        _ ≤ if d.val = 0 then 4 else if d.val = 2 then 2 else 0 := by
          exact quadraticCharacterFour_correlation_pattern (k : ZMod 4) d
        _ = (2 : ℝ) := by simp [hzero, htwo]
        _ ≤ (Nat.gcd 4 (l - k).natAbs : ℝ) := by
          exact_mod_cast Nat.le_of_dvd
            (Nat.gcd_pos_of_pos_left (l - k).natAbs (by norm_num))
            (Nat.dvd_gcd (by norm_num) hdiv)
    · calc
        _ ≤ if d.val = 0 then 4 else if d.val = 2 then 2 else 0 := by
          exact quadraticCharacterFour_correlation_pattern (k : ZMod 4) d
        _ = (0 : ℝ) := by simp [hzero, htwo]
        _ ≤ (Nat.gcd 4 (l - k).natAbs : ℝ) := by positivity

/-- The first conductor-eight local quadratic correlation has the exact gcd majorant. -/
theorem quadraticCharacterEight_shiftCorrelation_norm_le_gcd (k l : ℤ) :
    ‖∑ x : ZMod 8,
      quadraticCharacterEight (x + (k : ZMod 8)) *
        quadraticCharacterEight (x + (l : ZMod 8))‖ ≤
      (Nat.gcd 8 (l - k).natAbs : ℝ) := by
  let d : ZMod 8 := ((l - k : ℤ) : ZMod 8)
  have hshift : (l : ZMod 8) = (k : ZMod 8) + d := by
    dsimp [d]
    push_cast
    ring
  rw [hshift]
  by_cases hzero : d.val = 0
  · have hdzero : ((l - k : ℤ) : ZMod 8) = 0 := by
      change d = 0
      exact (ZMod.val_eq_zero d).mp hzero
    have hdivInt : (8 : ℤ) ∣ l - k :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (l - k) 8).mp hdzero
    have hdiv : 8 ∣ (l - k).natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdivInt)
    calc
      _ ≤ if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
        exact quadraticCharacterEight_correlation_pattern (k : ZMod 8) d
      _ = (8 : ℝ) := by simp [hzero]
      _ ≤ (Nat.gcd 8 (l - k).natAbs : ℝ) := by
        exact_mod_cast Nat.le_of_dvd
          (Nat.gcd_pos_of_pos_left (l - k).natAbs (by norm_num))
          (Nat.dvd_gcd dvd_rfl hdiv)
  · by_cases hfour : d.val = 4
    · have hdFour : ((l - k : ℤ) : ZMod 8) = (4 : ZMod 8) := by
        change d = (4 : ZMod 8)
        rw [← ZMod.natCast_zmod_val d]
        simp [hfour]
      have height : (8 : ℤ) ∣ 4 - (l - k) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (l - k) 4 8).mp hdFour
      have hfourInt : (4 : ℤ) ∣ l - k := by
        have h : (4 : ℤ) ∣ 4 - (4 - (l - k)) :=
          Int.dvd_sub (by norm_num) (dvd_trans (by norm_num) height)
        simpa using h
      have hdiv : 4 ∣ (l - k).natAbs :=
        Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hfourInt)
      calc
        _ ≤ if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
          exact quadraticCharacterEight_correlation_pattern (k : ZMod 8) d
        _ = (4 : ℝ) := by simp [hzero, hfour]
        _ ≤ (Nat.gcd 8 (l - k).natAbs : ℝ) := by
          exact_mod_cast Nat.le_of_dvd
            (Nat.gcd_pos_of_pos_left (l - k).natAbs (by norm_num))
            (Nat.dvd_gcd (by norm_num) hdiv)
    · calc
        _ ≤ if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
          exact quadraticCharacterEight_correlation_pattern (k : ZMod 8) d
        _ = (0 : ℝ) := by simp [hzero, hfour]
        _ ≤ (Nat.gcd 8 (l - k).natAbs : ℝ) := by positivity

/-- The second conductor-eight local quadratic correlation has the exact gcd majorant. -/
theorem quadraticCharacterEightPrime_shiftCorrelation_norm_le_gcd (k l : ℤ) :
    ‖∑ x : ZMod 8,
      quadraticCharacterEightPrime (x + (k : ZMod 8)) *
        quadraticCharacterEightPrime (x + (l : ZMod 8))‖ ≤
      (Nat.gcd 8 (l - k).natAbs : ℝ) := by
  let d : ZMod 8 := ((l - k : ℤ) : ZMod 8)
  have hshift : (l : ZMod 8) = (k : ZMod 8) + d := by
    dsimp [d]
    push_cast
    ring
  rw [hshift]
  by_cases hzero : d.val = 0
  · have hdzero : ((l - k : ℤ) : ZMod 8) = 0 := by
      change d = 0
      exact (ZMod.val_eq_zero d).mp hzero
    have hdivInt : (8 : ℤ) ∣ l - k :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (l - k) 8).mp hdzero
    have hdiv : 8 ∣ (l - k).natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdivInt)
    calc
      _ ≤ if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
        exact quadraticCharacterEightPrime_correlation_pattern (k : ZMod 8) d
      _ = (8 : ℝ) := by simp [hzero]
      _ ≤ (Nat.gcd 8 (l - k).natAbs : ℝ) := by
        exact_mod_cast Nat.le_of_dvd
          (Nat.gcd_pos_of_pos_left (l - k).natAbs (by norm_num))
          (Nat.dvd_gcd dvd_rfl hdiv)
  · by_cases hfour : d.val = 4
    · have hdFour : ((l - k : ℤ) : ZMod 8) = (4 : ZMod 8) := by
        change d = (4 : ZMod 8)
        rw [← ZMod.natCast_zmod_val d]
        simp [hfour]
      have height : (8 : ℤ) ∣ 4 - (l - k) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (l - k) 4 8).mp hdFour
      have hfourInt : (4 : ℤ) ∣ l - k := by
        have h : (4 : ℤ) ∣ 4 - (4 - (l - k)) :=
          Int.dvd_sub (by norm_num) (dvd_trans (by norm_num) height)
        simpa using h
      have hdiv : 4 ∣ (l - k).natAbs :=
        Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hfourInt)
      calc
        _ ≤ if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
          exact quadraticCharacterEightPrime_correlation_pattern (k : ZMod 8) d
        _ = (4 : ℝ) := by simp [hzero, hfour]
        _ ≤ (Nat.gcd 8 (l - k).natAbs : ℝ) := by
          exact_mod_cast Nat.le_of_dvd
            (Nat.gcd_pos_of_pos_left (l - k).natAbs (by norm_num))
            (Nat.dvd_gcd (by norm_num) hdiv)
    · calc
        _ ≤ if d.val = 0 then 8 else if d.val = 4 then 4 else 0 := by
          exact quadraticCharacterEightPrime_correlation_pattern (k : ZMod 8) d
        _ = (0 : ℝ) := by simp [hzero, hfour]
        _ ≤ (Nat.gcd 8 (l - k).natAbs : ℝ) := by positivity

end RHTower
