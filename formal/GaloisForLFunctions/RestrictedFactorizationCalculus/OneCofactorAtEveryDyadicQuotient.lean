import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSharpHeightOfARemovablePrimeHead

/-!
# One cofactor on the dyadic quotient chain

At a fixed outer observation, freeze its sieve and its prime weights. At
each dyadic quotient keep only the unit cofactor, using the counting
center through half that quotient. These signed readings telescope to
the full terminal head. One reading carries at least the full absolute
signal divided by the number of binary digits.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Signed unit-cofactor reading at the j-th dyadic quotient of X. -/
def dyadicUnitReading (a : ArithmeticFunction ℝ) (y X j : ℕ) :=
  let n := X / 2^j
  roughInteriorReading a y n (n/2)

private abbrev headAt (a : ArithmeticFunction ℝ) (y : ℕ) :=
  quotientReading (roughFloorCoefficient y a)

private theorem unit_difference (a : ArithmeticFunction ℝ) (y n : ℕ) :
    roughInteriorReading a y n (n/2) = headAt a y n - headAt a y (n/2) := by
  have h := rough_head_and_interior a y n (n/2)
  rw [rough_action_as_a_coefficient_prefix,min_eq_right (Nat.div_le_self ..)] at h
  exact (eq_sub_iff_add_eq.mpr h.symm)

/-- At positive quotient the corrected reading uses exactly one cofactor. -/
theorem half_cut_has_one_cofactor {n : ℕ} (hn : 0 < n) : n/(n/2+1) = 1 := by
  omega

/-- Exact reconstruction from the dyadic chain, with the sieve and the
prime reading held at their original observation. -/
theorem dyadic_unit_readings_telescope (a : ArithmeticFunction ℝ) (y X : ℕ) :
    ∑ j ∈ range (Nat.log 2 X+1), dyadicUnitReading a y X j = headAt a y X := by
  let F := fun j : ℕ => headAt a y (X/2^j)
  have term (j : ℕ) : dyadicUnitReading a y X j = F j-F (j+1) := by
    simp only [dyadicUnitReading,unit_difference,F,pow_succ,Nat.div_div_eq_div_mul]
  have hsum (J : ℕ) : ∑ j ∈ range J, (F j-F (j+1)) = F 0-F J := by
    induction J with
    | zero => simp
    | succ J ih => rw [sum_range_succ,ih]; ring
  simp only [term,hsum,F,pow_zero,Nat.div_one,
    Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) X)]
  simp [quotientReading]

/-- Some single-cofactor reading captures the full absolute prefix up to
the exact number of binary digits, without a sign assumption. -/
theorem exists_dyadic_unit_reading (a : ArithmeticFunction ℝ) (y X : ℕ) :
    ∃ j < Nat.log 2 X+1, |headAt a y X| ≤
      ((Nat.log 2 X:ℕ)+1:ℝ)*|dyadicUnitReading a y X j| := by
  obtain ⟨j,hj,hmax⟩ := (range (Nat.log 2 X+1)).exists_max_image
    (fun j => |dyadicUnitReading a y X j|) ⟨0,mem_range.mpr (Nat.succ_pos _)⟩
  refine ⟨j,mem_range.mp hj,?_⟩
  rw [←dyadic_unit_readings_telescope]
  exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum hmax).trans_eq (by simp))

private theorem binary_digits_price {η : ℝ} (he : 0 < η) {X : ℕ} (xp : 0 < X) :
    ((Nat.log 2 X:ℕ)+1:ℝ) ≤ (1+1/(η*Real.log 2))*(X:ℝ)^η := by
  have h2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hnat := Nat.pow_log_le_self 2 xp.ne'
  have low : (2:ℝ)^Nat.log 2 X ≤ X := by exact_mod_cast hnat
  have logbound := Real.log_le_log (by positivity) low
  rw [Real.log_pow] at logbound
  have r := Real.log_le_rpow_div (Nat.cast_nonneg X) he
  have q := (le_div_iff₀ h2).mpr (logbound.trans r)
  have one := Real.one_le_rpow (Nat.one_le_cast.mpr xp) he.le
  calc ((Nat.log 2 X:ℕ)+1:ℝ) ≤ (X:ℝ)^η/η/Real.log 2 + (X:ℝ)^η := add_le_add q one
       _ = _ := by ring

/-- The zero abscissa is exactly the growth boundary of the dyadic
unit-cofactor readings. At each X only its binary quotient chain is tested. -/
theorem dyadic_single_cofactors_detect_the_strip {b : ℝ} (hb : 1/2 ≤ b)
    (a : ℕ → ArithmeticFunction ℝ) (dom : ∀ X q, |a X q| ≤ vonMangoldt q)
    (fix : ∀ X p, p.Prime → a X p=roughMangoldtWeight (logSquareCutoff X) p) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ j < Nat.log 2 X+1,
        |dyadicUnitReading (a X) (logSquareCutoff X) X j| ≤ C*(X:ℝ)^(b+ε)) ↔
      RHTower.zetaZeroAbscissa ≤ b := by
  have full := one_perturbed_terminal_head_detects_the_strip (α := 1) zero_lt_one le_rfl hb a dom fix
  simp only [one_mul] at full
  constructor
  · intro cells
    apply full.mp
    intro ε ep
    let η := ε/2
    have he : 0 < η := half_pos ep
    obtain ⟨C,c0,hc⟩ := cells η he
    let K := 1+1/(η*Real.log 2)
    apply prefixPower_of_eventual (C := K*C) (by simp [terminalPrimeHead,quotientReading])
      ((by norm_num : (0:ℝ)<1/2).trans_le (hb.trans (le_add_of_nonneg_right ep.le)))
    filter_upwards [hc,eventually_ge_atTop (1:ℕ)] with X h xp
    obtain ⟨j,hj,large⟩ := exists_dyadic_unit_reading (a X) (logSquareCutoff X) X
    have cost := mul_le_mul (binary_digits_price he xp) (h j hj) (abs_nonneg _)
      (mul_nonneg (by dsimp only [K]; positivity) (Real.rpow_nonneg (Nat.cast_nonneg X) _))
    simp only [terminalPrimeHead,Real.rpow_one,Nat.floor_natCast]
    apply large.trans (cost.trans_eq ?_)
    rw [show b+ε=η+(b+η) by dsimp only [η]; ring,Real.rpow_add (Nat.cast_pos.mpr xp)]
    ring
  · intro strip ε ep
    obtain ⟨C,c0,hC⟩ := shrinking_the_cofactor_range_for_prime_readings (α := 1)
      zero_lt_one (by simpa using strip.trans_lt (lt_add_of_pos_right b ep))
    refine ⟨C+C,add_nonneg c0 c0,?_⟩
    filter_upwards [hC] with X h
    have heads (n : ℕ) (hn : n ≤ X) :
        |headAt (a X) (logSquareCutoff X) n| ≤ C*(X:ℝ)^(b+ε) := by
      have hc := h n (by simpa using (Nat.cast_le.mpr hn : (n:ℝ) ≤ X)) (a X) (dom X) (fix X)
      rwa [rough_head_and_interior,add_sub_cancel_left,min_eq_right hn] at hc
    intro j _
    let n := X/2^j
    have nx : n ≤ X := Nat.div_le_self .. 
    rw [dyadicUnitReading,unit_difference]
    exact (abs_sub ..).trans ((add_le_add (heads n nx) (heads (n/2) ((Nat.div_le_self ..).trans nx))).trans_eq
      (add_mul ..).symm)

#print axioms dyadic_unit_readings_telescope
#print axioms exists_dyadic_unit_reading
#print axioms dyadic_single_cofactors_detect_the_strip

end GaloisForLFunctions.RestrictedFactorizationCalculus
