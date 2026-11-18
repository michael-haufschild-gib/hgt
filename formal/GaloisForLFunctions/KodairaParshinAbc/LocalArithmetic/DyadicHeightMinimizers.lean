import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.DyadicUnitEquationHeights

/-!
# Weil height on dyadic coefficient classes

For reduced odd numerator A and denominator B, multiplying by a dyadic
unit only enlarges one coordinate of the reduced fraction. The minimum
height is log(max(A,B)). The entire plateau of minimizing exponents is
given by the interval B/A ≤ 2^e ≤ 1 if B≤A, and the reversed interval
if A≤B. This computes the unit minimization in Ziegler, Lemma 2(4).
-/

noncomputable section
namespace GaloisForLFunctions.KodairaParshinAbc
open Height RHTower IsDedekindDomain

private theorem height_ratio (A B : ℕ) (hB : 0 < B) (hr : A.Coprime B) :
    logHeight₁ ((A : ℚ)/B) = Real.log (max A B : ℕ) := by
  have hB' : 0 < (B : ℤ) := by exact_mod_cast hB
  have hcop : (A : ℤ).natAbs.Coprime (B : ℤ).natAbs := hr
  have hnum : ((A:ℚ)/B).num = (A:ℤ) := by
    simpa only [Int.cast_natCast] using Rat.num_div_eq_of_coprime hB' hcop
  have hden : ((A:ℚ)/B).den = B := by
    exact_mod_cast (show (((A:ℚ)/B).den : ℤ) = B from by
      simpa only [Int.cast_natCast] using Rat.den_div_eq_of_coprime hB' hcop)
  rw [Rat.logHeight₁_eq_log_max, hnum, hden, Int.natAbs_natCast]

/-- Positive exponents enlarge only the odd numerator, even before taking logarithms. -/
theorem oddRatio_height_mul_pow (A B k : ℕ) (hB : Odd B) (hr : A.Coprime B) :
    logHeight₁ ((A:ℚ)/B * 2^k) = Real.log (max (A*2^k) B : ℕ) := by
  have hB' : 0 < B := by obtain ⟨m,hm⟩ := hB; omega
  have hcop := hr.mul_left ((Nat.coprime_two_left.mpr hB).pow_left k)
  rw [show (A:ℚ)/B * 2^k = (↑(A*2^k):ℚ)/B by push_cast; ring]
  exact height_ratio _ _ hB' hcop

/-- Negative exponents enlarge only the odd denominator. -/
theorem oddRatio_height_div_pow (A B k : ℕ) (hA : Odd A) (hB : 0 < B) (hr : A.Coprime B) :
    logHeight₁ ((A:ℚ)/B / 2^k) = Real.log (max A (B*2^k) : ℕ) := by
  have hcop := hr.mul_right ((Nat.coprime_two_right.mpr hA).pow_right k)
  rw [show (A:ℚ)/B / 2^k = (A:ℚ)/(↑(B*2^k):ℚ) by push_cast; rw [div_div]]
  exact height_ratio _ _ (Nat.mul_pos hB (pow_pos zero_lt_two _)) hcop

private theorem log_nat_eq_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Real.log m = Real.log n ↔ m=n := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.log_injOn_pos.eq_iff hm' hn', Nat.cast_inj]

/-- The two inequalities describe exactly when rescaling by an exponent of given sign is minimal. -/
theorem oddRatio_height_minimizer_pos (A B k : ℕ) (hB : Odd B) (hr : A.Coprime B) :
    logHeight₁ ((A:ℚ)/B * 2^k) = logHeight₁ ((A:ℚ)/B) ↔ A*2^k ≤ max A B := by
  have hb : 0 < B := by obtain ⟨m,hm⟩ := hB; omega
  rw [oddRatio_height_mul_pow _ _ _ hB hr, height_ratio _ _ hb hr,
    log_nat_eq_iff (hb.trans_le (le_max_right _ _)) (hb.trans_le (le_max_right _ _))]
  have ha : A ≤ A * 2^k := Nat.le_mul_of_pos_right _ (pow_pos zero_lt_two _)
  exact ⟨fun h => h ▸ le_max_left _ _, fun h => le_antisymm (max_le h (le_max_right _ _))
    (max_le_max_right _ ha)⟩

theorem oddRatio_height_minimizer_neg (A B k : ℕ) (hA : Odd A) (hB : Odd B) (hr : A.Coprime B) :
    logHeight₁ ((A:ℚ)/B / 2^k) = logHeight₁ ((A:ℚ)/B) ↔ B*2^k ≤ max A B := by
  have hb : 0 < B := by obtain ⟨m,hm⟩ := hB; omega
  have ha : 0 < A := by obtain ⟨m,hm⟩ := hA; omega
  rw [oddRatio_height_div_pow _ _ _ hA hb hr, height_ratio _ _ hb hr,
    log_nat_eq_iff (ha.trans_le (le_max_left _ _)) (ha.trans_le (le_max_left _ _))]
  have hle : B ≤ B * 2^k := Nat.le_mul_of_pos_right _ (pow_pos zero_lt_two _)
  exact ⟨fun h => h ▸ le_max_right _ _, fun h => le_antisymm (max_le (le_max_left _ _) h)
    (max_le_max_left _ hle)⟩

/-- Every normalized odd fraction realizes the least Weil height of its entire dyadic unit orbit. -/
theorem oddRatio_height_isLeast (A B : ℕ) (hA : Odd A) (hB : Odd B) (hr : A.Coprime B) :
    IsLeast (Set.range fun u : fieldOneSUnitSubgroup dyadicUnitPlaces =>
      logHeight₁ ((A:ℚ)/B * (u.val:ℚ))) (Real.log (max A B : ℕ)) := by
  have hb : 0 < B := by obtain ⟨m,hm⟩ := hB; omega
  refine ⟨⟨1, by simpa only [Subgroup.coe_one, Units.val_one, mul_one] using height_ratio A B hb hr⟩, ?_⟩
  rintro _ ⟨u,rfl⟩
  change Real.log (max A B : ℕ) ≤ logHeight₁ ((A:ℚ)/B * (u.val:ℚ))
  have hmax : (0:ℝ) < (max A B : ℕ) := by exact_mod_cast hb.trans_le (le_max_right A B)
  have hm : |(u.val:ℚ)| ∈ Set.range (fun e : ℤ => (2:ℚ)^e) := dyadicUnit_abs_range ▸ ⟨u,rfl⟩
  obtain ⟨e, he⟩ := hm
  change (2:ℚ)^e = |(u.val:ℚ)| at he
  have hab : logHeight₁ ((A:ℚ)/B * (u.val:ℚ)) = logHeight₁ ((A:ℚ)/B * 2^e) := by
    rw [he]
    rcases le_or_gt 0 (u.val:ℚ) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, logHeight₁_neg]
  rw [hab]
  cases e with
  | ofNat k =>
    change Real.log (max A B : ℕ) ≤ logHeight₁ ((A:ℚ)/B * 2^(k : ℤ))
    rw [zpow_natCast, oddRatio_height_mul_pow _ _ _ hB hr]
    apply Real.log_le_log hmax
    exact_mod_cast max_le_max_right B (Nat.le_mul_of_pos_right A (pow_pos (zero_lt_two : 0 < (2:ℕ)) k))
  | negSucc k =>
    rw [zpow_negSucc, ← div_eq_mul_inv, oddRatio_height_div_pow _ _ _ hA hb hr]
    apply Real.log_le_log hmax
    exact_mod_cast max_le_max_left A (Nat.le_mul_of_pos_right B (pow_pos (zero_lt_two : 0 < (2:ℕ)) (k+1)))

/-- Odd solvable targets remain unbounded even after minimizing their height over every dyadic unit. -/
theorem dyadic_solvable_minimum_unbounded (T : ℝ) :
    ∃ C : ℕ, Odd C ∧ T < logHeight₁ (C:ℚ) ∧
      IsLeast (Set.range fun u : fieldOneSUnitSubgroup dyadicUnitPlaces =>
        logHeight₁ ((C:ℚ) * (u.val:ℚ))) (logHeight₁ (C:ℚ)) ∧
      Nonempty (RationalUnitSolutions dyadicUnitPlaces 3 5 (C:ℚ)) := by
  obtain ⟨C,hC,hT,hs⟩ := dyadic_odd_solvable_targets T
  have hpos : 0 < C := by obtain ⟨m,hm⟩ := hC; omega
  letI : NeZero C := ⟨hpos.ne'⟩
  refine ⟨C,hC,hT,?_,hs⟩
  simpa only [Nat.cast_one, div_one, Rat.logHeight₁_natCast, max_eq_left (show 1 ≤ C by omega)] using
    oddRatio_height_isLeast C 1 hC odd_one (Nat.coprime_one_right C)

#print axioms dyadic_solvable_minimum_unbounded
#print axioms oddRatio_height_mul_pow
#print axioms oddRatio_height_div_pow
#print axioms oddRatio_height_minimizer_pos
#print axioms oddRatio_height_minimizer_neg
#print axioms oddRatio_height_isLeast

end GaloisForLFunctions.KodairaParshinAbc
