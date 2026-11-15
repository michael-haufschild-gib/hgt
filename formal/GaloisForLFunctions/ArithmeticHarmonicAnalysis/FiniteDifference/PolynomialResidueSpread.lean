import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteDifference.ShortModularRigidity

/-!
# Spread of polynomial residues

Reduction modulo an integer commutes with finite differences up to
congruence. Hence values of a degree `d` integer polynomial confined
to an interval of width less than `k / 2^d` are constant modulo `k`.
The same principle applies to any integer sequence with vanishing
positive order finite difference.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Function Polynomial

/-- Pointwise congruence persists under every finite difference. -/
theorem iterated_difference_modEq (f g : ℕ → ℤ) (k : ℤ)
    (hfg : ∀ j, f j ≡ g j [ZMOD k]) (n j : ℕ) :
    (fwdDiff 1)^[n] f j ≡ (fwdDiff 1)^[n] g j [ZMOD k] := by
  induction n generalizing j with
  | zero => exact hfg j
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact (ih (j + 1)).sub (ih j)

/-- Restriction of integer finite differences to natural inputs commutes with iteration. -/
theorem iterated_difference_natCast (f : ℤ → ℤ) (n j : ℕ) :
    (fwdDiff 1)^[n] (fun i : ℕ => f i) j = (fwdDiff 1)^[n] f (j : ℤ) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    change (fwdDiff 1)^[n] (fun i : ℕ => f i) (j + 1) -
        (fwdDiff 1)^[n] (fun i : ℕ => f i) j =
      (fwdDiff 1)^[n] f ((j : ℤ) + 1) - (fwdDiff 1)^[n] f (j : ℤ)
    rw [ih, ih, Nat.cast_add, Nat.cast_one]

/-- Polynomial values on natural inputs have their expected vanishing difference. -/
theorem polynomial_nat_iterated_difference_zero (P : ℤ[X]) :
    (fwdDiff 1)^[P.natDegree + 1] (fun j : ℕ => P.eval (j : ℤ)) = 0 := by
  funext j
  rw [iterated_difference_natCast (fun z : ℤ => P.eval z),
    P.fwdDiff_iter_degree_add_one_eq_zero]
  rfl

/-- Short residues of an integer polynomial sequence are constant. -/
theorem short_residue_sequence_constant (f : ℕ → ℤ) (n : ℕ) (D k : ℤ)
    (hk : 0 < k) (hsize : 2 ^ n * D < k)
    (hz : (fwdDiff 1)^[n + 1] f = 0)
    (hb : ∀ j, f j % k ≤ D) : ∀ j, f j % k = f 0 % k := by
  apply (short_modular_iterated_difference_iff (fun j => f j % k) 0 D k
    (fun j => ⟨Int.emod_nonneg _ (ne_of_gt hk), by simpa only [zero_add] using hb j⟩)
    n hsize).mp
  intro j
  have he := iterated_difference_modEq (fun j => f j % k) f k
    (fun j => Int.mod_modEq (f j) k) (n + 1) j
  rw [hz] at he
  exact he

/-- Exact confinement criterion for values of any integer polynomial. -/
theorem polynomial_residue_interval_iff (P : ℤ[X]) (D k : ℤ)
    (hk : 0 < k) (hsize : 2 ^ P.natDegree * D < k) :
    (∀ j : ℕ, P.eval (j : ℤ) % k ≤ D) ↔
      P.eval 0 % k ≤ D ∧ ∀ j : ℕ, P.eval (j : ℤ) % k = P.eval 0 % k := by
  constructor
  · intro hb
    exact ⟨by simpa only [Nat.cast_zero] using hb 0,
      short_residue_sequence_constant _ _ _ _ hk hsize
        (polynomial_nat_iterated_difference_zero P) hb⟩
  · rintro ⟨h0, hc⟩ j
    rw [hc j]
    exact h0

/-- Every nonconstant polynomial residue sequence escapes each interval below
its degree-dependent threshold. -/
theorem polynomial_residue_escape (P : ℤ[X]) (D k : ℤ)
    (hk : 0 < k) (hsize : 2 ^ P.natDegree * D < k) :
    (∀ j : ℕ, P.eval (j : ℤ) % k = P.eval 0 % k) ∨ ∃ j : ℕ, D < P.eval (j : ℤ) % k := by
  by_cases hc : ∀ j : ℕ, P.eval (j : ℤ) % k = P.eval 0 % k
  · exact Or.inl hc
  · right
    by_contra hn
    have hb : ∀ j : ℕ, P.eval (j : ℤ) % k ≤ D := by
      intro j
      by_contra hj
      exact hn ⟨j, lt_of_not_ge hj⟩
    exact hc ((polynomial_residue_interval_iff P D k hk hsize).mp hb).2

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iterated_difference_modEq
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iterated_difference_natCast
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.polynomial_nat_iterated_difference_zero
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.short_residue_sequence_constant
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.polynomial_residue_interval_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.polynomial_residue_escape
