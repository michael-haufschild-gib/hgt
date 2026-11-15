import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueDifferentialCharacters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDifferentialCutoffs

/-!
# Character weights of regular Kummer monomials

The regular monomials are indexed by an inverse radical character and
a polynomial degree below its exact cutoff. Their full cyclic weights
are distinct, positive, and smaller than `N(q-1)`. Multiplication by
the prime-power branch degree strictly increases each such residue.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s d r : ℕ)

/-- Indices of the polynomial inverse-character monomials allowed by global regularity. -/
abbrev SquareKummerRegularIndex :=
  (i : Fin (p ^ (s + 1) + 1)) × Fin (kummerDifferentialCutoff p s d r i.val)

/-- The full cyclic weight of the regular monomial with indices `(i,k)` is `N(k+1)-i`. -/
def squareKummerRegularWeight (a : SquareKummerRegularIndex p s d r) : ℕ :=
  (p ^ (s + 1) + 1) * (a.2.val + 1) - a.1.val

private theorem regularWeight_add (a : SquareKummerRegularIndex p s d r) :
    squareKummerRegularWeight p s d r a + a.1.val =
      (p ^ (s + 1) + 1) * (a.2.val + 1) := by
  apply Nat.sub_add_cancel
  have h := Nat.mul_le_mul_left (p ^ (s + 1) + 1)
    (Nat.succ_le_succ (Nat.zero_le a.2.val))
  rw [mul_one] at h
  exact le_trans a.1.isLt.le h

/-- Every regular monomial has a positive full cyclic weight below the cyclic covering degree. -/
theorem squareKummerRegularWeight_bounds (a : SquareKummerRegularIndex p s d r) :
    0 < squareKummerRegularWeight p s d r a ∧
      squareKummerRegularWeight p s d r a < (p ^ (s + 1) + 1) * (p ^ (d + 1) - 1) := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hcop := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega] at hcop
  have h := reducedResidue_regular_character_rise
    (p ^ (s + 1) + 1) (p ^ (d + 1) - 1) (kummerExponent (p ^ (d + 1)) r)
    (Nat.succ_pos _) (by omega) hcop a.1 a.2.val a.2.isLt
  exact ⟨h.1, h.2.1⟩

/-- The branch degree strictly increases the residue of every regular monomial character weight. -/
theorem squareKummerRegularWeight_frobenius_rise (a : SquareKummerRegularIndex p s d r) :
    squareKummerRegularWeight p s d r a <
      ((p ^ (d + 1)) ^ r * squareKummerRegularWeight p s d r a) %
        ((p ^ (s + 1) + 1) * (p ^ (d + 1) - 1)) := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have he : p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 := by omega
  have hcop := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [he] at hcop
  have h := reducedResidue_regular_character_rise
    (p ^ (s + 1) + 1) (p ^ (d + 1) - 1) (kummerExponent (p ^ (d + 1)) r)
    (Nat.succ_pos _) (by omega) hcop a.1 a.2.val a.2.isLt
  have hdegree := kummerInfinity_primePower_poleDegree p d r
  rw [he] at hdegree
  simpa only [squareKummerRegularWeight, hdegree] using h.2.2

/-- Distinct regular monomials have distinct full cyclic character weights. -/
theorem squareKummerRegularWeight_injective :
    Function.Injective (squareKummerRegularWeight p s d r) := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  have hx := regularWeight_add p s d r ⟨i, k⟩
  have hy := regularWeight_add p s d r ⟨i', k'⟩
  have he : (p ^ (s + 1) + 1) * (k.val + 1) + i'.val =
      (p ^ (s + 1) + 1) * (k'.val + 1) + i.val := by omega
  have hm := congrArg (fun x : ℕ => x % (p ^ (s + 1) + 1)) he
  simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt i'.isLt] at hm
  have hi : i = i' := Fin.ext hm.symm
  subst i'
  have he' : (p ^ (s + 1) + 1) * (k.val + 1) =
      (p ^ (s + 1) + 1) * (k'.val + 1) := by omega
  have hk : k = k' := Fin.ext (Nat.succ.inj
    (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos _) he'))
  cases hk
  rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
