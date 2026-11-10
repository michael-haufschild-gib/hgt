import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Field.ZMod

/-!
# Nonvanishing binomial coefficients and digit selection

Lucas's theorem and invertibility of the small binomial factors identify
nonzero binomial coefficients in characteristic `p` with coordinatewise
containment of base-`p` digits.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {p : ℕ} [Fact p.Prime]

private theorem small_choose_ne_zero_iff {a b : ℕ} (ha : a < p) :
    (a.choose b : ZMod p) ≠ 0 ↔ b ≤ a := by
  have hp : p.Prime := Fact.out
  constructor
  · intro hn
    by_contra hba
    have hz := Nat.choose_eq_zero_of_lt (show a < b by omega)
    exact hn (by rw [hz, Nat.cast_zero])
  · intro hba hz
    have hd : p ∣ a.choose b := (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact (hp.coprime_iff_not_dvd.mp (hp.coprime_choose_of_lt ha hba)) hd

/-- A binomial coefficient survives in characteristic `p` precisely when
the lower argument's base-`p` digits fit inside those of the upper argument. -/
theorem choose_ne_zero_iff_digits_le (n k : ℕ) :
    (n.choose k : ZMod p) ≠ 0 ↔
      ∀ e : ℕ, k / p ^ e % p ≤ n / p ^ e % p := by
  have hp : p.Prime := Fact.out
  let E := max n k
  have hpow : 2 ^ E ≤ p ^ E := by gcongr; exact hp.two_le
  have hE : max n k < p ^ E := Nat.lt_two_pow_self.trans_le hpow
  have hn : n < p ^ E := (le_max_left n k).trans_lt hE
  have hk : k < p ^ E := (le_max_right n k).trans_lt hE
  have hLucas : (n.choose k : ZMod p) =
      ∏ e ∈ range E, ((n / p ^ e % p).choose (k / p ^ e % p) : ZMod p) := by
    rw [← Nat.cast_prod]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (Choose.choose_modEq_prod_range_choose_nat hn hk)
  rw [hLucas, prod_ne_zero_iff]
  constructor
  · intro h e
    by_cases he : e < E
    · exact (small_choose_ne_zero_iff (Nat.mod_lt _ hp.pos)).mp (h e (mem_range.mpr he))
    · have hpow : p ^ E ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
      rw [Nat.div_eq_of_lt (hk.trans_le hpow), Nat.zero_mod]
      exact Nat.zero_le _
  · intro h e _
    exact (small_choose_ne_zero_iff (Nat.mod_lt _ hp.pos)).mpr (h e)

/-- The same digit criterion holds in every ring of characteristic `p`. -/
theorem cast_choose_ne_zero_iff_digits_le (K : Type*) [Semiring K] [CharP K p] (n k : ℕ) :
    (n.choose k : K) ≠ 0 ↔ ∀ e : ℕ, k / p ^ e % p ≤ n / p ^ e % p := by
  rw [← choose_ne_zero_iff_digits_le (p := p) n k]
  simp only [ne_eq, CharP.cast_eq_zero_iff K p, ZMod.natCast_eq_zero_iff]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.choose_ne_zero_iff_digits_le
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.cast_choose_ne_zero_iff_digits_le
