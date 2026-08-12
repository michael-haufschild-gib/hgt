import GaloisForLFunctions.RHTower.Sieve.FiniteFiberCorrelation
import GaloisForLFunctions.RHTower.Sieve.VinogradovDiagonalMoment
import Mathlib.Algebra.Field.ZMod

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Modulus large enough that equality of the first `k` power sums for
length-`b` tuples is equivalent to equality modulo this number. -/
def vinogradovMomentModulus (N b k : ℕ) : ℕ :=
  2 * b * N ^ k + 1

instance vinogradovMomentModulusNeZero (N b k : ℕ) :
    NeZero (vinogradovMomentModulus N b k) := by
  refine ⟨?_⟩
  unfold vinogradovMomentModulus
  omega

/-- First `k` power sums of a tuple modulo an arbitrary modulus. -/
def vinogradovPowerSignatureMod (q k : ℕ) {N b : ℕ} (m : Fin b → Fin N) :
    Fin k → ZMod q :=
  fun j => ∑ i : Fin b, ((m i).val : ZMod q) ^ (j.val + 1)

/-- First `k` power sums of a tuple, placed in one finite additive group. -/
def vinogradovModularPowerSignature {N b k : ℕ} (m : Fin b → Fin N) :
    Fin k → ZMod (vinogradovMomentModulus N b k) :=
  vinogradovPowerSignatureMod (vinogradovMomentModulus N b k) k m

theorem sum_power_lt_vinogradovMomentModulus
    {N b k : ℕ} (hN : N ≠ 0) (m : Fin b → Fin N) (j : Fin k) :
    (∑ i : Fin b, (m i).val ^ (j.val + 1)) <
      vinogradovMomentModulus N b k := by
  have hterm : ∀ i : Fin b, (m i).val ^ (j.val + 1) ≤ N ^ k := by
    intro i
    calc
      (m i).val ^ (j.val + 1) ≤ N ^ (j.val + 1) :=
        Nat.pow_le_pow_left (Nat.le_of_lt (m i).isLt) _
      _ ≤ N ^ k := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN) (by omega)
  calc
    (∑ i : Fin b, (m i).val ^ (j.val + 1)) ≤
        ∑ _i : Fin b, N ^ k := Finset.sum_le_sum fun i _ => hterm i
    _ = b * N ^ k := by simp
    _ < vinogradovMomentModulus N b k := by
      unfold vinogradovMomentModulus
      exact Nat.lt_succ_of_le
        (Nat.mul_le_mul_right (N ^ k) (by omega : b ≤ 2 * b))

theorem sum_power_lt_of_large_modulus
    {q N b k : ℕ} (hN : N ≠ 0) (hq : 2 * b * N ^ k < q)
    (m : Fin b → Fin N) (j : Fin k) :
    (∑ i : Fin b, (m i).val ^ (j.val + 1)) < q := by
  have hterm : ∀ i : Fin b, (m i).val ^ (j.val + 1) ≤ N ^ k := by
    intro i
    calc
      (m i).val ^ (j.val + 1) ≤ N ^ (j.val + 1) :=
        Nat.pow_le_pow_left (Nat.le_of_lt (m i).isLt) _
      _ ≤ N ^ k := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN) (by omega)
  calc
    (∑ i : Fin b, (m i).val ^ (j.val + 1)) ≤
        ∑ _i : Fin b, N ^ k := Finset.sum_le_sum fun i _ => hterm i
    _ = b * N ^ k := by simp
    _ ≤ 2 * b * N ^ k :=
      Nat.mul_le_mul_right (N ^ k) (by omega : b ≤ 2 * b)
    _ < q := hq

/-- Any modulus larger than twice the maximal power sum preserves every
first-`k` power-sum equation exactly. -/
theorem vinogradovPowerSignatureMod_eq_iff_of_large
    {q N b k : ℕ} (hN : N ≠ 0) (hq : 2 * b * N ^ k < q)
    (m n : Fin b → Fin N) :
    vinogradovPowerSignatureMod q k m = vinogradovPowerSignatureMod q k n ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        ∑ i : Fin b, (m i).val ^ j = ∑ i : Fin b, (n i).val ^ j := by
  constructor
  · intro hsig j hjpos hjk
    let a : Fin k := ⟨j - 1, by omega⟩
    have hcoord := congrFun hsig a
    have hj : j - 1 + 1 = j := by omega
    have hcast :
        ((∑ i : Fin b, (m i).val ^ j : ℕ) : ZMod q) =
          ((∑ i : Fin b, (n i).val ^ j : ℕ) : ZMod q) := by
      simpa [vinogradovPowerSignatureMod, a, hj, Nat.cast_sum,
        Nat.cast_pow] using hcoord
    have hmod := (ZMod.natCast_eq_natCast_iff'
      (∑ i : Fin b, (m i).val ^ j)
      (∑ i : Fin b, (n i).val ^ j) q).mp hcast
    have hm_lt : (∑ i : Fin b, (m i).val ^ j) < q := by
      simpa [a, hj] using sum_power_lt_of_large_modulus hN hq m a
    have hn_lt : (∑ i : Fin b, (n i).val ^ j) < q := by
      simpa [a, hj] using sum_power_lt_of_large_modulus hN hq n a
    simpa [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hn_lt] using hmod
  · intro hpower
    funext a
    have hnat := hpower (a.val + 1) (by omega) (by omega)
    simpa [vinogradovPowerSignatureMod, Nat.cast_sum, Nat.cast_pow] using
      congrArg (fun z : ℕ => (z : ZMod q)) hnat

/-- The large finite modulus loses no information about the power-sum
equations. -/
theorem vinogradovModularPowerSignature_eq_iff
    {N b k : ℕ} (hN : N ≠ 0) (m n : Fin b → Fin N) :
    vinogradovModularPowerSignature (k := k) m =
      vinogradovModularPowerSignature (k := k) n ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        ∑ i : Fin b, (m i).val ^ j = ∑ i : Fin b, (n i).val ^ j := by
  constructor
  · intro hsig j hjpos hjk
    let q : Fin k := ⟨j - 1, by omega⟩
    have hcoord := congrFun hsig q
    have hj : j - 1 + 1 = j := by omega
    have hcast :
        ((∑ i : Fin b, (m i).val ^ j : ℕ) :
            ZMod (vinogradovMomentModulus N b k)) =
          ((∑ i : Fin b, (n i).val ^ j : ℕ) :
            ZMod (vinogradovMomentModulus N b k)) := by
      simpa [vinogradovModularPowerSignature, vinogradovPowerSignatureMod,
        q, hj, Nat.cast_sum,
        Nat.cast_pow] using hcoord
    have hmod := (ZMod.natCast_eq_natCast_iff'
      (∑ i : Fin b, (m i).val ^ j)
      (∑ i : Fin b, (n i).val ^ j)
      (vinogradovMomentModulus N b k)).mp hcast
    have hm_lt : (∑ i : Fin b, (m i).val ^ j) <
        vinogradovMomentModulus N b k := by
      simpa [q, hj] using sum_power_lt_vinogradovMomentModulus hN m q
    have hn_lt : (∑ i : Fin b, (n i).val ^ j) <
        vinogradovMomentModulus N b k := by
      simpa [q, hj] using sum_power_lt_vinogradovMomentModulus hN n q
    simpa [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hn_lt] using hmod
  · intro hpower
    funext q
    have hnat := hpower (q.val + 1) (by omega) (by omega)
    simpa [vinogradovModularPowerSignature, vinogradovPowerSignatureMod,
      Nat.cast_sum, Nat.cast_pow] using
      congrArg (fun z : ℕ =>
        (z : ZMod (vinogradovMomentModulus N b k))) hnat

/-- Finite-group Vinogradov moment at an arbitrary nonzero modulus. -/
def vinogradovModularMomentAt (q N b k : ℕ) [NeZero q] : ℕ :=
  finiteFiberEnergy
    (vinogradovPowerSignatureMod q k :
      (Fin b → Fin N) → Fin k → ZMod q)

theorem vinogradovModularMomentAt_eq_card_of_large
    {q N b k : ℕ} [NeZero q] (hN : N ≠ 0)
    (hq : 2 * b * N ^ k < q) :
    vinogradovModularMomentAt q N b k =
      Fintype.card (VinogradovDiagonalSolution N b k) := by
  let signature : (Fin b → Fin N) → Fin k → ZMod q :=
    vinogradovPowerSignatureMod q k
  let e : {p : (Fin b → Fin N) × (Fin b → Fin N) //
        signature p.1 = signature p.2} ≃
      VinogradovDiagonalSolution N b k :=
    { toFun := fun p => ⟨p.1,
        (vinogradovPowerSignatureMod_eq_iff_of_large hN hq p.1.1 p.1.2).mp p.2⟩
      invFun := fun p => ⟨p.1,
        (vinogradovPowerSignatureMod_eq_iff_of_large hN hq p.1.1 p.1.2).mpr p.2⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext rfl }
  calc
    vinogradovModularMomentAt q N b k =
        Fintype.card {p : (Fin b → Fin N) × (Fin b → Fin N) //
          signature p.1 = signature p.2} := by
      exact finiteFiberEnergy_eq_card signature
    _ = Fintype.card (VinogradovDiagonalSolution N b k) :=
      Fintype.card_congr e

/-- Finite-group formulation of the Vinogradov moment. -/
def vinogradovModularMoment (N b k : ℕ) : ℕ :=
  finiteFiberEnergy
    (vinogradovModularPowerSignature :
      (Fin b → Fin N) → Fin k → ZMod (vinogradovMomentModulus N b k))

theorem vinogradovModularMoment_eq_card
    {N b k : ℕ} (hN : N ≠ 0) :
    vinogradovModularMoment N b k =
      Fintype.card (VinogradovDiagonalSolution N b k) := by
  let signature : (Fin b → Fin N) →
      Fin k → ZMod (vinogradovMomentModulus N b k) :=
    vinogradovModularPowerSignature
  let e : {p : (Fin b → Fin N) × (Fin b → Fin N) //
        signature p.1 = signature p.2} ≃
      VinogradovDiagonalSolution N b k :=
    { toFun := fun p => ⟨p.1,
        (vinogradovModularPowerSignature_eq_iff hN p.1.1 p.1.2).mp p.2⟩
      invFun := fun p => ⟨p.1,
        (vinogradovModularPowerSignature_eq_iff hN p.1.1 p.1.2).mpr p.2⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext rfl }
  calc
    vinogradovModularMoment N b k =
        Fintype.card {p : (Fin b → Fin N) × (Fin b → Fin N) //
          signature p.1 = signature p.2} := by
      exact finiteFiberEnergy_eq_card signature
    _ = Fintype.card (VinogradovDiagonalSolution N b k) :=
      Fintype.card_congr e

end

end RHTower.Sieve
