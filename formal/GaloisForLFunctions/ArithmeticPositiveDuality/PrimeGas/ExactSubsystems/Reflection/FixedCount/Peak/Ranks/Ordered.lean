import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.ShortPackets

/-! # Adjacent prime energy gaps in any ordered finite packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks

open Real Finset

local instance : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective

def enumeration (S : Finset Nat.Primes) : Fin S.card ≃ S := (S.orderIsoOfFin rfl).toEquiv

def mode (S : Finset Nat.Primes) (i : ℕ) (hi : i < S.card) := enumeration S ⟨i,hi⟩

theorem mode_lt {S : Finset Nat.Primes} {i j : ℕ} {hi : i < S.card} {hj : j < S.card} (h : i < j) :
    (mode S i hi).val.val < (mode S j hj).val.val :=
  (S.orderIsoOfFin rfl).strictMono (show (⟨i,hi⟩ : Fin S.card) < ⟨j,hj⟩ from h)

theorem energy_inc {S : Finset Nat.Primes} {i j : ℕ} {hi : i < S.card} {hj : j < S.card} (h : i < j) :
    primeEnergy (mode S i hi) < primeEnergy (mode S j hj) :=
  log_lt_log (Nat.cast_pos.mpr (mode S i hi).val.property.pos) (Nat.cast_lt.mpr (mode_lt h))

def gap (S : Finset Nat.Primes) (i : ℕ) (h : i+1 < S.card) :=
  primeEnergy (mode S (i+1) h) - primeEnergy (mode S i (by omega))

private theorem gap_ne_of_lt (S : Finset Nat.Primes) (i j : ℕ)
    (hi : i+1 < S.card) (hj : j+1 < S.card) (hlt : i < j) : gap S i hi ≠ gap S j hj := by
  let A : ShortPacket := ⟨(mode S i (by omega)).val, (mode S (i+1) hi).val,
    (mode S j (by omega)).val, (mode S (j+1) hj).val, mode_lt (Nat.lt_succ_self i),
    (S.orderIsoOfFin rfl).monotone (show (⟨i+1,hi⟩ : Fin S.card) ≤ ⟨j,by omega⟩ from hlt),
    mode_lt (Nat.lt_succ_self j)⟩
  exact A.gaps_ne

/-- Equality of two adjacent log gaps forces the same rank by unique prime factorization. -/
theorem gap_eq_iff (S : Finset Nat.Primes) (i j : ℕ) (hi : i+1 < S.card) (hj : j+1 < S.card) :
    gap S i hi = gap S j hj ↔ i = j := by
  constructor
  · intro h
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (gap_ne_of_lt S i j hi hj hij h).elim
    · exact hij
    · exact (gap_ne_of_lt S j i hj hi hij h.symm).elim
  · rintro rfl; rfl

variable (S : Finset Nat.Primes) (h : 3 ≤ S.card)

abbrev bottom := mode S 0 (by omega : 0 < S.card)
abbrev nextLow := mode S 1 (by omega : 1 < S.card)
abbrev nextHigh := mode S (S.card-2) (by omega : S.card-2 < S.card)
abbrev topMode := mode S (S.card-2+1) (by omega : S.card-2+1 < S.card)

theorem low_lt : primeEnergy (bottom S h) < primeEnergy (nextLow S h) := energy_inc (by omega)
theorem high_lt : primeEnergy (nextHigh S h) < primeEnergy (topMode S h) := energy_inc (by omega)

theorem above_nextLow (x : S) (hl : x ≠ bottom S h) (hq : x ≠ nextLow S h) :
    primeEnergy (nextLow S h) < primeEnergy x := by
  obtain ⟨k,rfl⟩ := (enumeration S).surjective x
  have h₀ : k.val ≠ 0 := fun he => hl (congrArg (enumeration S) (Fin.ext he))
  have h₁ : k.val ≠ 1 := fun he => hq (congrArg (enumeration S) (Fin.ext he))
  exact energy_inc (hi := by omega) (hj := k.isLt) (show 1 < k.val by omega)

theorem below_nextHigh (x : S) (hu : x ≠ topMode S h) (hr : x ≠ nextHigh S h) :
    primeEnergy x < primeEnergy (nextHigh S h) := by
  obtain ⟨k,rfl⟩ := (enumeration S).surjective x
  have h₀ : k.val ≠ S.card-2+1 := fun he => hu (congrArg (enumeration S) (Fin.ext he))
  have h₁ : k.val ≠ S.card-2 := fun he => hr (congrArg (enumeration S) (Fin.ext he))
  exact energy_inc (hi := k.isLt) (hj := by omega) (show k.val < S.card-2 by omega)

def edgeDifference := gap S 0 (by omega) - gap S (S.card-2) (by omega)

theorem edgeDifference_ne : edgeDifference S h ≠ 0 :=
  sub_ne_zero.mpr (gap_ne_of_lt S 0 (S.card-2) (by omega) (by omega) (by omega))

#print axioms gap_eq_iff
#print axioms edgeDifference_ne

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks
