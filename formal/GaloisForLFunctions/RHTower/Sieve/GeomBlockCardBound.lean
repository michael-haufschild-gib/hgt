import GaloisForLFunctions.RHTower.Sieve.StepMassCard

/-!
# The size of a ladder step against its right endpoint

A step of a geometric ladder is contained in the integer interval between the floors of its two
endpoints, so its size never exceeds the right endpoint.  This is the crude counting bound the disc
and annulus estimates use, where the step scale is meant to cancel rather than to be saved on.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **A ladder step is no larger than its right endpoint.** -/
theorem card_geomBlock_le_endpoint {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    ((geomBlock P Q (1 + η) j).card : ℝ) ≤ (Q * (1 + η) ^ j) * (1 + η) := by
  classical
  have hsub := Finset.card_le_card (geomBlock_subset_Ioc (P := P) hQ hη j)
  have hIoc : ((Finset.Ioc ⌊Q * (1 + η) ^ j⌋₊ ⌊Q * (1 + η) ^ (j + 1)⌋₊).card : ℕ)
      = ⌊Q * (1 + η) ^ (j + 1)⌋₊ - ⌊Q * (1 + η) ^ j⌋₊ := Nat.card_Ioc _ _
  have hnat : (geomBlock P Q (1 + η) j).card ≤ ⌊Q * (1 + η) ^ (j + 1)⌋₊ := by
    rw [hIoc] at hsub; omega
  have hcast : ((geomBlock P Q (1 + η) j).card : ℝ)
      ≤ ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnat
  have hfl : ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ Q * (1 + η) ^ (j + 1) :=
    Nat.floor_le (by positivity)
  have hval : Q * (1 + η) ^ (j + 1) = (Q * (1 + η) ^ j) * (1 + η) := by rw [pow_succ]; ring
  linarith [hcast, hfl, hval.le, hval.ge]

end

end RHTower.Sieve
