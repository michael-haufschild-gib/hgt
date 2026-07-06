/-
The band-edge pairing is exactly the evenness of the event count.

The paired-flux interface requires a fixed-point-free involution on the odd events.  Such an
involution — the consecutive-crossing pairing, pairing event `2j` with event `2j+1` — exists on
`Fin n` precisely when `n` is even: any fixed-point-free involution forces an even cardinality,
and conversely an even cardinality carries the canonical pairing that swaps within each adjacent
pair.  So the entire remaining content of the paired-flux interface is a single parity fact: the
number of forced band-edge crossings is even.  This is the consecutive-crossing pairing of the
band-edge algebra, constructed rather than assumed.
-/
import GaloisForLFunctions.RHTower.BandEdgePairing

open Function

namespace RHTower

/-- Swap `0` and `1` in `Fin 2` has no fixed point. -/
private theorem swap01_ne_self (a : Fin 2) : Equiv.swap (0 : Fin 2) 1 a ≠ a := by
  fin_cases a <;> decide

/-- The consecutive-pairing map on `Fin (2m)`: swap within each adjacent pair, via the
identification `Fin (2m) ≃ Fin 2 × Fin m`. -/
noncomputable def pairMap (m : ℕ) (x : Fin (2 * m)) : Fin (2 * m) :=
  finProdFinEquiv (Equiv.swap (0 : Fin 2) 1 (finProdFinEquiv.symm x).1,
    (finProdFinEquiv.symm x).2)

theorem pairMap_involutive (m : ℕ) : Involutive (pairMap m) := by
  intro x
  simp only [pairMap, Equiv.symm_apply_apply, Equiv.swap_apply_self, Prod.mk.eta,
    Equiv.apply_symm_apply]

theorem pairMap_ne_self (m : ℕ) (x : Fin (2 * m)) : pairMap m x ≠ x := by
  intro h
  have h2 : finProdFinEquiv.symm (pairMap m x) = finProdFinEquiv.symm x := by rw [h]
  simp only [pairMap, Equiv.symm_apply_apply] at h2
  exact swap01_ne_self _ (congrArg Prod.fst h2)

/-- **The consecutive-crossing pairing.**  For every `m`, the even set `Fin (2m)` carries a
fixed-point-free pairing: the involution swapping within each adjacent pair. -/
noncomputable def consecutivePairing (m : ℕ) : BandEdgePairing (Fin (2 * m)) where
  pair := (pairMap_involutive m).toPerm
  pair_sq := by
    ext x
    simp only [pow_two, Equiv.Perm.mul_apply, Involutive.coe_toPerm, Equiv.Perm.one_apply]
    exact congrArg Fin.val (pairMap_involutive m x)
  no_fixed e := by
    simp only [Involutive.coe_toPerm]; exact pairMap_ne_self m e

/-- An even event count carries the band-edge pairing. -/
theorem nonempty_bandEdgePairing_of_even {n : ℕ} (hn : 2 ∣ n) :
    Nonempty (BandEdgePairing (Fin n)) := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨consecutivePairing m⟩

/-- **The pairing exists exactly when the event count is even.**  The band-edge pairing on
`Fin n` — the consecutive-crossing involution — is available precisely for an even `n`, so the
paired-flux interface's odd class is closed iff the number of forced crossings is even. -/
theorem nonempty_bandEdgePairing_iff_even {n : ℕ} :
    Nonempty (BandEdgePairing (Fin n)) ↔ 2 ∣ n := by
  constructor
  · rintro ⟨P⟩
    have h := fixedPointFreePairing_two_dvd_card (Event := Fin n) P
    simpa using h
  · exact nonempty_bandEdgePairing_of_even

end RHTower
