import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionCounts

/-!
# Residues of affine prime-incidence maps

CRT constructs the inverse-multiplier residue without choosing a residue
field inverse. Two affine maps select the same residue precisely when their
cross-products agree. Both signs of the integer offset are retained.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence


/-- A coprime multiplier selects exactly one residue class. -/
theorem exists_multiplier_residue {p k b : ℕ} (hpk : p.Coprime k) :
    ∃ r : ℕ, k * r ≡ b [MOD p] ∧
      ∀ n : ℕ, k * n ≡ b [MOD p] ↔ n ≡ r [MOD p] := by
  let v := Nat.chineseRemainder hpk.symm 0 b
  have hkv : k ∣ (v : ℕ) := Nat.modEq_zero_iff_dvd.mp v.property.1
  have hkr : k * ((v : ℕ) / k) ≡ b [MOD p] := by
    rw [Nat.mul_div_cancel' hkv]
    exact v.property.2
  refine ⟨(v : ℕ) / k, hkr, fun n => ?_⟩
  constructor
  · intro hn
    exact Nat.ModEq.cancel_left_of_coprime hpk (hn.trans hkr.symm)
  · intro hn
    exact (hn.mul_left k).trans hkr

/-- A fixed representative of the inverse-multiplier residue, zero for nonunits. -/
def multiplierResidue (p k b : ℕ) : ℕ :=
  if hpk : p.Coprime k then Classical.choose (exists_multiplier_residue (b := b) hpk) else 0

theorem multiplierResidue_spec {p k b : ℕ} (hpk : p.Coprime k) :
    k * multiplierResidue p k b ≡ b [MOD p] ∧
      ∀ n : ℕ, k * n ≡ b [MOD p] ↔ n ≡ multiplierResidue p k b [MOD p] := by
  rw [multiplierResidue, dif_pos hpk]
  exact Classical.choose_spec (exists_multiplier_residue (b := b) hpk)

/-- Two inverse-multiplier residues agree exactly when their cross-products agree. -/
theorem multiplier_residues_equal_iff {p k l b c r s : ℕ}
    (hpk : p.Coprime k) (hpl : p.Coprime l)
    (hr : k * r ≡ b [MOD p]) (hs : l * s ≡ c [MOD p]) :
    r ≡ s [MOD p] ↔ l * b ≡ k * c [MOD p] := by
  have hleft : (k * l) * r ≡ l * b [MOD p] := by
    rw [show (k * l) * r = l * (k * r) by ring]
    exact hr.mul_left l
  have hright : (k * l) * s ≡ k * c [MOD p] := by
    simpa only [mul_assoc] using hs.mul_left k
  constructor
  · intro h
    exact hleft.symm.trans ((h.mul_left (k * l)).trans hright)
  · intro h
    exact Nat.ModEq.cancel_left_of_coprime (hpk.mul_right hpl)
      (hleft.trans (h.trans hright.symm))

/-- The chosen representatives preserve the exact affine collision condition. -/
theorem multiplierResidue_collision_iff {p k l b c : ℕ}
    (hpk : p.Coprime k) (hpl : p.Coprime l) :
    multiplierResidue p k b ≡ multiplierResidue p l c [MOD p] ↔ l * b ≡ k * c [MOD p] :=
  multiplier_residues_equal_iff hpk hpl (multiplierResidue_spec hpk).1 (multiplierResidue_spec hpl).1

theorem dvd_positive_shift_iff {p k n h : ℕ} (hh : h ≤ p) :
    p ∣ k * n + h ↔ k * n ≡ p - h [MOD p] := by
  have hc : (p - h) + h ≡ 0 [MOD p] := by
    rw [Nat.sub_add_cancel hh]
    exact Nat.modulus_modEq_zero
  rw [← Nat.modEq_zero_iff_dvd]
  constructor
  · intro hn
    exact Nat.ModEq.add_right_cancel' h (hn.trans hc.symm)
  · intro hn
    exact (hn.add_right h).trans hc

theorem dvd_negative_shift_iff {p k n h : ℕ} (hh : h ≤ k * n) :
    p ∣ k * n - h ↔ k * n ≡ h [MOD p] := by
  rw [← Nat.modEq_iff_dvd' hh, Nat.ModEq.comm]

#print axioms exists_multiplier_residue
#print axioms multiplier_residues_equal_iff
#print axioms multiplierResidue_collision_iff

end GaloisForLFunctions.BezoutValuationIncidence
