import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineResidues
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ResidueCovariance
import Mathlib.Data.Nat.Prime.Basic

/-!
# Affine prime incidences as centered residues

Invertible multipliers identify both affine offset incidences with their
chosen residue classes. Every nonzero offset below the prime is a unit.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BezoutValuationIncidence
open Finset
open GaloisForLFunctions.BezoutValuationIncidence

/-- Unit positive affine incidences are the exact chosen centered residue. -/
theorem unit_positive_incidence {p k h : ℕ} (hpk : p.Coprime k) (hh : h ≤ p) (n : ℕ) :
    ((if p ∣ k * n + h then (1 : ℝ) else 0) - 1 / p) =
      centeredResidue p (multiplierResidue p k (p - h)) n := by
  simp only [centeredResidue, residueIndicator, dvd_positive_shift_iff hh,
    (multiplierResidue_spec (b := p - h) hpk).2 n]

/-- Genuine negative offsets select the inverse-multiplier residue of the offset itself. -/
theorem unit_negative_incidence {p k h n : ℕ} (hpk : p.Coprime k) (hh : h ≤ k * n) :
    ((if p ∣ k * n - h then (1 : ℝ) else 0) - 1 / p) =
      centeredResidue p (multiplierResidue p k h) n := by
  simp only [centeredResidue, residueIndicator, dvd_negative_shift_iff hh,
    (multiplierResidue_spec (b := h) hpk).2 n]

/-- Positive offsets below a prime are units modulo that prime. -/
theorem prime_positive_offset_unit {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    p.Coprime (p - h) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hpos : 0 < p - h := Nat.sub_pos_of_lt hhp
  have hlt : p - h < p := Nat.sub_lt hp.pos hh
  exact (not_le.mpr hlt) (Nat.le_of_dvd hpos hd)

/-- Negative offset targets below a prime are units modulo that prime. -/
theorem prime_negative_offset_unit {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    p.Coprime h := by
  exact hp.coprime_iff_not_dvd.mpr (fun hd => (not_le.mpr hhp) (Nat.le_of_dvd hh hd))

#print axioms unit_positive_incidence
#print axioms unit_negative_incidence
#print axioms prime_positive_offset_unit

end GaloisForLFunctions.BezoutValuationIncidence
