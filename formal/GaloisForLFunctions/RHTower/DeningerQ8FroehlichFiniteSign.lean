import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSource
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Fröhlich's finite sign certificate for the actual Q8 witness

For the biquadratic field `ℚ(√5, √41)`, Fröhlich's Theorem 6 uses the
quadratic factor `(41 / 5)` and the biquadratic-residue factor `[5 / 41]`.
The other two biquadratic-residue factors are `[41 / 5] = 1` and
`[1 / 205] = 1`.

This file proves the complete finite residue calculation:

* `(41 / 5) = 1`;
* `5 ^ (10 : ℕ) = -1` in `ZMod 41`, hence `[5 / 41] = -1`;
* their product is `-1`.

The resulting value is deliberately named `deningerQ8FroehlichFiniteSign`,
not an Artin root number.  Identifying it with the global Artin epsilon
factor is the separate Fröhlich bridge.
-/

namespace RHTower

noncomputable section

local instance deningerQ8FroehlichPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

/-- Fröhlich's quadratic factor `α_K = (41 / 5)` for
`K = ℚ(√5, √41)`. -/
def deningerQ8FroehlichAlpha : ℤ := legendreSym 5 41

/-- Choice-independent value of the only nontrivial biquadratic-residue
factor in Fröhlich's `β_K` for `K = ℚ(√5, √41)`.

The exponent `10 = (41 - 1) / 4` is the quartic Euler exponent.  The
following theorem proves that its residue is exactly `-1`, so this branch
does not hide a choice of primitive quartic character. -/
def deningerQ8FroehlichBeta : ℤ :=
  if (((5 : ℤ) : ZMod 41) ^ (10 : ℕ)) = 1 then 1 else -1

/-- Finite residue side of Fröhlich's root-number formula for the actual
SST quaternion field. -/
def deningerQ8FroehlichFiniteSign : ℤ :=
  deningerQ8FroehlichAlpha * deningerQ8FroehlichBeta

/-- Exact quadratic-residue calculation `(41 / 5) = 1`. -/
theorem deningerQ8FroehlichAlpha_eq_one : deningerQ8FroehlichAlpha = 1 := by
  rw [deningerQ8FroehlichAlpha, legendreSym.eq_one_iff (p := 5)]
  · refine ⟨1, ?_⟩
    change (1 : ZMod 5) * 1 = (41 : ℕ)
    rw [one_mul]
    change ((1 : ℤ) : ZMod 5) = ((41 : ℤ) : ZMod 5)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  · intro h
    change ((41 : ℤ) : ZMod 5) = ((0 : ℤ) : ZMod 5) at h
    rw [ZMod.intCast_eq_intCast_iff'] at h
    norm_num at h

/-- Exact quartic-residue calculation `5^(10 : ℕ) = -1 (mod 41)`. -/
theorem deningerQ8_five_pow_ten_eq_neg_one_mod_fortyOne :
    ((5 : ZMod 41) ^ (10 : ℕ)) = -1 := by
  change ((9765625 : ℕ) : ZMod 41) = -1
  have hneg : (-1 : ZMod 41) = (40 : ℕ) := by
    change ((-1 : ℤ) : ZMod 41) = ((40 : ℤ) : ZMod 41)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  rw [hneg, ZMod.natCast_eq_natCast_iff']

/-- Fröhlich's biquadratic-residue factor is `-1`. -/
theorem deningerQ8FroehlichBeta_eq_neg_one : deningerQ8FroehlichBeta = -1 := by
  rw [deningerQ8FroehlichBeta, if_neg]
  intro h
  have hq : (((5 : ℤ) : ZMod 41) ^ (10 : ℕ)) = -1 := by
    simpa using deningerQ8_five_pow_ten_eq_neg_one_mod_fortyOne
  rw [hq] at h
  have hne : (-1 : ZMod 41) ≠ 1 := by
    change ((-1 : ℤ) : ZMod 41) ≠ ((1 : ℤ) : ZMod 41)
    intro heq
    rw [ZMod.intCast_eq_intCast_iff'] at heq
    norm_num at heq
  exact hne h

/-- The complete finite residue invariant in Fröhlich's Theorem 6 is `-1`
for `ℚ(√5, √41)`. -/
theorem deningerQ8FroehlichFiniteSign_eq_neg_one :
    deningerQ8FroehlichFiniteSign = -1 := by
  rw [deningerQ8FroehlichFiniteSign, deningerQ8FroehlichAlpha_eq_one,
    deningerQ8FroehlichBeta_eq_neg_one, one_mul]

/-- Single certificate exposing both source factors and their product. -/
theorem deningerQ8FroehlichFiveFortyOneResidueCertificate :
    deningerQ8FroehlichAlpha = 1 ∧
      ((5 : ZMod 41) ^ (10 : ℕ)) = -1 ∧
      deningerQ8FroehlichFiniteSign = -1 :=
  ⟨deningerQ8FroehlichAlpha_eq_one,
    deningerQ8_five_pow_ten_eq_neg_one_mod_fortyOne,
    deningerQ8FroehlichFiniteSign_eq_neg_one⟩

end

end RHTower
