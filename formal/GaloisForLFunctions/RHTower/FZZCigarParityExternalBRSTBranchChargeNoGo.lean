import GaloisForLFunctions.RHTower.FZZCigarParityMarkedOPEChargeIncidenceNoGo

/-!
# FZZ external-BRST branch-charge classification

The surviving local FZZ-P producer after the marked same-winding no-go is the branch cut of the
fractional-winding area insertion against a legitimate external vertex.  This file classifies that
cut directly from Halder--Jafferis' cigar formulas, arXiv:2402.00932v3, (3.16)--(3.19), (3.29),
and the analogous explicit BTZ OPE in arXiv:2310.02313, (4.26)--(4.27).

For the quantized cigar momenta

`m = (p-kν)/2`, `mbar = -(p+kν)/2`,

the first replica derivatives of the left/right OPE exponents are

`L⁺_L = -j/q+m`, `L⁺_R = -j/q+mbar`,
`L⁻_L = -j/q-m`, `L⁻_R = -j/q-mbar`,

where `q=1-2/k`.  Their logarithmic monodromy charges are therefore exactly `p` and `-p`.
Thus branch incidence is equivalent to `p ≠ 0` and is independent of the radial label `j`, level
`k`, and winding `ν`.  Even the pair of both signed branch charges cannot select zero physical
radial momentum.  This kills the chain

`external-BRST branch incidence → torus area Ward law → divisor-mode passivity
  → Mellin completeness → RH`

when its first arrow uses only branch existence or logarithmic discontinuity.

The positive survivor is sharp.  The charge-even mean of the two log-modulus coefficients is
`-2j/q`, while their odd half-difference is `kν`; hence the modulus channel reconstructs the radial
label exactly for physical `k>2`.  A live external-BRST route must use that modulus/on-shell data,
the full branch kernel, support motion, or higher replica order.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Quantized left cigar momentum `m=(p-kν)/2`. -/
def fzzCigarExternalVertexMomentum (k : ℝ) (p ν : ℤ) : ℂ :=
  (((p : ℝ) - k * (ν : ℝ)) / 2 : ℝ)

/-- Quantized right cigar momentum `mbar=-(p+kν)/2`. -/
def fzzCigarExternalVertexBarMomentum (k : ℝ) (p ν : ℤ) : ℂ :=
  (-(((p : ℝ) + k * (ν : ℝ)) / 2) : ℝ)

/-- Cigar replica radial denominator `q=1-2/k`. -/
def fzzCigarReplicaRadialDenominator (k : ℝ) : ℂ :=
  ((1 - 2 / k : ℝ) : ℂ)

/-- Marked holomorphic OPE coefficient for `W⁺`. -/
def fzzCigarExternalBRSTPlusHolLogCoefficient
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  -j / fzzCigarReplicaRadialDenominator k +
    fzzCigarExternalVertexMomentum k p ν

/-- Marked antiholomorphic OPE coefficient for `W⁺`. -/
def fzzCigarExternalBRSTPlusAntiLogCoefficient
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  -j / fzzCigarReplicaRadialDenominator k +
    fzzCigarExternalVertexBarMomentum k p ν

/-- Marked holomorphic OPE coefficient for `W⁻`. -/
def fzzCigarExternalBRSTMinusHolLogCoefficient
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  -j / fzzCigarReplicaRadialDenominator k -
    fzzCigarExternalVertexMomentum k p ν

/-- Marked antiholomorphic OPE coefficient for `W⁻`. -/
def fzzCigarExternalBRSTMinusAntiLogCoefficient
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  -j / fzzCigarReplicaRadialDenominator k -
    fzzCigarExternalVertexBarMomentum k p ν

/-- Signed logarithmic monodromy charge of the marked `W⁺` OPE. -/
def fzzCigarExternalBRSTPlusBranchCharge
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  fzzCigarExternalBRSTPlusHolLogCoefficient k j p ν -
    fzzCigarExternalBRSTPlusAntiLogCoefficient k j p ν

/-- Signed logarithmic monodromy charge of the marked `W⁻` OPE. -/
def fzzCigarExternalBRSTMinusBranchCharge
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  fzzCigarExternalBRSTMinusHolLogCoefficient k j p ν -
    fzzCigarExternalBRSTMinusAntiLogCoefficient k j p ν

/-- The marked `W⁺` branch charge is exactly the integral target momentum. -/
theorem fzzCigarExternalBRSTPlusBranchCharge_eq_momentum
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    fzzCigarExternalBRSTPlusBranchCharge k j p ν = (p : ℂ) := by
  rw [fzzCigarExternalBRSTPlusBranchCharge,
    fzzCigarExternalBRSTPlusHolLogCoefficient,
    fzzCigarExternalBRSTPlusAntiLogCoefficient,
    fzzCigarExternalVertexMomentum, fzzCigarExternalVertexBarMomentum]
  push_cast
  ring

/-- The marked `W⁻` branch charge is the opposite integral target momentum. -/
theorem fzzCigarExternalBRSTMinusBranchCharge_eq_neg_momentum
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    fzzCigarExternalBRSTMinusBranchCharge k j p ν = -(p : ℂ) := by
  rw [fzzCigarExternalBRSTMinusBranchCharge,
    fzzCigarExternalBRSTMinusHolLogCoefficient,
    fzzCigarExternalBRSTMinusAntiLogCoefficient,
    fzzCigarExternalVertexMomentum, fzzCigarExternalVertexBarMomentum]
  push_cast
  ring

/-- Branch incidence of either marked winding sign. -/
def FZZCigarExternalBRSTMarkedBranchIncident
    (k : ℝ) (j : ℂ) (p ν : ℤ) : Prop :=
  fzzCigarExternalBRSTPlusBranchCharge k j p ν ≠ 0 ∨
    fzzCigarExternalBRSTMinusBranchCharge k j p ν ≠ 0

/-- **External-BRST branch-incidence classification.**  The marked area OPE has logarithmic
monodromy exactly when external target momentum is nonzero.  Radial label, level, and winding
drop out. -/
theorem fzzCigarExternalBRSTMarkedBranchIncident_iff_momentum_ne_zero
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    FZZCigarExternalBRSTMarkedBranchIncident k j p ν ↔ p ≠ 0 := by
  rw [FZZCigarExternalBRSTMarkedBranchIncident,
    fzzCigarExternalBRSTPlusBranchCharge_eq_momentum,
    fzzCigarExternalBRSTMinusBranchCharge_eq_neg_momentum]
  constructor
  · intro h hp
    subst p
    simp at h
  · intro hp
    left
    exact_mod_cast hp

/-- Charge-symmetric logarithmic modulus coefficient for `W⁺`. -/
def fzzCigarExternalBRSTPlusLogModulus
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  fzzCigarExternalBRSTPlusHolLogCoefficient k j p ν +
    fzzCigarExternalBRSTPlusAntiLogCoefficient k j p ν

/-- Charge-symmetric logarithmic modulus coefficient for `W⁻`. -/
def fzzCigarExternalBRSTMinusLogModulus
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  fzzCigarExternalBRSTMinusHolLogCoefficient k j p ν +
    fzzCigarExternalBRSTMinusAntiLogCoefficient k j p ν

theorem fzzCigarExternalBRSTPlusLogModulus_eq
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    fzzCigarExternalBRSTPlusLogModulus k j p ν =
      -2 * j / fzzCigarReplicaRadialDenominator k -
        ((k * (ν : ℝ) : ℝ) : ℂ) := by
  rw [fzzCigarExternalBRSTPlusLogModulus,
    fzzCigarExternalBRSTPlusHolLogCoefficient,
    fzzCigarExternalBRSTPlusAntiLogCoefficient,
    fzzCigarExternalVertexMomentum, fzzCigarExternalVertexBarMomentum,
    fzzCigarReplicaRadialDenominator]
  push_cast
  ring

theorem fzzCigarExternalBRSTMinusLogModulus_eq
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    fzzCigarExternalBRSTMinusLogModulus k j p ν =
      -2 * j / fzzCigarReplicaRadialDenominator k +
        ((k * (ν : ℝ) : ℝ) : ℂ) := by
  rw [fzzCigarExternalBRSTMinusLogModulus,
    fzzCigarExternalBRSTMinusHolLogCoefficient,
    fzzCigarExternalBRSTMinusAntiLogCoefficient,
    fzzCigarExternalVertexMomentum, fzzCigarExternalVertexBarMomentum,
    fzzCigarReplicaRadialDenominator]
  push_cast
  ring

/-- Charge-even mean of both log-modulus channels. -/
def fzzCigarExternalBRSTEvenLogModulusMean
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  (fzzCigarExternalBRSTPlusLogModulus k j p ν +
    fzzCigarExternalBRSTMinusLogModulus k j p ν) / 2

/-- Charge-odd half-difference of both log-modulus channels. -/
def fzzCigarExternalBRSTOddLogModulusHalfDifference
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  (fzzCigarExternalBRSTMinusLogModulus k j p ν -
    fzzCigarExternalBRSTPlusLogModulus k j p ν) / 2

/-- **Positive survivor.**  The even modulus channel retains precisely the radial label. -/
theorem fzzCigarExternalBRSTEvenLogModulusMean_eq
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    fzzCigarExternalBRSTEvenLogModulusMean k j p ν =
      -2 * j / fzzCigarReplicaRadialDenominator k := by
  rw [fzzCigarExternalBRSTEvenLogModulusMean,
    fzzCigarExternalBRSTPlusLogModulus_eq,
    fzzCigarExternalBRSTMinusLogModulus_eq]
  ring

/-- The odd modulus channel retains precisely level times winding. -/
theorem fzzCigarExternalBRSTOddLogModulusHalfDifference_eq
    (k : ℝ) (j : ℂ) (p ν : ℤ) :
    fzzCigarExternalBRSTOddLogModulusHalfDifference k j p ν =
      ((k * (ν : ℝ) : ℝ) : ℂ) := by
  rw [fzzCigarExternalBRSTOddLogModulusHalfDifference,
    fzzCigarExternalBRSTPlusLogModulus_eq,
    fzzCigarExternalBRSTMinusLogModulus_eq]
  ring

/-- At every physical level, the even modulus channel reconstructs the external radial label. -/
theorem fzzCigarExternalBRSTEvenLogModulusMean_reconstructs_radialLabel
    {k : ℝ} (hk : 2 < k) (j : ℂ) (p ν : ℤ) :
    -(fzzCigarReplicaRadialDenominator k / 2) *
        fzzCigarExternalBRSTEvenLogModulusMean k j p ν = j := by
  rw [fzzCigarExternalBRSTEvenLogModulusMean_eq]
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans (by norm_num) hk)
  have hqR : 1 - 2 / k ≠ 0 := by
    intro h
    field_simp [hk0] at h
    linarith
  have hq : fzzCigarReplicaRadialDenominator k ≠ 0 := by
    rw [fzzCigarReplicaRadialDenominator]
    exact_mod_cast hqR
  field_simp [hq]

/-- Both signed branch charges evaluated on the physical continuum `j=-1/2+iP`. -/
def fzzCigarExternalBRSTPhysicalBranchChargePair
    (k radialMomentum : ℝ) (p ν : ℤ) : ℂ × ℂ :=
  let j : ℂ := -(1 : ℂ) / 2 + (radialMomentum : ℂ) * Complex.I
  (fzzCigarExternalBRSTPlusBranchCharge k j p ν,
    fzzCigarExternalBRSTMinusBranchCharge k j p ν)

theorem fzzCigarExternalBRSTPhysicalBranchChargePair_eq
    (k radialMomentum : ℝ) (p ν : ℤ) :
    fzzCigarExternalBRSTPhysicalBranchChargePair k radialMomentum p ν =
      ((p : ℂ), -(p : ℂ)) := by
  rw [fzzCigarExternalBRSTPhysicalBranchChargePair]
  rw [fzzCigarExternalBRSTPlusBranchCharge_eq_momentum,
    fzzCigarExternalBRSTMinusBranchCharge_eq_neg_momentum]

/-- **External-BRST branch-charge route kill.**  No physical cigar level, quantized external
charges, or predicate of the complete signed branch-charge pair selects zero radial momentum. -/
theorem not_exists_physical_fzzCigarExternalBRSTBranchCharge_radialSelector :
    ¬ ∃ (k : ℝ) (p ν : ℤ) (P : ℂ × ℂ → Prop), 2 < k ∧
      ∀ radialMomentum : ℝ,
        P (fzzCigarExternalBRSTPhysicalBranchChargePair
          k radialMomentum p ν) ↔ radialMomentum = 0 := by
  rintro ⟨k, p, ν, P, hk, h⟩
  have h0 : P (fzzCigarExternalBRSTPhysicalBranchChargePair k 0 p ν) :=
    (h 0).mpr rfl
  have h1 : P (fzzCigarExternalBRSTPhysicalBranchChargePair k 1 p ν) := by
    rw [fzzCigarExternalBRSTPhysicalBranchChargePair_eq]
    rw [fzzCigarExternalBRSTPhysicalBranchChargePair_eq] at h0
    exact h0
  have := (h 1).mp h1
  norm_num at this

end

end GaloisForLFunctions.RHTower
