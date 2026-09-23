import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedContinuous

/-!
# Polynomial normal forms for omitted-head continuous moments

Writing `A = log(M/q)`, `B = log(M/r)`, and `u = log(M/max(q,r))` removes every
pair-dependent endpoint from the continuous omitted-head kernels.  The resulting finite Selberg
forms are the arithmetic objects whose normalized limits evaluate the omitted detector energy.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- Polynomial boundary form for the omitted-head base moment. -/
def barbanVehovOmittedLongBasePolynomialMain (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let u := Real.log ((M : ℝ) / ((max p.1 p.2 : ℕ) : ℝ))
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 /
      (Nat.lcm p.1 p.2 : ℝ) * u

/-- Polynomial boundary form for the omitted-head base/differentiated cross moment. -/
def barbanVehovOmittedLongCrossPolynomialMain (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := Real.log ((M : ℝ) / ((max p.1 p.2 : ℕ) : ℝ))
    (-1 : ℝ) * (barbanVehovWeight M p.1 * barbanVehovWeight M p.2 /
      (Nat.lcm p.1 p.2 : ℝ)) *
        (u * (ell + B) - u ^ (2 : ℕ) / 2)

/-- Polynomial boundary form for the omitted-head differentiated square moment. -/
def barbanVehovOmittedLongDerivativePolynomialMain (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let A := Real.log ((M : ℝ) / (p.1 : ℝ))
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := Real.log ((M : ℝ) / ((max p.1 p.2 : ℕ) : ℝ))
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 /
      (Nat.lcm p.1 p.2 : ℝ) *
        (u * (ell + A) * (ell + B) -
          u ^ (2 : ℕ) / 2 * (2 * ell + A + B) + u ^ (3 : ℕ) / 3)

/-- The omitted base continuous form has no dependence on the detector scale after its endpoint
is reduced to logarithmic boundary coordinates. -/
theorem barbanVehovOmittedLongBaseContinuous_eq_polynomialMain
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M) :
    barbanVehovOmittedLongBaseContinuous L M =
      barbanVehovOmittedLongBasePolynomialMain M := by
  rw [barbanVehovOmittedLongBaseContinuous,
    barbanVehovOmittedLongBasePolynomialMain]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  rw [barbanVehovLongHarmonicKernelContinuous_maxEndpoint_eq
    hL hM hp1.1 hp2.1]
  dsimp only
  ring

/-- The omitted cross continuous form is its boundary polynomial at `ell = log L`. -/
theorem barbanVehovOmittedLongCrossContinuous_eq_polynomialMain
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M) :
    barbanVehovOmittedLongCrossContinuous L M =
      barbanVehovOmittedLongCrossPolynomialMain (Real.log L) M := by
  rw [barbanVehovOmittedLongCrossContinuous,
    barbanVehovOmittedLongCrossPolynomialMain]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hm : 0 < max p.1 p.2 := lt_max_iff.mpr (Or.inl hp1.1)
  rw [barbanVehovLongFirstLogKernelContinuous_maxEndpoint_eq
    hL hM hp1.1 hp2.1]
  rw [log_nat_mul_div hL hm hp2.1,
    log_nat_div hM hp2.1, log_nat_div hM hm]
  dsimp only
  ring

/-- The omitted derivative-square continuous form is its boundary polynomial at `ell = log L`. -/
theorem barbanVehovOmittedLongDerivativeContinuous_eq_polynomialMain
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M) :
    barbanVehovOmittedLongDerivativeContinuous L M =
      barbanVehovOmittedLongDerivativePolynomialMain (Real.log L) M := by
  rw [barbanVehovOmittedLongDerivativeContinuous,
    barbanVehovOmittedLongDerivativePolynomialMain]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hm : 0 < max p.1 p.2 := lt_max_iff.mpr (Or.inl hp1.1)
  rw [barbanVehovLongSecondLogKernelContinuous_maxEndpoint_eq
    hL hM hp1.1 hp2.1]
  rw [log_nat_mul_div hL hm hp1.1, log_nat_mul_div hL hm hp2.1,
    log_nat_div hM hp1.1, log_nat_div hM hp2.1,
    log_nat_div hM hm]
  dsimp only
  ring

end

end RHTower.Sieve
