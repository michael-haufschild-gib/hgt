import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationInversionLawOfTheSource
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CompensationNeedsItsCrossTerms

/-!
# The self-improving energy identity

The damped unit dilation `D^{ζ_ε}` differs from the prime dilation in one decisive respect: its
weight at `j = 1` is `1`, not `Λ(1) = 0`.  So its diagonal *is* the critical energy, and the
inversion law of the source turns that diagonal into an explicit linear pairing:

`E_T(ε) = ⟪A_ε, ρ_ε⟫_T − ⟪A_ε, D^{ζ_ε,≥2} A_ε⟫_T`,
`ρ_ε(n) = n − m₀(ε) Φ_ε(n)`  (`dampedMobiusEnergy_eq_pairing_sub`),

where `ρ_ε` is the explicit defect of the inversion law and `D^{ζ_ε,≥2}` is the dilation with the
unit level removed.  Both terms on the right are pairings of the source against something *other*
than its own square.

This changes the shape of what suffices.  No transport, no interval and no horizon-free budget are
needed: if at one damping the two pairings are each at most `κ √E_T + κ'`, the identity closes on
itself and the energy is bounded by `(κ + √(κ² + 2κ'))²`
(`admits_of_sublinear_pairings`), so that damping is admitted and cofinal versions give the Riemann
hypothesis (`riemannHypothesis_of_cofinal_sublinear_pairings`).

The demand is therefore *sublinear cancellation* of two explicit sums at a single damping, in place
of a budget along a damping interval.  The first is the source against a smooth explicit weight,
the second its anti-correlation with its own proper dilations — and a term-by-term majorant of the
second meets the divergent `Σ_j j^{−ε−1/2}`, which is precisely why a signed statement is required.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The identity -/

/-- The explicit defect of the inversion law: `ρ_ε(n) = n − m₀(ε) Φ_ε(n)`. -/
def inversionDefect (ε : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) - (pmPowerDampedDivisorDensity ε).re * dampedUnitFloorSum ε n

/-- The damped unit dilation with the unit level removed. -/
def offDiagonalUnitDilation (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 n, (j : ℝ) ^ (-ε) * pmPowerDampedCenteredDivisorPrefix ε (n / j)

/-- The unit level of the damped unit dilation is the source itself. -/
theorem sum_rpow_mul_centeredPrefix_split (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) * pmPowerDampedCenteredDivisorPrefix ε (n / j)) =
      pmPowerDampedCenteredDivisorPrefix ε n + offDiagonalUnitDilation ε n := by
  have hins : (Icc 1 n : Finset ℕ) = insert 1 (Icc 2 n) := by
    ext j
    rw [mem_Icc, Finset.mem_insert, mem_Icc]
    omega
  have hnot : (1 : ℕ) ∉ (Icc 2 n : Finset ℕ) := by
    rw [mem_Icc]
    omega
  rw [hins, Finset.sum_insert hnot, offDiagonalUnitDilation]
  norm_num

/-- **The energy is an explicit linear pairing minus the off-diagonal dilation form.**  The unit
level of the positive dilation kernel contributes exactly the energy, and the inversion law
replaces the whole dilation by its explicit defect. -/
theorem dampedMobiusEnergy_eq_pairing_sub (ε : ℝ) (T : ℕ) :
    dampedMobiusEnergy ε T =
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) -
        pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε) := by
  unfold dampedMobiusEnergy pmPowerDampedDivisorDiscreteEnergy pronicPairing
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hsplit := sum_rpow_mul_centeredPrefix_split ε hn1
  rw [sum_rpow_mul_centeredPrefix_eq ε n] at hsplit
  have hdef : pmPowerDampedCenteredDivisorPrefix ε n =
      inversionDefect ε n - offDiagonalUnitDilation ε n := by
    rw [inversionDefect]
    linarith
  rw [sq, hdef]
  ring

/-! ## §2. Sublinear pairings close the identity -/

/-- **Admission from two sublinear pairings at one damping.**  No transport and no interval: the
identity closes on itself. -/
theorem admits_of_sublinear_pairings {ε κ κ' : ℝ} (_hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (h1 : ∀ T : ℕ, pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) ≤
      κ * Real.sqrt (dampedMobiusEnergy ε T) + κ')
    (h2 : ∀ T : ℕ,
      -(pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε)) ≤
        κ * Real.sqrt (dampedMobiusEnergy ε T) + κ') :
    Admits dampedMobiusEnergy ε := by
  refine ⟨(κ + Real.sqrt (κ ^ 2 + 2 * κ')) ^ 2, fun T => ?_⟩
  have hE0 := dampedMobiusEnergy_nonneg ε T
  have hx0 : 0 ≤ Real.sqrt (dampedMobiusEnergy ε T) := Real.sqrt_nonneg _
  have hxx : Real.sqrt (dampedMobiusEnergy ε T) ^ 2 = dampedMobiusEnergy ε T :=
    Real.sq_sqrt hE0
  have hle : dampedMobiusEnergy ε T ≤
      2 * κ * Real.sqrt (dampedMobiusEnergy ε T) + 2 * κ' := by
    have hid := dampedMobiusEnergy_eq_pairing_sub ε T
    linarith [h1 T, h2 T]
  have hroot : 0 ≤ κ ^ 2 + 2 * κ' := by positivity
  have hsq : Real.sqrt (κ ^ 2 + 2 * κ') ^ 2 = κ ^ 2 + 2 * κ' := Real.sq_sqrt hroot
  have hsqrt0 : 0 ≤ Real.sqrt (κ ^ 2 + 2 * κ') := Real.sqrt_nonneg _
  have hbound : Real.sqrt (dampedMobiusEnergy ε T) ≤ κ + Real.sqrt (κ ^ 2 + 2 * κ') := by
    nlinarith [hxx, hsq, hx0, hsqrt0]
  calc dampedMobiusEnergy ε T = Real.sqrt (dampedMobiusEnergy ε T) ^ 2 := hxx.symm
    _ ≤ (κ + Real.sqrt (κ ^ 2 + 2 * κ')) ^ 2 :=
        pow_le_pow_left₀ hx0 hbound 2

/-- **The sublinear-pairing criterion for the Riemann hypothesis.**  Sublinear cancellation of the
two explicit pairings, at dampings accumulating at zero, gives RH. -/
theorem riemannHypothesis_of_cofinal_sublinear_pairings
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε κ κ' : ℝ, 0 < ε ∧ ε < δ ∧ 0 ≤ κ ∧ 0 ≤ κ' ∧
      (∀ T : ℕ, pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) ≤
          κ * Real.sqrt (dampedMobiusEnergy ε T) + κ') ∧
        (∀ T : ℕ,
          -(pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
            (offDiagonalUnitDilation ε)) ≤
            κ * Real.sqrt (dampedMobiusEnergy ε T) + κ')) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  obtain ⟨ε, κ, κ', hε0, hεδ, hκ, hκ', h1, h2⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ, admits_of_sublinear_pairings hκ hκ' h1 h2⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
