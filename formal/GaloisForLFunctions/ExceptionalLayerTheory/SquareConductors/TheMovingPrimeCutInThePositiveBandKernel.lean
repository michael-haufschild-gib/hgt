import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheLastTwoQuotientCellsOfTheSpline
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMassAtAQuadraticProductDivider

/-!
# The moving prime cutoff in the integrated positive band

The kernel obtained by integrating conductors on the last quadratic prime
band is linear below its first knot. Its entire small-prime contribution
therefore uses the ordinary first moment with the same integer endpoint.
-/

noncomputable section
open Finset
open GaloisForLFunctions.CountingHolography.Sections GaloisForLFunctions.ArithmeticWeightTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The quadratic band density as a function of the first-prime spacing. -/
def lastPrimeBandProfile (h : ℝ) : ℝ :=
  (1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1*dyadicSpline (2*h)

/-- Kernel of the prime scale after integrating through the terminal conductor. -/
def integratedPrimeBandKernel (y : ℝ) : ℝ :=
  if 0 ≤ y ∧ y ≤ upperFirstPrimeBandRight then
    y/2*(∫ h in max upperFirstPrimeBandLeft y..upperFirstPrimeBandRight, lastPrimeBandProfile h/h^2)
  else 0

/-- Slope of the kernel before its first knot. -/
def integratedPrimeBandSlope : ℝ :=
  (∫ h in upperFirstPrimeBandLeft..upperFirstPrimeBandRight, lastPrimeBandProfile h/h^2)/2

private theorem kernel_below_one {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1) :
    integratedPrimeBandKernel y = integratedPrimeBandSlope*y := by
  have he := Real.one_le_exp (show (0:ℝ) ≤ 8 by norm_num)
  have hleft : 1 ≤ upperFirstPrimeBandLeft := by unfold upperFirstPrimeBandLeft; linarith only [he]
  have hright : 1 ≤ upperFirstPrimeBandRight := by unfold upperFirstPrimeBandRight; linarith only [he]
  rw [integratedPrimeBandKernel,if_pos ⟨hy,hy'.trans hright⟩,max_eq_left (hy'.trans hleft),
    integratedPrimeBandSlope]
  ring

/-- At scale X the small primes through its nineteen-twentieths power cost
only their explicit quadratic density and an error below the five-sixths target. -/
theorem integrated_prime_band_small_primes :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℝ}, 1 ≤ X →
      let P := ⌊X^(19/20:ℝ)⌋₊
      |(∑ p ∈ ordinaryPrimeLags P, Real.log p*integratedPrimeBandKernel (p/X)) -
        integratedPrimeBandSlope*((P:ℝ)*((P:ℝ)+1)/2)/X| ≤ C*X^(143/180:ℝ) := by
  obtain ⟨B,hB,h⟩ := first_prime_moment_at_cut
  let k := integratedPrimeBandSlope
  refine ⟨|k| * B,mul_nonneg (abs_nonneg _) hB,fun {X} hX => ?_⟩
  let P := ⌊X^(19/20:ℝ)⌋₊
  have hX0 := zero_lt_one.trans_le hX
  have hP : 1 ≤ P := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow hX (by norm_num)
  have hP' : (P:ℝ) ≤ X^(19/20:ℝ) := Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have hPX : (P:ℝ) ≤ X := hP'.trans ((Real.rpow_le_rpow_of_exponent_le hX
    (by norm_num : (19/20:ℝ) ≤ 1)).trans_eq (Real.rpow_one X))
  have hf : (∑ p ∈ ordinaryPrimeLags P, Real.log p*integratedPrimeBandKernel (p/X)) =
      (k/X)*∑ p ∈ ordinaryPrimeLags P, (p:ℝ)*Real.log p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    have ht : p ≤ P := (mem_Icc.mp (mem_filter.mp hp).1).2
    have hpX : (p:ℝ)/X ≤ 1 := (div_le_one hX0).mpr ((Nat.cast_le.mpr ht).trans hPX)
    rw [kernel_below_one (div_nonneg (Nat.cast_nonneg _) hX0.le) hpX]
    dsimp only [k]; ring
  have hpow : (P:ℝ)^(17/9:ℝ)/X ≤ X^(143/180:ℝ) := by
    apply (div_le_iff₀ hX0).mpr
    have hs := Real.rpow_le_rpow (Nat.cast_nonneg P) hP' (by norm_num : (0:ℝ) ≤ 17/9)
    rw [←Real.rpow_mul hX0.le,show (19/20:ℝ)*(17/9)=143/180+1 by norm_num,
      Real.rpow_add hX0,Real.rpow_one] at hs
    exact hs
  change |(∑ p ∈ ordinaryPrimeLags P, _) - k*((P:ℝ)*((P:ℝ)+1)/2)/X| ≤ _
  rw [hf,show k*((P:ℝ)*((P:ℝ)+1)/2)/X=(k/X)*((P:ℝ)*((P:ℝ)+1)/2) by ring,
    ←mul_sub,abs_mul,abs_div,abs_of_pos hX0]
  calc _ ≤ (|k|/X)*(B*(P:ℝ)^(17/9:ℝ)) :=
            mul_le_mul_of_nonneg_left (h P hP) (div_nonneg (abs_nonneg _) hX0.le)
       _ = (|k| * B)*((P:ℝ)^(17/9:ℝ)/X) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) hB)

#print axioms integrated_prime_band_small_primes
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
