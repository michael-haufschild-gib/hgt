import Mathlib.Algebra.BigOperators.Field
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells0
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells4
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells8
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells12
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells16
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells20
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells24
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells28
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells32
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells36
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells40
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells44
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells48
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells52
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells56
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells60

/-!
# Kernel-checked first-atom quadrature certificates

Outward rounding bounds the original rational polynomials coefficient by coefficient.
The five remaining comparisons reduce to integer arithmetic with a fixed denominator.
-/

open scoped BigOperators

namespace RHTower.ThetaRationalQuadrature

-- Replace each enclosure by its separately checked integer numerator before summation.
macro "normalize_first_atom_cells " side:ident r:num : tactic => do
  let mut numerators := #[]
  let bound := Lean.mkIdent
    (if side.getId == `Lo then ``Enclosure.lower else ``Enclosure.upper)
  for j in [:64] do
    let name := Lean.mkIdent
      (`RHTower.ThetaRationalQuadrature.Certificates ++
        .mkSimple ("raw" ++ side.getId.toString ++ toString r.getNat ++
        "_" ++ toString j))
    numerators := numerators.push (← `(Lean.Parser.Tactic.simpLemma| ← ($name).property))
  `(tactic| (
    simp only [$bound:ident]
    rw [← Finset.sum_div]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, $[$numerators],*]))

private theorem lower_zero_certificate :
    (0.4969488 : ℚ) < ∑ j ∈ Finset.range 64, Enclosure.lower (Enclosure.massLo 0 j) := by
  normalize_first_atom_cells Lo 0
  norm_num [Enclosure.precision]

private theorem lower_one_certificate :
    (0.02297 : ℚ) < ∑ j ∈ Finset.range 64, Enclosure.lower (Enclosure.massLo 1 j) := by
  normalize_first_atom_cells Lo 1
  norm_num [Enclosure.precision]

private theorem lower_two_certificate :
    (0.0029627 : ℚ) < ∑ j ∈ Finset.range 64, Enclosure.lower (Enclosure.massLo 2 j) := by
  normalize_first_atom_cells Lo 2
  norm_num [Enclosure.precision]

private theorem upper_one_certificate :
    (∑ j ∈ Finset.range 64, Enclosure.upper (Enclosure.massHi 1 j)) + 1 / 40000000 <
      (0.0229718 : ℚ) := by
  normalize_first_atom_cells Hi 1
  norm_num [Enclosure.precision]

private theorem upper_three_certificate :
    (∑ j ∈ Finset.range 64, Enclosure.upper (Enclosure.massHi 3 j)) + 1 / 40000000 <
      (0.00059935 : ℚ) := by
  normalize_first_atom_cells Hi 3
  norm_num [Enclosure.precision]

/-- Rounded enclosures imply the five bounds for the original, unrounded rational masses. -/
theorem firstAtom_bounds :
    ((0.4969488 : ℚ) < ∑ j ∈ Finset.range 64, lowerMass 0 j) ∧
    ((0.02297 : ℚ) < ∑ j ∈ Finset.range 64, lowerMass 1 j) ∧
    ((0.0029627 : ℚ) < ∑ j ∈ Finset.range 64, lowerMass 2 j) ∧
    ((∑ j ∈ Finset.range 64, upperMass 1 j) + 1 / 40000000 < (0.0229718 : ℚ)) ∧
    ((∑ j ∈ Finset.range 64, upperMass 3 j) + 1 / 40000000 < (0.00059935 : ℚ)) := by
  have hlo (r : ℕ) :
      (∑ j ∈ Finset.range 64, Enclosure.lower (Enclosure.massLo r j)) ≤
        ∑ j ∈ Finset.range 64, lowerMass r j := by
    apply Finset.sum_le_sum
    intro j _
    exact (Enclosure.contains_massLo r j).1
  have hhi (r : ℕ) :
      (∑ j ∈ Finset.range 64, upperMass r j) ≤
        ∑ j ∈ Finset.range 64, Enclosure.upper (Enclosure.massHi r j) := by
    apply Finset.sum_le_sum
    intro j _
    exact (Enclosure.contains_massHi r j).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      (0.4969488 : ℚ) < ∑ j ∈ Finset.range 64,
          Enclosure.lower (Enclosure.massLo 0 j) := lower_zero_certificate
      _ ≤ ∑ j ∈ Finset.range 64, lowerMass 0 j := hlo 0
  · calc
      (0.02297 : ℚ) < ∑ j ∈ Finset.range 64,
          Enclosure.lower (Enclosure.massLo 1 j) := lower_one_certificate
      _ ≤ ∑ j ∈ Finset.range 64, lowerMass 1 j := hlo 1
  · calc
      (0.0029627 : ℚ) < ∑ j ∈ Finset.range 64,
          Enclosure.lower (Enclosure.massLo 2 j) := lower_two_certificate
      _ ≤ ∑ j ∈ Finset.range 64, lowerMass 2 j := hlo 2
  · calc
      (∑ j ∈ Finset.range 64, upperMass 1 j) + 1 / 40000000 ≤
          (∑ j ∈ Finset.range 64, Enclosure.upper (Enclosure.massHi 1 j)) + 1 / 40000000 :=
        add_le_add_right (hhi 1) (1 / 40000000)
      _ < (0.0229718 : ℚ) := upper_one_certificate
  · calc
      (∑ j ∈ Finset.range 64, upperMass 3 j) + 1 / 40000000 ≤
          (∑ j ∈ Finset.range 64, Enclosure.upper (Enclosure.massHi 3 j)) + 1 / 40000000 :=
        add_le_add_right (hhi 3) (1 / 40000000)
      _ < (0.00059935 : ℚ) := upper_three_certificate

end RHTower.ThetaRationalQuadrature
