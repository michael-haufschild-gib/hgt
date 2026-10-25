import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells0
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells16
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells32
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureCells48

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
  let mut values := #[]
  let bound := Lean.mkIdent
    (if side.getId == `Lo then ``Enclosure.lower else ``Enclosure.upper)
  for j in [:64] do
    let name := Lean.mkIdent
      (`RHTower.ThetaRationalQuadrature.Certificates ++
        .mkSimple ("raw" ++ side.getId.toString ++ toString r.getNat ++
        "_" ++ toString j))
    numerators := numerators.push (← `(Lean.Parser.Tactic.simpLemma| ← ($name).property))
    values := values.push (← `(Lean.Parser.Tactic.simpLemma| $name:ident))
  `(tactic| (simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    $bound:ident, $[$numerators],*]; dsimp only [$[$values],*]))

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
        ∑ j ∈ Finset.range 64, lowerMass r j :=
    Finset.sum_le_sum fun j _ => (Enclosure.contains_massLo r j).1
  have hhi (r : ℕ) :
      (∑ j ∈ Finset.range 64, upperMass r j) ≤
        ∑ j ∈ Finset.range 64, Enclosure.upper (Enclosure.massHi r j) :=
    Finset.sum_le_sum fun j _ => (Enclosure.contains_massHi r j).2
  exact ⟨lower_zero_certificate.trans_le (hlo 0),
    lower_one_certificate.trans_le (hlo 1), lower_two_certificate.trans_le (hlo 2),
    (add_le_add_right (hhi 1) _).trans_lt upper_one_certificate,
    (add_le_add_right (hhi 3) _).trans_lt upper_three_certificate⟩

end RHTower.ThetaRationalQuadrature
