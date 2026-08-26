import GaloisForLFunctions.HTGeometry.AffineExponentialCosetRelations
import GaloisForLFunctions.HTGeometry.AffineExponentialCoLieClassification
import GaloisForLFunctions.RHTower.SchanuelLatticeBakerAssembly

/-!
# Algebraic-coset Baker assembly for Schanuel defects

This file connects the exact mixed subgroup quotient classification to the unconditional Baker
endgame.  If an exponential point lies in a coset represented by a coordinatewise algebraic
point, then vanishing of the algebraic-coefficient invariant differential in the subgroup
quotient forces every coefficient to vanish.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open AffineExponentialGroup AffineExponentialSubgroups
open AffineExponentialPointEvaluation AffineExponentialPointClosure
open AffineExponentialProjectionClassification MixedAdditiveProjectionClassification
open AffineExponentialCosetRelations AffineExponentialCoLieClassification
open TorusCharacterCoLie

noncomputable section

/-- Algebraicity over `ℚ` is stable under integral powers in `ℂ`. -/
theorem isAlgebraic_zpow_complex {z : ℂ} (hz : IsAlgebraic ℚ z) (m : ℤ) :
    IsAlgebraic ℚ (z ^ m) := by
  cases m with
  | ofNat n => simpa using hz.pow n
  | negSucc n => simpa [zpow_negSucc] using (hz.pow (n + 1)).inv

/-- Coercion from complex units commutes with integral powers. -/
theorem coe_units_zpow_complex (z : ℂˣ) (m : ℤ) :
    ((z ^ m : ℂˣ) : ℂ) = (z : ℂ) ^ m := by
  change (Units.coeHom ℂ) (z ^ m) = (Units.coeHom ℂ) z ^ m
  exact map_zpow (Units.coeHom ℂ) z m

/-- A finite additive-linear value of algebraic complex coordinates and coefficients is
algebraic. -/
theorem isAlgebraic_additiveLinearEval {n : ℕ}
    (x v : Fin n → ℂ)
    (hx : ∀ i, IsAlgebraic ℚ (x i))
    (hv : ∀ i, IsAlgebraic ℚ (v i)) :
    IsAlgebraic ℚ (additiveLinearEval (k := ℂ) x v) := by
  classical
  change IsAlgebraic ℚ (∑ i, v i * x i)
  apply Finset.sum_induction
  · intro a b ha hb
    exact ha.add hb
  · exact isAlgebraic_zero
  · intro i _
    exact (hv i).mul (hx i)

/-- A torus character evaluated at coordinatewise algebraic complex units is algebraic. -/
theorem isAlgebraic_torusCharacter {n : ℕ}
    (y : Fin n → ℂˣ)
    (hy : ∀ i, IsAlgebraic ℚ (y i : ℂ))
    (m : Fin n →₀ ℤ) :
    IsAlgebraic ℚ (AlgebraicTorusCharacter.character y m : ℂ) := by
  classical
  rw [AlgebraicTorusCharacter.character]
  rw [Units.coe_prod]
  apply Finset.prod_induction
  · intro a b ha hb
    exact ha.mul hb
  · exact isAlgebraic_one
  · intro i _
    rw [coe_units_zpow_complex]
    exact isAlgebraic_zpow_complex (hy i) (m i)

/-- Exact coset-and-relation form of the algebraic-coefficient Baker contradiction. -/
theorem algebraic_coefficients_eq_zero_of_coset_relations
    {n : ℕ} (x : Fin n → ℂ) (hx : LinearIndependent ℚ x)
    (I : Ideal (CoordinateAlgebra ℂ n)) [I.IsHopfIdeal ℂ]
    (p q : Point ℂ n)
    (hpadd : additivePart p = x)
    (hptorus : ∀ i, (torusPart p i : ℂ) = Complex.exp (x i))
    (hqadd : ∀ i, IsAlgebraic ℚ (additivePart q i))
    (hqtorus : ∀ i, IsAlgebraic ℚ (torusPart q i : ℂ))
    (hdiv : p * q⁻¹ ∈ zeroLocus I)
    (c : Fin n → algebraicClosure ℚ ℂ)
    (hcTorus : (fun i => (c i : ℂ)) ∈ latticeSpan ℂ (torusRelationLattice ℂ I))
    (hcAdditive : (fun i => -(c i : ℂ)) ∈ additiveRelationSubspace ℂ I) :
    c = 0 := by
  classical
  apply algebraic_coefficients_eq_zero_of_latticeSpan x hx
    (torusRelationLattice ℂ I) c hcTorus
  · intro m hm
    have hcoset := torusCharacter_eq_of_div_mem_zeroLocus ℂ I p q hdiv hm
    have hpchar :
        (AlgebraicTorusCharacter.character (torusPart p) m : ℂ) =
          ∏ i, Complex.exp (x i) ^ (m i) := by
      rw [AlgebraicTorusCharacter.character_apply_of_subset
        (Finset.subset_univ m.support) (torusPart p)]
      rw [Units.coe_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [coe_units_zpow_complex]
      exact congrArg (fun z : ℂ => z ^ (m i)) (hptorus i)
    rw [← hpchar, hcoset]
    exact isAlgebraic_torusCharacter (torusPart q) hqtorus m
  · have hcAdditive' :
        (fun i => (c i : ℂ)) ∈ additiveRelationSubspace ℂ I := by
      have hneg := (additiveRelationSubspace ℂ I).neg_mem hcAdditive
      rw [show (fun i => (c i : ℂ)) = -(fun i => -(c i : ℂ)) by
        funext i
        simp]
      exact hneg
    have hcoset := additiveLinearEval_eq_of_div_mem_zeroLocus ℂ I p q hdiv hcAdditive'
    have hqvalue := isAlgebraic_additiveLinearEval
      (additivePart q) (fun i => (c i : ℂ)) hqadd
      (fun i => mem_algebraicClosure_iff.mp (c i).2)
    rw [hpadd] at hcoset
    have hpvalue : IsAlgebraic ℚ
        (additiveLinearEval (k := ℂ) x (fun i => (c i : ℂ))) := by
      rw [hcoset]
      exact hqvalue
    simpa [additiveLinearEval] using hpvalue

/-- If the algebraic-coefficient invariant differential dies in the actual subgroup quotient and
the exponential point lies in a coset with an algebraic representative, then every coefficient
vanishes. -/
theorem algebraic_coefficients_eq_zero_of_algebraic_coset_coLie
    {n : ℕ} (x : Fin n → ℂ) (hx : LinearIndependent ℚ x)
    (I : Ideal (CoordinateAlgebra ℂ n)) [I.IsHopfIdeal ℂ]
    (p q : Point ℂ n)
    (hpadd : additivePart p = x)
    (hptorus : ∀ i, (torusPart p i : ℂ) = Complex.exp (x i))
    (hqadd : ∀ i, IsAlgebraic ℚ (additivePart q i))
    (hqtorus : ∀ i, IsAlgebraic ℚ (torusPart q i : ℂ))
    (hdiv : p * q⁻¹ ∈ zeroLocus I)
    (c : Fin n → algebraicClosure ℚ ℂ)
    (hcoLie : subgroupQuotientCoLieMap ℂ I
      (mixedCoLieVector ℂ (fun i => (c i : ℂ)) (fun i => -(c i : ℂ))) = 0) :
    c = 0 := by
  have hrelations :=
    (coLieMap_subgroupQuotient_eq_zero_iff ℂ I
      (fun i => (c i : ℂ)) (fun i => -(c i : ℂ))).mp hcoLie
  exact algebraic_coefficients_eq_zero_of_coset_relations x hx I p q hpadd hptorus
    hqadd hqtorus hdiv c hrelations.1 hrelations.2

end

end GaloisForLFunctions.RHTower
