import GaloisForLFunctions.RepresentationLifting.Probability.PrimePowerNilpotentMatrices
import GaloisForLFunctions.RepresentationLifting.Probability.FittingDegreeDistribution

/-!
# Residue degree distributions at every prime-power level

Uniform matrices modulo `p^(r+1)` have uniform reductions modulo `p`.
Consequently the generalized zero-eigenspace dimension of the residue
endomorphism has exactly the same finite-product law and geometric tail
at every level. These are statements about the complete finite matrix
spaces, with no sampling or asymptotic assumptions.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open OperatorKernels

/-- Reduction followed by standard matrix coordinates on the residue vector space. -/
def primePowerResidueEnd (p r n : ℕ) :
    Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1))) →+* Module.End (ZMod p) (Fin n → ZMod p) :=
  (LinearMap.toMatrixAlgEquiv' (R := ZMod p) (n := Fin n)).symm.toRingHom.comp
    (primePowerMatrixReduction p r (Fin n))

theorem primePowerResidueEnd_surjective (p r n : ℕ) :
    Function.Surjective (primePowerResidueEnd p r n) :=
  (LinearMap.toMatrixAlgEquiv' (R := ZMod p) (n := Fin n)).symm.surjective.comp
    (primePowerMatrixReduction_surjective p r (Fin n))

variable (p : ℕ) [Fact p.Prime]

/-- Proportion of matrices whose residue has generalized zero-eigenspace dimension `d`. -/
def primePowerFittingDegreeDensity (r n d : ℕ) : ℚ :=
  (Nat.card {A : Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1))) //
      Module.finrank (ZMod p) (nilpotentPart (primePowerResidueEnd p r n A)) = d} : ℚ) /
    Nat.card (Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1))))

/-- Every residue degree proportion is independent of the prime-power thickness. -/
theorem primePowerFittingDegreeDensity_eq (r n d : ℕ) :
    primePowerFittingDegreeDensity p r n d = fittingDegreeDensity (ZMod p) n d := by
  have hc := card_additivePredicate_reduction_mul_card (primePowerResidueEnd p r n).toAddMonoidHom
    (primePowerResidueEnd_surjective p r n)
    (fun A => Module.finrank (ZMod p) (nilpotentPart (primePowerResidueEnd p r n A)) = d)
    (fun T => Module.finrank (ZMod p) (nilpotentPart T) = d) (fun _ => Iff.rfl)
  have hsize : Nat.card (Module.End (ZMod p) (Fin n → ZMod p)) = p ^ (n * n) := by
    rw [Nat.card_congr (LinearMap.toMatrixAlgEquiv' (R := ZMod p) (n := Fin n)).toEquiv]
    simp only [Matrix, Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul]
  rw [hsize] at hc
  have hden : (Nat.card (Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1)))) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1))))).ne'
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold primePowerFittingDegreeDensity fittingDegreeDensity
  rw [Nat.card_zmod]
  apply (div_eq_div_iff hden (pow_ne_zero _ hp)).mpr
  exact_mod_cast hc

/-- The exact distinguished-degree product law holds at every finite prime-power level. -/
theorem primePowerFittingDegreeDensity_eq_product (r d k : ℕ) :
    primePowerFittingDegreeDensity p r (d + k) d =
      (∏ i : Fin k, (1 - 1 / (p : ℚ) ^ (d + (i : ℕ) + 1))) / (p : ℚ) ^ d := by
  rw [primePowerFittingDegreeDensity_eq, fittingDegreeDensity_eq_product, Nat.card_zmod]

/-- A uniform geometric tail bound, simultaneously in matrix dimension and ring thickness. -/
theorem primePowerFittingDegreeDensity_tail_le (r d k : ℕ) :
    (∑ i : Fin (k + 1), primePowerFittingDegreeDensity p r (d + k) (d + (i : ℕ))) ≤
      (1 / (p : ℚ) ^ d) / (1 - 1 / (p : ℚ)) := by
  simp_rw [primePowerFittingDegreeDensity_eq]
  simpa only [Nat.card_zmod] using sum_fittingDegreeDensity_tail_le (ZMod p) d k

#print axioms primePowerFittingDegreeDensity_eq
#print axioms primePowerFittingDegreeDensity_eq_product
#print axioms primePowerFittingDegreeDensity_tail_le

end GaloisForLFunctions.RepresentationLifting
