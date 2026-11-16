import GaloisForLFunctions.RepresentationLifting.Probability.PadicMatrixHaar
import GaloisForLFunctions.RepresentationLifting.Probability.PrimePowerFittingDistribution

/-!
# Generalized zero-eigenspace degrees for p-adic Haar matrices

Reduction of Haar measure is uniform. Thus the dimension of the
generalized zero-eigenspace modulo `p` has the finite-field product law
and its uniform geometric tail bound.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open OperatorKernels

variable (p : ℕ) [Fact p.Prime]

/-- Haar probability of residue generalized zero-eigenspace dimension `d`. -/
def padicFittingDegreeProbability (n d : ℕ) : ℝ :=
  (padicMatrixHaar p n).real {A |
    Module.finrank (ZMod p) (nilpotentPart
      (primePowerResidueEnd p 0 n (padicMatrixProjection p 1 (Fin n) A))) = d}

/-- Haar residue-degree probabilities agree exactly with the rational finite-field law. -/
theorem padicFittingDegreeProbability_eq (n d : ℕ) :
    padicFittingDegreeProbability p n d = (fittingDegreeDensity (ZMod p) n d : ℝ) := by
  have h := padicMatrixHaar_residue_probability p 1 n
    (fun A => Module.finrank (ZMod p) (nilpotentPart (primePowerResidueEnd p 0 n A)) = d)
  have he : padicFittingDegreeProbability p n d =
      (primePowerFittingDegreeDensity p 0 n d : ℝ) := by
    simpa only [padicFittingDegreeProbability, primePowerFittingDegreeDensity,
      Rat.cast_div, Rat.cast_natCast] using h
  rw [he, primePowerFittingDegreeDensity_eq]

/-- Exact degree law for a Haar matrix of size `d+k`. -/
theorem padicFittingDegreeProbability_eq_product (d k : ℕ) :
    padicFittingDegreeProbability p (d + k) d =
      (∏ i : Fin k, (1 - 1 / (p : ℝ) ^ (d + (i : ℕ) + 1))) / (p : ℝ) ^ d := by
  rw [padicFittingDegreeProbability_eq, fittingDegreeDensity_eq_product, Nat.card_zmod]
  push_cast

/-- The residue-degree probabilities form a probability law. -/
theorem sum_padicFittingDegreeProbability (n : ℕ) :
    (∑ d : Fin (n + 1), padicFittingDegreeProbability p n (d : ℕ)) = 1 := by
  simp_rw [padicFittingDegreeProbability_eq]
  have h := congrArg (fun x : ℚ => (x : ℝ)) (sum_fittingDegreeDensity (ZMod p) n)
  push_cast at h
  exact h

/-- Geometric tail bound, uniform in matrix size. -/
theorem padicFittingDegreeProbability_tail_le (d k : ℕ) :
    (∑ i : Fin (k + 1), padicFittingDegreeProbability p (d + k) (d + (i : ℕ))) ≤
      (1 / (p : ℝ) ^ d) / (1 - 1 / (p : ℝ)) := by
  simp_rw [padicFittingDegreeProbability_eq]
  have hq : (∑ i : Fin (k + 1), fittingDegreeDensity (ZMod p) (d + k)
      (d + (i : ℕ))) ≤ (1 / (p : ℚ) ^ d) / (1 - 1 / (p : ℚ)) := by
    simpa only [Nat.card_zmod] using sum_fittingDegreeDensity_tail_le (ZMod p) d k
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr
  exact hr

#print axioms padicFittingDegreeProbability_eq_product
#print axioms sum_padicFittingDegreeProbability
#print axioms padicFittingDegreeProbability_tail_le

end GaloisForLFunctions.RepresentationLifting
