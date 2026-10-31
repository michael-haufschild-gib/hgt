import GaloisForLFunctions.AdelicKreinGeometry.Haar.MovingLimit
import GaloisForLFunctions.HeckeKreinToeplitz.Index.PositiveCoefficients

/-!
# The canonical positive part of an integer-invariant Haar kernel

The coefficient of the invariant moving form is positive definite and retains the Haar successor. The remaining coefficient is invariant under rational translations.
-/

open Complex Module Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The group coefficient of the invariant positive moving form. -/
def haarPositivePart (k : AffineGroupQ → ℂ) (hp : ∀ g, k (g * translation 1) = k g)
    (g : AffineGroupQ) : ℂ :=
  haarMovingLimit k hp (kernelColumnPoint k g) (kernelColumnPoint k 1)

/-- Cyclic exhaustion constructs a positive-definite affine kernel. -/
theorem haarPositivePart_posDef {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) : IsPosDefKernel (haarPositivePart k hp) := by
  obtain ⟨hH, hpos⟩ := haarMovingLimit_hermitian_nonnegative hk hi hs hp
  have h := isPosDefKernel_of_invariantHermitianForm (kernelColumnRepresentation k) hH hpos
    (haarMovingLimit_invariant hk hi hs hp) (kernelColumnPoint k 1)
  change IsPosDefKernel (fun g =>
    haarMovingLimit k hp (kernelColumnPoint k g) (kernelColumnPoint k 1))
  simpa only [kernelColumnRepresentation_point, mul_one] using h

/-- The identity column retains unit norm in the limiting positive form. -/
theorem haarPositivePart_one {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) : haarPositivePart k hp 1 = 1 := by
  let v := kernelColumnPoint k 1
  have hbase : kernelColumnPairing k v v = 1 := by
    rw [kernelColumnPairing_point_left hk]
    change k (1⁻¹ * 1) = 1
    rw [inv_one, one_mul, hasIntegerSuccessor_one hs]
  have hfixed (n : ℕ) : kernelColumnPairing k
      (translationFixedProjection k hp (factorialTranslationStep n) v)
      (translationFixedProjection k hp (factorialTranslationStep n) v) = (n.factorial : ℂ)⁻¹ := by
    have h := integer_successor_projection_pairing hk hs hp (factorialTranslationStep n) (1 : ℚˣ)
    simpa only [map_one, Units.val_one, div_one, factorialTranslationStep_den] using h
  have hn (n : ℕ) : translationMovingForm k hp (factorialTranslationStep n) v v =
      1 - (n.factorial : ℂ)⁻¹ := by
    have h := columnPairing_sub_translationMovingForm hk hp (factorialTranslationStep n) v v
    rw [hbase, hfixed] at h
    linear_combination -h
  have hinv : Tendsto (fun n : ℕ => (n.factorial : ℂ)⁻¹) atTop (𝓝 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_factorialTranslationStep
    simpa only [Function.comp_def, factorialTranslationStep, Rat.cast_inv, Rat.cast_natCast,
      Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using h
  have hlim := (tendsto_const_nhds (x := (1 : ℂ))).sub hinv
  have hlim' := hlim.congr' (Eventually.of_forall fun n => (hn n).symm)
  have he := tendsto_nhds_unique (tendsto_haarMovingLimit hk hi hs hp v v) hlim'
  simpa only [haarPositivePart, sub_zero] using he

/-- The discarded coefficient is unchanged by every left rational translation. -/
theorem haarPositivePart_remainder_translation {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    k (translation b * g) - haarPositivePart k hp (translation b * g) = k g - haarPositivePart k hp g := by
  have h := columnPairing_sub_haarMovingLimit_translation hk hi hs hp b
    (kernelColumnPoint k g) (kernelColumnPoint k 1)
  rw [kernelColumnRepresentation_point, kernelColumnPairing_point_left hk,
    kernelColumnPairing_point_left hk] at h
  change k (1⁻¹ * (translation b * g)) - haarPositivePart k hp (translation b * g) =
    k (1⁻¹ * g) - haarPositivePart k hp g at h
  simpa only [inv_one, one_mul] using h

/-- The positive part keeps the entire integer Haar successor. -/
theorem haarPositivePart_hasIntegerSuccessor {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) : HasIntegerSuccessor (haarPositivePart k hp) := by
  intro b
  have h := haarPositivePart_remainder_translation hk hi hs hp b 1
  rw [mul_one, hasIntegerSuccessor_one hs, haarPositivePart_one hk hi hs hp, sub_self] at h
  exact (sub_eq_zero.mp h).symm.trans (hs b)

#print axioms haarPositivePart_posDef
#print axioms haarPositivePart_one
#print axioms haarPositivePart_hasIntegerSuccessor
end GaloisForLFunctions.AdelicKreinGeometry
