import GaloisForLFunctions.HTGeometry.LinearAlgebra.PositiveMatrixForcing
import GaloisForLFunctions.HyperbolicArakelovTheory.TheDirichletGreenKernelsOfTheAdelicCarrier

/-!
# Signed Dirichlet correction heights on the adelic carrier

A finitely supported real charge has a unique maximizing Dirichlet potential.
The maximum is its Green height. Enlarging the domain increases this height
by exactly the energy of the difference between the two potentials; equality
holds precisely when those potentials agree everywhere. Charges may have either
sign, so this strengthens pointwise domain monotonicity of the Green kernel.

The finite negative-definite correction mechanism in Liu's Lemma 5.15 applies
here to the negative of the existing carrier precision form. Positivity and
invertibility are supplied by the carrier's ground-state energy theorem.
-/

noncomputable section
open Matrix
open scoped Classical BigOperators
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic CoupledProductObstruction
open GaloisForLFunctions.HTGeometry

/-- The Green potential of a finite signed charge, extended by zero outside the domain. -/
def finiteDirichletPotential (S F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) : ℝ := ∑ x ∈ S, f x * dirichletGreen F x y

/-- Pair the charge with its Dirichlet potential. -/
def finiteDirichletHeight (S F : Finset FiniteVertices) (f : FiniteVertices → ℝ) : ℝ :=
  ∑ y ∈ S, f y * finiteDirichletPotential S F f y

theorem finiteDirichletPotential_outside (S F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) {y : FiniteVertices} (hy : y ∉ F) :
    finiteDirichletPotential S F f y = 0 := by
  simp only [finiteDirichletPotential, dirichletGreen_outside F _ _ hy,
    mul_zero, Finset.sum_const_zero]

/-- Restriction of the potential is the inverse precision response to the charge. -/
theorem finiteDirichletPotential_eq_inverse (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f : FiniteVertices → ℝ) :
    (precisionMatrix F)⁻¹ *ᵥ (fun y : F => finiteSource S f y.1) =
      fun y : F => finiteDirichletPotential S F f y.1 := by
  funext y
  calc
    _ = ∑ x ∈ F, finiteSource S f x * dirichletGreen F x y.1 := by
      rw [← Finset.sum_coe_sort F (fun x => finiteSource S f x * dirichletGreen F x y.1)]
      change (∑ x : F, (precisionMatrix F)⁻¹ y x * finiteSource S f x.1) = _
      apply Finset.sum_congr rfl
      intro x _
      simp only [dirichletGreen, dif_pos y.2, dif_pos x.2]
      ring
    _ = _ := sum_finiteSource_mul S F hSF f _

/-- The potential solves the signed charge equation at every vertex of the domain. -/
theorem finiteDirichletPotential_source (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f : FiniteVertices → ℝ) (y : FiniteVertices) (hy : y ∈ F) :
    precision F (finiteDirichletPotential S F f) y = finiteSource S f y := by
  have h := matrix_positive_response (precisionMatrix F) (precisionMatrix_posDef F)
    (fun z : F => finiteSource S f z.1)
  rw [finiteDirichletPotential_eq_inverse S F hSF f] at h
  have hy' := congrFun h (⟨y, hy⟩ : F)
  rwa [precisionMatrix_mulVec] at hy'

theorem finiteDirichletHeight_eq_inverse_energy (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f : FiniteVertices → ℝ) :
    (fun y : F => finiteSource S f y.1) ⬝ᵥ
      ((precisionMatrix F)⁻¹ *ᵥ (fun y : F => finiteSource S f y.1)) =
      finiteDirichletHeight S F f := by
  rw [finiteDirichletPotential_eq_inverse S F hSF f]
  change (∑ y : F, finiteSource S f y.1 * finiteDirichletPotential S F f y.1) = _
  rw [Finset.sum_coe_sort F (fun y => finiteSource S f y * finiteDirichletPotential S F f y)]
  exact sum_finiteSource_mul S F hSF f _

theorem matrixForcedValue_carrier (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f g : FiniteVertices → ℝ) :
    matrixForcedValue (precisionMatrix F) (fun y : F => finiteSource S f y.1)
      (fun y : F => g y.1) = 2 * (∑ y ∈ S, f y * g y) - energy F g := by
  rw [matrixForcedValue, precisionMatrix_energy]
  change 2 * (∑ y : F, finiteSource S f y.1 * g y.1) - energy F g = _
  rw [Finset.sum_coe_sort F (fun y => finiteSource S f y * g y),
    sum_finiteSource_mul S F hSF f g]

/-- Every candidate potential has forced quadratic value at most the Green height. -/
theorem finiteDirichletHeight_variational (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f g : FiniteVertices → ℝ) :
    2 * (∑ y ∈ S, f y * g y) - energy F g ≤ finiteDirichletHeight S F f := by
  have h := matrix_forced_value_le (precisionMatrix F) (precisionMatrix_posDef F)
    (fun y : F => finiteSource S f y.1) (fun y : F => g y.1)
  rwa [matrixForcedValue_carrier S F hSF f g,
    finiteDirichletHeight_eq_inverse_energy S F hSF f] at h

theorem energy_finiteDirichletPotential (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f : FiniteVertices → ℝ) :
    energy F (finiteDirichletPotential S F f) = finiteDirichletHeight S F f := by
  rw [← precisionMatrix_energy, ← finiteDirichletPotential_eq_inverse S F hSF f,
    matrix_positive_response _ (precisionMatrix_posDef F), dotProduct_comm,
    finiteDirichletHeight_eq_inverse_energy S F hSF f]

/-- Equality in the variational bound characterizes the potential on the domain. -/
theorem finiteDirichletHeight_variational_eq_iff (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f g : FiniteVertices → ℝ) :
    2 * (∑ y ∈ S, f y * g y) - energy F g = finiteDirichletHeight S F f ↔
      ∀ y ∈ F, g y = finiteDirichletPotential S F f y := by
  have h := matrix_forced_value_eq_iff (precisionMatrix F) (precisionMatrix_posDef F)
    (fun y : F => finiteSource S f y.1) (fun y : F => g y.1)
  rw [matrixForcedValue_carrier S F hSF f g,
    finiteDirichletHeight_eq_inverse_energy S F hSF f,
    finiteDirichletPotential_eq_inverse S F hSF f] at h
  rw [h]
  constructor
  · intro heq y hy
    exact congrFun heq ⟨y, hy⟩
  · intro heq
    funext y
    exact heq y.1 y.2

/-- Zero extension of a supported potential preserves its precision energy. -/
theorem energy_enlarge_supported (F E : Finset FiniteVertices) (hFE : F ⊆ E)
    (g : FiniteVertices → ℝ) (hg : ∀ y, y ∉ F → g y = 0) : energy E g = energy F g := by
  have hsource : finiteSource E g = finiteSource F g := by
    funext y
    by_cases hy : y ∈ F
    · simp only [finiteSource, if_pos hy, if_pos (hFE hy)]
    · simp only [finiteSource, if_neg hy, hg y hy, ite_self]
  have hp : precision E g = precision F g := by
    funext y
    simp only [precision, hsource]
  rw [energy_eq_precision, energy_eq_precision, hp]
  symm
  exact Finset.sum_subset hFE (fun y _ hy => by rw [hg y hy, zero_mul])

/-- The gain from enlarging the domain is exactly the energy of the potential difference. -/
theorem finiteDirichletHeight_domain_gap (S F E : Finset FiniteVertices)
    (hSF : S ⊆ F) (hFE : F ⊆ E) (f : FiniteVertices → ℝ) :
    finiteDirichletHeight S E f - finiteDirichletHeight S F f =
      energy E (finiteDirichletPotential S F f - finiteDirichletPotential S E f) := by
  have hSE : S ⊆ E := hSF.trans hFE
  have hload : (fun y : E => finiteSource S f y.1) ⬝ᵥ
      (fun y : E => finiteDirichletPotential S F f y.1) = finiteDirichletHeight S F f := by
    change (∑ y : E, finiteSource S f y.1 * finiteDirichletPotential S F f y.1) = _
    rw [Finset.sum_coe_sort E (fun y => finiteSource S f y * finiteDirichletPotential S F f y)]
    exact sum_finiteSource_mul S E hSE f _
  have hv : matrixForcedValue (precisionMatrix E) (fun y : E => finiteSource S f y.1)
      (fun y : E => finiteDirichletPotential S F f y.1) = finiteDirichletHeight S F f := by
    rw [matrixForcedValue, hload, precisionMatrix_energy,
      energy_enlarge_supported F E hFE _
        (fun y hy => finiteDirichletPotential_outside S F f hy),
      energy_finiteDirichletPotential S F hSF f]
    ring
  have h := matrix_forced_value_gap (precisionMatrix E) (precisionMatrix_posDef E)
    (fun y : E => finiteSource S f y.1) (fun y : E => finiteDirichletPotential S F f y.1)
  rw [finiteDirichletHeight_eq_inverse_energy S E hSE f, hv,
    finiteDirichletPotential_eq_inverse S E hSE f] at h
  rw [← precisionMatrix_energy]
  exact h

/-- Green height increases with the domain for every finite signed charge. -/
theorem finiteDirichletHeight_mono (S F E : Finset FiniteVertices)
    (hSF : S ⊆ F) (hFE : F ⊆ E) (f : FiniteVertices → ℝ) :
    finiteDirichletHeight S F f ≤ finiteDirichletHeight S E f := by
  apply sub_nonneg.mp
  rw [finiteDirichletHeight_domain_gap S F E hSF hFE f]
  rw [← precisionMatrix_energy]
  simpa only [star_trivial] using
    (precisionMatrix_posDef E).posSemidef.dotProduct_mulVec_nonneg
      (fun y : E => (finiteDirichletPotential S F f - finiteDirichletPotential S E f) y.1)

/-- Height stays constant exactly when enlarging the domain leaves the potential unchanged. -/
theorem finiteDirichletHeight_eq_iff_potential (S F E : Finset FiniteVertices)
    (hSF : S ⊆ F) (hFE : F ⊆ E) (f : FiniteVertices → ℝ) :
    finiteDirichletHeight S F f = finiteDirichletHeight S E f ↔
      finiteDirichletPotential S F f = finiteDirichletPotential S E f := by
  have hgap := finiteDirichletHeight_domain_gap S F E hSF hFE f
  constructor
  · intro hheight
    funext y
    by_cases hy : y ∈ E
    · by_contra hne
      have hp := (energy_pos_iff E
        (finiteDirichletPotential S F f - finiteDirichletPotential S E f)).mpr
        ⟨y, hy, sub_ne_zero.mpr hne⟩
      rw [← hgap, hheight, sub_self] at hp
      exact (lt_irrefl 0) hp
    · rw [finiteDirichletPotential_outside S E f hy,
        finiteDirichletPotential_outside S F f (fun hf => hy (hFE hf))]
  · intro hp
    rw [hp, sub_self] at hgap
    have hz : energy E 0 = 0 := by
      simp only [energy, Pi.zero_apply, zero_pow two_ne_zero, zero_mul,
        Finset.sum_const_zero, mul_zero, sub_self]
    rw [hz] at hgap
    exact (sub_eq_zero.mp hgap).symm

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen

#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen.finiteDirichletHeight_domain_gap
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen.finiteDirichletPotential_source
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen.finiteDirichletHeight_mono
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen.finiteDirichletHeight_eq_iff_potential
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen.finiteDirichletHeight_variational_eq_iff
