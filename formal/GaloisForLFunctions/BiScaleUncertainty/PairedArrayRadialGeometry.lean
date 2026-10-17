import GaloisForLFunctions.BiScaleUncertainty.PairedCollarCapacity
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicArrayRadialComparison

/-!
# Paired array norms and finite radial penalties

The Euclidean norm of the two whole-sign norms has unit capacity in added
nonnegative mass. Its physical radial penalty is integrable because it is the
difference between transported mass and the paired kernel.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

def logarithmicPairedArrayNorm (n : ℕ) (a : Bool → ℕ → ℝ) : ℝ :=
  Real.sqrt (logarithmicSignNorm n (a false) ^ 2 + logarithmicSignNorm n (a true) ^ 2)

theorem logarithmicPairedArrayNorm_nonneg (n : ℕ) (a : Bool → ℕ → ℝ) :
    0 ≤ logarithmicPairedArrayNorm n a := Real.sqrt_nonneg _

theorem logarithmicArrayBlockNorm_eq_signNorm_add (n : ℕ) (a : Bool → ℕ → ℝ) :
    logarithmicArrayBlockNorm n a =
      logarithmicSignNorm n (a false) + logarithmicSignNorm n (a true) := by
  simp only [logarithmicArrayBlockNorm, logarithmicSignNorm, blockWeightNorm,
    logarithmicSignedCosets, Finset.sum_product, Fintype.sum_bool, Finset.sum_add_distrib]
  exact add_comm _ _

theorem logarithmicPairedArrayNorm_le_blockNorm (n : ℕ) (a : Bool → ℕ → ℝ) :
    logarithmicPairedArrayNorm n a ≤ logarithmicArrayBlockNorm n a := by
  rw [logarithmicArrayBlockNorm_eq_signNorm_add]
  apply Real.sqrt_le_iff.mpr
  have hf := logarithmicSignNorm_nonneg n (a false)
  have ht := logarithmicSignNorm_nonneg n (a true)
  constructor
  · exact add_nonneg hf ht
  · nlinarith [mul_nonneg hf ht]

theorem logarithmicPairedArrayNorm_le_mass (n : ℕ) (a : Bool → ℕ → ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) :
    logarithmicPairedArrayNorm n a ≤ logarithmicArrayMass n a :=
  (logarithmicPairedArrayNorm_le_blockNorm n a).trans (logarithmicArrayBlockNorm_le_mass n a ha)

theorem logarithmicPairedArrayNorm_pad {n m : ℕ} (hm : n ≤ m) (a : Bool → ℕ → ℝ) :
    logarithmicPairedArrayNorm m (collarArrayPad n a) = logarithmicPairedArrayNorm n a := by
  unfold logarithmicPairedArrayNorm
  rw [show logarithmicSignNorm m (collarArrayPad n a false) = logarithmicSignNorm n (a false)
    from logarithmicSignNorm_pad hm (a false),
    show logarithmicSignNorm m (collarArrayPad n a true) = logarithmicSignNorm n (a true)
    from logarithmicSignNorm_pad hm (a true)]

theorem logarithmicPairedArrayNorm_mono (n : ℕ) (a b : Bool → ℕ → ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) (hab : ∀ σ k, a σ k ≤ b σ k) :
    logarithmicPairedArrayNorm n a ≤ logarithmicPairedArrayNorm n b := by
  have hf := (logarithmicSignNorm_monotone_bounds n (a false) (b false) (ha false) (hab false)).1
  have ht := (logarithmicSignNorm_monotone_bounds n (a true) (b true) (ha true) (hab true)).1
  apply Real.sqrt_le_sqrt
  nlinarith [logarithmicSignNorm_nonneg n (a false), logarithmicSignNorm_nonneg n (a true)]

/-- Unordered paired arrays are controlled by an actual added-mass budget. -/
theorem logarithmicPairedArrayNorm_le_add_mass (n : ℕ) (a b e : Bool → ℕ → ℝ)
    (ha : ∀ σ k, 0 ≤ a σ k) (hb : ∀ σ k, 0 ≤ b σ k) (he : ∀ σ k, 0 ≤ e σ k)
    (hab : ∀ σ k, b σ k ≤ a σ k + e σ k) :
    logarithmicPairedArrayNorm n b ≤ logarithmicPairedArrayNorm n a + logarithmicArrayMass n e := by
  have hmono := logarithmicPairedArrayNorm_mono n b (fun σ k => a σ k + e σ k) hb hab
  have hf := logarithmicSignNorm_monotone_bounds n (a false) (fun k => a false k + e false k)
    (ha false) (fun k => le_add_of_nonneg_right (he false k))
  have ht := logarithmicSignNorm_monotone_bounds n (a true) (fun k => a true k + e true k)
    (ha true) (fun k => le_add_of_nonneg_right (he true k))
  have hr := pairedRadial_monotone_bounds 0 (logarithmicSignNorm_nonneg n (a false))
    (logarithmicSignNorm_nonneg n (a true)) (sub_nonneg.mp hf.1) (sub_nonneg.mp ht.1)
  simp only [zero_pow, zero_add] at hr
  change 0 ≤ logarithmicPairedArrayNorm n (fun σ k => a σ k + e σ k) -
      logarithmicPairedArrayNorm n a ∧
    logarithmicPairedArrayNorm n (fun σ k => a σ k + e σ k) - logarithmicPairedArrayNorm n a ≤
      (logarithmicSignNorm n (fun k => a false k + e false k) - logarithmicSignNorm n (a false)) +
      (logarithmicSignNorm n (fun k => a true k + e true k) - logarithmicSignNorm n (a true)) at hr
  simp only [add_sub_cancel_left] at hf ht
  rw [logarithmicArrayMass, Finset.sum_add_distrib]
  linarith [hf.2, ht.2, hr.2]

namespace PhysicalCollarPartition
variable {n : ℕ}

def pairedBlockNorm (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  logarithmicPairedArrayNorm n (fun σ k => ρ.weight σ k y)

theorem pairedBlockNorm_nonneg (ρ : PhysicalCollarPartition n) (y : ℝ) :
    0 ≤ ρ.pairedBlockNorm y := logarithmicPairedArrayNorm_nonneg _ _

theorem pairedBlockNorm_le_mass (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.pairedBlockNorm y ≤ ρ.mass y :=
  logarithmicPairedArrayNorm_le_mass n _ (fun σ k => ρ.weight_nonneg σ k y)

theorem pairedBlockNorm_le_sqrt_cutoff (ρ : PhysicalCollarPartition n) {y : ℝ}
    (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    ρ.pairedBlockNorm y ≤ 32 * Real.sqrt ((n + 2 : ℕ) : ℝ) :=
  (ρ.pairedBlockNorm_le_mass y).trans (ρ.mass_le_sqrt_cutoff hy)

def pairedRadialPenalty (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  collarRadialPenalty (archLevySinhWeight y) (ρ.pairedBlockNorm y)

theorem pairedRadialPenalty_eq_mass_sub_kernel (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.pairedRadialPenalty y = ρ.mass y - ρ.pairedKernel y := by
  change Real.sqrt (archLevySinhWeight y ^ 2 +
      (Real.sqrt (ρ.signBlockNorm false y ^ 2 + ρ.signBlockNorm true y ^ 2)) ^ 2) -
    archLevySinhWeight y = ρ.mass y - ρ.pairedKernel y
  rw [Real.sq_sqrt (by positivity)]
  unfold pairedKernel
  simp only [add_assoc]
  ring

theorem integrableOn_pairedRadialPenalty (ρ : PhysicalCollarPartition n) :
    IntegrableOn ρ.pairedRadialPenalty (Ioo 0 logarithmicCollarRadius) := by
  rw [show ρ.pairedRadialPenalty = (fun y => ρ.mass y - ρ.pairedKernel y) from
    funext ρ.pairedRadialPenalty_eq_mass_sub_kernel]
  exact ρ.integrableOn_mass.sub ρ.integrableOn_pairedKernel

theorem pairedRadialPenalty_bounds (ρ : PhysicalCollarPartition n) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ρ.pairedRadialPenalty y ∧ ρ.pairedRadialPenalty y ≤ ρ.mass y :=
  ⟨collarRadialPenalty_nonneg _ _,
    (collarRadialPenalty_le (archLevySinhWeight_nonneg hy) (ρ.pairedBlockNorm_nonneg y)).trans
      (ρ.pairedBlockNorm_le_mass y)⟩

theorem pairedCoefficient_eq_mass_sub_penalty (ρ : PhysicalCollarPartition n) :
    ρ.pairedCoefficient =
      (∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x) -
      ∫ y in Ioo 0 logarithmicCollarRadius, ρ.pairedRadialPenalty y := by
  rw [← ρ.integral_mass, show ρ.pairedRadialPenalty = fun y => ρ.mass y - ρ.pairedKernel y from
    funext ρ.pairedRadialPenalty_eq_mass_sub_kernel,
    integral_sub ρ.integrableOn_mass ρ.integrableOn_pairedKernel]
  unfold pairedCoefficient
  ring

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
