import GaloisForLFunctions.BiScaleUncertainty.CappedSupportComparison

/-!
# Capacity and constraint growth for full-grid collar arrays

Physical coordinate growth and an increased low cutoff both increase the capped
energy kernel. The all-low endpoint is exactly the paired kernel. The two effects
are proved separately, without imposing any source-energy comparison as a premise.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

def logarithmicCappedArraySupport (n k : ℕ) (a : Bool → ℕ → ℝ) : ℝ :=
  cappedCosetSupport (logarithmicOddCosets n)
    (fun σ p => collarBlockSize (logarithmicCosetNodes k p) (a σ))
    (fun σ p => collarBlockSize (logarithmicHighCosetNodes n k p) (a σ))

def logarithmicCappedArrayKernel (n k : ℕ) (a : Bool → ℕ → ℝ) (W : ℝ) : ℝ :=
  W + (∑ j ∈ Finset.range (n + 1), (a false j + a true j)) -
    Real.sqrt (W ^ 2 + logarithmicCappedArraySupport n k a ^ 2)

theorem logarithmicCappedArraySupport_nonneg (n k : ℕ) (a : Bool → ℕ → ℝ) :
    0 ≤ logarithmicCappedArraySupport n k a :=
  cappedCosetSupport_nonneg _ _ _ (fun _ _ => Real.sqrt_nonneg _)

theorem logarithmicCappedBlock_split {n k : ℕ} (hk : k ≤ n) (p : ℕ) (a : ℕ → ℝ) :
    collarBlockSize (logarithmicCosetNodes k p) a ^ 2 +
      collarBlockSize (logarithmicHighCosetNodes n k p) a ^ 2 =
        collarBlockSize (logarithmicCosetNodes n p) a ^ 2 := by
  simp only [collarBlockSize_sq]
  exact sum_logarithmic_low_high hk p _

/-- Enlarging the low portion tightens the same whole-block sphere. -/
theorem logarithmicCappedArraySupport_antitone_low {n k l : ℕ}
    (hkl : k ≤ l) (hln : l ≤ n) (a : Bool → ℕ → ℝ) :
    logarithmicCappedArraySupport n l a ≤ logarithmicCappedArraySupport n k a := by
  apply cappedCosetSupport_mono_of_blocks
  intro σ p _ t ht
  apply cappedBlockSupport_antitone_low (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum_of_subset_of_nonneg (logarithmicCosetNodes_subset hkl p)
      (fun j _ _ => sq_nonneg (a σ j))
  · exact (logarithmicCappedBlock_split (hkl.trans hln) p (a σ)).trans
      (logarithmicCappedBlock_split hln p (a σ)).symm
  · exact ht

theorem logarithmicCappedArrayKernel_mono_low {n k l : ℕ}
    (hkl : k ≤ l) (hln : l ≤ n) (a : Bool → ℕ → ℝ) (W : ℝ) :
    logarithmicCappedArrayKernel n k a W ≤ logarithmicCappedArrayKernel n l a W := by
  have hs := logarithmicCappedArraySupport_antitone_low hkl hln a
  have hn := logarithmicCappedArraySupport_nonneg n l a
  have h : Real.sqrt (W ^ 2 + logarithmicCappedArraySupport n l a ^ 2) ≤
      Real.sqrt (W ^ 2 + logarithmicCappedArraySupport n k a ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  exact sub_le_sub_left h _

/-- Ordered nonnegative physical weights change the kernel by at most added mass. -/
theorem logarithmicCappedArrayKernel_weight_bounds {n k : ℕ} (hk : k ≤ n)
    (a b : Bool → ℕ → ℝ) (W : ℝ)
    (ha : ∀ σ j, 0 ≤ a σ j) (hab : ∀ σ j, a σ j ≤ b σ j) :
    0 ≤ logarithmicCappedArrayKernel n k b W - logarithmicCappedArrayKernel n k a W ∧
      logarithmicCappedArrayKernel n k b W - logarithmicCappedArrayKernel n k a W ≤
        ∑ j ∈ Finset.range (n + 1), ((b false j - a false j) + (b true j - a true j)) := by
  let L (c : Bool → ℕ → ℝ) (σ : Bool) (p : ℕ) :=
    collarBlockSize (logarithmicCosetNodes k p) (c σ)
  let H (c : Bool → ℕ → ℝ) (σ : Bool) (p : ℕ) :=
    collarBlockSize (logarithmicHighCosetNodes n k p) (c σ)
  have hl (σ : Bool) (p : ℕ) := collarBlockSize_monotone_bounds
    (logarithmicCosetNodes k p) (a σ) (b σ) (fun j _ => ha σ j) (fun j _ => hab σ j)
  have hh (σ : Bool) (p : ℕ) := collarBlockSize_monotone_bounds
    (logarithmicHighCosetNodes n k p) (a σ) (b σ) (fun j _ => ha σ j) (fun j _ => hab σ j)
  have hz := cappedCosetSupport_weight_bounds (logarithmicOddCosets n) (L a) (H a) (L b) (H b)
    (fun _ _ _ => Real.sqrt_nonneg _) (fun σ p _ => sub_nonneg.mp (hl σ p).1)
    (fun σ p _ => sub_nonneg.mp (hh σ p).1)
  change 0 ≤ logarithmicCappedArraySupport n k b - logarithmicCappedArraySupport n k a ∧
    logarithmicCappedArraySupport n k b - logarithmicCappedArraySupport n k a ≤ _ at hz
  have htotal : (∑ σ : Bool, ∑ p ∈ logarithmicOddCosets n,
      ((L b σ p - L a σ p) + (H b σ p - H a σ p))) ≤
      ∑ j ∈ Finset.range (n + 1), ((b false j - a false j) + (b true j - a true j)) := by
    calc
      _ ≤ ∑ σ : Bool, ∑ p ∈ logarithmicOddCosets n,
          ((∑ j ∈ logarithmicCosetNodes k p, (b σ j - a σ j)) +
           (∑ j ∈ logarithmicHighCosetNodes n k p, (b σ j - a σ j))) :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun p _ => add_le_add (hl σ p).2 (hh σ p).2
      _ = _ := by
        simp_rw [sum_logarithmic_low_high hk]
        simp only [sum_logarithmicCosetNodes, Fintype.sum_bool, Finset.sum_add_distrib, add_comm]
  have hmass := hz.2.trans htotal
  have hr := cappedRadial_monotone_bounds W (logarithmicCappedArraySupport_nonneg n k a)
    (sub_nonneg.mp hz.1)
  simp only [logarithmicCappedArrayKernel, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hmass
  constructor <;> linarith [hr.1, hr.2]

theorem logarithmicCappedArrayKernel_mono_weights {n k : ℕ} (hk : k ≤ n)
    (a b : Bool → ℕ → ℝ) (W : ℝ)
    (ha : ∀ σ j, 0 ≤ a σ j) (hab : ∀ σ j, a σ j ≤ b σ j) :
    logarithmicCappedArrayKernel n k a W ≤ logarithmicCappedArrayKernel n k b W :=
  sub_nonneg.mp (logarithmicCappedArrayKernel_weight_bounds hk a b W ha hab).1

/-- The all-low endpoint agrees exactly with the previous paired sign geometry. -/
theorem logarithmicCappedArraySupport_all_low (n : ℕ) (a : Bool → ℕ → ℝ) :
    logarithmicCappedArraySupport n n a =
      Real.sqrt (logarithmicSignNorm n (a false) ^ 2 + logarithmicSignNorm n (a true) ^ 2) := by
  have hh : (fun σ p => collarBlockSize (logarithmicHighCosetNodes n n p) (a σ)) =
      (fun (_ : Bool) (_ : ℕ) => (0 : ℝ)) := by
    funext σ p
    simp only [logarithmicHighCosetNodes, Finset.sdiff_self, collarBlockSize,
      Finset.sum_empty, Real.sqrt_zero]
  unfold logarithmicCappedArraySupport
  rw [hh]
  exact cappedCosetSupport_zero_high (logarithmicOddCosets n)
    (fun σ p => collarBlockSize (logarithmicCosetNodes n p) (a σ))
    (fun _ _ _ => Real.sqrt_nonneg _)

theorem logarithmicCappedArrayKernel_all_low (n : ℕ) (a : Bool → ℕ → ℝ) (W : ℝ) :
    logarithmicCappedArrayKernel n n a W = logarithmicPairedArrayKernel n a W := by
  unfold logarithmicCappedArrayKernel logarithmicPairedArrayKernel
  rw [logarithmicCappedArraySupport_all_low,
    Real.sq_sqrt (by positivity : 0 ≤ logarithmicSignNorm n (a false) ^ 2 + logarithmicSignNorm n (a true) ^ 2)]
  simp only [add_assoc]

namespace PhysicalCollarPartition
variable {n : ℕ}

theorem cappedKernel_eq_array (ρ : PhysicalCollarPartition n) (k : ℕ) (y : ℝ) :
    ρ.cappedKernel k y = logarithmicCappedArrayKernel n k
      (fun σ j => ρ.weight σ j y) (archLevySinhWeight y) := rfl

theorem cappedKernel_all_low (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.cappedKernel n y = ρ.pairedKernel y := by
  rw [ρ.cappedKernel_eq_array, logarithmicCappedArrayKernel_all_low, ρ.pairedKernel_eq_array]

theorem cappedCoefficient_all_low (ρ : PhysicalCollarPartition n) :
    ρ.cappedCoefficient n = ρ.pairedCoefficient := by
  unfold cappedCoefficient pairedCoefficient
  congr 1
  funext y
  exact ρ.cappedKernel_all_low y

theorem cappedKernel_mono_low (ρ : PhysicalCollarPartition n) {k l : ℕ}
    (hkl : k ≤ l) (hln : l ≤ n) (y : ℝ) : ρ.cappedKernel k y ≤ ρ.cappedKernel l y := by
  rw [ρ.cappedKernel_eq_array, ρ.cappedKernel_eq_array]
  exact logarithmicCappedArrayKernel_mono_low hkl hln _ _

theorem cappedCoefficient_mono_low (ρ : PhysicalCollarPartition n) {k l : ℕ}
    (hkl : k ≤ l) (hln : l ≤ n) : ρ.cappedCoefficient k ≤ ρ.cappedCoefficient l :=
  integral_mono_ae (ρ.integrableOn_cappedKernel (hkl.trans hln)) (ρ.integrableOn_cappedKernel hln)
    (Filter.Eventually.of_forall (ρ.cappedKernel_mono_low hkl hln))

theorem cappedCoefficient_le_pairedCoefficient (ρ : PhysicalCollarPartition n) {k : ℕ}
    (hk : k ≤ n) : ρ.cappedCoefficient k ≤ ρ.pairedCoefficient := by
  rw [← ρ.cappedCoefficient_all_low]
  exact ρ.cappedCoefficient_mono_low hk le_rfl

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
