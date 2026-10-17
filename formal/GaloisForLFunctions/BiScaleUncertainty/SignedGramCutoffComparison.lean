import GaloisForLFunctions.BiScaleUncertainty.SignedGramCapacity
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarCutoffStability

/-!
# Physical cutoff comparison with all signed Gram entries retained

Actual partition extension increases the measured Gram certificate. Retraction
loses at most twice the source norm squared times the physical retention tail.
The Gram capacity theorem controls cross entries, without any locality or
orthogonality assumption on the source's correlations.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n m : ℕ}

def signedGramArrayKernel (n : ℕ) (f : C_c(ℝ, ℝ)) (a : Bool → ℕ → ℝ) (W : ℝ) : ℝ :=
  AnchoredGram.kernel f (signedGramNodes n) (fun p => a p.1 p.2) signedGramShift W

theorem signedGramNodes_subset (hm : n ≤ m) : signedGramNodes n ⊆ signedGramNodes m := by
  intro p hp
  have hk := Finset.mem_range.mp (Finset.mem_product.mp hp).2
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩

theorem signedGramArrayKernel_pad (hm : n ≤ m) (f : C_c(ℝ, ℝ))
    (a : Bool → ℕ → ℝ) (W : ℝ) :
    signedGramArrayKernel m f (collarArrayPad n a) W = signedGramArrayKernel n f a W := by
  apply AnchoredGram.kernel_subset f (signedGramNodes_subset hm)
  · intro p hp
    exact (if_pos (Finset.mem_range.mp (Finset.mem_product.mp hp).2)).symm
  · intro p _ hp
    have hk : ¬p.2 < n + 1 := by simpa [signedGramNodes] using hp
    exact if_neg hk

theorem signedGramKernel_eq_array (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ρ.signedGramKernel f y =
      signedGramArrayKernel n f (fun σ k => ρ.weight σ k y) (archLevySinhWeight y) := rfl

theorem signedGramKernel_le_extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m)
    (f : C_c(ℝ, ℝ)) (y : ℝ) : ρ.signedGramKernel f y ≤ (ρ.extend hm).signedGramKernel f y := by
  rw [ρ.signedGramKernel_eq_array, (ρ.extend hm).signedGramKernel_eq_array,
    ← signedGramArrayKernel_pad hm]
  apply AnchoredGram.kernel_mono
  exact fun p _ => ρ.pad_weight_le_extend hm p.1 p.2 y

theorem signedGramCoefficient_le_extend (ρ : PhysicalCollarPartition n) (hm : n ≤ m)
    (f : C_c(ℝ, ℝ)) : ρ.signedGramCoefficient f ≤ (ρ.extend hm).signedGramCoefficient f :=
  integral_mono_ae (ρ.integrableOn_signedGramKernel f) ((ρ.extend hm).integrableOn_signedGramKernel f)
    (Filter.Eventually.of_forall (ρ.signedGramKernel_le_extend hm f))

theorem signedGramKernel_sub_retract_le_retentionFibre (η : PhysicalCollarPartition m)
    (hm : n ≤ m) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    η.signedGramKernel f y - (η.retract hm).signedGramKernel f y ≤
      2 * autocorr f 0 * η.retentionFibre n y := by
  let a := collarArrayPad n (fun σ k => (η.retract hm).weight σ k y)
  let e := fun σ k => η.weight σ k y *
    collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y)
  have ha (σ : Bool) (k : ℕ) : 0 ≤ a σ k := by
    dsimp [a, collarArrayPad]
    split_ifs
    · exact (η.retract hm).weight_nonneg σ k y
    · exact le_rfl
  have he (σ : Bool) (k : ℕ) : 0 ≤ e σ k :=
    mul_nonneg (η.weight_nonneg σ k y) (collarRetentionPrice_bounds n _).1
  have hab (σ : Bool) (k : ℕ) : η.weight σ k y ≤ a σ k + e σ k := by
    by_cases hx : logarithmicCollarNode k + collarSignedOffset σ y < logarithmicCollarRetention n
    · have heq : a σ k = η.weight σ k y := η.pad_retract_weight_eq hm σ k y hx
      rw [heq]
      exact le_add_of_nonneg_right (he σ k)
    · have hp : collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y) = 1 :=
        indicator_of_mem (show logarithmicCollarNode k + collarSignedOffset σ y ∈
          Ici (logarithmicCollarRetention n) from le_of_not_gt hx) (fun _ => (1 : ℝ))
      dsimp only [e]
      rw [hp, mul_one]
      exact le_add_of_nonneg_left (ha σ k)
  have h := AnchoredGram.kernel_error_bound f (signedGramNodes m)
    (fun p => a p.1 p.2) (fun p => η.weight p.1 p.2 y) (fun p => e p.1 p.2)
    signedGramShift (archLevySinhWeight y) (fun p _ => he p.1 p.2) (fun p _ => hab p.1 p.2)
  change signedGramArrayKernel m f (fun σ k => η.weight σ k y) (archLevySinhWeight y) -
    signedGramArrayKernel m f a (archLevySinhWeight y) ≤ _ at h
  dsimp only [a] at h
  rw [signedGramArrayKernel_pad hm] at h
  rw [η.signedGramKernel_eq_array, (η.retract hm).signedGramKernel_eq_array]
  have hs : (∑ p ∈ signedGramNodes m, e p.1 p.2) = η.retentionFibre n y := by
    simp [signedGramNodes, Finset.sum_product, e, retentionFibre, collarSignedOffset,
      Finset.sum_add_distrib, sub_eq_add_neg, add_comm]
  rwa [hs] at h

/-- A concrete repaired partition loses at most twice source energy times the unprotected tail. -/
theorem signedGramCoefficient_sub_retract_le_tail (η : PhysicalCollarPartition m)
    (hm : n ≤ m) (f : C_c(ℝ, ℝ)) :
    η.signedGramCoefficient f - (η.retract hm).signedGramCoefficient f ≤
      2 * autocorr f 0 * collarCutoffTailMass n := by
  have h := integral_mono_ae
    ((η.integrableOn_signedGramKernel f).sub ((η.retract hm).integrableOn_signedGramKernel f))
    ((η.integrableOn_retentionFibre n).const_mul (2 * autocorr f 0))
    (Filter.Eventually.of_forall (η.signedGramKernel_sub_retract_le_retentionFibre hm f))
  change (∫ y in Ioo 0 logarithmicCollarRadius,
    η.signedGramKernel f y - (η.retract hm).signedGramKernel f y) ≤
      ∫ y in Ioo 0 logarithmicCollarRadius, 2 * autocorr f 0 * η.retentionFibre n y at h
  rw [integral_sub (η.integrableOn_signedGramKernel f)
    ((η.retract hm).integrableOn_signedGramKernel f), integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (η.integral_retentionFibre_le_tail n)
    (mul_nonneg (by norm_num) (autocorr_zero_nonneg f)))

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
