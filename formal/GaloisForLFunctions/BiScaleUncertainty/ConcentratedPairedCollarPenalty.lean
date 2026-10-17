import GaloisForLFunctions.BiScaleUncertainty.PairedArrayRadialGeometry
import GaloisForLFunctions.BiScaleUncertainty.ConcentratedCollarRetraction

/-!
# Paired radial cost of actual concentrated cutoff changes

The added tail and the repaired old window are actual physical partitions.
Their radial penalty increments are uniformly bounded on intervals of widths
1/N and 2/N, respectively. The two whole-sign norms remain coupled in the Euclidean radial norm.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
namespace PhysicalCollarPartition
variable {n m : ℕ}

theorem concentratedExtend_pairedPenalty_le (ρ : PhysicalCollarPartition n) (hm : n ≤ m)
    (hn : 6 ≤ n) {y : ℝ} (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    (ρ.concentratedExtend hm).pairedRadialPenalty y - ρ.pairedRadialPenalty y ≤
      if y ≤ 1 / ((n + 2 : ℕ) : ℝ) then 8192 else 0 := by
  let e : Bool → ℕ → ℝ := fun σ k => rightTailWeight m n σ k y
  let A := ρ.pairedBlockNorm y
  let B := (ρ.concentratedExtend hm).pairedBlockNorm y
  let G := logarithmicArrayMass m e
  have hA : 0 ≤ A := ρ.pairedBlockNorm_nonneg y
  have hB : 0 ≤ B := (ρ.concentratedExtend hm).pairedBlockNorm_nonneg y
  have hG : 0 ≤ G := logarithmicArrayMass_nonneg m e
    (fun σ k => rightTailWeight_nonneg m n σ k y)
  have hBG : B ≤ A + G := by
    have h := logarithmicPairedArrayNorm_le_add_mass m
      (collarArrayPad n (fun σ k => ρ.weight σ k y))
      (fun σ k => (ρ.concentratedExtend hm).weight σ k y) e
      (by
        intro σ k
        unfold collarArrayPad
        split_ifs
        · exact ρ.weight_nonneg σ k y
        · exact le_rfl)
      (fun σ k => (ρ.concentratedExtend hm).weight_nonneg σ k y)
      (fun σ k => rightTailWeight_nonneg m n σ k y)
      (fun σ k => (ρ.concentratedExtend_weight hm σ k y).le)
    rw [logarithmicPairedArrayNorm_pad hm] at h
    exact h
  by_cases hyr : y ≤ 1 / ((n + 2 : ℕ) : ℝ)
  · rw [if_pos hyr]
    have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hNy : ((n + 2 : ℕ) : ℝ) * y ≤ 1 := by
      have h := (le_div_iff₀ hN).mp hyr
      nlinarith
    have hy1 : y ≤ 1 := by
      have hN1 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ n + 2 by omega)
      nlinarith [mul_nonneg hy.1.le (sub_nonneg.mpr hN1)]
    have hGs : G ≤ 64 / Real.sqrt y := by
      apply logarithmicArrayMass_le_inverse_sqrt_offset m e hy.1 hy1
      · intro σ k hk
        exact (rightTailWeight_le m n σ k y).trans
          ((rightNode m).weight_le_inverse_sqrt k hk σ hy)
      · intro σ k _ hk
        exact (rightTailWeight_nonzero hn hy.1 hk).2.1
    have hGy : G * Real.sqrt y ≤ 64 :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hy.1)).mp hGs
    have hroot : Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.sqrt y ≤ 1 := by
      rw [← Real.sqrt_mul hN.le]
      exact Real.sqrt_le_iff.mpr ⟨zero_le_one, by simpa only [one_pow] using hNy⟩
    have hAy : A * Real.sqrt y ≤ 32 := by
      have h := mul_le_mul_of_nonneg_right (ρ.pairedBlockNorm_le_sqrt_cutoff hy) (Real.sqrt_nonneg y)
      nlinarith
    have h := collarRadialPenalty_increment_scaled (archLevySinhWeight_pos hy.1)
      hA hB hG hBG hy.1.le (one_le_two_mul_offset_weight hy)
      (by norm_num : (0 : ℝ) ≤ 32) (by norm_num : (0 : ℝ) ≤ 64) hAy hGy
    norm_num at h
    change collarRadialPenalty (archLevySinhWeight y) B -
      collarRadialPenalty (archLevySinhWeight y) A ≤ 8192
    linarith
  · rw [if_neg hyr]
    have hz : G = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp only [e, rightTailWeight_zero_above_mesh hn (lt_of_not_ge hyr), add_zero]
    rw [hz, add_zero] at hBG
    exact sub_nonpos.mpr (collarRadialPenalty_mono hB hBG)

theorem concentratedRetract_pairedPenalty_le (η : PhysicalCollarPartition m) (hm : n ≤ m)
    (hn : 6 ≤ n) {y : ℝ} (hy : y ∈ Ioo 0 logarithmicCollarRadius) :
    (η.concentratedRetract hm).pairedRadialPenalty y - η.pairedRadialPenalty y ≤
      if y ≤ 2 / ((n + 2 : ℕ) : ℝ) then 6144 else 0 := by
  let a : Bool → ℕ → ℝ := fun σ k => η.weight σ k y
  let e : Bool → ℕ → ℝ := fun σ k => η.rightRepairWeight n σ k y
  let A := logarithmicPairedArrayNorm n a
  let B := (η.concentratedRetract hm).pairedBlockNorm y
  let G := logarithmicArrayMass n e
  have hA : 0 ≤ A := logarithmicPairedArrayNorm_nonneg n a
  have hB : 0 ≤ B := (η.concentratedRetract hm).pairedBlockNorm_nonneg y
  have hG : 0 ≤ G := logarithmicArrayMass_nonneg n e
    (fun σ k => η.rightRepairWeight_nonneg hm σ k y)
  have hBG : B ≤ A + G :=
    logarithmicPairedArrayNorm_le_add_mass n a
      (fun σ k => (η.concentratedRetract hm).weight σ k y) e
      (fun σ k => η.weight_nonneg σ k y)
      (fun σ k => (η.concentratedRetract hm).weight_nonneg σ k y)
      (fun σ k => η.rightRepairWeight_nonneg hm σ k y)
      (fun σ k => η.concentratedRetract_weight_le hm σ k y)
  have hAold : A ≤ η.pairedBlockNorm y := by
    rw [show A = logarithmicPairedArrayNorm m (collarArrayPad n a) from
      (logarithmicPairedArrayNorm_pad hm a).symm]
    change logarithmicPairedArrayNorm m (collarArrayPad n a) ≤ logarithmicPairedArrayNorm m a
    apply logarithmicPairedArrayNorm_mono m _ a
    · intro σ k
      unfold collarArrayPad
      split_ifs
      · exact η.weight_nonneg σ k y
      · exact le_rfl
    · intro σ k
      unfold collarArrayPad
      split_ifs
      · exact le_rfl
      · exact η.weight_nonneg σ k y
  have hrad := collarRadialPenalty_mono (W := archLevySinhWeight y) hA hAold
  by_cases hyr : y ≤ 2 / ((n + 2 : ℕ) : ℝ)
  · rw [if_pos hyr]
    have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hNy : ((n + 2 : ℕ) : ℝ) * y ≤ 2 := by
      have h := (le_div_iff₀ hN).mp hyr
      nlinarith
    have hAmax : A ≤ 32 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
      refine (logarithmicPairedArrayNorm_le_mass n a (fun σ k => η.weight_nonneg σ k y)).trans ?_
      apply logarithmicArrayMass_le_sqrt_cutoff
      intro σ k hk
      exact η.weight_le_inverse_sqrt k
        (Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)) σ hy
    have hGmax : G ≤ 32 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
      have hmass : G ≤ (rightNode n).mass y := by
        apply Finset.sum_le_sum
        intro k _
        exact add_le_add (η.rightRepairWeight_le n false k y) (η.rightRepairWeight_le n true k y)
      exact hmass.trans ((rightNode n).mass_le_sqrt_cutoff hy)
    have hprod := mul_le_mul hAmax hGmax hG (by positivity)
    have hsq := mul_le_mul hGmax hGmax hG (by positivity)
    have hNN : (32 * Real.sqrt ((n + 2 : ℕ) : ℝ)) *
        (32 * Real.sqrt ((n + 2 : ℕ) : ℝ)) = 1024 * ((n + 2 : ℕ) : ℝ) := by
      nlinarith [Real.sq_sqrt hN.le]
    rw [hNN] at hprod hsq
    have hpoly : 2 * A * G + G ^ 2 ≤ 3072 * ((n + 2 : ℕ) : ℝ) := by nlinarith
    have hmult := mul_le_mul_of_nonneg_left hpoly hy.1.le
    have hinc := collarRadialPenalty_increment_offset (archLevySinhWeight_pos hy.1)
      hA hB hG hBG hy.1.le (one_le_two_mul_offset_weight hy)
    change collarRadialPenalty (archLevySinhWeight y) B -
      collarRadialPenalty (archLevySinhWeight y) (η.pairedBlockNorm y) ≤ _
    nlinarith
  · rw [if_neg hyr]
    have hz : G = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [e, η.rightRepairWeight_zero_above_mesh hm hk hn (lt_of_not_ge hyr), add_zero]
    rw [hz, add_zero] at hBG
    have h := collarRadialPenalty_mono (W := archLevySinhWeight y) hB hBG
    change collarRadialPenalty (archLevySinhWeight y) B -
      collarRadialPenalty (archLevySinhWeight y) (η.pairedBlockNorm y) ≤ _
    linarith

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
