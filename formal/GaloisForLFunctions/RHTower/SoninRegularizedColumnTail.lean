import GaloisForLFunctions.RHTower.SoninRegularizedNuclearBudget
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection

/-!
# Exact prime-labelled Hilbert--Schmidt tail of the common-source Sonin column

Source coefficients and prime/depth labels are not changed. No Xi or RH premise is used.
This module does not assert a determinant weld or an RH conclusion.
-/

open ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

theorem soninAllPrimeColumnTail_eq_sourceProjection
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    soninAllPrimeColumnOperator a ha - soninAllPrimeColumnFiniteHead a s =
      GaloisForLFunctions.HTGeometry.lpCoordinateProjection
        {z : SoninAllPrimeIndex | z.1 ∉ s} ∘L soninAllPrimeColumnOperator a ha := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext z
  rcases z with ⟨pk, i⟩
  by_cases h : pk ∈ s <;>
    simp [sub_apply, soninAllPrimeColumnFiniteHead_apply,
      soninAllPrimeColumnOperator_apply,
      GaloisForLFunctions.HTGeometry.lpCoordinateProjection_apply,
      Set.indicator, h]

theorem soninAllPrimeColumnTail_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    IsHilbertSchmidt
      (soninAllPrimeColumnOperator a ha - soninAllPrimeColumnFiniteHead a s) := by
  rw [soninAllPrimeColumnTail_eq_sourceProjection]
  exact (soninAllPrimeColumnOperator_isHilbertSchmidt a ha).comp_left _

set_option maxHeartbeats 1500000 in
theorem hsNormSq_soninAllPrimeColumnTail_eq_blockTail
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    hsNormSq (soninAllPrimeColumnOperator a ha - soninAllPrimeColumnFiniteHead a s) =
      ∑' pk : Nat.Primes × ℕ, if pk ∈ s then 0 else
        hsNormSq (centralSoninWeightedPrimePowerResidual a pk) := by
  classical
  let b := ContinuousLinearMap.hsBasis ℂ SoninL2
  let T := soninAllPrimeColumnOperator a ha - soninAllPrimeColumnFiniteHead a s
  let F : (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) → ℝ :=
    fun z => if z.1 ∈ s then 0 else
      ‖inner ℂ (b z.2.2) (centralSoninWeightedPrimePowerResidual a z.1 (b z.2.1))‖ ^ (2 : ℕ)
  have hF : Summable F := by
    apply (summable_all_prime_residual_matrix_entries a ha).of_nonneg_of_le
    · intro z
      dsimp [F]
      split_ifs <;> positivity
    · intro z
      dsimp [F, b]
      split_ifs <;> simp
  let e : (SoninHilbertIndex × SoninAllPrimeIndex) ≃
      (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) :=
    { toFun := fun z => (z.2.1, (z.1, z.2.2))
      invFun := fun z => (z.2.1, (z.1, z.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hG : Summable (fun z => F (e z)) := e.summable_iff.mpr hF
  rw [hsNormSq_eq (soninAllPrimeColumnTail_isHilbertSchmidt a ha s) b]
  change (∑' j, ‖T (b j)‖ ^ (2 : ℕ)) = _
  calc
    _ = ∑' j, ∑' z : SoninAllPrimeIndex, F (e (j, z)) := by
      apply tsum_congr
      intro j
      rw [HilbertSchmidt.lp_norm_sq_eq]
      apply tsum_congr
      rintro ⟨pk, i⟩
      by_cases h : pk ∈ s <;>
        simp [T, F, e, b, sub_apply, soninAllPrimeColumnOperator_apply,
          soninAllPrimeColumnFiniteHead_apply, h]
    _ = ∑' z, F (e z) := hG.tsum_prod.symm
    _ = ∑' z, F z := e.tsum_eq F
    _ = ∑' pk, ∑' ji, F (pk, ji) := hF.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro pk
      by_cases h : pk ∈ s
      · simp [F, h]
      · rw [if_neg h]
        have hpk : Summable (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
            F (pk, ji)) := hF.comp_injective (fun _ _ hh => (Prod.mk.inj hh).2)
        rw [hpk.tsum_prod, hsNormSq_eq
          (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk) b]
        apply tsum_congr
        intro j
        simpa [F, h] using tsum_sq_norm_inner_hilbertBasis b
          (centralSoninWeightedPrimePowerResidual a pk (b j))

theorem hsNormSq_soninAllPrimeColumnTail_le_coefficientTail
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    hsNormSq (soninAllPrimeColumnOperator a ha - soninAllPrimeColumnFiniteHead a s) ≤
      (128 * a ^ (2 : ℕ)) * ∑' pk : Nat.Primes × ℕ,
        if pk ∈ s then 0 else ‖soninLogPrimePowerCoefficient pk‖ ^ (2 : ℕ) := by
  classical
  rw [hsNormSq_soninAllPrimeColumnTail_eq_blockTail, ← tsum_mul_left]
  have hs := (summable_centralSoninWeightedPrimePowerResidual_hsNormSq a ha).indicator
    {pk | pk ∉ s}
  have ht := (summable_norm_soninLogPrimePowerCoefficient_sq.indicator
    {pk | pk ∉ s}).mul_left (128 * a ^ (2 : ℕ))
  have hs' : Summable (fun pk : Nat.Primes × ℕ => if pk ∈ s then 0 else
      hsNormSq (centralSoninWeightedPrimePowerResidual a pk)) := by
    apply hs.congr
    intro pk
    by_cases h : pk ∈ s <;> simp [Set.indicator, h]
  have ht' : Summable (fun pk : Nat.Primes × ℕ => (128 * a ^ (2 : ℕ)) *
      (if pk ∈ s then 0 else ‖soninLogPrimePowerCoefficient pk‖ ^ (2 : ℕ))) := by
    apply ht.congr
    intro pk
    by_cases h : pk ∈ s <;> simp [Set.indicator, h]
  apply Summable.tsum_le_tsum _ hs' ht'
  intro pk
  by_cases h : pk ∈ s
  · simp [h]
  · simpa [h] using centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq a ha pk

end
end RHTower

