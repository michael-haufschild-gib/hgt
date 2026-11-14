import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxIntegerResiduals
import GaloisForLFunctions.RHTower.Sieve.VinogradovPowerSumRigidity

/-!
# Uniform Gamma–Cox detection of Vinogradov diagonal tuples

The integer sum of squared power-sum discrepancies vanishes exactly when two
natural-number tuples agree as multisets. Integrality gives uniform recovery
even for tuples with unbounded, arbitrarily moving entries.
-/

open Filter Topology Finset
open scoped BigOperators Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace RHTower.Sieve
noncomputable section

/-- Integer energy of the moment discrepancies through the tuple length. -/
def vinogradovIntegerEnergy {b : ℕ} (x y : Fin b → ℕ) : ℤ :=
  ∑ j ∈ range (b + 1), ((∑ i, (x i : ℤ) ^ j) - ∑ i, (y i : ℤ) ^ j) ^ 2

/-- Zero integer energy is exactly the diagonal multiset relation. -/
theorem vinogradovIntegerEnergy_zero_iff {b : ℕ} (x y : Fin b → ℕ) :
    vinogradovIntegerEnergy x y = 0 ↔ univ.val.map x = univ.val.map y := by
  constructor
  · intro h
    apply nat_multiset_eq_of_powerSums_eq x y
    intro j _ hj
    have hz := (sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ((∑ i, (x i : ℤ) ^ j) - ∑ i, (y i : ℤ) ^ j))).mp h j
      (mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    have hp := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    exact_mod_cast hp
  · intro h
    apply sum_eq_zero
    intro j _
    have hm := congrArg
      (fun M : Multiset ℕ => (M.map fun (n : ℕ) => (n : ℤ) ^ j).sum) h
    have he : (∑ i, (x i : ℤ) ^ j) = ∑ i, (y i : ℤ) ^ j := by
      simpa [Multiset.map_map, Function.comp_def] using hm
    simp only [he, sub_self, zero_pow two_ne_zero]

/-- Moment-energy detection recognizes equality up to permutation, including repeated entries. -/
theorem cox_vinogradov_diagonal {b : ℕ} (x y : Fin b → ℕ) :
    Tendsto (fun K => detection K (vinogradovIntegerEnergy x y : ℝ)) atTop
      (𝓝 (if univ.val.map x = univ.val.map y then 1 else 0)) := by
  simpa only [Int.cast_eq_zero, vinogradovIntegerEnergy_zero_iff] using
    tendsto_detection (vinogradovIntegerEnergy x y : ℝ)

/-- Tuples may change arbitrarily with concentration; no entry bound is needed. -/
theorem cox_moving_vinogradov_diagonal {ι : Type*} [Fintype ι] {b : ℕ}
    (x y : ℝ → ι → Fin b → ℕ) :
    Tendsto (fun K => (binaryLaw K
      (fun i => (vinogradovIntegerEnergy (x K i) (y K i) : ℝ))).real
      {d | d ≠ fun i => decide (univ.val.map (x K i) = univ.val.map (y K i))})
      atTop (𝓝 0) := by
  exact tendsto_moving_integer_classification
    (fun K i => vinogradovIntegerEnergy (x K i) (y K i))
    (fun K i => univ.val.map (x K i) = univ.val.map (y K i))
    (fun K i => vinogradovIntegerEnergy_zero_iff (x K i) (y K i))

end
end RHTower.Sieve

#print axioms RHTower.Sieve.vinogradovIntegerEnergy_zero_iff
#print axioms RHTower.Sieve.cox_vinogradov_diagonal
#print axioms RHTower.Sieve.cox_moving_vinogradov_diagonal
