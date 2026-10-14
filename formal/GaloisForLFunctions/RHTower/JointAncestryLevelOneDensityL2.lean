import GaloisForLFunctions.RHTower.JointAncestryLevelOneSectorL2
import GaloisForLFunctions.RHTower.JointAncestryKroneckerLineCriterion
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery

/-! # The literal signed level-one JAS density in L²

The unconditional strip-width budget makes the actual complex zero-weighted
sector series absolutely summable in L². Its finite-prime approximations agree
almost everywhere with the native `jasZeroSumDensity` and converge in L².
-/

namespace RHTower

open MeasureTheory Filter GaloisForLFunctions.HTGeometry
open scoped BigOperators Topology

noncomputable section

def jasLevelOneSectorLimit (q : XiZeroCopy) : Lp ℂ 2 (torusHaar Nat.Primes) :=
  (exists_jasLevelOneSectorLp_limit q).choose

theorem tendsto_jasLevelOneSectorLp (q : XiZeroCopy) :
    Tendsto (fun N => jasLevelOneSectorLp q (jasPrimePrefix N)) atTop
      (𝓝 (jasLevelOneSectorLimit q)) :=
  (exists_jasLevelOneSectorLp_limit q).choose_spec.1

theorem norm_jasLevelOneSectorLimit_le (q : XiZeroCopy) :
    ‖jasLevelOneSectorLimit q‖ ≤ jasSectorNormBudget q :=
  (exists_jasLevelOneSectorLp_limit q).choose_spec.2

theorem summable_norm_lagWeight_smul_jasLevelOneSectorLimit :
    Summable fun q : XiZeroCopy => ‖lagWeight q • jasLevelOneSectorLimit q‖ := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (f := fun q => ‖lagWeight q‖ * jasSectorNormBudget q)
  · intro q
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_jasLevelOneSectorLimit_le q) (norm_nonneg _)
  · exact summable_lagWeight_mul_jasSectorNormBudget

theorem summable_norm_lagWeight_smul_jasLevelOneSectorLp (P : Finset Nat.Primes) :
    Summable fun q : XiZeroCopy => ‖lagWeight q • jasLevelOneSectorLp q P‖ := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (f := fun q => ‖lagWeight q‖ * jasSectorNormBudget q)
  · intro q
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_jasLevelOneSectorLp_le q P) (norm_nonneg _)
  · exact summable_lagWeight_mul_jasSectorNormBudget

def jasLevelOneDensity : Lp ℂ 2 (torusHaar Nat.Primes) :=
  ∑' q : XiZeroCopy, lagWeight q • jasLevelOneSectorLimit q

def jasLevelOneFiniteDensity (P : Finset Nat.Primes) : Lp ℂ 2 (torusHaar Nat.Primes) :=
  ∑' q : XiZeroCopy, lagWeight q • jasLevelOneSectorLp q P

theorem tendsto_jasLevelOneFiniteDensity :
    Tendsto (fun N => jasLevelOneFiniteDensity (jasPrimePrefix N)) atTop
      (𝓝 jasLevelOneDensity) := by
  simpa only [jasLevelOneFiniteDensity, jasLevelOneDensity] using
    (tendsto_tsum_of_dominated_convergence summable_lagWeight_mul_jasSectorNormBudget
      (fun q => (tendsto_jasLevelOneSectorLp q).const_smul (lagWeight q))
      (Eventually.of_forall fun N q => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (norm_jasLevelOneSectorLp_le q (jasPrimePrefix N)) (norm_nonneg _)))

theorem coeFn_jasLevelOneFiniteDensity (P : Finset Nat.Primes) :
    jasLevelOneFiniteDensity P =ᵐ[torusHaar Nat.Primes]
      fun x => jasZeroSumDensity (1 / 2) P (fun i => fourier 1 (x i)) := by
  have hsum := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr
    (summable_norm_lagWeight_smul_jasLevelOneSectorLp P))
  have hterms : ∀ᵐ x ∂torusHaar Nat.Primes, ∀ q : XiZeroCopy,
      (lagWeight q • jasLevelOneSectorLp q P : Lp ℂ 2 (torusHaar Nat.Primes)) x =
        lagWeight q * ∏ p ∈ P, jasLevelOneCircle q p (x p) := by
    rw [ae_all_iff]
    intro q
    filter_upwards [Lp.coeFn_smul (lagWeight q) (jasLevelOneSectorLp q P),
      coeFn_torusFiniteProductLp (jasLevelOneCircle q) P] with x hs hp
    change _ = lagWeight q * _ at hs
    rw [hs]
    change lagWeight q * torusFiniteProductLp (jasLevelOneCircle q) P x = _
    rw [hp]
    rfl
  filter_upwards [hsum, hterms] with x hs hx
  change (∑' q : XiZeroCopy, lagWeight q • jasLevelOneSectorLp q P) x = _
  rw [hs]
  unfold jasZeroSumDensity
  apply tsum_congr
  intro q
  rw [hx q]
  unfold lagWeight
  congr 1
  exact (Finset.prod_attach P (fun p => jasLevelOneCircle q p (x p))).symm

theorem memLp_jasZeroSumDensity_levelOne (P : Finset Nat.Primes) :
    MemLp (fun x : UnitAddTorus Nat.Primes =>
      jasZeroSumDensity (1 / 2) P (fun i => fourier 1 (x i))) 2 (torusHaar Nat.Primes) :=
  (Lp.memLp (jasLevelOneFiniteDensity P)).ae_eq (coeFn_jasLevelOneFiniteDensity P)

end

end RHTower
