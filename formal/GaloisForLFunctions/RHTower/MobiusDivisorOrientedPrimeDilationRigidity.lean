import GaloisForLFunctions.RHTower.MobiusDivisorOrientedPrimeDilationRenormalization

/-!
# Finite detector rigidity for CCM-FU prime-dilation cancellation

At a fresh prime dilation, every oriented residual coordinate is its literal
large-cutoff `p`-free background minus a square-root-amplified old coordinate.
This file proves that a finite positive weighted detector cannot make those
coordinates cancel each other: zero post-insertion detector energy forces the
background/copy equality separately at every observed residual label.

Thus a prospective CCM-FU budget cannot repay inherited covariance by aggregate
cross-label cancellation.  It must establish simultaneous pointwise matching on
every residual label measured by its detector.
-/

noncomputable section

open Finset

namespace RHTower

/-- Finite positive-weighted energy of oriented residual source coordinates. -/
def mobiusDivisorOrientedResidualEnergy
    (M : ℕ) (P : Finset ℕ) (T : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) : ℝ :=
  ∑ R ∈ T, w R * (mobiusDivisorOrientedFibre M P R) ^ (2 : ℕ)

/-- The post-insertion residual energy is exactly the detector energy of the
background-minus-copy coordinates. -/
theorem mobiusDivisorOrientedResidualEnergy_insert_mul_prime_eq_sum_sq
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P : Finset ℕ) (T : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) (hpP : p ∉ P)
    (hpT : ∀ R ∈ T, p ∉ R) :
    mobiusDivisorOrientedResidualEnergy (p * N) (insert p P) T w =
      ∑ R ∈ T, w R *
        (mobiusDivisorOrientedFibre (p * N) P R -
          Real.sqrt p * mobiusDivisorOrientedFibre N P R) ^ (2 : ℕ) := by
  unfold mobiusDivisorOrientedResidualEnergy
  apply Finset.sum_congr rfl
  intro R hR
  rw [mobiusDivisorOrientedFibre_insert_mul_prime_renormalization
    hp hNp P R hpP (hpT R hR)]

/-- **Detector rigidity.** If a finite positive weighted residual detector has
zero post-insertion energy, every residual coordinate observed by that detector
has exact background/copy cancellation. -/
theorem mobiusDivisorOrientedResidualEnergy_insert_mul_prime_eq_zero_rigid
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P : Finset ℕ) (T : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) (hpP : p ∉ P)
    (hpT : ∀ R ∈ T, p ∉ R) (hw : ∀ R ∈ T, 0 < w R)
    (hzero : mobiusDivisorOrientedResidualEnergy (p * N) (insert p P) T w = 0) :
    ∀ R ∈ T,
      mobiusDivisorOrientedFibre (p * N) P R =
        Real.sqrt p * mobiusDivisorOrientedFibre N P R := by
  have hnonneg : ∀ R ∈ T,
      0 ≤ w R * (mobiusDivisorOrientedFibre (p * N) (insert p P) R) ^ (2 : ℕ) := by
    intro R hR
    exact mul_nonneg (le_of_lt (hw R hR)) (sq_nonneg _)
  have hsum : ∀ R ∈ T,
      w R * (mobiusDivisorOrientedFibre (p * N) (insert p P) R) ^ (2 : ℕ) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
    simpa only [mobiusDivisorOrientedResidualEnergy] using hzero
  intro R hR
  have hterm := hsum R hR
  have hnew : mobiusDivisorOrientedFibre (p * N) (insert p P) R = 0 := by
    rcases mul_eq_zero.mp hterm with hw0 | hsquare
    · exact False.elim ((ne_of_gt (hw R hR)) hw0)
    · exact sq_eq_zero_iff.mp hsquare
  exact (mobiusDivisorOrientedFibre_insert_mul_prime_eq_zero_iff_background_eq_copy
    hp hNp P R hpP (hpT R hR)).mp hnew

end RHTower
