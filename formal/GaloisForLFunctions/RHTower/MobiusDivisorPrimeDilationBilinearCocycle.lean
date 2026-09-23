import GaloisForLFunctions.RHTower.MobiusDivisorOrientedPrimeDilationRenormalization

/-!
# Prime dilation of the residual covariance kernel

The changing-core charge is off-diagonal covariance, not diagonal energy.
For every finite residual kernel this file retains the two directed
background/copy cross terms under a fresh processed dilation.  Consequently
any cumulative CCM-FU payment law has to control this signed Gram cross
kernel; no diagonal observer can replace it.
-/

noncomputable section
open Finset
namespace RHTower

/-- A finite directed bilinear observer of two oriented residual fields. -/
def mobiusDivisorOrientedResidualBilinear
    (M N : ℕ) (P : Finset ℕ) (T U : Finset (Finset ℕ))
    (w : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ R ∈ T, ∑ S ∈ U,
    w R S * mobiusDivisorOrientedFibre M P R *
      mobiusDivisorOrientedFibre N P S

private lemma bilinear_affine_compose (w a b c d r p : ℝ) (hr : r * r = p) :
    w * (a - r * b) * (c - r * d) =
      w * a * c + p * (w * b * d) - r * (w * a * d) - r * (w * b * c) := by
  calc
    _ = w * a * c + (r * r) * (w * b * d) - r * (w * a * d) - r * (w * b * c) := by ring
    _ = _ := by rw [hr]

/-- **Directed residual Gram cocycle.** Processing a fresh prime transforms
every finite residual covariance into its large-cutoff background covariance,
its amplified inherited covariance, and both literal directed background/copy
cross covariances. -/
theorem mobiusDivisorOrientedResidualBilinear_insert_mul_prime
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P : Finset ℕ) (T U : Finset (Finset ℕ))
    (w : Finset ℕ → Finset ℕ → ℝ)
    (hpP : p ∉ P)
    (hpT : ∀ R ∈ T, p ∉ R) (hpU : ∀ S ∈ U, p ∉ S) :
    mobiusDivisorOrientedResidualBilinear (p * N) (p * N) (insert p P) T U w =
      mobiusDivisorOrientedResidualBilinear (p * N) (p * N) P T U w +
        (p : ℝ) * mobiusDivisorOrientedResidualBilinear N N P T U w -
          Real.sqrt p * mobiusDivisorOrientedResidualBilinear (p * N) N P T U w -
            Real.sqrt p * mobiusDivisorOrientedResidualBilinear N (p * N) P T U w := by
  have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt p = p :=
    Real.mul_self_sqrt (Nat.cast_nonneg p)
  unfold mobiusDivisorOrientedResidualBilinear
  rw [mul_sum, mul_sum, mul_sum]
  simp_rw [mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro R hR
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro S hS
  rw [mobiusDivisorOrientedFibre_insert_mul_prime_renormalization
      hp hNp P R hpP (hpT R hR),
    mobiusDivisorOrientedFibre_insert_mul_prime_renormalization
      hp hNp P S hpP (hpU S hS)]
  exact bilinear_affine_compose _ _ _ _ _ _ _ hsqrt

end RHTower
