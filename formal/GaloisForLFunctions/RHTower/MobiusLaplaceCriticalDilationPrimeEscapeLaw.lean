import GaloisForLFunctions.RHTower.MobiusLaplaceCriticalDilationNoGo

/-!
# Critical Möbius renewal prime escape

Bare critical renewal weights are nonsummable already on prime dilations, while the actual
Möbius--Laplace renewal series is absolutely summable. Consequently transform-value cancellation
cannot stay uniformly away from zero: at every log coordinate, the critical profile falls below
every positive threshold along cofinitely many prime dilations.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

theorem primeAsPositiveDilation_injective :
    Function.Injective primeAsPositiveDilation := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun k : ℕ+ => (k : ℕ)) hpq

theorem frequently_norm_mobiusLaplaceCriticalProfile_primeDilation_lt
    (y : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ᶠ p : Nat.Primes in cofinite,
      ‖mobiusLaplaceCriticalProfile
        (y - Real.log (primeAsPositiveDilation p : ℝ))‖ < epsilon := by
  have hcomplex :=
    (summable_mobiusLaplaceCriticalRenewal y).comp_injective
      primeAsPositiveDilation_injective
  have hweighted : Summable (fun p : Nat.Primes =>
      mobiusLaplaceCriticalRenewalWeight (primeAsPositiveDilation p) *
        ‖mobiusLaplaceCriticalProfile
          (y - Real.log (primeAsPositiveDilation p : ℝ))‖) := by
    have hweightNonneg (p : Nat.Primes) :
        0 ≤ mobiusLaplaceCriticalRenewalWeight (primeAsPositiveDilation p) := by
      dsimp only [mobiusLaplaceCriticalRenewalWeight]
      positivity
    simpa only [Function.comp_apply, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hweightNonneg _)] using hcomplex.norm
  by_contra hfrequent
  push Not at hfrequent
  let w : Nat.Primes → ℝ := fun p =>
    mobiusLaplaceCriticalRenewalWeight (primeAsPositiveDilation p)
  let v : Nat.Primes → ℝ := fun p =>
    ‖mobiusLaplaceCriticalProfile
      (y - Real.log (primeAsPositiveDilation p : ℝ))‖
  let g : Nat.Primes → ℝ := fun p => if epsilon ≤ v p then w p else 0
  change ∀ᶠ p : Nat.Primes in cofinite, epsilon ≤ v p at hfrequent
  have hscaled : Summable (fun p : Nat.Primes =>
      (1 / epsilon) * (w p * v p)) := by
    have hwv : Summable (fun p : Nat.Primes => w p * v p) := by
      simpa only [w, v] using hweighted
    simpa only [one_div] using hwv.mul_left (1 / epsilon)
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le
    · intro p
      dsimp only [g]
      split_ifs
      · dsimp only [w, mobiusLaplaceCriticalRenewalWeight]
        positivity
      · exact le_rfl
    · intro p
      dsimp only [g]
      split_ifs with hp
      · have hw : 0 ≤ w p := by
          dsimp only [w, mobiusLaplaceCriticalRenewalWeight]
          positivity
        have hmul : w p * epsilon ≤ w p * v p :=
          mul_le_mul_of_nonneg_left hp hw
        have hbound : w p ≤ (w p * v p) / epsilon :=
          (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using hmul)
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hbound
      · have hw : 0 ≤ w p := by
          dsimp only [w, mobiusLaplaceCriticalRenewalWeight]
          positivity
        have hv : 0 ≤ v p := by
          dsimp only [v]
          positivity
        exact mul_nonneg (by positivity) (mul_nonneg hw hv)
    · simpa only [one_div] using hscaled
  have hgw : g =ᶠ[cofinite] w := by
    filter_upwards [hfrequent] with p hp
    simp [g, hp]
  have hw : Summable w := hg.congr_cofinite hgw
  exact not_summable_prime_mobiusLaplaceCriticalRenewalWeight (by
    simpa only [w] using hw)

end

end RHTower
