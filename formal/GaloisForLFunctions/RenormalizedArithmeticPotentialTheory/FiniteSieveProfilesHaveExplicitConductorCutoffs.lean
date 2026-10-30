import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.FiniteSieveProfilesHaveEffectiveRamanujanApproximations

/-!
# Explicit horizon and conductor cutoffs for finite sieve profiles

The logarithmic spectral tail gives a relative squared approximation error in
the actual harmonic class weights. Exponentiating its two logarithmic bounds
makes both cutoffs explicit and independent of the profile coefficients.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry

/-- A horizon admitting the uniform comparison of harmonic class weights. -/
def sieveProfileHorizon (Q : Finset Nat.Primes) (A : ℕ) : ℕ :=
  max (A ^ 2) ⌈Real.exp (2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4)⌉₊

/-- Conductors sufficient for relative squared error `η` on a sieve prefix. -/
def sieveProfileConductorCutoff (Q : Finset Nat.Primes) (A : ℕ) (η : ℝ) : ℕ :=
  max 2 ⌈Real.exp (16 * (Real.log A + (sieveEuler Q - Real.eulerMascheroniConstant)) / η)⌉₊

/-- The explicit cutoffs approximate every finite sieve profile in its actual class mass. -/
theorem exists_sieveProfile_ramanujan_approximation_explicit
    (Q : Finset Nat.Primes) (A : ℕ) {η : ℝ} (hη : 0 < η)
    {N : ℕ} (hN : sieveProfileHorizon Q A ≤ N) (f : SieveClass Q → ℝ) :
    ∃ b : SieveClass Q → ℝ,
      (∑ a ∈ sieveClassPrefix Q N, sieveClassMass Q a N *
        ((if (a : ℕ) ≤ A then f a else 0) -
          ∑ m ∈ sieveClassPrefix Q (sieveProfileConductorCutoff Q A η),
            b m * normalizedRamanujanMode m a) ^ 2) ≤
        η * ∑ a ∈ sieveClassPrefix Q A, sieveClassMass Q a N * f a ^ 2 := by
  let R := sieveProfileConductorCutoff Q A η
  have hR : 1 < R := lt_of_lt_of_le (by omega : 1 < 2) (Nat.le_max_left _ _)
  have hRreal : (1 : ℝ) < R := by exact_mod_cast hR
  have hA : A ^ 2 ≤ N + 1 :=
    ((Nat.le_max_left _ _).trans hN).trans (Nat.le_succ N)
  have hNH : Real.exp (2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4) ≤
      (N + 1 : ℕ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast ((Nat.le_max_right _ _).trans hN).trans (Nat.le_succ N)
  have hNlog : 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4 ≤
      Real.log (N + 1 : ℕ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hNH
  have hRE : Real.exp
      (16 * (Real.log A + (sieveEuler Q - Real.eulerMascheroniConstant)) / η) ≤ (R : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast Nat.le_max_right 2
      ⌈Real.exp (16 * (Real.log A + (sieveEuler Q - Real.eulerMascheroniConstant)) / η)⌉₊
  have hRlog :
      16 * (Real.log A + (sieveEuler Q - Real.eulerMascheroniConstant)) / η ≤ Real.log R := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hRE
  have hcoef :
      16 * (Real.log A + (sieveEuler Q - Real.eulerMascheroniConstant)) / Real.log R ≤ η := by
    apply (div_le_iff₀ (Real.log_pos hRreal)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hRlog
  obtain ⟨b, hb⟩ := exists_sieveProfile_ramanujan_approximation Q hR hA hNlog f
  exact ⟨b, hb.trans (mul_le_mul_of_nonneg_right hcoef
    (sum_nonneg fun a _ => mul_nonneg
      (div_nonneg (sievedHarmonic_nonneg Q _) (Nat.cast_nonneg (a : ℕ)))
      (sq_nonneg _)))⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_sieveProfile_ramanujan_approximation_explicit
