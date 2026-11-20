import GaloisForLFunctions.goldbach.OddCharacterProjection
import GaloisForLFunctions.goldbach.ReducedResidueAntidiagonal
import Mathlib.NumberTheory.Chebyshev

/-!
# The smoothed Goldbach correlation and its finite projection

The two canonical representatives of opposite units supply precisely the
coprime antidiagonal. Applying odd-character orthogonality to their smoothed
von Mangoldt weights gives the normalized diagonal minus the odd moment.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu

open Finset ArithmeticFunction
open scoped Classical
noncomputable section

/-- The von Mangoldt polynomial coefficient before normalization by √N. -/
def coefficient (φ : ℝ → ℝ) (N n : ℕ) : ℝ := Λ n * φ (n / (N : ℝ))

/-- Normalized correlation over the ordered coprime antidiagonal (1.3). -/
def correlation (φ : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ p ∈ antidiagonal N, if p.1.Coprime N then
    coefficient φ N p.1 * coefficient φ N p.2 else 0) / N

/-- On the antidiagonal, testing either endpoint tests their product. -/
theorem product_coprime_iff {n m N : ℕ} (h : n + m = N) :
    (n * m).Coprime N ↔ n.Coprime N := by
  subst N
  rw [Nat.coprime_mul_iff_left, Nat.coprime_add_self_right, Nat.add_comm n m,
    Nat.coprime_add_self_right]
  exact ⟨And.left, fun h => ⟨h, h.symm⟩⟩

/-- The diagonal with the same coprimality and normalization as the correlation. -/
def diagonal (φ : ℝ → ℝ) (N : ℕ) [NeZero N] : ℝ :=
  (∑ a : (ZMod N)ˣ, coefficient φ N (a : ZMod N).val ^ 2) / N

/-- The second moment of the unnormalized finite polynomials, divided by N. -/
def oddMoment (φ : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 * (∑ χ : DirichletCharacter ℂ (k + 1) with χ.Odd,
    ‖unitCharacterSum k (fun a => (coefficient φ (k + 1) (a : ZMod (k + 1)).val : ℂ)) χ‖ ^ 2) /
      ((k + 1).totient * ((k + 1 : ℕ) : ℝ))

/-- Exact finite projection (2.2), valid for arbitrary real weights and every modulus ≥ 2. -/
theorem correlation_eq_diagonal_sub_oddMoment (φ : ℝ → ℝ) (k : ℕ) :
    correlation φ (k + 2) = diagonal φ (k + 2) - oddMoment φ (k + 1) := by
  let w := fun a : (ZMod (k + 2))ˣ => coefficient φ (k + 2) (a : ZMod (k + 2)).val
  have ht : (0 : ℝ) < (k + 2).totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < k + 2)
  have h := twice_sum_odd_norm_sq_unitCharacterSum (k + 1) w
  unfold correlation diagonal oddMoment
  rw [← sum_units_eq_coprime_antidiagonal k (fun n m => coefficient φ (k + 2) n *
    coefficient φ (k + 2) m), h]
  change (∑ a, w a * w (-a)) / ((k + 2 : ℕ) : ℝ) =
    (∑ a, w a ^ 2) / ((k + 2 : ℕ) : ℝ) -
    ((k + 2).totient : ℝ) * ((∑ a, w a ^ 2) - ∑ a, w (-a) * w a) /
      ((k + 2).totient * ((k + 2 : ℕ) : ℝ))
  simp_rw [mul_comm (w _) (w (-_))]
  field_simp [ht.ne']
  ring

#print axioms product_coprime_iff
#print axioms correlation_eq_diagonal_sub_oddMoment

end
end GaloisForLFunctions.Goldbach.LiLiu
