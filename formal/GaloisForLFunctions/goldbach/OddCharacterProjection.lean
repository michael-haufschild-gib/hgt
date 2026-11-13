import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Odd characters and reflected correlations

Character orthogonality on reduced residues identifies the odd-character
second moment with diagonal mass minus correlation under negation. This is
the finite projection of Li--Liu, Lemma 3.1, for arbitrary complex profiles
and every positive modulus. No analytic continuation is involved.
-/

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped BigOperators

/-- A finite character transform of a profile on reduced residues. -/
def unitCharacterSum (N : ℕ) (w : (ZMod (N + 1))ˣ → ℂ)
    (χ : DirichletCharacter ℂ (N + 1)) : ℂ :=
  ∑ a, w a * χ a

/-- Orthogonality in the character variable, including imprimitive characters. -/
theorem sum_unitCharacter_mul_star (N : ℕ) (a b : (ZMod (N + 1))ˣ) :
    (∑ χ : DirichletCharacter ℂ (N + 1), χ a * star (χ b)) =
      if a = b then ((N + 1).totient : ℂ) else 0 := by
  classical
  simp_rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ← map_mul]
  rw [DirichletCharacter.sum_characters_eq]
  have he : (a : ZMod (N + 1)) * ↑b⁻¹ = 1 ↔ a = b := by
    change Units.val (a * b⁻¹) = Units.val (1 : (ZMod (N + 1))ˣ) ↔ a = b
    rw [Units.val_inj, mul_inv_eq_one]
  simp only [he]

/-- The odd selector is an exact difference of the diagonal and opposite-residue kernels. -/
theorem twice_sum_odd_unitCharacter_mul_star (N : ℕ) (a b : (ZMod (N + 1))ˣ) :
    2 * (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd, χ a * star (χ b)) =
      (if a = b then ((N + 1).totient : ℂ) else 0) -
        (if -a = b then ((N + 1).totient : ℂ) else 0) := by
  classical
  have hselector (χ : DirichletCharacter ℂ (N + 1)) :
      2 * (if χ.Odd then χ a * star (χ b) else 0) =
        χ a * star (χ b) - χ (↑(-a) : ZMod (N + 1)) * star (χ b) := by
    rcases χ.even_or_odd with h | h
    · rw [if_neg h.not_odd, show χ (↑(-a) : ZMod (N + 1)) = χ a from h.to_fun a]
      ring
    · rw [if_pos h, show χ (↑(-a) : ZMod (N + 1)) = -χ a from h.to_fun a]
      ring
  rw [sum_filter, mul_sum]
  simp_rw [hselector]
  rw [sum_sub_distrib, sum_unitCharacter_mul_star, sum_unitCharacter_mul_star]

/-- Parseval's identity with the totient normalization left explicit. -/
theorem sum_unitCharacterSum_mul_star (N : ℕ) (w v : (ZMod (N + 1))ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ (N + 1),
      unitCharacterSum N w χ * star (unitCharacterSum N v χ)) =
        ((N + 1).totient : ℂ) * ∑ a, w a * star (v a) := by
  classical
  simp only [unitCharacterSum, star_sum, star_mul, sum_mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ a, ∑ b, w a * star (v b) *
        ∑ χ : DirichletCharacter ℂ (N + 1), χ a * star (χ b) := by
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [mul_sum]
      exact sum_congr rfl fun χ _ => by ring
    _ = _ := by
      simp only [sum_unitCharacter_mul_star, mul_ite, mul_zero]
      simp only [sum_ite_eq, mem_univ, if_true]
      rw [mul_sum]
      exact sum_congr rfl fun a _ => by ring

/-- Multiplication by the parity character reflects the residue profile. -/
theorem unitCharacterSum_neg (N : ℕ) (w : (ZMod (N + 1))ˣ → ℂ)
    (χ : DirichletCharacter ℂ (N + 1)) :
    unitCharacterSum N (fun a => w (-a)) χ = χ (-1) * unitCharacterSum N w χ := by
  classical
  simp only [unitCharacterSum, mul_sum]
  apply Fintype.sum_equiv (Equiv.neg _) _ _
  intro a
  simp only [Equiv.neg_apply, Units.val_neg, ← neg_one_mul (a : ZMod (N + 1)),
    map_mul]
  have hp : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  linear_combination -(w (-a) * χ a) * hp

/-- The parity-weighted second moment is the reflected correlation. -/
theorem sum_parity_unitCharacterSum_mul_star (N : ℕ)
    (w v : (ZMod (N + 1))ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ (N + 1),
      χ (-1) * unitCharacterSum N w χ * star (unitCharacterSum N v χ)) =
        ((N + 1).totient : ℂ) * ∑ a, w (-a) * star (v a) := by
  simp_rw [← unitCharacterSum_neg]
  exact sum_unitCharacterSum_mul_star N (fun a => w (-a)) v

/-- The odd-character moment measures precisely the loss from diagonal to reflection. -/
theorem twice_sum_odd_unitCharacterSum_mul_star (N : ℕ)
    (w v : (ZMod (N + 1))ˣ → ℂ) :
    2 * (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
      unitCharacterSum N w χ * star (unitCharacterSum N v χ)) =
        ((N + 1).totient : ℂ) *
          ((∑ a, w a * star (v a)) - ∑ a, w (-a) * star (v a)) := by
  classical
  have hs (χ : DirichletCharacter ℂ (N + 1)) (z : ℂ) :
      2 * (if χ.Odd then z else 0) = z - χ (-1) * z := by
    rcases χ.even_or_odd with h | h
    · rw [if_neg h.not_odd, h]
      ring
    · rw [if_pos h, h]
      ring
  rw [sum_filter, mul_sum]
  simp_rw [hs, ← mul_assoc]
  rw [sum_sub_distrib, sum_unitCharacterSum_mul_star, sum_parity_unitCharacterSum_mul_star,
    mul_sub]

/-- Real Parseval identity for an arbitrary complex reduced-residue profile. -/
theorem sum_norm_sq_unitCharacterSum (N : ℕ) (w : (ZMod (N + 1))ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ (N + 1), ‖unitCharacterSum N w χ‖ ^ 2) =
      ((N + 1).totient : ℝ) * ∑ a, ‖w a‖ ^ 2 := by
  have h := sum_unitCharacterSum_mul_star N w w
  simp only [show ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) from
    fun z => by
      change z * (starRingEnd ℂ) z = _
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]] at h
  exact_mod_cast h

/-- The odd-character moment of a real profile is its diagonal-reflection gap. -/
theorem twice_sum_odd_norm_sq_unitCharacterSum (N : ℕ)
    (w : (ZMod (N + 1))ˣ → ℝ) :
    2 * (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
      ‖unitCharacterSum N (fun a => (w a : ℂ)) χ‖ ^ 2) =
        ((N + 1).totient : ℝ) *
          ((∑ a, w a ^ 2) - ∑ a, w (-a) * w a) := by
  have h := twice_sum_odd_unitCharacterSum_mul_star N
    (fun a => (w a : ℂ)) (fun a => (w a : ℂ))
  simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Four times the odd-character moment equals the totient times the reflection defect. -/
theorem four_mul_odd_moment_eq_reflection_defect (N : ℕ)
    (w : (ZMod (N + 1))ˣ → ℝ) :
    4 * (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
      ‖unitCharacterSum N (fun a => (w a : ℂ)) χ‖ ^ 2) =
        ((N + 1).totient : ℝ) * ∑ a, (w a - w (-a)) ^ 2 := by
  have hn : (∑ a, w (-a) ^ 2) = ∑ a, w a ^ 2 :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  have he : (∑ a, (w a - w (-a)) ^ 2) =
      2 * ((∑ a, w a ^ 2) - ∑ a, w (-a) * w a) := by
    simp_rw [show ∀ a, (w a - w (-a)) ^ 2 =
      w a ^ 2 + w (-a) ^ 2 - 2 * (w (-a) * w a) from fun a => by ring]
    rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hn]
    ring
  rw [he]
  linear_combination 2 * twice_sum_odd_norm_sq_unitCharacterSum N w

end GaloisForLFunctions.Goldbach

-- Temporary dependency audit.
#print axioms GaloisForLFunctions.Goldbach.unitCharacterSum
#print axioms GaloisForLFunctions.Goldbach.sum_unitCharacter_mul_star
#print axioms GaloisForLFunctions.Goldbach.twice_sum_odd_unitCharacter_mul_star
#print axioms GaloisForLFunctions.Goldbach.sum_unitCharacterSum_mul_star
#print axioms GaloisForLFunctions.Goldbach.unitCharacterSum_neg
#print axioms GaloisForLFunctions.Goldbach.sum_parity_unitCharacterSum_mul_star
#print axioms GaloisForLFunctions.Goldbach.twice_sum_odd_unitCharacterSum_mul_star
#print axioms GaloisForLFunctions.Goldbach.sum_norm_sq_unitCharacterSum
#print axioms GaloisForLFunctions.Goldbach.twice_sum_odd_norm_sq_unitCharacterSum
#print axioms GaloisForLFunctions.Goldbach.four_mul_odd_moment_eq_reflection_defect
