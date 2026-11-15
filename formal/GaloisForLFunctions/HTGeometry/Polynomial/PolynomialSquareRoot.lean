import GaloisForLFunctions.HTGeometry.Polynomial.FiniteJetCRT
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Polynomial square roots modulo a nonvanishing polynomial

Over a field of characteristic different from two, a nonzero scalar square root
lifts through every power of its point ideal. At each step, the next error
coefficient is cancelled by dividing by twice the chosen scalar root.

Over an algebraically closed field, finite Chinese remainder interpolation patches
these lifts over the roots of any polynomial with nonzero constant term. Thus
`X` is a square modulo that polynomial, even when it has repeated roots.
This is the polynomial mechanism behind the self-adjoint square root used in
Proposition 4.10 of Garai–Jha–Shekhar, *p-parity conjecture for Panchishkin
Galois representations*, in the algebraically closed case.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {K : Type*} [Field K] [NeZero (2 : K)]

private theorem exists_square_root_mod_succ (u : Kˣ) (n : ℕ) :
    ∃ q : K[X], q.eval ((u : K) ^ 2) = u ∧
      (X - C ((u : K) ^ 2)) ^ (n + 1) ∣ X - q ^ 2 := by
  induction n with
  | zero =>
    refine ⟨C (u : K), by simp, ?_⟩
    rw [pow_one, ← map_pow]
  | succ n ih =>
    obtain ⟨q, hq, d, hd⟩ := ih
    let c : K := d.eval ((u : K) ^ 2) / (2 * u)
    have hc : 2 * (u : K) * c = d.eval ((u : K) ^ 2) := by
      dsimp [c]
      field_simp
    have hfactor : X - C ((u : K) ^ 2) ∣
        d - 2 * q * C c - (X - C ((u : K) ^ 2)) ^ (n + 1) * (C c) ^ 2 := by
      apply (Polynomial.dvd_iff_isRoot).mpr
      change eval ((u : K) ^ 2) _ = 0
      simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat,
        hq, sub_self, zero_pow (Nat.succ_ne_zero n), zero_mul, sub_zero]
      exact sub_eq_zero.mpr hc.symm
    obtain ⟨r, hr⟩ := hfactor
    refine ⟨q + (X - C ((u : K) ^ 2)) ^ (n + 1) * C c, ?_, r, ?_⟩
    · simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (Nat.succ_ne_zero n), zero_mul, add_zero, hq]
    · calc
        X - (q + (X - C ((u : K) ^ 2)) ^ (n + 1) * C c) ^ 2 =
            (X - C ((u : K) ^ 2)) ^ (n + 1) *
              (d - 2 * q * C c - (X - C ((u : K) ^ 2)) ^ (n + 1) * (C c) ^ 2) := by
                linear_combination hd
        _ = (X - C ((u : K) ^ 2)) ^ (n + 1 + 1) * r := by
          rw [hr, pow_succ]
          ring

/-- A chosen nonzero square root lifts modulo every power of its point ideal. -/
theorem exists_polynomial_square_root_mod_power (u : Kˣ) (n : ℕ) :
    ∃ q : K[X], q.eval ((u : K) ^ 2) = u ∧
      (X - C ((u : K) ^ 2)) ^ n ∣ X - q ^ 2 := by
  cases n with
  | zero => exact ⟨C (u : K), by simp, by simp⟩
  | succ n => exact exists_square_root_mod_succ u n

/-- The variable is a square modulo any polynomial not vanishing at zero. -/
theorem exists_polynomial_square_root_mod [IsAlgClosed K]
    (f : K[X]) (hzero : f.eval 0 ≠ 0) : ∃ q : K[X], f ∣ X - q ^ 2 := by
  classical
  have hf : f ≠ 0 := fun h => hzero (by simp [h])
  let S := f.roots.toFinset
  have hlocal (a : S) : ∃ q : K[X],
      (X - C (a : K)) ^ rootMultiplicity (a : K) f ∣ X - q ^ 2 := by
    have ha : (a : K) ≠ 0 := by
      intro h
      have hr : f.eval (a : K) = 0 := (mem_roots hf).mp (Multiset.mem_toFinset.mp a.2)
      exact hzero (by simpa only [h] using hr)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) (Nat.succ_pos 1)
    have hu0 : u ≠ 0 := by
      intro h
      exact ha (hu.symm.trans (by simp [h]))
    obtain ⟨q, _, hq⟩ := exists_polynomial_square_root_mod_power (Units.mk0 u hu0)
      (rootMultiplicity (a : K) f)
    exact ⟨q, by simpa only [Units.val_mk0, hu] using hq⟩
  choose target htarget using hlocal
  obtain ⟨q, hq⟩ := exists_polynomial_power_linear_dvd_sub
    (fun a : S => (a : K)) Subtype.val_injective
    (fun a : S => rootMultiplicity (a : K) f) target
  have hresidue (a : S) : (X - C (a : K)) ^ rootMultiplicity (a : K) f ∣ X - q ^ 2 := by
    have hdiff : (X - C (a : K)) ^ rootMultiplicity (a : K) f ∣
        q ^ 2 - (target a) ^ 2 := by
      obtain ⟨d, hd⟩ := hq a
      refine ⟨d * (q + target a), ?_⟩
      calc
        q ^ 2 - (target a) ^ 2 = (q - target a) * (q + target a) := by ring
        _ = _ := by rw [hd]; ring
    rw [show X - q ^ 2 = (X - (target a) ^ 2) - (q ^ 2 - (target a) ^ 2) by ring]
    exact dvd_sub (htarget a) hdiff
  have hprod : (∏ a : S, (X - C (a : K)) ^ rootMultiplicity (a : K) f) ∣
      X - q ^ 2 := by
    apply Ideal.mem_span_singleton.mp
    rw [← Ideal.iInf_span_singleton (fun i j hij =>
      (pairwise_coprime_X_sub_C (show Function.Injective (fun a : S => (a : K)) from
        Subtype.val_injective) hij).pow)]
    simp only [Ideal.mem_iInf, Ideal.mem_span_singleton]
    exact hresidue
  have hfprod : f = C f.leadingCoeff *
      ∏ a : S, (X - C (a : K)) ^ rootMultiplicity (a : K) f := by
    calc
      f = C f.leadingCoeff * (f.roots.map fun a => X - C a).prod :=
        (IsAlgClosed.splits f).eq_prod_roots
      _ = _ := by rw [prod_multiset_root_eq_finset_root, ← Finset.prod_coe_sort]
  have hlead : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hC : C f.leadingCoeff * C f.leadingCoeff⁻¹ = (1 : K[X]) := by
    rw [← map_mul, mul_inv_cancel₀ hlead, map_one]
  obtain ⟨d, hd⟩ := hprod
  refine ⟨q, C f.leadingCoeff⁻¹ * d, ?_⟩
  calc
    X - q ^ 2 = (∏ a : S, (X - C (a : K)) ^ rootMultiplicity (a : K) f) * d := hd
    _ = (C f.leadingCoeff * C f.leadingCoeff⁻¹) *
        ((∏ a : S, (X - C (a : K)) ^ rootMultiplicity (a : K) f) * d) := by rw [hC, one_mul]
    _ = (C f.leadingCoeff * ∏ a : S, (X - C (a : K)) ^ rootMultiplicity (a : K) f) *
        (C f.leadingCoeff⁻¹ * d) := by ring
    _ = f * (C f.leadingCoeff⁻¹ * d) := by rw [← hfprod]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_polynomial_square_root_mod_power
#print axioms GaloisForLFunctions.HTGeometry.exists_polynomial_square_root_mod
