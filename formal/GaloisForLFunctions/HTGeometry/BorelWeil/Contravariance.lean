/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.Apolarity
import GaloisForLFunctions.HTGeometry.BorelWeil.PolySections

/-!
# Contravariance of the apolarity pairing

Left translation by a matrix `x` is adjoint, for the apolarity pairing, to left translation by the
transpose `xᵀ`.  The proof is two nested inductions: the chain rule for `pderiv` under a linear
substitution, and then the adjointness itself, using that multiplication by a variable is adjoint
to differentiation.

## Main results

* `pderiv_substLeft` — the chain rule.
* `apolar_substLeft` — `⟨x · p, q⟩ = ⟨p, xᵀ · q⟩`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {k : Type*} [Field k]

theorem substLeft_X_eq (y : Matrix n n k) (u s : n) :
    substLeft y (MvPolynomial.X (u, s)) = ∑ r : n, MvPolynomial.C (y u r) * MvPolynomial.X (r, s) :=
  by simp [substLeft]

theorem pderiv_substLeft_X (y : Matrix n n k) (i j u s : n) :
    MvPolynomial.pderiv (i, j) (substLeft y (MvPolynomial.X (u, s)))
      = if s = j then MvPolynomial.C (y u i) else 0 := by
  classical
  rw [substLeft_X_eq, map_sum]
  have hterm : ∀ r : n, MvPolynomial.pderiv (i, j)
      (MvPolynomial.C (y u r) * MvPolynomial.X (r, s))
      = if (i, j) = (r, s) then MvPolynomial.C (y u r) else 0 := by
    intro r
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases h : (i, j) = (r, s)
    · rw [if_pos h.symm, if_pos h, mul_one]
    · rw [if_neg fun hc => h hc.symm, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => hterm r]
  by_cases hs : s = j
  · subst hs
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro r _ hr
      exact if_neg (by simp [Ne.symm hr])
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hs, Finset.sum_eq_zero]
    intro r _
    exact if_neg (by rintro ⟨-, rfl⟩; exact hs rfl)

theorem substLeft_pderiv_X_sum (y : Matrix n n k) (i j u s : n) :
    ∑ r : n, (y r i) • substLeft y (MvPolynomial.pderiv (r, j) (MvPolynomial.X (u, s)))
      = if s = j then MvPolynomial.C (y u i) else 0 := by
  classical
  have hterm : ∀ r : n, (y r i) • substLeft y (MvPolynomial.pderiv (r, j)
      (MvPolynomial.X (u, s)))
      = if (r, j) = (u, s) then MvPolynomial.C (y r i) else 0 := by
    intro r
    rw [MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases h : (r, j) = (u, s)
    · rw [if_pos h.symm, map_one, if_pos h, MvPolynomial.smul_eq_C_mul, mul_one]
    · rw [if_neg fun hc => h hc.symm, map_zero, if_neg h, smul_zero]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => hterm r]
  by_cases hs : s = j
  · subst hs
    rw [if_pos rfl, Finset.sum_eq_single u]
    · simp
    · intro r _ hr
      exact if_neg (by rintro ⟨rfl, -⟩; exact hr rfl)
    · intro h; exact absurd (Finset.mem_univ u) h
  · rw [if_neg hs, Finset.sum_eq_zero]
    intro r _
    exact if_neg (by rintro ⟨-, rfl⟩; exact hs rfl)

/-- **Chain rule for a linear substitution.** -/
theorem pderiv_substLeft (y : Matrix n n k) (i j : n) (q : MvPolynomial (n × n) k) :
    MvPolynomial.pderiv (i, j) (substLeft y q)
      = ∑ r : n, (y r i) • substLeft y (MvPolynomial.pderiv (r, j) q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C c => simp [substLeft]
  | add q₁ q₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by rw [map_add, map_add, smul_add]
  | mul_X q' v ih =>
    obtain ⟨u, s⟩ := v
    rw [map_mul, MvPolynomial.pderiv_mul, ih]
    have hrhs : ∑ r : n, (y r i) • substLeft y (MvPolynomial.pderiv (r, j)
        (q' * MvPolynomial.X (u, s)))
        = (∑ r : n, (y r i) • substLeft y (MvPolynomial.pderiv (r, j) q'))
            * substLeft y (MvPolynomial.X (u, s))
          + substLeft y q'
            * ∑ r : n, (y r i) • substLeft y (MvPolynomial.pderiv (r, j)
              (MvPolynomial.X (u, s))) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, smul_add, smul_mul_assoc,
        mul_smul_comm]
    rw [hrhs, substLeft_pderiv_X_sum, ← pderiv_substLeft_X y i j u s]

/-- **Contravariance.**  Left translation by `x` is adjoint to left translation by `xᵀ`. -/
theorem apolar_substLeft (x : Matrix n n k) (p q : MvPolynomial (n × n) k) :
    apolar (substLeft x p) q = apolar p (substLeft xᵀ q) := by
  classical
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
    have hconst : ∀ (y : Matrix n n k) (r : MvPolynomial (n × n) k),
        MvPolynomial.constantCoeff (substLeft y r) = MvPolynomial.constantCoeff r := by
      intro y r
      have h0 : ∀ z : MvPolynomial (n × n) k,
          matEval (0 : Matrix n n k) z = MvPolynomial.constantCoeff z := by
        intro z
        show MvPolynomial.eval (fun ij : n × n => (0 : Matrix n n k) ij.1 ij.2) z
            = MvPolynomial.constantCoeff z
        simp
      rw [← h0, ← h0, matEval_substLeft, Matrix.mul_zero]
    have hCsub : substLeft x (MvPolynomial.C c : MvPolynomial (n × n) k) = MvPolynomial.C c := by
      simp [substLeft]
    rw [hCsub, apolar_C_left, apolar_C_left, hconst]
  | add p₁ p₂ h₁ h₂ => rw [map_add, apolar_add_left, apolar_add_left, h₁, h₂]
  | mul_X p' v ih =>
    obtain ⟨i, j⟩ := v
    have hcomm1 : p' * MvPolynomial.X (i, j) = MvPolynomial.X (i, j) * p' := mul_comm _ _
    rw [map_mul, substLeft_X_eq, hcomm1, apolar_X_mul]
    have hlhs : apolar (substLeft x p' * ∑ r : n, MvPolynomial.C (x i r)
          * MvPolynomial.X (r, j)) q
        = ∑ r : n, (x i r) * apolar (substLeft x p') (MvPolynomial.pderiv (r, j) q) := by
      rw [Finset.mul_sum, apolar_sum_left]
      refine Finset.sum_congr rfl fun r _ => ?_
      have : substLeft x p' * (MvPolynomial.C (x i r) * MvPolynomial.X (r, j))
          = (x i r) • (MvPolynomial.X (r, j) * substLeft x p') := by
        rw [MvPolynomial.smul_eq_C_mul]; ring
      rw [this, apolar_smul_left, apolar_X_mul]
    rw [hlhs]
    have hstep : ∀ r : n, (x i r) * apolar (substLeft x p') (MvPolynomial.pderiv (r, j) q)
        = (x i r) * apolar p' (substLeft xᵀ (MvPolynomial.pderiv (r, j) q)) := by
      intro r
      rw [ih (MvPolynomial.pderiv (r, j) q)]
    rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => hstep r]
    have hchain : MvPolynomial.pderiv (i, j) (substLeft xᵀ q)
        = ∑ r : n, (x i r) • substLeft xᵀ (MvPolynomial.pderiv (r, j) q) := by
      have := pderiv_substLeft (xᵀ) i j q
      simpa using this
    rw [hchain, apolar_sum_right]
    exact Finset.sum_congr rfl fun r _ => by rw [apolar_smul_right]

end GaloisForLFunctions.HTGeometry.BorelWeil
