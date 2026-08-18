import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw

/-!
# The Pauli depolarizing identity and the one-replica full-Pauli Casimir

Summing the outer product of a single-qubit Pauli label with itself over the four labels gives
twice the swap; taking the product over the register turns this into `2^n` times the swap for the
whole Pauli string family.  Contracting the swap against an operator is exactly conjugation, so the
Pauli family is an exact one-design: `∑_P P X P = 2^n (Tr X) I`.

Every Pauli string is an involution, so its squared commutator action is `2X - 2PXP`.  Summing over
all labels — the identity contributes nothing — the depolarizing identity evaluates the full-Pauli
Casimir exactly: it is `2D²` on the traceless operators, with the trace direction in its kernel.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Single-qubit swap identity.**  Summing the outer product of a Pauli label with itself over
the four labels gives twice the swap. -/
theorem sum_boolPauliOption_entry_mul (a b c d : Bool) :
    ∑ p : Option (Fin 3), boolPauliOption p a b * boolPauliOption p c d =
      2 * ((if a = d then (1 : ℂ) else 0) * (if b = c then (1 : ℂ) else 0)) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Fintype.sum_option, Fin.sum_univ_three, boolPauliOption, finiteQubitPauli,
      Complex.ext_iff] <;>
    ring

variable {sigma : Type*} [Fintype sigma] [DecidableEq sigma]

/-- **Pauli-string swap identity.**  Over the whole Pauli label set of a register the outer
product of a string with itself is `2^n` times the swap. -/
theorem sum_finitePauliMatrix_entry_mul
    (r u v c : FiniteQubitConfiguration sigma) :
    ∑ L : sigma → Option (Fin 3), finitePauliMatrix L r u * finitePauliMatrix L v c =
      (2 : ℂ) ^ Fintype.card sigma *
        ((if r = c then (1 : ℂ) else 0) * (if u = v then (1 : ℂ) else 0)) := by
  classical
  set g : sigma → Option (Fin 3) → ℂ :=
    fun s p => boolPauliOption p (r s) (u s) * boolPauliOption p (v s) (c s) with hgdef
  have hprod : ∀ L : sigma → Option (Fin 3),
      finitePauliMatrix L r u * finitePauliMatrix L v c = ∏ s, g s (L s) := by
    intro L
    unfold finitePauliMatrix boolPauliOptionEntry
    rw [← Finset.prod_mul_distrib]
  simp_rw [hprod]
  have hswap : (∑ L : sigma → Option (Fin 3), ∏ s, g s (L s)) =
      ∏ s, ∑ p : Option (Fin 3), g s p := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hswap]
  have hstep : ∀ s : sigma,
      (∑ p : Option (Fin 3), g s p) =
        2 * ((if r s = c s then (1 : ℂ) else 0) * (if u s = v s then (1 : ℂ) else 0)) := fun s =>
    sum_boolPauliOption_entry_mul (r s) (u s) (v s) (c s)
  have hboolPair : ∀ a b : FiniteQubitConfiguration sigma,
      (∏ s : sigma, (if a s = b s then (1 : ℂ) else 0)) = if a = b then 1 else 0 := by
    intro a b
    rw [Finset.prod_boole]
    by_cases h : a = b
    · simp [h]
    · obtain ⟨s0, hs0⟩ := Function.ne_iff.mp h
      rw [if_neg h, if_neg]
      intro hall
      exact hs0 (hall s0 (Finset.mem_univ s0))
  simp_rw [hstep]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    hboolPair r c, hboolPair u v]

/-- **Pauli depolarizing identity.**  Conjugating by every Pauli string of the register and summing
gives `2^n` times the trace, times the identity: the Pauli family is an exact one-design. -/
theorem sum_finitePauliMatrix_conj
    (X : Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ) :
    (∑ L : sigma → Option (Fin 3), finitePauliMatrix L * X * finitePauliMatrix L) =
      ((2 : ℂ) ^ Fintype.card sigma * X.trace) •
        (1 : Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ) := by
  classical
  ext r c
  rw [Matrix.sum_apply]
  have hterm : ∀ L : sigma → Option (Fin 3),
      (finitePauliMatrix L * X * finitePauliMatrix L) r c =
        ∑ v, ∑ u, (finitePauliMatrix L r u * finitePauliMatrix L v c) * X u v := by
    intro L
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner : ∀ v : FiniteQubitConfiguration sigma,
      (∑ L : sigma → Option (Fin 3), ∑ u,
          (finitePauliMatrix L r u * finitePauliMatrix L v c) * X u v) =
        ∑ u, ((2 : ℂ) ^ Fintype.card sigma *
          ((if r = c then (1 : ℂ) else 0) * (if u = v then (1 : ℂ) else 0))) * X u v := by
    intro v
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul, sum_finitePauliMatrix_entry_mul r u v c]
  simp_rw [hinner]
  have hcollapse : ∀ v : FiniteQubitConfiguration sigma,
      (∑ u, ((2 : ℂ) ^ Fintype.card sigma *
        ((if r = c then (1 : ℂ) else 0) * (if u = v then (1 : ℂ) else 0))) * X u v) =
        (2 : ℂ) ^ Fintype.card sigma * (if r = c then (1 : ℂ) else 0) * X v v := by
    intro v
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro hv
      exact absurd (Finset.mem_univ v) hv
  simp_rw [hcollapse]
  rw [← Finset.mul_sum]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.trace,
    Matrix.diag_apply]
  by_cases h : r = c
  · simp [h]
  · simp [h]

/-- The commutator action of a Pauli string on operators. -/
def pauliAd
    (P X : Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ) :
    Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ :=
  P * X - X * P

/-- The square of a commutator action by an involution. -/
theorem pauliAd_sq
    {P X : Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ}
    (hP : P * P = 1) :
    pauliAd P (pauliAd P X) = (2 : ℂ) • X - (2 : ℂ) • (P * X * P) := by
  unfold pauliAd
  have h1 : P * (P * X) = X := by rw [← mul_assoc, hP, one_mul]
  have h2 : X * P * P = X := by rw [mul_assoc, hP, mul_one]
  rw [mul_sub, sub_mul, h1, h2, two_smul, two_smul, ← mul_assoc]
  abel

/-- **The one-replica full-Pauli Casimir.**  Summing the squared commutator action over every
Pauli label of the register gives `2D²` on operators, corrected by the trace direction. -/
theorem sum_pauliCasimir_eq
    (X : Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ) :
    (∑ L : sigma → Option (Fin 3),
        pauliAd (finitePauliMatrix L) (pauliAd (finitePauliMatrix L) X)) =
      (2 * (4 : ℂ) ^ Fintype.card sigma) • X -
        (2 * (2 : ℂ) ^ Fintype.card sigma * X.trace) •
          (1 : Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ) := by
  classical
  have hstep : ∀ L : sigma → Option (Fin 3),
      pauliAd (finitePauliMatrix L) (pauliAd (finitePauliMatrix L) X) =
        (2 : ℂ) • X - (2 : ℂ) • (finitePauliMatrix L * X * finitePauliMatrix L) :=
    fun L => pauliAd_sq (finitePauliMatrix_mul_self L)
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.smul_sum,
    sum_finitePauliMatrix_conj X]
  have hcard : (Finset.univ : Finset (sigma → Option (Fin 3))).card =
      4 ^ Fintype.card sigma := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp
  rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  push_cast
  module

/-- **`(16)`, lower half, one replica.**  On the traceless operators the full-Pauli Casimir is
exactly `2D²`. -/
theorem sum_pauliCasimir_traceless
    (X : Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ)
    (hX : X.trace = 0) :
    (∑ L : sigma → Option (Fin 3),
        pauliAd (finitePauliMatrix L) (pauliAd (finitePauliMatrix L) X)) =
      (2 * (4 : ℂ) ^ Fintype.card sigma) • X := by
  rw [sum_pauliCasimir_eq X, hX]
  simp

end

end GaloisForLFunctions.HTGeometry
