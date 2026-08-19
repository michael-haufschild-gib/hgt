import GaloisForLFunctions.HTGeometry.DifferentialPolynomialRank
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The separant

Differentiating a scalar differential polynomial of order `n` produces exactly one occurrence of the
next jet `y_{n+1}`, and it occurs linearly with coefficient the partial derivative with respect to
the leader `y_n` — the separant.  Everything else has order at most `n`.

This is the structural fact behind Ritt's reduction: it is what lets one lower the order of a
differential polynomial by pseudo-dividing by a derivative of a fixed polynomial.

The proof presents the polynomial through the jets of order at most `n`, where the induction over
monomials never meets a variable of larger order.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions

noncomputable section

theorem mvPolynomial_vars_X_subset {σ R : Type*} [CommSemiring R] (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ R).vars ⊆ {i} := by
  rcases subsingleton_or_nontrivial R with h | h
  · have : (MvPolynomial.X i : MvPolynomial σ R) = 0 := Subsingleton.elim _ _
    simp [this]
  · rw [MvPolynomial.vars_X]

/-- The separant: the partial derivative with respect to the leader. -/
def scalarSeparant {K : Type*} [CommRing K]
    (A : DifferentialPolynomial Unit K) : DifferentialPolynomial Unit K :=
  MvPolynomial.pderiv (scalarDifferentialPolynomialLeader A) A

variable {K : Type*} [CommRing K] [Differential K]

/-- On polynomials in the jets of order at most `n`, differentiation is linear in the next jet with
coefficient the partial derivative at order `n`. -/
theorem exists_separant_decomposition_aux (n : ℕ)
    (A' : MvPolynomial {p : Unit × ℕ // p.2 ≤ n} K) :
    ∃ B : DifferentialPolynomial Unit K, (∀ p ∈ B.vars, p.2 ≤ n) ∧
      differentialPolynomialOverDerivation Unit K
          (MvPolynomial.rename Subtype.val A')
        = MvPolynomial.pderiv ((), n) (MvPolynomial.rename Subtype.val A')
            * MvPolynomial.X ((), n + 1) + B := by
  classical
  induction A' using MvPolynomial.induction_on with
  | C a =>
      refine ⟨MvPolynomial.C (Differential.deriv a), ?_, ?_⟩
      · intro p hp
        rw [MvPolynomial.vars_C] at hp
        exact absurd hp (Finset.notMem_empty p)
      · rw [MvPolynomial.rename_C, differentialPolynomialOverDerivation_C,
          MvPolynomial.pderiv_C, zero_mul, zero_add]
  | add p q hp hq =>
      obtain ⟨Bp, hBp, hep⟩ := hp
      obtain ⟨Bq, hBq, heq⟩ := hq
      refine ⟨Bp + Bq, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hx) with h | h
        · exact hBp x h
        · exact hBq x h
      · rw [map_add, map_add, map_add, hep, heq]
        ring
  | mul_X q i hq =>
      obtain ⟨Bq, hBq, heq⟩ := hq
      obtain ⟨⟨u, m⟩, him⟩ := i
      have hu : u = () := Subsingleton.elim u ()
      subst hu
      have hren : MvPolynomial.rename Subtype.val (q * MvPolynomial.X ⟨((), m), him⟩)
          = MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), m) := by
        rw [map_mul, MvPolynomial.rename_X]
      have hqvars : ∀ x ∈ (MvPolynomial.rename Subtype.val q).vars, x.2 ≤ n := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename _ q hx)
        exact y.property
      have hleib : differentialPolynomialOverDerivation Unit K
            (MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), m))
          = MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), m + 1)
            + MvPolynomial.X ((), m)
              * differentialPolynomialOverDerivation Unit K
                  (MvPolynomial.rename Subtype.val q) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul, differentialPolynomialOverDerivation_X]
      by_cases hi : m = n
      · subst hi
        refine ⟨Bq * MvPolynomial.X ((), m), ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hx) with h | h
          · exact hBq x h
          · have hx' := mvPolynomial_vars_X_subset (R := K) ((), m) h
            simp only [Finset.mem_singleton] at hx'
            subst hx'
            exact le_rfl
        · have hpd : MvPolynomial.pderiv ((), m)
                (MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), m))
              = MvPolynomial.rename Subtype.val q
                + MvPolynomial.X ((), m) * MvPolynomial.pderiv ((), m)
                    (MvPolynomial.rename Subtype.val q) := by
            rw [Derivation.leibniz, MvPolynomial.pderiv_X]
            simp only [smul_eq_mul, Pi.single_eq_same]
            ring
          rw [hren, hleib, heq, hpd]
          ring
      · have hlt : m + 1 ≤ n := by omega
        refine ⟨Bq * MvPolynomial.X ((), m)
            + MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), m + 1), ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hx) with h | h
          · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h) with h' | h'
            · exact hBq x h'
            · have hx' := mvPolynomial_vars_X_subset (R := K) ((), m) h'
              simp only [Finset.mem_singleton] at hx'
              subst hx'
              exact him
          · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h) with h' | h'
            · exact hqvars x h'
            · have hx' := mvPolynomial_vars_X_subset (R := K) ((), m + 1) h'
              simp only [Finset.mem_singleton] at hx'
              subst hx'
              exact hlt
        · have hpd : MvPolynomial.pderiv ((), n)
                (MvPolynomial.rename Subtype.val q * MvPolynomial.X ((), m))
              = MvPolynomial.X ((), m) * MvPolynomial.pderiv ((), n)
                  (MvPolynomial.rename Subtype.val q) := by
            rw [Derivation.leibniz, MvPolynomial.pderiv_X,
              Pi.single_eq_of_ne (by simp [hi] : (((), m) : Unit × ℕ) ≠ ((), n))]
            simp only [smul_eq_mul, mul_zero, zero_add]
          rw [hren, hleib, heq, hpd]
          ring

/-- **The separant decomposition.**  Differentiating a scalar differential polynomial of order `n`
produces the next jet exactly once, linearly, with coefficient the separant. -/
theorem exists_separant_decomposition (A : DifferentialPolynomial Unit K) :
    ∃ B : DifferentialPolynomial Unit K,
      (∀ p ∈ B.vars, p.2 ≤ scalarDifferentialPolynomialOrder A) ∧
      differentialPolynomialOverDerivation Unit K A
        = scalarSeparant A
            * MvPolynomial.X ((), scalarDifferentialPolynomialOrder A + 1) + B := by
  set n := scalarDifferentialPolynomialOrder A with hn
  have hsub : ↑A.vars ⊆ {p : Unit × ℕ | p.2 ≤ n} := by
    intro p hp
    simp only [Finset.mem_coe] at hp
    simp only [Set.mem_setOf_eq, hn, scalarDifferentialPolynomialOrder]
    exact Finset.le_sup (f := fun j : Unit × ℕ => j.2) hp
  have hmem : A ∈ MvPolynomial.supported K {p : Unit × ℕ | p.2 ≤ n} :=
    MvPolynomial.mem_supported.mpr hsub
  rw [MvPolynomial.supported_eq_range_rename] at hmem
  obtain ⟨A', hA'⟩ := hmem
  have hA'' : MvPolynomial.rename (Subtype.val) A' = A := hA'
  obtain ⟨B, hB, hEq⟩ := exists_separant_decomposition_aux n A'
  refine ⟨B, hB, ?_⟩
  have key : differentialPolynomialOverDerivation Unit K A
      = MvPolynomial.pderiv ((), n) A * MvPolynomial.X ((), n + 1) + B := by
    rw [← hA'']
    exact hEq
  rw [key, scalarSeparant, scalarDifferentialPolynomialLeader, ← hn]

end

end GaloisForLFunctions.HTGeometry
