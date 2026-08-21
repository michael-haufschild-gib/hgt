import GaloisForLFunctions.HTGeometry.BiDualAdjointDerivative

/-!
# Extracting the `εη`-coefficient

On the part of `C[ε, η]/(ε², η²)` where the `η`-coefficient vanishes, the pair `(1, εη)` multiplies
exactly like a dual number:

`(z·w).re = z.re·w.re`,  `(z·w).mx = z.re·w.mx + z.mx·w.re`  when `z.et = w.et = 0`,

and the `η`-coefficient of a product of such elements vanishes again.  Since the derivation is
componentwise, the same holds for every jet, so evaluating a differential polynomial at a point
whose `η`-coefficients vanish gives an element whose `(re, mx)` pair is the value of the same
polynomial at the dual-number point `re + εmx`.

Applied to the adjoint derivative `1 + εY + εη(XY − YX)`, this turns the commutator from a
coefficient of a member of the zero set into a tangent direction at the identity: the Lie algebra of
a differential algebraic group is closed under the bracket.

* `BiDual.jet_re`, `BiDual.jet_ep`, `BiDual.jet_et`, `BiDual.jet_mx`;
* `evalOver_biDual_of_et_zero`;
* `mem_zeroSet_of_biMatrix_et_zero`;
* `bracket_mem_zeroSet`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C]

namespace BiDual

@[simp] theorem jet_re (n : ℕ) (z : BiDual C) :
    (differentialJet n z).re = differentialJet n z.re := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, deriv_re, ih]

@[simp] theorem jet_ep (n : ℕ) (z : BiDual C) :
    (differentialJet n z).ep = differentialJet n z.ep := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, deriv_ep, ih]

@[simp] theorem jet_et (n : ℕ) (z : BiDual C) :
    (differentialJet n z).et = differentialJet n z.et := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, deriv_et, ih]

@[simp] theorem jet_mx (n : ℕ) (z : BiDual C) :
    (differentialJet n z).mx = differentialJet n z.mx := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, deriv_mx, ih]

end BiDual

theorem differentialJet_zero_elt'' (n : ℕ) : differentialJet n (0 : C) = 0 := by
  induction n with
  | zero => rw [differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, ih, map_zero]

/-- **The `(1, εη)` pair of an evaluation at an `η`-free point is a dual-number evaluation.** -/
theorem evalOver_biDual_of_et_zero {ι : Type*} (x : ι → BiDual C) (hx : ∀ i, (x i).et = 0) :
    ∀ P : DifferentialPolynomial ι C,
      (differentialPolynomialEvalOver (K := C) x P).et = 0 ∧
      dualMk (differentialPolynomialEvalOver (K := C) x P).re
          (differentialPolynomialEvalOver (K := C) x P).mx
        = differentialPolynomialEvalOver (K := C)
            (fun i => dualMk (x i).re (x i).mx) P := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_C,
        BiDual.algebraMap_eq, TrivSqZeroExt.algebraMap_eq_inl]
      refine ⟨rfl, ?_⟩
      apply TrivSqZeroExt.ext <;> simp [dualMk]
  | add p q hp hq =>
      rw [map_add, map_add]
      refine ⟨by simp [hp.1, hq.1], ?_⟩
      rw [← hp.2, ← hq.2]
      apply TrivSqZeroExt.ext <;> simp [dualMk]
  | mul_X p v hp =>
      rw [map_mul, map_mul, differentialPolynomialEvalOver_X,
        differentialPolynomialEvalOver_X]
      have hjet : (differentialJet v.2 (x v.1)).et = 0 := by
        rw [BiDual.jet_et, hx v.1, differentialJet_zero_elt'']
      have hjetdual : differentialJet v.2 (dualMk (x v.1).re (x v.1).mx)
          = dualMk (differentialJet v.2 (x v.1).re) (differentialJet v.2 (x v.1).mx) := by
        rw [differentialJet_dual]
        apply TrivSqZeroExt.ext <;> simp
      refine ⟨by simp [hp.1, hjet], ?_⟩
      rw [← hp.2, hjetdual, dualMk_mul]
      apply TrivSqZeroExt.ext
      · simp [BiDual.jet_re]
      · simp [hp.1, hjet, BiDual.jet_re, BiDual.jet_mx]

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- **The `εη`-coefficient of an `η`-free member of the zero set is a tangent direction.** -/
theorem mem_zeroSet_of_biMatrix_et_zero {a b d : Matrix (Fin 2) (Fin 2) C}
    (h : biMatrix a b 0 d ∈ matrixZeroSet (C := C) (A := BiDual C) S) :
    dualMatrix a d ∈ matrixZeroSet (C := C) (A := DualNumber C) S := by
  intro P hP
  have hx : ∀ q : Fin 2 × Fin 2, (biMatrix a b 0 d q.1 q.2).et = 0 := by
    intro q
    simp
  obtain ⟨-, heq⟩ := evalOver_biDual_of_et_zero
    (fun q : Fin 2 × Fin 2 => biMatrix a b 0 d q.1 q.2) hx P
  have hpt : (fun q : Fin 2 × Fin 2 =>
      dualMk (biMatrix a b 0 d q.1 q.2).re (biMatrix a b 0 d q.1 q.2).mx)
      = fun q : Fin 2 × Fin 2 => dualMatrix a d q.1 q.2 := by
    funext q
    simp [dualMatrix]
  rw [hpt] at heq
  rw [← heq, h P hP]
  apply TrivSqZeroExt.ext <;> simp [dualMk]

/-- **The Lie algebra of a differential algebraic group is closed under the bracket.**  If
`1 + ηX`, `1 − ηX` and `1 + ηY` are tangent directions at the identity and the zero set is closed
under multiplication over `C[ε, η]/(ε², η²)`, then so is `1 + η(XY − YX)`. -/
theorem bracket_mem_zeroSet
    (hmul : ∀ u ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      ∀ v ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      u * v ∈ matrixZeroSet (C := C) (A := BiDual C) S)
    {X Y : Matrix (Fin 2) (Fin 2) C}
    (hX : dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    (hXneg : dualMatrix 1 (-X) ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    (hY : dualMatrix 1 Y ∈ matrixZeroSet (C := C) (A := DualNumber C) S) :
    dualMatrix 1 (X * Y - Y * X) ∈ matrixZeroSet (C := C) (A := DualNumber C) S :=
  mem_zeroSet_of_biMatrix_et_zero S (adjointDerivative_mem_zeroSet S hmul hX hXneg hY)

end

end GaloisForLFunctions.HTGeometry
