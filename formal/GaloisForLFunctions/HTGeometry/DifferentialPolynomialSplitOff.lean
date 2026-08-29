import GaloisForLFunctions.HTGeometry.DifferentialSystemSolution

/-!
# Splitting one differential indeterminate off the top

`C{y, z₁, z₂, …}` is `(C{z₁, z₂, …}){y}`: renaming the jet index along `Option ι ≃ Unit ⊕ ι` and
then separating the two blocks of variables gives a ring isomorphism, and both total derivatives
send a jet to the next jet and a constant to its derivative, so the isomorphism is differential.

* `splitOffEquiv`, with its values on constants and jets;
* `splitOffEquiv_deriv`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Splitting the jet index of one distinguished indeterminate off the rest. -/
def optionIndexSplit (ι : Type*) : (Option ι) × ℕ ≃ (Unit × ℕ) ⊕ (ι × ℕ) where
  toFun p := match p.1 with
    | none => Sum.inl ((), p.2)
    | some i => Sum.inr (i, p.2)
  invFun s := match s with
    | Sum.inl q => (none, q.2)
    | Sum.inr q => (some q.1, q.2)
  left_inv := by rintro ⟨(_ | i), n⟩ <;> rfl
  right_inv := by rintro (⟨⟨⟩, n⟩ | ⟨i, n⟩) <;> rfl

variable (C ι : Type*) [CommRing C]

/-- **One differential indeterminate splits off the top**: `C{Option ι} ≃ (C{ι}){y}`. -/
def splitOffEquiv :
    DifferentialPolynomial (Option ι) C ≃+*
      DifferentialPolynomial Unit (DifferentialPolynomial ι C) :=
  (MvPolynomial.renameEquiv C (optionIndexSplit ι)).toRingEquiv.trans
    (MvPolynomial.sumRingEquiv C (Unit × ℕ) (ι × ℕ))

@[simp] theorem splitOffEquiv_C (c : C) :
    splitOffEquiv C ι (MvPolynomial.C c) = MvPolynomial.C (MvPolynomial.C c) := by
  simp [splitOffEquiv, MvPolynomial.sumRingEquiv_C]

@[simp] theorem splitOffEquiv_X_none (n : ℕ) :
    splitOffEquiv C ι (MvPolynomial.X ((none, n) : (Option ι) × ℕ))
      = MvPolynomial.X (((), n) : Unit × ℕ) := by
  simp [splitOffEquiv, optionIndexSplit, MvPolynomial.sumRingEquiv_X_inl]

@[simp] theorem splitOffEquiv_X_some (i : ι) (n : ℕ) :
    splitOffEquiv C ι (MvPolynomial.X ((some i, n) : (Option ι) × ℕ))
      = MvPolynomial.C (MvPolynomial.X ((i, n) : ι × ℕ)) := by
  simp [splitOffEquiv, optionIndexSplit, MvPolynomial.sumRingEquiv_X_inr]

variable [Differential C]

attribute [local instance] differentialPolynomialOverDifferential

/-- **The splitting is differential**: it intertwines the total derivative of `C{Option ι}` with
the total derivative of `(C{ι}){y}` over the total derivative of `C{ι}`. -/
theorem splitOffEquiv_deriv (P : DifferentialPolynomial (Option ι) C) :
    splitOffEquiv C ι (differentialPolynomialOverDerivation (Option ι) C P)
      = differentialPolynomialOverDerivation Unit (DifferentialPolynomial ι C)
          (splitOffEquiv C ι P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [differentialPolynomialOverDerivation_C, splitOffEquiv_C, splitOffEquiv_C,
        differentialPolynomialOverDerivation_C]
      exact congrArg MvPolynomial.C (differentialPolynomialOverDerivation_C c).symm
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      have hX : splitOffEquiv C ι (differentialPolynomialOverDerivation (Option ι) C
          (MvPolynomial.X j))
          = differentialPolynomialOverDerivation Unit (DifferentialPolynomial ι C)
            (splitOffEquiv C ι (MvPolynomial.X j)) := by
        obtain ⟨u, n⟩ := j
        cases u with
        | none => simp
        | some i =>
            rw [differentialPolynomialOverDerivation_X, splitOffEquiv_X_some,
              splitOffEquiv_X_some, differentialPolynomialOverDerivation_C]
            exact congrArg MvPolynomial.C
              (differentialPolynomialOverDerivation_X (K := C) i n).symm
      have hL : differentialPolynomialOverDerivation (Option ι) C (P * MvPolynomial.X j)
          = differentialPolynomialOverDerivation (Option ι) C P * MvPolynomial.X j
            + P * differentialPolynomialOverDerivation (Option ι) C (MvPolynomial.X j) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      have hR : differentialPolynomialOverDerivation Unit (DifferentialPolynomial ι C)
          (splitOffEquiv C ι P * splitOffEquiv C ι (MvPolynomial.X j))
          = differentialPolynomialOverDerivation Unit (DifferentialPolynomial ι C)
              (splitOffEquiv C ι P) * splitOffEquiv C ι (MvPolynomial.X j)
            + splitOffEquiv C ι P * differentialPolynomialOverDerivation Unit
                (DifferentialPolynomial ι C) (splitOffEquiv C ι (MvPolynomial.X j)) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      rw [hL, map_add, map_mul, map_mul, hP, hX, map_mul, hR]

end

end GaloisForLFunctions.HTGeometry
