import GaloisForLFunctions.HTGeometry.ProductLawJetDeterminant
import GaloisForLFunctions.HTGeometry.ProductLawBaseCase

/-!
# Algebraic independence for a two-map linear cascade

Everything assembled: the rational determinant of a two-map linear-terminal product law is nonzero
whenever the first factor is nonconstant, it certifies the polynomial jet Jacobian, and the coordinate
contributes a unit column.  The coordinate together with the state and its derivative is therefore
algebraically independent — the hypothesis the analytic transfer theorem consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- **The two-map jet Jacobian, in the polynomial model.** -/
theorem jetDet_ne_zero_two {Q : ℕ → Polynomial ℂ} {α β : ℂ} (hα : α ≠ 0)
    (hv : v 2 = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hQ : ∀ j, Q j ≠ 0) (hQ1 : (Q 1).derivative ≠ 0) :
    (Matrix.of fun i j : Fin 2 =>
        (MvPolynomial.pderiv ((i : ℕ) + 1))
          (modelJet (polyProdDerivation Q v) 2 (j : ℕ))).det ≠ 0 := by
  refine jetDet_ne_zero_of_field Q v (m := 1) (N := 2) ?_
  have hshape : (Matrix.of fun i j : Fin 2 =>
      fpderiv ((j : ℕ) + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
      = Matrix.of fun i j : Fin 2 =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv 2
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
          (fun j' : Fin 1 => fpderiv ((j' : ℕ) + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
          j := by
    funext i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · show fpderiv (((Fin.last 1 : Fin 2) : ℕ) + 1)
          (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv 2
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
            (fun j' : Fin 1 => fpderiv ((j' : ℕ) + 1)
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
            (Fin.last 1)
      rw [Fin.lastCases_last]
      norm_num
    · show fpderiv (((j'.castSucc : Fin 2) : ℕ) + 1)
          (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv 2
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
            (fun j'' : Fin 1 => fpderiv ((j'' : ℕ) + 1)
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
            j'.castSucc
      rw [Fin.lastCases_castSucc, Fin.val_castSucc]
  rw [hshape]
  exact prodOutput_det_ne_zero_two v hα hv hQ hQ1

/-- **The coordinate, the state and its derivative are algebraically independent.** -/
theorem algebraicIndependent_two_map {Q : ℕ → Polynomial ℂ} {α β : ℂ} (hα : α ≠ 0)
    (hv : v 2 = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hQ : ∀ j, Q j ≠ 0) (hQ1 : (Q 1).derivative ≠ 0) :
    AlgebraicIndependent ℂ
      (Fin.cons (MvPolynomial.X (0 : ℕ))
        (fun j : Fin 2 => modelJet (polyProdDerivation Q v) 2 (j : ℕ)) :
        Fin 3 → MvPolynomial ℕ ℂ) :=
  algebraicIndependent_cons_of_jetDet (jetDet_ne_zero_two v hα hv hQ hQ1)

end GaloisForLFunctions.HTGeometry
