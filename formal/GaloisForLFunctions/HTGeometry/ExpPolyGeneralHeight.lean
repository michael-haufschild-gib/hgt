import GaloisForLFunctions.HTGeometry.ExpPolyTwoMap

/-!
# Every height, modulo one determinant

The chain from the bordered determinant to the analytic conclusion is height-independent: only the
`1×1` evaluation at the base was special.  This file states the general form — a cascade of
polynomial-coefficient first-order linear entire maps has differential order equal to its length as
soon as the bordered Bell determinant of its head product is nonzero.

Everything else — the analytic law, the transcendence, the upper bound, the reductions, and the
transport between the polynomial and rational models — is already discharged.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {A : ℕ → Polynomial ℂ} {c d : ℕ → ℂ}

/-- The general shape identification: the last column of the output Jacobian is the newest
derivation. -/
theorem jetDet_ne_zero_general {Q v : ℕ → Polynomial ℂ} {m : ℕ} {α β : ℂ} (hα : α ≠ 0)
    (hv : v (m + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hbord : (headJetJacobian Q v m).det ≠ 0) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1))
          (modelJet (polyProdDerivation Q v) (m + 1) (j : ℕ))).det ≠ 0 := by
  refine jetDet_ne_zero_of_field Q v (m := m) (N := m + 1) ?_
  have hshape : (Matrix.of fun i j : Fin (m + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
      = Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j := by
    funext i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · show fpderiv (((Fin.last m : Fin (m + 1)) : ℕ) + 1)
          (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1)))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv (m + 1)
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (fun j'' : Fin m => fpderiv ((j'' : ℕ) + 1)
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (Fin.last m)
      rw [Fin.lastCases_last, Fin.val_last]
    · show fpderiv (((j'.castSucc : Fin (m + 1)) : ℕ) + 1)
          (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1)))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv (m + 1)
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (fun j'' : Fin m => fpderiv ((j'' : ℕ) + 1)
              (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            j'.castSucc
      rw [Fin.lastCases_castSucc, Fin.val_castSucc]
  rw [hshape]
  exact prodOutput_det_ne_zero_of_headJetJacobian Q v hα hv hbord

/-- **The card's law for a polynomial-coefficient cascade, modulo the head determinant.** -/
theorem exactDifferentialOrder_expPolyCascade
    (hc : ∀ k, c k ≠ 0) (hA : ∀ k, 1 ≤ (A k).natDegree) {m : ℕ}
    (hbord : (headJetJacobian (polyQ A d) (polyV d) m).det ≠ 0) :
    ExactDifferentialOrder (entireCascade (expPoly A c d) (m + 1)) (m + 1) := by
  have hall : ∀ k, TranscendentalEntire (expPoly A c d k) :=
    fun k => transcendentalEntire_expPoly (hc k) (hA k)
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall
    (fun k _ => differentiallyAlgebraicOfOrder_one_expPoly A c d k), ?_⟩
  intro n hn hDA
  -- the top order is excluded, and orders are monotone
  have htop : ¬ DifferentiallyAlgebraicOfOrder (entireCascade (expPoly A c d) (m + 1)) m := by
    refine not_differentiallyAlgebraicOfOrder_of_model
      (δ := polyProdDerivation (polyQ A d) (polyV d))
      (Y := entireCascade (expPoly A c d)) (N := m + 1) (m := m)
      (fun k => differentiable_expPolyCascade A c d k)
      (fun k z => law_expPolyCascade A c d k z)
      (fun Q hQ => exists_evalAt_ne_zero_of_transcendental hall hQ) ?_ rfl
    refine algebraicIndependent_cons_of_jetDet ?_
    refine jetDet_ne_zero_general (α := 1) (β := -(d m)) one_ne_zero ?_ hbord
    rw [polyV_succ, map_neg, map_one]
    ring
  exact htop (hDA.mono (by omega))

end GaloisForLFunctions.HTGeometry
