import GaloisForLFunctions.HTGeometry.PairAffineTop
import GaloisForLFunctions.HTGeometry.ProductLawJetDeterminant

/-!
# From the rational model back to the polynomial one, for the two-coordinate law

The two-coordinate law is polynomial in the states, so its model lives in the polynomial ring; the
fraction field was needed only to run the determinant argument.  The two laws agree, because two
derivations of a polynomial ring into any module that agree on the variables are equal, so the
polynomial jets map onto the rational ones and a determinant computed in the field certifies the
polynomial one.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (p : ℕ → MvPolynomial (Fin 2) ℂ)

/-- The two-coordinate law on the polynomial ring. -/
noncomputable def polyPairDerivation :
    Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ fun k => ∏ j ∈ Finset.range k, pairPoly (p j) j

@[simp] theorem polyPairDerivation_X (k : ℕ) :
    polyPairDerivation p (MvPolynomial.X k) = ∏ j ∈ Finset.range k, pairPoly (p j) j :=
  MvPolynomial.mkDerivation_X ℂ _ k

theorem algebraMap_polyPairDerivation_X (k : ℕ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (∏ j ∈ Finset.range k, pairPoly (p j) j)
      = pairJet p k := by
  rw [map_prod, pairJet]
  rfl

/-- **The polynomial law maps onto the rational one.** -/
theorem algebraMap_polyPairDerivation (P : MvPolynomial ℕ ℂ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (polyPairDerivation p P)
      = pairDerivation p (algebraMap (MvPolynomial ℕ ℂ) CascadeField P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [show (MvPolynomial.C c : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) c from rfl,
        (polyPairDerivation p).map_algebraMap, map_zero,
        ← IsScalarTower.algebraMap_apply ℂ (MvPolynomial ℕ ℂ) CascadeField,
        (pairDerivation p).map_algebraMap]
  | add P R hP hR =>
      rw [map_add, map_add, map_add, map_add, hP, hR]
  | mul_X P k hP =>
      have hsmul : (polyPairDerivation p) (P * MvPolynomial.X k)
          = P * (polyPairDerivation p) (MvPolynomial.X k)
            + MvPolynomial.X k * (polyPairDerivation p) P := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      have hfield : pairDerivation p
          (algebraMap (MvPolynomial ℕ ℂ) CascadeField P
            * algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k))
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField P
              * pairDerivation p (algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k))
            + algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k)
              * pairDerivation p (algebraMap (MvPolynomial ℕ ℂ) CascadeField P) := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      rw [hsmul, map_add, map_mul, map_mul, hP, polyPairDerivation_X,
        algebraMap_polyPairDerivation_X, map_mul, hfield,
        show algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X k) = fx k from rfl,
        pairDerivation_fx]

theorem algebraMap_iterate_polyPairDerivation (P : MvPolynomial ℕ ℂ) (i : ℕ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField
        (((polyPairDerivation p : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) P)
      = ((pairDerivation p : CascadeField → CascadeField)^[i])
        (algebraMap (MvPolynomial ℕ ℂ) CascadeField P) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        algebraMap_polyPairDerivation, ih]

theorem algebraMap_pairModelJet (N i : ℕ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (modelJet (polyPairDerivation p) N i)
      = ((pairDerivation p : CascadeField → CascadeField)^[i]) (fx N) := by
  rw [modelJet, algebraMap_iterate_polyPairDerivation]
  rfl

/-- **A nonvanishing rational jet determinant certifies the polynomial one.** -/
theorem pairJetDet_ne_zero_of_field {N m : ℕ}
    (hfield : (Matrix.of fun i j : Fin (m + 1) =>
        fpderiv ((j : ℕ) + 1)
          (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx N))).det ≠ 0) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1))
          (modelJet (polyPairDerivation p) N (j : ℕ))).det ≠ 0 := by
  intro hzero
  refine hfield ?_
  have hmap : (Matrix.of fun i j : Fin (m + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx N)))
      = ((algebraMap (MvPolynomial ℕ ℂ) CascadeField).mapMatrix
          (Matrix.of fun i j : Fin (m + 1) =>
            (MvPolynomial.pderiv ((i : ℕ) + 1))
              (modelJet (polyPairDerivation p) N (j : ℕ)))).transpose := by
    funext i j
    rw [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.of_apply, algebraMap_pderiv, algebraMap_pairModelJet]
  rw [hmap, Matrix.det_transpose, ← RingHom.map_det, hzero, map_zero]

/-- **The output jet determinant of the two-coordinate law, in the plain shape.** -/
theorem pairJetDet_ne_zero_general {a b : ℕ → Polynomial ℂ}
    (hp : ∀ j, p j = affinePair (a j) (b j)) (ha : ∀ j, a j ≠ 0) (m : ℕ) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1))
          (modelJet (polyPairDerivation p) (m + 1) (j : ℕ))).det ≠ 0 := by
  refine pairJetDet_ne_zero_of_field p (N := m + 1) ?_
  have hshape : (Matrix.of fun i j : Fin (m + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
      = Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j := by
    funext i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · show fpderiv (((Fin.last m : Fin (m + 1)) : ℕ) + 1)
          (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1)))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv (m + 1)
              (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (fun j'' : Fin m => fpderiv ((j'' : ℕ) + 1)
              (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (Fin.last m)
      rw [Fin.lastCases_last, Fin.val_last]
    · show fpderiv (((j'.castSucc : Fin (m + 1)) : ℕ) + 1)
          (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1)))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv (m + 1)
              (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (fun j'' : Fin m => fpderiv ((j'' : ℕ) + 1)
              (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            j'.castSucc
      rw [Fin.lastCases_castSucc, Fin.val_castSucc]
  rw [hshape]
  exact pairOutput_det_ne_zero a b hp ha m

end GaloisForLFunctions.HTGeometry
