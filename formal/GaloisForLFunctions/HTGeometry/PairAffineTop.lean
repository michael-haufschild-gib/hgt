import GaloisForLFunctions.HTGeometry.PairHeadJetJacobian

/-!
# The output jets of the newest coordinate

The two-coordinate law is affine in the newest coordinate,

`δ X_(m+1) = (∏_(j<m) p_j · α(X_m))·X_(m+1) + (∏_(j<m) p_j · β(X_m))`,

with both coefficients free of that coordinate.  The corpus's affine-top reduction then turns the
output-jet Jacobian of `X_(m+1)` into the Jacobian of the affine Bell values of the multiplier, and
the Bell identification turns that into the head product's jet Jacobian — which the peel has
already proved nonsingular.

Unlike the univariate law, the multiplier here is not a complex scalar times a head product: it *is*
the head product, with its own head factor `α(X_m)`.  That is why the peel had to carry a head.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ} {α β : Polynomial ℂ}

/-- **The law is affine in the newest coordinate, with the head product as multiplier.** -/
theorem pairDerivation_fx_affine {m : ℕ} (hp : p m = affinePair α β) :
    pairDerivation p (fx (m + 1))
      = pairHead p α m * fx (m + 1) + pairJet p m * fact β m := by
  rw [pairDerivation_fx, pairJet_succ, pairFactor_top_eq hp, pairHead]
  ring

/-- **The affine-top reduction for the two-coordinate law.** -/
theorem pair_det_ne_zero_of_top {m : ℕ} (hp : p m = affinePair α β)
    (hsub : (Matrix.of fun i j : Fin m =>
        fpderiv ((j : ℕ) + 1)
          (genJetA (pairDerivation p) (pairHead p α m) ((i : ℕ) + 1))).det ≠ 0) :
    (Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j).det ≠ 0 := by
  refine det_ne_zero_of_affine_top_general (δ := pairDerivation p) (dtop := fpderiv (m + 1))
    (c := fun j : Fin m => fpderiv ((j : ℕ) + 1)) (S := (coordField m).toSubalgebra)
    (pairDerivation_fx_affine hp)
    (fun z hz => pairDerivation_mem_coordField hz)
    (pairHead_mem_coordField α m)
    (mul_mem (pairJet_mem_coordField (le_refl m)) (fact_mem_coordField (le_refl m) β))
    (fpderiv_fx_self (m + 1))
    (fun z hz => by
      have hz' : z ∈ coordField m := hz
      rw [mem_coordField_iff] at hz'
      exact hz' (m + 1) (by omega))
    (fun j => fpderiv_fx_of_ne (by omega))
    (fun j z hz => fpderiv_mem_coordField _ hz)
    (injective_aeval_fx_coordField m)
    hsub

/-- **The output-jet Jacobian of the newest coordinate is nonsingular, at every height.** -/
theorem pairOutput_det_ne_zero (a b : ℕ → Polynomial ℂ)
    (hp : ∀ j, p j = affinePair (a j) (b j)) (ha : ∀ j, a j ≠ 0) (m : ℕ) :
    (Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j).det ≠ 0 := by
  refine pair_det_ne_zero_of_top (hp m) ?_
  match m with
  | 0 => simp
  | (n + 1) =>
      have hbell := det_genJetA_eq_det_jets (pairDerivation p) n
        (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1)) (pairHead p (a (n + 1)) (n + 1))
      have hL : (Matrix.of fun i j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (genJetA (pairDerivation p) (pairHead p (a (n + 1)) (n + 1)) ((i : ℕ) + 1)))
          = Matrix.of fun i j : Fin (n + 1) =>
            (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1)) j.castSucc
              (genJetA (pairDerivation p) (pairHead p (a (n + 1)) (n + 1)) ((i : ℕ) + 1)) := by
        funext i j
        rfl
      have hR : (Matrix.of fun i j : Fin (n + 1) =>
          (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1)) j.castSucc
            (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)])
              (pairHead p (a (n + 1)) (n + 1))))
          = pairHeadJetJacobian p (a (n + 1)) (n + 1) := by
        funext i j
        simp only [Matrix.of_apply, pairHeadJetJacobian, Fin.val_castSucc]
      rw [hL, hbell, hR]
      exact pairHeadJetJacobian_det_ne_zero a b hp ha (ha (n + 1)) (n + 1)

end GaloisForLFunctions.HTGeometry
