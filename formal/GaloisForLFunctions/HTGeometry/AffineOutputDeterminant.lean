import GaloisForLFunctions.HTGeometry.AffinePeelInduction
import GaloisForLFunctions.HTGeometry.PairFamHeadJacobian
import GaloisForLFunctions.HTGeometry.PairHeadProduct

/-!
# The output jets of the newest coordinate, for a rational affine family

The law is affine in the newest coordinate,

`δ X_(m+1) = (∏_(j<m) fac j · lead m)·X_(m+1) + (∏_(j<m) fac j · cnst m)`,

with both coefficients one level down.  The corpus's affine-top reduction then turns the output-jet
Jacobian of `X_(m+1)` into the Jacobian of the affine Bell values of the multiplier, and the Bell
identification turns that into the head product's jet Jacobian — which the peel has proved
nonsingular.

The multiplier *is* the head product `(∏_(j<m) fac j)·lead m`, with the leading coefficient of the
factor as its head.  That is why the peel had to carry a head.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace AffineFam

variable (E : AffineFam)

/-- **The law is affine in the newest coordinate, with the head product as multiplier.** -/
theorem law_fx_affine (m : ℕ) :
    E.toPairFam.law (fx (m + 1))
      = E.toPairFam.head (E.lead m) m * fx (m + 1)
        + E.toPairFam.jet m * E.cnst m := by
  rw [PairFam.law_fx, E.jet_succ_eq m, fac, PairFam.head]
  ring

/-- **The affine-top reduction.** -/
theorem det_ne_zero_of_top {m : ℕ}
    (hsub : (Matrix.of fun i j : Fin m =>
        fpderiv ((j : ℕ) + 1)
          (genJetA E.toPairFam.law (E.toPairFam.head (E.lead m) m) ((i : ℕ) + 1))).det ≠ 0) :
    (Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((E.toPairFam.law : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((E.toPairFam.law : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j).det ≠ 0 := by
  refine det_ne_zero_of_affine_top_general (δ := E.toPairFam.law) (dtop := fpderiv (m + 1))
    (c := fun j : Fin m => fpderiv ((j : ℕ) + 1)) (S := (coordField m).toSubalgebra)
    (E.law_fx_affine m)
    (fun z hz => E.toPairFam.law_mem_coordField hz)
    (E.toPairFam.head_mem_coordField (E.lead_mem_coordField (le_refl m)))
    (mul_mem (E.toPairFam.jet_mem_coordField (le_refl m)) (E.cnst_mem_coordField (le_refl m)))
    (fpderiv_fx_self (m + 1))
    (fun z hz => by
      have hz' : z ∈ coordField m := hz
      rw [mem_coordField_iff] at hz'
      exact hz' (m + 1) (by omega))
    (fun j => fpderiv_fx_of_ne (by omega))
    (fun j z hz => fpderiv_mem_coordField _ hz)
    (injective_aeval_fx_coordField m)
    hsub

end AffineFam

namespace RatAffineFam

variable (R : RatAffineFam)

/-- **The head product's jet Jacobian is nonsingular.** -/
theorem headJetJacobian_det_ne_zero
    (hdeg : ∀ j, (R.ld j).natDegree ≤ (R.ln j).natDegree) (m : ℕ) :
    (R.toAffineFam.toPairFam.headJetJacobian (R.toAffineFam.lead m) m).det ≠ 0 := by
  match m with
  | 0 =>
      rw [Matrix.det_fin_zero]
      exact one_ne_zero
  | (n + 1) =>
      refine R.toAffineFam.toPairFam.headJetJacobian_det_ne_zero_of_orbit n
        (R.toAffineFam.lead_ne_zero (n + 1))
        (R.toAffineFam.lead_mem_coordField (le_refl (n + 1))) ?_
      rw [R.lead_eq (n + 1)]
      refine R.det_orbitMatrix_ne_zero_of_peelHyp hdeg n (R.ln (n + 1)) (R.ld (n + 1))
        (R.ln_ne_zero (n + 1)) (R.ld_ne_zero (n + 1)) ?_ _
        (R.peelHyp_headBorder (R.ln_ne_zero (n + 1)) (R.ld_ne_zero (n + 1)) n)
      have := hdeg (n + 1)
      omega

/-- **The output-jet Jacobian of the newest coordinate is nonsingular, at every height.** -/
theorem output_det_ne_zero (hdeg : ∀ j, (R.ld j).natDegree ≤ (R.ln j).natDegree) (m : ℕ) :
    (Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((R.toAffineFam.toPairFam.law : CascadeField → CascadeField)^[(i : ℕ)])
              (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((R.toAffineFam.toPairFam.law : CascadeField → CascadeField)^[(i : ℕ)])
              (fx (m + 1))))
          j).det ≠ 0 := by
  refine R.toAffineFam.det_ne_zero_of_top ?_
  match m with
  | 0 => simp
  | (n + 1) =>
      have hbell := det_genJetA_eq_det_jets R.toAffineFam.toPairFam.law n
        (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1))
        (R.toAffineFam.toPairFam.head (R.toAffineFam.lead (n + 1)) (n + 1))
      have hL : (Matrix.of fun i j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (genJetA R.toAffineFam.toPairFam.law
              (R.toAffineFam.toPairFam.head (R.toAffineFam.lead (n + 1)) (n + 1))
              ((i : ℕ) + 1)))
          = Matrix.of fun i j : Fin (n + 1) =>
            (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1)) j.castSucc
              (genJetA R.toAffineFam.toPairFam.law
                (R.toAffineFam.toPairFam.head (R.toAffineFam.lead (n + 1)) (n + 1))
                ((i : ℕ) + 1)) := by
        funext i j
        rfl
      have hR : (Matrix.of fun i j : Fin (n + 1) =>
          (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1)) j.castSucc
            (((R.toAffineFam.toPairFam.law : CascadeField → CascadeField)^[(i : ℕ)])
              (R.toAffineFam.toPairFam.head (R.toAffineFam.lead (n + 1)) (n + 1))))
          = R.toAffineFam.toPairFam.headJetJacobian (R.toAffineFam.lead (n + 1)) (n + 1) := by
        funext i j
        simp only [Matrix.of_apply, PairFam.headJetJacobian, Fin.val_castSucc]
      rw [hL, hbell, hR]
      exact R.headJetJacobian_det_ne_zero hdeg (n + 1)

end RatAffineFam

end GaloisForLFunctions.HTGeometry
