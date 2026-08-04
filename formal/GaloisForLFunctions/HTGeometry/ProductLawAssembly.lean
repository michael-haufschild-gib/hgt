import GaloisForLFunctions.HTGeometry.ProductLawDiagonal
import GaloisForLFunctions.HTGeometry.AffineTopBellJacobian

/-!
# Assembling the reductions for the product law

The top reduction and the Bell identification chain into a single statement: the output-jet Jacobian
of the newest coordinate of a linear-terminal product law is nonzero as soon as the jet Jacobian of
its head product is.

The head product is `∏_(j≤m) Q_j(X_j)`, one factor per earlier coordinate.  Its own multiplier is the
logarithmic sum, which — unlike the exponential tower's partial sums — still involves the coordinate
being eliminated, because the cancellation `(1/X)·X = 1` that the tower enjoys has no analogue for a
general pair `(Q_m, v_m)`.  That is precisely the step where the general product law parts company with
the tower, and it is the one remaining hypothesis here.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- Scalars pass through the jets. -/
theorem iterate_prodDerivation_algebraMap_mul (c : ℂ) (z : CascadeField) (i : ℕ) :
    ((prodDerivation Q v : CascadeField → CascadeField)^[i])
        (algebraMap ℂ CascadeField c * z)
      = algebraMap ℂ CascadeField c
        * ((prodDerivation Q v : CascadeField → CascadeField)^[i]) z := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz,
        (prodDerivation Q v).map_algebraMap, smul_zero, add_zero, smul_eq_mul,
        Function.iterate_succ_apply' (prodDerivation Q v : CascadeField → CascadeField) i z]

/-- The Jacobian of the jets of the head product. -/
noncomputable def headJetJacobian (m : ℕ) : Matrix (Fin m) (Fin m) CascadeField :=
  Matrix.of fun i j => fpderiv ((j : ℕ) + 1)
    (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (prodHead Q (m + 1)))

/-- **The output-jet Jacobian of the newest coordinate reduces to the head product's.** -/
theorem prodOutput_det_ne_zero_of_headJetJacobian {m : ℕ} {α β : ℂ} (hα : α ≠ 0)
    (hv : v (m + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hhead : (headJetJacobian Q v m).det ≠ 0) :
    (Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j).det ≠ 0 := by
  refine det_ne_zero_of_top_prod Q v hv ?_
  match m with
  | 0 => simp
  | (n + 1) =>
      have hbell := det_genJetA_eq_det_jets (prodDerivation Q v) n
        (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1))
        (algebraMap ℂ CascadeField α * prodHead Q (n + 2))
      have hL : (Matrix.of fun i j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (genJetA (prodDerivation Q v)
              (algebraMap ℂ CascadeField α * prodHead Q (n + 1 + 1)) ((i : ℕ) + 1)))
          = Matrix.of fun i j : Fin (n + 1) =>
            (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1)) j.castSucc
              (genJetA (prodDerivation Q v)
                (algebraMap ℂ CascadeField α * prodHead Q (n + 2)) ((i : ℕ) + 1)) := by
        funext i j
        rfl
      have hR : (Matrix.of fun i j : Fin (n + 1) =>
          (fun l : Fin (n + 2) => fpderiv ((l : ℕ) + 1)) j.castSucc
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)])
              (algebraMap ℂ CascadeField α * prodHead Q (n + 2))))
          = (algebraMap ℂ CascadeField α) • headJetJacobian Q v (n + 1) := by
        funext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, headJetJacobian,
          iterate_prodDerivation_algebraMap_mul Q v, Derivation.leibniz,
          Derivation.map_algebraMap, smul_zero, add_zero, Fin.val_castSucc]
      rw [hL, hbell, hR, Matrix.det_smul]
      refine mul_ne_zero (pow_ne_zero _ ?_) hhead
      simpa using hα

end GaloisForLFunctions.HTGeometry
