import GaloisForLFunctions.HTGeometry.SourceBox
import GaloisForLFunctions.HTGeometry.BlockMonomialEval
import GaloisForLFunctions.HTGeometry.FamilyTaylorFormalBridge

/-!
# The orbit family of finitely many exponential phases

A *member* of the orbit family is a source index together with an additive shift; its carrier is the
source composed with the exponential phase of that member.  The jets of the carrier are the
jet-weighted series of the source at the *node* of the member, times a power of the frequency.

Consequently every jet monomial of the family, evaluated at finitely many sample points, is a
block monomial in the sample points and in those jet values, and is a continuous function of the
sources.  So a nonsingular evaluation matrix is an open condition on the sources.
-/

open Polynomial Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {L : ℕ} {ι : Type}

/-- The node of a member at a sample point. -/
def orbNode (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) (i : ι) (t : ℂ) : ℂ :=
  Complex.exp (lam (src i) * t + sh i)

theorem orbNode_ne_zero (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) (i : ι) (t : ℂ) :
    orbNode lam src sh i t ≠ 0 := Complex.exp_ne_zero _

/-- The carrier of a member: the source along its exponential phase. -/
def orbFun (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) (C : Fin L → sourceBox) (i : ι) :
    ℂ → ℂ :=
  fun t => jetSeriesFun (boxSeq (C (src i))) 0 (Complex.exp (lam (src i) * t + sh i))

/-- **The jets of a member's carrier are the jet-weighted series at its node.** -/
theorem iteratedDeriv_orbFun (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ)
    (C : Fin L → sourceBox) (i : ι) (r : ℕ) (t : ℂ) :
    iteratedDeriv r (orbFun lam src sh C i) t =
      lam (src i) ^ r * jetSeriesFun (boxSeq (C (src i))) r (orbNode lam src sh i t) :=
  iteratedDeriv_expComp_jetSeriesFun (boxSeq_bound (C (src i))) _ _ r t

/-- The jet point of the orbit family, in terms of the nodes. -/
theorem famJetPoint_orbFun (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ)
    (C : Fin L → sourceBox) (n : ℕ) (t : ℂ) :
    famJetPoint (orbFun lam src sh C) n t =
      fun v => v.elim t fun p =>
        lam (src p.1) ^ (p.2 : ℕ) *
          jetSeriesFun (boxSeq (C (src p.1))) (p.2 : ℕ) (orbNode lam src sh p.1 t) := by
  funext v
  cases v with
  | none => rfl
  | some p => exact iteratedDeriv_orbFun lam src sh C p.1 (p.2 : ℕ) t

/-! ### Continuity in the sources -/

theorem continuous_famJetPoint_orbFun (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ)
    (n : ℕ) (t : ℂ) (v : Option (ι × Fin (n + 1))) :
    Continuous fun C : Fin L → sourceBox => famJetPoint (orbFun lam src sh C) n t v := by
  have hfun : (fun C : Fin L → sourceBox => famJetPoint (orbFun lam src sh C) n t v) =
      fun C : Fin L → sourceBox => v.elim t fun p =>
        lam (src p.1) ^ (p.2 : ℕ) *
          jetSeriesFun (boxSeq (C (src p.1))) (p.2 : ℕ) (orbNode lam src sh p.1 t) := by
    funext C
    exact congrFun (famJetPoint_orbFun lam src sh C n t) v
  rw [hfun]
  cases v with
  | none => exact continuous_const
  | some p =>
      exact continuous_const.mul
        ((continuous_jetSeriesFun_box (p.2 : ℕ) (orbNode lam src sh p.1 t)).comp
          (continuous_apply (src p.1)))

/-! ### The evaluation determinant -/

variable [Fintype ι] [DecidableEq ι]

/-- The evaluation matrix of a finite family of jet monomials at finitely many sample points. -/
def orbEvalMatrix (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ) (C : Fin L → sourceBox)
    {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) (t : Fin K → ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i a => (M i).prod fun v e => (famJetPoint (orbFun lam src sh C) n (t a) v) ^ e

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_orbEvalMatrix_det (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ)
    {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) (t : Fin K → ℂ) :
    Continuous fun C : Fin L → sourceBox => (orbEvalMatrix lam src sh C M t).det := by
  classical
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun a => ?_
  rw [show (fun C : Fin L → sourceBox => orbEvalMatrix lam src sh C M t i a) =
      fun C : Fin L → sourceBox =>
        ∏ v ∈ (M i).support, (famJetPoint (orbFun lam src sh C) n (t a) v) ^ ((M i) v) from rfl]
  exact continuous_finsetProd _ fun v _ =>
    (continuous_famJetPoint_orbFun lam src sh n (t a) v).pow _

/-- The set of sources for which a finite family of jet monomials has a nonsingular evaluation
matrix at some sample points. -/
def orbGood (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ)
    {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) : Set (Fin L → sourceBox) :=
  {C | ∃ t : Fin K → ℂ, (orbEvalMatrix lam src sh C M t).det ≠ 0}

omit [Fintype ι] [DecidableEq ι] in
/-- **A nonsingular evaluation matrix is an open condition on the sources.** -/
theorem isOpen_orbGood (lam : Fin L → ℂ) (src : ι → Fin L) (sh : ι → ℂ)
    {n K : ℕ} (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) :
    IsOpen (orbGood lam src sh M) := by
  have hunion : orbGood lam src sh M =
      ⋃ t : Fin K → ℂ, {C : Fin L → sourceBox | (orbEvalMatrix lam src sh C M t).det ≠ 0} := by
    ext C
    simp [orbGood]
  rw [hunion]
  refine isOpen_iUnion fun t => ?_
  exact (continuous_orbEvalMatrix_det lam src sh M t).isOpen_preimage {0}ᶜ isOpen_compl_singleton

omit [Fintype ι] [DecidableEq ι] in
/-- **A nonsingular evaluation matrix forces the jet monomials to be linearly independent.** -/
theorem linearIndependent_of_orbEvalMatrix_det_ne_zero (lam : Fin L → ℂ) (src : ι → Fin L)
    (sh : ι → ℂ) (C : Fin L → sourceBox) {n K : ℕ}
    (M : Fin K → (Option (ι × Fin (n + 1)) →₀ ℕ)) (t : Fin K → ℂ)
    (hdet : (orbEvalMatrix lam src sh C M t).det ≠ 0) {γ : Fin K → ℂ}
    (hrel : ∀ z : ℂ, ∑ i : Fin K, γ i *
      ((M i).prod fun v e => (famJetPoint (orbFun lam src sh C) n z v) ^ e) = 0) :
    γ = 0 := by
  classical
  have hzero : (orbEvalMatrix lam src sh C M t).vecMul γ = 0 := by
    funext a
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    exact hrel (t a)
  exact Matrix.eq_zero_of_vecMul_eq_zero hdet hzero

end

end GaloisForLFunctions.HTGeometry
