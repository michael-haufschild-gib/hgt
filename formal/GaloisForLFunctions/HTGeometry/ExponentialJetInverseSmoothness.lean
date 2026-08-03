import GaloisForLFunctions.HTGeometry.JetMapSmoothness

/-!
# Smoothness of the inverse exponential jet map

The inverse of the exponential jet recursion is a logarithm in the zeroth entry followed by a
triangular back-substitution.  Both steps are smooth where they are defined: the branch is smooth
off the cut, and the back-substitution divides by the zeroth entry, which is never zero there.

This is what makes the Cayley outer chart a local diffeomorphism rather than merely an open map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The back-substituted tail of the inverse exponential jet map. -/
def expJetTail (a : ℂ) (w : ℕ → ℂ) : ℕ → ℂ :=
  triangularSolve (Complex.exp (logBranch a (w 0))) (expJetLower (logBranch a (w 0)))
    fun k => w (k + 1)

theorem expJetInv_succ (a : ℂ) (w : ℕ → ℂ) (k : ℕ) :
    expJetInv a w (k + 1) = expJetTail a w k := rfl

/-- The tail recursion, with the diagonal slot of the lower part already zeroed. -/
theorem expJetTail_eq (a : ℂ) (w : ℕ → ℂ) (k : ℕ) :
    expJetTail a w k
      = (w (k + 1) - expJetScalar (expJetExtend (logBranch a (w 0))
          (fun j => if _ : j < k then expJetTail a w j else 0)) (k + 1))
        / Complex.exp (logBranch a (w 0)) := by
  rw [expJetTail, triangularSolve_eq, expJetLower]
  simp only [dif_neg (lt_irrefl k), mul_zero, sub_zero]

theorem contDiffOn_logBranch_comp {V : Set X} {W : X → ℕ → ℂ} (a : ℂ)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => W x 0) V)
    (hslit : ∀ x ∈ V, W x 0 / Complex.exp a ∈ Complex.slitPlane) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => logBranch a (W x 0)) V := by
  have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => W x 0 / Complex.exp a) V := hW.div_const _
  refine contDiffOn_const.add ?_
  intro x hx
  exact ((Complex.contDiffAt_log (hslit x hx)).restrict_scalars ℝ).comp_contDiffWithinAt x
    (hdiv x hx)

/-- **The inverse exponential jet map is smooth where the branch is.** -/
theorem contDiffOn_expJetTail_comp {V : Set X} {W : X → ℕ → ℂ} (a : ℂ)
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => W x j) V)
    (hslit : ∀ x ∈ V, W x 0 / Complex.exp a ∈ Complex.slitPlane) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => expJetTail a (W x) k) V := by
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => logBranch a (W x 0)) V :=
    contDiffOn_logBranch_comp a (hW 0) hslit
  have hexpb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Complex.exp (logBranch a (W x 0))) V :=
    Complex.contDiff_exp.comp_contDiffOn hb
  have hexpbne : ∀ x ∈ V, Complex.exp (logBranch a (W x 0)) ≠ 0 := fun x _ =>
    Complex.exp_ne_zero _
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hcoord : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => expJetExtend (logBranch a (W x 0))
          (fun j => if _ : j < k then expJetTail a (W x) j else 0) j) V := by
      intro j
      cases j with
      | zero =>
          simpa only [expJetExtend_zero] using hb
      | succ l =>
          simp only [expJetExtend_succ]
          by_cases hl : l < k
          · simp only [dif_pos hl]
            exact ih l hl
          · simp only [dif_neg hl]
            exact contDiffOn_const
    have hnum : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => W x (k + 1) - expJetScalar (expJetExtend (logBranch a (W x 0))
          (fun j => if _ : j < k then expJetTail a (W x) j else 0)) (k + 1)) V :=
      (hW (k + 1)).sub (contDiffOn_expJetScalar_comp
        (A := fun x j => expJetExtend (logBranch a (W x 0))
          (fun j => if _ : j < k then expJetTail a (W x) j else 0) j) hcoord (k + 1))
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => (W x (k + 1) - expJetScalar (expJetExtend (logBranch a (W x 0))
          (fun j => if _ : j < k then expJetTail a (W x) j else 0)) (k + 1))
            * (Complex.exp (logBranch a (W x 0)))⁻¹) V :=
      hnum.mul (hexpb.inv hexpbne)
    have hval : ∀ x : X, (W x (k + 1) - expJetScalar (expJetExtend (logBranch a (W x 0))
        (fun j => if _ : j < k then expJetTail a (W x) j else 0)) (k + 1))
          * (Complex.exp (logBranch a (W x 0)))⁻¹ = expJetTail a (W x) k := by
      intro x
      rw [expJetTail_eq, div_eq_mul_inv]
    simpa only [hval] using hdiv

theorem contDiffOn_expJetInv_comp {V : Set X} {W : X → ℕ → ℂ} (a : ℂ)
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => W x j) V)
    (hslit : ∀ x ∈ V, W x 0 / Complex.exp a ∈ Complex.slitPlane) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => expJetInv a (W x) k) V := by
  cases k with
  | zero =>
      simpa only [expJetInv_zero] using contDiffOn_logBranch_comp a (hW 0) hslit
  | succ l =>
      simpa only [expJetInv_succ] using contDiffOn_expJetTail_comp a hW hslit l

end

end GaloisForLFunctions.HTGeometry
