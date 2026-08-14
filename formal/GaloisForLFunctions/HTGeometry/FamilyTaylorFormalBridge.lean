import GaloisForLFunctions.HTGeometry.TaylorFormalBridge
import GaloisForLFunctions.HTGeometry.FamilyJetFlattening

/-!
# Joint hypertranscendence of a family, from formal survival

A family of smooth functions is **jointly differentially algebraic** when one nonzero polynomial in
the point and in the jets of *all* members vanishes identically.  This file transports that notion
across the Taylor map exactly as the single-function bridge does: the Taylor series of a joint jet
substitution is the formal substitution into the family jet vector of the Taylor series, so a family
whose formal jet vector survives every nonzero relation is jointly hypertranscendental.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*}

/-- The joint jet point of a family at `z`: the point slot carries `z`, the slot `(i, j)` the
`j`-th derivative of the `i`-th member. -/
def famJetPoint (f : ι → ℂ → ℂ) (n : ℕ) (z : ℂ) : Option (ι × Fin (n + 1)) → ℂ
  | none => z
  | some p => iteratedDeriv (p.2 : ℕ) (f p.1) z

@[simp] theorem famJetPoint_none (f : ι → ℂ → ℂ) (n : ℕ) (z : ℂ) :
    famJetPoint f n z none = z := rfl

@[simp] theorem famJetPoint_some (f : ι → ℂ → ℂ) (n : ℕ) (z : ℂ) (p : ι × Fin (n + 1)) :
    famJetPoint f n z (some p) = iteratedDeriv (p.2 : ℕ) (f p.1) z := rfl

/-- **Jointly differentially algebraic.**  One nonzero polynomial in the point and in the jets of
every member vanishes identically. -/
def JointlyDifferentiallyAlgebraic (f : ι → ℂ → ℂ) : Prop :=
  ∃ (n : ℕ) (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ), Q ≠ 0 ∧
    ∀ z : ℂ, MvPolynomial.eval (famJetPoint f n z) Q = 0

/-- **Jointly hypertranscendental.**  The family satisfies no joint algebraic differential
equation. -/
def JointlyHypertranscendental (f : ι → ℂ → ℂ) : Prop :=
  ¬ JointlyDifferentiallyAlgebraic f

variable (f : ι → ℂ → ℂ) (n : ℕ)

/-- The joint jet substitution as a function of the point. -/
def famJetFun (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) : ℂ → ℂ :=
  fun z => MvPolynomial.eval (famJetPoint f n z) Q

theorem famJetFun_C (a : ℂ) : famJetFun f n (C a) = fun _ => a := by
  funext z
  simp [famJetFun]

theorem famJetFun_add (p q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    famJetFun f n (p + q) = famJetFun f n p + famJetFun f n q := by
  funext z
  simp only [famJetFun, map_add]
  rfl

theorem famJetFun_mul (p q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    famJetFun f n (p * q) = famJetFun f n p * famJetFun f n q := by
  funext z
  simp only [famJetFun, map_mul]
  rfl

theorem famJetFun_X_none : famJetFun f n (MvPolynomial.X none) = fun z => z := by
  funext z
  simp [famJetFun]

theorem famJetFun_X_some (p : ι × Fin (n + 1)) :
    famJetFun f n (MvPolynomial.X (some p)) = iteratedDeriv (p.2 : ℕ) (f p.1) := by
  funext z
  simp [famJetFun]

/-- Every joint jet substitution of a smooth family is smooth. -/
theorem contDiff_famJetFun (hf : ∀ i, ContDiff ℂ (⊤ : ℕ∞) (f i))
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (famJetFun f n Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [famJetFun_C]; exact contDiff_const
  | add p q hp hq => rw [famJetFun_add]; exact hp.add hq
  | mul_X p s hp =>
    rw [famJetFun_mul]
    refine hp.mul ?_
    cases s with
    | none => rw [famJetFun_X_none]; exact contDiff_id
    | some r => rw [famJetFun_X_some]; exact contDiff_iteratedDeriv _ (hf r.1)

/-- **Family Taylor bridge.**  The Taylor series of a joint jet substitution is the formal
substitution into the family jet vector of the Taylor series. -/
theorem taylorPS_famJetFun (hf : ∀ i, ContDiff ℂ (⊤ : ℕ∞) (f i))
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    taylorPS (famJetFun f n Q) = aeval (familyJets n (fun i => taylorPS (f i))) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [famJetFun_C, taylorPS_const, aeval_C]; rfl
  | add p q hp hq =>
      rw [famJetFun_add, taylorPS_add (contDiff_famJetFun f n hf p)
        (contDiff_famJetFun f n hf q), hp, hq, map_add]
  | mul_X p s hp =>
      rw [famJetFun_mul, taylorPS_mul (contDiff_famJetFun f n hf p)
        (contDiff_famJetFun f n hf _), hp, map_mul]
      congr 1
      cases s with
      | none => rw [famJetFun_X_none, taylorPS_id, aeval_X, familyJets_none]
      | some r => rw [famJetFun_X_some, taylorPS_iteratedDeriv, aeval_X, familyJets_some]

/-- **Joint hypertranscendence from formal survival.**  If the family jet vector of the Taylor
series survives every nonzero formal relation, the family is jointly hypertranscendental. -/
theorem jointlyHypertranscendental_of_aeval_survives (hf : ∀ i, ContDiff ℂ (⊤ : ℕ∞) (f i))
    (hsurv : ∀ (m : ℕ) (Q : MvPolynomial (Option (ι × Fin (m + 1))) ℂ), Q ≠ 0 →
      aeval (familyJets m (fun i => taylorPS (f i))) Q ≠ 0) :
    JointlyHypertranscendental f := by
  rintro ⟨m, Q, hQ, hrel⟩
  refine hsurv m Q hQ ?_
  have hjz : famJetFun f m Q = 0 := by
    funext z
    exact hrel z
  rw [← taylorPS_famJetFun f m hf Q, hjz, show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl,
    taylorPS_const, map_zero]

end

end GaloisForLFunctions
