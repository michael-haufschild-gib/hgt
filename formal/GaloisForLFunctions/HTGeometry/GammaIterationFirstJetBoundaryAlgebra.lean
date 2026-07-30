import GaloisForLFunctions.HTGeometry.GammaIterationFirstJetBoundary
import GaloisForLFunctions.HTGeometry.GammaFirstJetRiccatiKernel
import GaloisForLFunctions.HTGeometry.MvPolynomialDiagonalScaleDomain
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Algebra of the complete first-jet Gamma boundary

The factorial boundary of the first-jet iterate tower has one apparent relation, the first-pair
Riccati equation `Z = W²`.  This file proves that it is the complete kernel.  After removing the
maximal power of `Z-W²`, the boundary remainder embeds as a nonzero polynomial in the preceding
first-jet coordinates.  The only subtle point is that later derivative variables are multiplied by
the nonunit `W²`; injectivity follows from diagonal scaling over an integral domain.
-/

namespace GaloisForLFunctions

noncomputable section

@[simp] theorem fin2_cases_one {α : Sort*} (z : α) (s : Fin 1 → α) :
    Fin.cases z s (1 : Fin 2) = s 0 := by
  change Fin.cases z s (Fin.succ 0) = s 0
  rw [Fin.cases_succ]

def firstJetBoundaryIndexEquiv (k : ℕ) :
    (Fin (k + 1) × Fin 2) ≃ Option (Option (Fin k × Fin 2)) where
  toFun p := Fin.cases
    (Fin.cases none (fun _ => some none) p.2)
    (fun j => some (some (j, p.2))) p.1
  invFun o := match o with
    | none => (0, 0)
    | some none => (0, 1)
    | some (some (j, slot)) => (j.succ, slot)
  left_inv p := by
    rcases p with ⟨j, slot⟩
    induction j using Fin.cases with
    | zero =>
        induction slot using Fin.cases with
        | zero => rfl
        | succ slot =>
            have hslot : slot = 0 := Subsingleton.elim _ _
            subst slot
            rfl
    | succ j => rfl
  right_inv o := by
    rcases o with (_ | (_ | ⟨j, slot⟩))
    · rfl
    · rfl
    · rfl

def firstJetTailNestedEquiv (k : ℕ) :
    MvPolynomial (Fin (k + 1) × Fin 2) ℂ ≃ₐ[ℂ]
      Polynomial (Polynomial (MvPolynomial (Fin k × Fin 2) ℂ)) :=
  (MvPolynomial.renameEquiv ℂ (firstJetBoundaryIndexEquiv k)).trans
    ((MvPolynomial.optionEquivLeft ℂ (Option (Fin k × Fin 2))).trans
      (Polynomial.mapAlgEquiv
        (MvPolynomial.optionEquivLeft ℂ (Fin k × Fin 2))))

theorem firstJetTailNestedEquiv_derivative_zero (k : ℕ) :
    firstJetTailNestedEquiv k (MvPolynomial.X (0, 0)) = Polynomial.X := by
  simp [firstJetTailNestedEquiv, firstJetBoundaryIndexEquiv]

theorem firstJetTailNestedEquiv_value_zero (k : ℕ) :
    firstJetTailNestedEquiv k (MvPolynomial.X (0, 1)) =
      Polynomial.C Polynomial.X := by
  have hindex : firstJetBoundaryIndexEquiv k (0, 1) = some none := by
    change Fin.cases (Fin.cases none (fun _ => some none) 1)
      (fun j => some (some (j, 1))) 0 = some none
    rw [Fin.cases_zero]
    change Fin.cases none (fun _ => some none) (Fin.succ 0) = some none
    rw [Fin.cases_succ]
  simp [firstJetTailNestedEquiv, hindex]

def firstJetBoundaryScale (i : Fin k × Fin 2) : Polynomial ℂ :=
  Fin.cases (Polynomial.X ^ 2) (fun _ => 1) i.2

def firstJetBoundaryVariablePolynomial (k : ℕ)
    (o : Option (Fin k × Fin 2)) :
    MvPolynomial (GammaIterateFirstJetIndex k) ℂ := match o with
  | none => MvPolynomial.X (Sum.inl 0)
  | some i => Fin.cases
      (MvPolynomial.X (Sum.inl 0) ^ 2 * MvPolynomial.X (Sum.inr i))
      (fun _ => MvPolynomial.X (Sum.inr i)) i.2

def firstJetBoundarySourceEmbedding (k : ℕ) :
    MvPolynomial (Option (Fin k × Fin 2)) ℂ →ₐ[ℂ]
      MvPolynomial (GammaIterateFirstJetIndex k) ℂ :=
  (MvPolynomial.rename
      (fun o : Option (Fin k × Fin 2) => o.elim (Sum.inl 0) Sum.inr)).comp
    ((MvPolynomial.optionEquivRight ℂ (Fin k × Fin 2)).symm.toAlgHom.comp
      ((mvPolynomialDiagonalScaleRing firstJetBoundaryScale).restrictScalars ℂ |>.comp
        (MvPolynomial.optionEquivRight ℂ (Fin k × Fin 2)).toAlgHom))

def firstJetBoundaryRemainderEmbedding (k : ℕ) :
    Polynomial (MvPolynomial (Fin k × Fin 2) ℂ) →
      MvPolynomial (GammaIterateFirstJetIndex k) ℂ := fun P =>
  firstJetBoundarySourceEmbedding k
    ((MvPolynomial.optionEquivLeft ℂ (Fin k × Fin 2)).symm P)

theorem firstJetBoundary_scaleEmbedding_eq_aeval
    (k : ℕ) (S : MvPolynomial (Option (Fin k × Fin 2)) ℂ) :
    firstJetBoundarySourceEmbedding k S =
      MvPolynomial.aeval (firstJetBoundaryVariablePolynomial k) S := by
  apply DFunLike.congr_fun ?_ S
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with (_ | ⟨j, slot⟩)
  · simp [firstJetBoundarySourceEmbedding, mvPolynomialDiagonalScaleRing,
      firstJetBoundaryVariablePolynomial]
  · induction slot using Fin.cases with
    | zero =>
        simp [firstJetBoundarySourceEmbedding, mvPolynomialDiagonalScaleRing,
          firstJetBoundaryScale, firstJetBoundaryVariablePolynomial]
    | succ slot =>
        have hslot : slot = 0 := Subsingleton.elim _ _
        subst slot
        simp [firstJetBoundarySourceEmbedding, mvPolynomialDiagonalScaleRing,
          firstJetBoundaryScale, firstJetBoundaryVariablePolynomial]

theorem firstJetBoundaryScale_ne_zero (i : Fin k × Fin 2) :
    firstJetBoundaryScale i ≠ 0 := by
  rcases i with ⟨j, slot⟩
  induction slot using Fin.cases with
  | zero => simp [firstJetBoundaryScale]
  | succ slot =>
      have hslot : slot = 0 := Subsingleton.elim _ _
      subst slot
      simpa only [firstJetBoundaryScale, Fin.cases_succ] using
        (one_ne_zero : (1 : Polynomial ℂ) ≠ 0)

theorem firstJetBoundaryRemainderEmbedding_ne_zero
    {k : ℕ} {P : Polynomial (MvPolynomial (Fin k × Fin 2) ℂ)} (hP : P ≠ 0) :
    firstJetBoundaryRemainderEmbedding k P ≠ 0 := by
  let E := MvPolynomial.optionEquivRight ℂ (Fin k × Fin 2)
  let L := MvPolynomial.optionEquivLeft ℂ (Fin k × Fin 2)
  let Q : MvPolynomial (Fin k × Fin 2) (Polynomial ℂ) := E (L.symm P)
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hP
    apply L.symm.injective
    apply E.injective
    simpa [Q] using hzero
  have hscale : mvPolynomialDiagonalScaleRing firstJetBoundaryScale Q ≠ 0 :=
    mvPolynomialDiagonalScaleRing_ne_zero firstJetBoundaryScale
      firstJetBoundaryScale_ne_zero hQ
  intro hzero
  apply hscale
  apply E.symm.injective
  let e : Option (Fin k × Fin 2) → GammaIterateFirstJetIndex k :=
    fun o => o.elim (Sum.inl 0) Sum.inr
  apply MvPolynomial.rename_injective e
  · intro a b hab
    rcases a with (_ | a) <;> rcases b with (_ | b)
    · rfl
    · simp [e] at hab
    · simp [e] at hab
    · change Sum.inr a = Sum.inr b at hab
      cases hab
      rfl
  · simpa [firstJetBoundaryRemainderEmbedding, E, L, Q, e] using! hzero

def gammaFirstJetBoundaryRestTuple (k : ℕ) (a : ℂ) : Fin k × Fin 2 → ℂ :=
  fun i => gammaFirstJetBoundaryTail k a (i.1.succ, i.2)

theorem eval_firstJetBoundaryVariablePolynomial (k : ℕ) (a : ℂ)
    (o : Option (Fin k × Fin 2)) :
    MvPolynomial.eval (gammaIterateFirstJetTuple k a)
        (firstJetBoundaryVariablePolynomial k o) =
      o.elim a (gammaFirstJetBoundaryRestTuple k a) := by
  rcases o with (_ | ⟨j, slot⟩)
  · simp [firstJetBoundaryVariablePolynomial, gammaIterateFirstJetTuple]
  · induction slot using Fin.cases with
    | zero =>
        simp [firstJetBoundaryVariablePolynomial, gammaIterateFirstJetTuple,
          gammaFirstJetBoundaryRestTuple, gammaFirstJetBoundaryTail,
          gammaFirstJetCompositionTail, gammaFirstJetCompositionData]
    | succ slot =>
        have hslot : slot = 0 := Subsingleton.elim _ _
        subst slot
        simp [firstJetBoundaryVariablePolynomial, gammaIterateFirstJetTuple,
          gammaFirstJetBoundaryRestTuple, gammaFirstJetBoundaryTail,
          gammaFirstJetCompositionTail, gammaFirstJetCompositionData]

theorem eval_firstJetBoundaryRemainderEmbedding
    (k : ℕ) (P : Polynomial (MvPolynomial (Fin k × Fin 2) ℂ)) (a : ℂ) :
    MvPolynomial.eval (gammaIterateFirstJetTuple k a)
        (firstJetBoundaryRemainderEmbedding k P) =
      Polynomial.eval a
        (Polynomial.map (MvPolynomial.eval (gammaFirstJetBoundaryRestTuple k a)) P) := by
  let L := MvPolynomial.optionEquivLeft ℂ (Fin k × Fin 2)
  let S : MvPolynomial (Option (Fin k × Fin 2)) ℂ := L.symm P
  rw [show firstJetBoundaryRemainderEmbedding k P =
      MvPolynomial.aeval (firstJetBoundaryVariablePolynomial k) S by
    simpa [firstJetBoundaryRemainderEmbedding, S] using
      firstJetBoundary_scaleEmbedding_eq_aeval k (L.symm P)]
  change MvPolynomial.aeval (gammaIterateFirstJetTuple k a)
      (MvPolynomial.aeval (firstJetBoundaryVariablePolynomial k) S) = _
  rw [MvPolynomial.comp_aeval_apply]
  have hfun : (fun o => MvPolynomial.aeval (gammaIterateFirstJetTuple k a)
      (firstJetBoundaryVariablePolynomial k o)) =
      fun o => o.elim a (gammaFirstJetBoundaryRestTuple k a) := by
    funext o
    simpa [MvPolynomial.aeval_eq_eval] using
      eval_firstJetBoundaryVariablePolynomial k a o
  rw [hfun]
  simpa [S, L, MvPolynomial.aeval_eq_eval] using
    MvPolynomial.optionEquivLeft_elim_eval
      ℂ (Fin k × Fin 2) (gammaFirstJetBoundaryRestTuple k a) a S

def firstJetNestedCoefficientEval (r : Fin k × Fin 2 → ℂ) (w : ℂ) :
    Polynomial (MvPolynomial (Fin k × Fin 2) ℂ) →+* ℂ :=
  (Polynomial.evalRingHom w).comp
    (Polynomial.mapRingHom (MvPolynomial.eval r))

def firstJetNestedEval (r : Fin k × Fin 2 → ℂ) (w z : ℂ)
    (P : Polynomial (Polynomial (MvPolynomial (Fin k × Fin 2) ℂ))) : ℂ :=
  Polynomial.eval₂ (firstJetNestedCoefficientEval r w) z P

theorem eval_firstJetTailNestedEquiv
    (k : ℕ) (r : Fin k × Fin 2 → ℂ) (w z : ℂ)
    (P : MvPolynomial (Fin (k + 1) × Fin 2) ℂ) :
    MvPolynomial.eval (fun i => Fin.cases
        (Fin.cases z (fun _ => w) i.2)
        (fun j => r (j, i.2)) i.1) P =
      firstJetNestedEval r w z (firstJetTailNestedEquiv k P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [firstJetNestedEval, firstJetNestedCoefficientEval,
      firstJetTailNestedEquiv]
  | add P Q hP hQ => simp [hP, hQ, firstJetNestedEval]
  | mul_X P i hP =>
      rw [map_mul, hP]
      rcases i with ⟨j, slot⟩
      induction j using Fin.cases with
      | zero =>
          induction slot using Fin.cases with
          | zero =>
              simp [firstJetNestedEval, firstJetNestedCoefficientEval,
                firstJetTailNestedEquiv, firstJetBoundaryIndexEquiv]
          | succ slot =>
              have hslot : slot = 0 := Subsingleton.elim _ _
              subst slot
              simp [firstJetNestedEval, firstJetNestedCoefficientEval,
                firstJetTailNestedEquiv, firstJetBoundaryIndexEquiv]
      | succ j =>
          induction slot using Fin.cases with
          | zero =>
              simp [firstJetNestedEval, firstJetNestedCoefficientEval,
                firstJetTailNestedEquiv, firstJetBoundaryIndexEquiv]
          | succ slot =>
              have hslot : slot = 0 := Subsingleton.elim _ _
              subst slot
              simp [firstJetNestedEval, firstJetNestedCoefficientEval,
                firstJetTailNestedEquiv, firstJetBoundaryIndexEquiv]

theorem firstJetNestedEval_riccatiBoundary
    (r : Fin k × Fin 2 → ℂ) (w : ℂ)
    (P : Polynomial (Polynomial (MvPolynomial (Fin k × Fin 2) ℂ))) :
    firstJetNestedEval r w (w ^ 2) P =
      Polynomial.eval w
        (Polynomial.map (MvPolynomial.eval r) (riccatiBoundarySubstitution P)) := by
  let f := firstJetNestedCoefficientEval r w
  have hX : f (Polynomial.X ^ 2) = w ^ 2 := by
    simp [f, firstJetNestedCoefficientEval]
  change Polynomial.eval₂ f (w ^ 2) P = _
  rw [← hX, Polynomial.eval₂_at_apply]
  simp [f, firstJetNestedCoefficientEval, riccatiBoundarySubstitution]

theorem firstJetNestedEval_riccatiNormalForm
    (r : Fin k × Fin 2 → ℂ) (w z : ℂ)
    (P Q : Polynomial (Polynomial (MvPolynomial (Fin k × Fin 2) ℂ)))
    (m : ℕ) (hP : P = riccatiBoundaryFactor ^ m * Q) :
    firstJetNestedEval r w z P =
      (z - w ^ 2) ^ m * firstJetNestedEval r w z Q := by
  rw [hP]
  simp only [firstJetNestedEval, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  have hfactor : Polynomial.eval₂ (firstJetNestedCoefficientEval r w) z
      riccatiBoundaryFactor = z - w ^ 2 := by
    rw [riccatiBoundaryFactor, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    simp [firstJetNestedCoefficientEval]
  rw [hfactor]

/-- Every nonzero first-jet tail polynomial has an exact maximal Riccati layer and a nonzero
polynomial on the preceding first-jet coordinates as its boundary quotient. -/
theorem exists_firstJetBoundaryMultiplicity_normalForm
    {k : ℕ} {P : MvPolynomial (Fin (k + 1) × Fin 2) ℂ} (hP : P ≠ 0) :
    ∃ Q : Polynomial (Polynomial (MvPolynomial (Fin k × Fin 2) ℂ)),
      ∃ B : MvPolynomial (GammaIterateFirstJetIndex k) ℂ,
        firstJetTailNestedEquiv k P =
            riccatiBoundaryFactor ^
              riccatiBoundaryMultiplicity (firstJetTailNestedEquiv k P) * Q ∧
          riccatiBoundarySubstitution Q ≠ 0 ∧
          B = firstJetBoundaryRemainderEmbedding k
            (riccatiBoundarySubstitution Q) ∧
          B ≠ 0 ∧
          ∀ a : ℂ, firstJetNestedEval (gammaFirstJetBoundaryRestTuple k a)
              a (a ^ 2) Q =
            MvPolynomial.eval (gammaIterateFirstJetTuple k a) B := by
  have hNested : firstJetTailNestedEquiv k P ≠ 0 := by
    intro hzero
    apply hP
    apply (firstJetTailNestedEquiv k).injective
    simpa using hzero
  obtain ⟨Q, hfactor, hQ⟩ :=
    exists_riccatiBoundaryMultiplicity_normalForm
      (firstJetTailNestedEquiv k P) hNested
  let B := firstJetBoundaryRemainderEmbedding k (riccatiBoundarySubstitution Q)
  have hB : B ≠ 0 := firstJetBoundaryRemainderEmbedding_ne_zero hQ
  refine ⟨Q, B, hfactor, hQ, rfl, hB, ?_⟩
  intro a
  rw [firstJetNestedEval_riccatiBoundary]
  exact (eval_firstJetBoundaryRemainderEmbedding k
    (riccatiBoundarySubstitution Q) a).symm

end

end GaloisForLFunctions
