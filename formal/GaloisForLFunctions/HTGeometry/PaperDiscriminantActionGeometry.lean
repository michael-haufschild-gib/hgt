import GaloisForLFunctions.HTGeometry.PaperDiscriminantAdditiveActions

/-!
# Fixed rings and commuting automorphisms of discriminant additive actions

Every additive action has a common invariant root speed. This determines
its exact fixed ring and its scalar-parameter automorphisms. All scalar
specializations of all these actions commute, and universal action
invariants are exactly the common-translation constants.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
/-- Algebra maps out of the root localization are determined by their root values. -/
theorem paperDiscriminantRoot_algHom_ext
    {B : Type*} [Semiring B] [Algebra K B]
    {f g : PaperRootDiscriminantOpen K n →ₐ[K] B}
    (h : ∀ i, f (paperDiscriminantRoot i) = g (paperDiscriminantRoot i)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (paperUniversalVandermonde K n ^ 2))
  apply MvPolynomial.algHom_ext
  exact h

/-- The root formula holds for every action, not just those initially built by exponentiation. -/
theorem paperDiscriminantAction_root
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1)))
    (i : Fin (n + 1)) :
    ρ.toAlgHom (paperDiscriminantRoot i) =
      Polynomial.C (paperDiscriminantRoot i) +
        Polynomial.C (paperDiscriminantActionSpeed ρ : PaperRootDiscriminantOpen K (n + 1)) *
          Polynomial.X := by
  calc
    _ = (paperDiscriminantAdditiveAction (paperDiscriminantActionSpeed ρ)).toAlgHom
        (paperDiscriminantRoot i) :=
      congrArg (fun α => α.toAlgHom (paperDiscriminantRoot i)) (paperDiscriminantAction_eq_speed ρ)
    _ = _ := paperDiscriminantAdditiveAction_root _ i

/-- An action fixes an element exactly when its speed vanishes or common translation fixes it. -/
theorem paperDiscriminantAction_fixed_iff
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1)))
    (a : PaperRootDiscriminantOpen K (n + 1)) :
    ρ.toAlgHom a = Polynomial.C a ↔
      (paperDiscriminantActionSpeed ρ : PaperRootDiscriminantOpen K (n + 1)) = 0 ∨
        paperDiscriminantTranslation K (n + 1) a = 0 := by
  rw [ρ.invariant_iff_derivation_eq_zero, paperDiscriminantAction_derivation_eq_speed,
    Derivation.smul_apply, smul_eq_mul, mul_eq_zero]

/-- Every action fixes the entire invariant coefficient algebra pointwise. -/
theorem paperDiscriminantAction_fixes_constants
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1)))
    (a : paperDiscriminantTranslationConstants K (n + 1)) :
    ρ.toAlgHom a = Polynomial.C (a : PaperRootDiscriminantOpen K (n + 1)) :=
  (paperDiscriminantAction_fixed_iff ρ a).mpr (Or.inr a.property)

/-- Universal invariants of every polynomial additive action are precisely translation constants. -/
theorem paperDiscriminantAction_universal_invariants_iff
    (a : PaperRootDiscriminantOpen K (n + 1)) :
    (∀ ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1)),
      ρ.toAlgHom a = Polynomial.C a) ↔ paperDiscriminantTranslation K (n + 1) a = 0 := by
  constructor
  · intro h
    have ha := (paperDiscriminantAction_fixed_iff
      (paperDiscriminantAdditiveAction (1 : paperDiscriminantTranslationConstants K (n + 1))) a).mp
        (h _)
    rw [paperDiscriminantActionSpeed_action] at ha
    rcases ha with ha | ha
    · exact False.elim (one_ne_zero ha)
    · exact ha
  · intro ha ρ
    exact (paperDiscriminantAction_fixed_iff ρ a).mpr (Or.inr ha)

/-- Each scalar specialization moves all roots by the invariant speed times that scalar. -/
theorem paperDiscriminantAction_specialize_root
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1)))
    (t : K) (i : Fin (n + 1)) :
    ρ.specialize t (paperDiscriminantRoot i) = paperDiscriminantRoot i +
      (paperDiscriminantActionSpeed ρ : PaperRootDiscriminantOpen K (n + 1)) *
        algebraMap K (PaperRootDiscriminantOpen K (n + 1)) t := by
  rw [PolynomialAdditiveAction.specialize_apply, paperDiscriminantAction_root]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]

/-- Scalar specializations preserve every invariant coefficient. -/
theorem paperDiscriminantAction_specialize_constants
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1)))
    (t : K) (a : paperDiscriminantTranslationConstants K (n + 1)) :
    ρ.specialize t a = a := by
  rw [PolynomialAdditiveAction.specialize_apply, paperDiscriminantAction_fixes_constants]
  exact Polynomial.eval_C

/-- Every scalar specialization of every additive action commutes with every other one. -/
theorem paperDiscriminantAction_specializations_commute
    (ρ σ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1))) (s t : K) :
    Function.Commute (ρ.specialize s : _ → _) (σ.specialize t : _ → _) := by
  have he : (ρ.specialize s).comp (σ.specialize t) =
      (σ.specialize t).comp (ρ.specialize s) := by
    apply paperDiscriminantRoot_algHom_ext
    intro i
    simp only [AlgHom.comp_apply, paperDiscriminantAction_specialize_root, map_add, map_mul,
      paperDiscriminantAction_specialize_constants, AlgHom.commutes]
    ring
  intro a
  exact AlgHom.congr_fun he a

/-- The empty root algebra admits only the trivial polynomial additive action. -/
theorem paperDiscriminantZero_action_fixed
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K 0))
    (a : PaperRootDiscriminantOpen K 0) : ρ.toAlgHom a = Polynomial.C a :=
  ρ.action_eq_C_of_derivation_eq_zero (paperDiscriminantZero_derivation_eq_zero ρ.derivation) a

end

end GaloisForLFunctions.HTGeometry
