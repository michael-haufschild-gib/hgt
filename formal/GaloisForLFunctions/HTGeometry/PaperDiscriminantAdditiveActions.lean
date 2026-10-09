import GaloisForLFunctions.HTGeometry.PaperDiscriminantAllDerivations
import GaloisForLFunctions.HTGeometry.PaperDiscriminantTranslationSlice
import GaloisForLFunctions.HTGeometry.PaperLNDLinearAction

/-!
# Every additive action on the ordered discriminant complement

The source's proved exponential correspondence integrates the native
classification of all locally nilpotent derivations. Actions are in
explicit bijection with translation-invariant speeds. Each action moves
every root by the same speed times the formal additive parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

private theorem speed_constant (q : paperDiscriminantTranslationConstants K n) :
    paperDiscriminantTranslation K n (q : PaperRootDiscriminantOpen K n) = 0 :=
  q.property

private theorem speed_locallyNilpotent (q : paperDiscriminantTranslationConstants K n) :
    IsLocallyNilpotent
      ((q : PaperRootDiscriminantOpen K n) • paperDiscriminantTranslation K n) :=
  (paperDiscriminantTranslation_smul_locallyNilpotent_iff (K := K) n
    (q : PaperRootDiscriminantOpen K n)).mpr (speed_constant q)

/-- Integrate every invariant speed using the source's full polynomial additive action. -/
def paperDiscriminantAdditiveAction (q : paperDiscriminantTranslationConstants K n) :
    PolynomialAdditiveAction K (PaperRootDiscriminantOpen K n) :=
  exponentialAction ((q : PaperRootDiscriminantOpen K n) • paperDiscriminantTranslation K n)
    (speed_locallyNilpotent q)

/-- The action's infinitesimal generator is exactly the prescribed invariant multiple. -/
@[simp] theorem paperDiscriminantAdditiveAction_derivation
    (q : paperDiscriminantTranslationConstants K n) :
    (paperDiscriminantAdditiveAction q).derivation =
      (q : PaperRootDiscriminantOpen K n) • paperDiscriminantTranslation K n :=
  exponentialAction_derivation _ _

/-- All native roots translate by the same invariant speed and formal parameter. -/
theorem paperDiscriminantAdditiveAction_root
    (q : paperDiscriminantTranslationConstants K n) (i : Fin n) :
    (paperDiscriminantAdditiveAction q).toAlgHom (paperDiscriminantRoot i) =
      Polynomial.C (paperDiscriminantRoot i) +
        Polynomial.C (q : PaperRootDiscriminantOpen K n) * Polynomial.X := by
  let D : Derivation K (PaperRootDiscriminantOpen K n) (PaperRootDiscriminantOpen K n) :=
    (q : PaperRootDiscriminantOpen K n) • paperDiscriminantTranslation K n
  have hi : D (paperDiscriminantRoot i) = q := by
    simp only [D, Derivation.smul_apply, paperDiscriminantTranslation_root, smul_eq_mul, mul_one]
  have hq : D (q : PaperRootDiscriminantOpen K n) = 0 := by
    change (q : PaperRootDiscriminantOpen K n) * paperDiscriminantTranslation K n q = 0
    rw [speed_constant q, mul_zero]
  have htwo : D (D (paperDiscriminantRoot i)) = 0 := by rw [hi]; exact hq
  change (exponentialAction D _).toAlgHom (paperDiscriminantRoot i) = _
  rw [paperLND_exponential_linear_on D _ _ htwo, hi]

/-- Recover the invariant speed from any action by differentiating its first root. -/
def paperDiscriminantActionSpeed
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1))) :
    paperDiscriminantTranslationConstants K (n + 1) := by
  refine ⟨ρ.derivation (paperDiscriminantRoot 0), ?_⟩
  change paperDiscriminantTranslation K (n + 1)
    (ρ.derivation (paperDiscriminantRoot 0)) = 0
  obtain ⟨q, ⟨hq, he⟩, _⟩ :=
    (paperDiscriminantLND_classification n ρ.derivation).mp ρ.locallyNilpotent
  rw [he, Derivation.smul_apply, paperDiscriminantTranslation_root, smul_eq_mul, mul_one]
  exact hq

/-- The recovered speed reconstructs the complete infinitesimal generator. -/
theorem paperDiscriminantAction_derivation_eq_speed
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1))) :
    ρ.derivation =
      (paperDiscriminantActionSpeed ρ : PaperRootDiscriminantOpen K (n + 1)) •
        paperDiscriminantTranslation K (n + 1) := by
  apply paperDiscriminantRoot_derivation_ext
  intro i
  rw [Derivation.smul_apply, paperDiscriminantTranslation_root, smul_eq_mul, mul_one]
  exact paperDiscriminantRoot_lnd_values_eq ρ.derivation ρ.locallyNilpotent i 0

/-- Every polynomial additive action is precisely the translation with its recovered speed. -/
theorem paperDiscriminantAction_eq_speed
    (ρ : PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1))) :
    ρ = paperDiscriminantAdditiveAction (paperDiscriminantActionSpeed ρ) := by
  apply additiveCoaction_ext
  apply ρ.toAlgHom_eq_of_derivation_eq
  rw [paperDiscriminantAdditiveAction_derivation]
  exact paperDiscriminantAction_derivation_eq_speed ρ

/-- Integrating and recovering an invariant speed returns the original coefficient. -/
@[simp] theorem paperDiscriminantActionSpeed_action
    (q : paperDiscriminantTranslationConstants K (n + 1)) :
    paperDiscriminantActionSpeed (paperDiscriminantAdditiveAction q) = q := by
  apply Subtype.ext
  change (paperDiscriminantAdditiveAction q).derivation (paperDiscriminantRoot 0) = q
  rw [paperDiscriminantAdditiveAction_derivation, Derivation.smul_apply,
    paperDiscriminantTranslation_root, smul_eq_mul, mul_one]

/-- Exact classification of all additive actions by the full invariant coefficient algebra. -/
def paperDiscriminantAdditiveActionEquiv (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    paperDiscriminantTranslationConstants K (n + 1) ≃
      PolynomialAdditiveAction K (PaperRootDiscriminantOpen K (n + 1)) where
  toFun := paperDiscriminantAdditiveAction
  invFun := paperDiscriminantActionSpeed
  left_inv := paperDiscriminantActionSpeed_action
  right_inv ρ := (paperDiscriminantAction_eq_speed ρ).symm

end

end GaloisForLFunctions.HTGeometry
