import GaloisForLFunctions.HTGeometry.LastVariableSplit
import GaloisForLFunctions.HTGeometry.EntireCascade

/-!
# State independence along a cascade, from edgewise growth separations

Independence of the first `m` states plus a growth separation for the next one gives independence of
the first `m+1`.  Iterating from the empty family, a sequence of growth separations makes the whole
state family algebraically independent over the constants.

This is the induction the lower bound runs on, with all algebra discharged: the only hypothesis is the
analytic separation at each step.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The separation required at one step: the new state outgrows any prescribed multiple of the joint
scale of the earlier ones, at a point carrying a floor for a prescribed polynomial in them. -/
def StepSeparation {m : ℕ} (X : Fin m → ℂ → ℂ) (F : ℂ → ℂ) : Prop :=
  ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
    ∃ (z : ℂ) (ε : ℝ), 0 < ε ∧ ε ≤ ‖MvPolynomial.eval (fun j => X j z) A‖ ∧
      c * (1 + (∑ j : Fin m, Real.posLog ‖X j z‖) + Real.posLog ε⁻¹)
        < Real.posLog ‖F z‖

/-- **The induction step.**  Independence of the earlier states plus a step separation gives
independence of the extended family. -/
theorem noRelation_snoc {m : ℕ} {X : Fin m → ℂ → ℂ} {F : ℂ → ℂ}
    (hind : ∀ Q : MvPolynomial (Fin m) ℂ, Q ≠ 0 →
      ¬ (∀ z : ℂ, MvPolynomial.eval (fun j => X j z) Q = 0))
    (hsep : StepSeparation X F)
    (P : MvPolynomial (Fin (m + 1)) ℂ) (hP : P ≠ 0) :
    ¬ (∀ z : ℂ, MvPolynomial.eval (Fin.snoc (fun j => X j z) (F z)) P = 0) := by
  intro hrel
  obtain ⟨D, A, hD, hAD, htop⟩ := exists_top_multi_var_relation hind hP hrel
  exact not_multi_var_relation_of_separation (X := X) (g := F) (A := A) hD
    (fun c hc => hsep (A D) hAD c hc) htop

/-- The first `m` members of a sequence of states. -/
def prefixFamily (Y : ℕ → ℂ → ℂ) (m : ℕ) : Fin m → ℂ → ℂ := fun j => Y (j : ℕ)

theorem prefixFamily_snoc (Y : ℕ → ℂ → ℂ) (m : ℕ) (z : ℂ) :
    Fin.snoc (fun j : Fin m => prefixFamily Y m j z) (Y m z)
      = fun j : Fin (m + 1) => prefixFamily Y (m + 1) j z := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Fin.snoc_last]
    rfl
  · intro i
    rw [Fin.snoc_castSucc]
    rfl

/-- **Independence of every finite prefix of a cascade.**  A growth separation at each step makes the
whole state family algebraically independent over the constants. -/
theorem noRelation_prefixFamily (Y : ℕ → ℂ → ℂ)
    (hsep : ∀ m : ℕ, StepSeparation (prefixFamily Y m) (Y m)) (m : ℕ) :
    ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      ¬ (∀ z : ℂ, MvPolynomial.eval (fun j => prefixFamily Y m j z) P = 0) := by
  induction m with
  | zero =>
      intro P hP hrel
      apply hP
      have heq : (MvPolynomial.eval (fun j => prefixFamily Y 0 j (0 : ℂ)) :
            MvPolynomial (Fin 0) ℂ →+* ℂ)
          = (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          rw [MvPolynomial.eval_C]
          exact (MvPolynomial.coeff_zero_C c).symm
        · intro i
          exact i.elim0
      have hz : (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ) P = 0 := by
        rw [← heq]
        exact hrel 0
      exact (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).injective (by simpa using hz)
  | succ m ih =>
      intro P hP hrel
      refine noRelation_snoc (X := prefixFamily Y m) (F := Y m) ih (hsep m) P hP ?_
      intro z
      rw [prefixFamily_snoc]
      exact hrel z

/-! ## The cascade instance

The zeroth cascade state is the identity, so the prefix family of `entireCascade f` is exactly the
coordinate together with the states — no special case is needed for the coordinate. -/

/-- **The cascade states are algebraically independent over the constants.** -/
theorem noRelation_entireCascade {f : ℕ → ℂ → ℂ}
    (hsep : ∀ m : ℕ,
      StepSeparation (prefixFamily (entireCascade f) m) (entireCascade f m))
    (m : ℕ) (P : MvPolynomial (Fin m) ℂ) (hP : P ≠ 0) :
    ¬ (∀ z : ℂ, MvPolynomial.eval (fun j : Fin m => entireCascade f (j : ℕ) z) P = 0) :=
  noRelation_prefixFamily (entireCascade f) hsep m P hP

end GaloisForLFunctions.HTGeometry
