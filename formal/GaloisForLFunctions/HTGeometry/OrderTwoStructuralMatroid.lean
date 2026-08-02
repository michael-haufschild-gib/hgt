import GaloisForLFunctions.HTGeometry.OrderTwoStructuralTranslateDecomposition
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCompleteDifferentialMatroid
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacketDisjointness
import GaloisForLFunctions.HTGeometry.FaceShiftLatticeNonresonance
import GaloisForLFunctions.HTGeometry.PeriodIntegralIndependenceWitness

/-!
# The order-two squarefree coordinate packet and its differential matroid

The squarefree relation `xᵢxⱼ ≡ 0` reduces every structural translate of the order-two primitive,
modulo differentially algebraic functions, to a constant-coefficient combination of

* the top primitive `Ψ`, and
* the translates `σ_{k τᵢ}` of the three codimension-one face coordinates.

This module labels that packet, proves it faithful, and identifies the differential matroid of
every finite constant-coefficient differential-operator family built on it with the localized
operator-row matroid over `Frac(ℂ[∂])`.  No nonlinear differential relation exists beyond the
linear ones visible in the rows.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

/-! ## The coordinate packet -/

/-- Labels of the order-two squarefree coordinate packet: the top primitive, and the translated
codimension-one face coordinates. -/
abbrev OrderTwoStructuralIndex := Option (Fin 3 × ℕ)

/-- The order-two squarefree coordinate packet. -/
def orderTwoStructuralCoordinate (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    OrderTwoStructuralIndex → meroField (Set.univ : Set ℂ)
  | none => multipleEllipticGammaLogDerivMero τ hτ
  | some (i, k) => addTranslationMeroEquiv ((k : ℂ) * τ i)
      (multipleEllipticGammaLogDerivFaceMero τ hτ {i})

theorem orderTwoStructuralFace_compl_card (i : Fin 3) :
    ((({i} : Finset (Fin 3))ᶜ)).card = 2 := by
  have htotal := Finset.card_add_card_compl ({i} : Finset (Fin 3))
  simp only [Fintype.card_fin, Finset.card_singleton] at htotal
  omega

theorem orderTwoStructuralCoordinate_mem (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (c : OrderTwoStructuralIndex) :
    orderTwoStructuralCoordinate τ hτ c ∈
      facePacketUnion τ hτ {J : Finset (Fin 3) | 2 ≤ (Jᶜ).card} := by
  match c with
  | none =>
      refine Set.mem_iUnion₂.mpr ⟨∅, ?_, ?_⟩
      · simp
      · refine ⟨0, ⟨0, fun _ _ => rfl, by simp⟩, ?_⟩
        show addTranslationMeroEquiv (0 : ℂ)
            (multipleEllipticGammaLogDerivFaceMero τ hτ ∅) = _
        rw [addTranslationMeroEquiv_zero_apply, multipleEllipticGammaLogDerivFaceMero_empty]
        rfl
  | some (i, k) =>
      refine Set.mem_iUnion₂.mpr ⟨{i}, ?_, mem_facePacket_translate_faceMero τ hτ i k⟩
      simp [orderTwoStructuralFace_compl_card i]

/-! ## Faithfulness of the labelling -/

theorem orderTwoStructuralSurvivors (i : Fin 3) :
    ∃ a b : Fin 3, a ∉ ({i} : Finset (Fin 3)) ∧ b ∉ ({i} : Finset (Fin 3)) ∧ a ≠ b ∧
      ∀ p : Fin 3, p ∉ ({i} : Finset (Fin 3)) → p = a ∨ p = b := by
  fin_cases i
  · exact ⟨1, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide⟩

theorem orderTwoStructuralCoordinate_injective (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) :
    Function.Injective (orderTwoStructuralCoordinate τ hτ) := by
  have hzeroEmpty : (0 : ℂ) ∈ faceShiftLattice τ (∅ : Finset (Fin 3)) :=
    ⟨0, fun _ _ => rfl, by simp⟩
  have hemptycard : 2 ≤ ((∅ : Finset (Fin 3))ᶜ).card := by simp
  have hsinglecard : ∀ i : Fin 3, 2 ≤ ((({i} : Finset (Fin 3))ᶜ)).card :=
    fun i => le_of_eq (orderTwoStructuralFace_compl_card i).symm
  have htopEq :
      addTranslationMeroEquiv (0 : ℂ) (multipleEllipticGammaLogDerivFaceMero τ hτ ∅) =
        multipleEllipticGammaLogDerivMero τ hτ := by
    rw [addTranslationMeroEquiv_zero_apply, multipleEllipticGammaLogDerivFaceMero_empty]
  rintro (_ | ⟨i, k⟩) (_ | ⟨j, l⟩) h
  · rfl
  · exfalso
    refine multipleEllipticGammaFace_translate_ne_of_ne τ hτ hQ ∅ {j} (by simp)
      hemptycard (hsinglecard j) hzeroEmpty
      (natCast_mul_mem_faceShiftLattice_singleton τ j l) ?_
    rw [htopEq]
    exact h
  · exfalso
    refine multipleEllipticGammaFace_translate_ne_of_ne τ hτ hQ ∅ {i} (by simp)
      hemptycard (hsinglecard i) hzeroEmpty
      (natCast_mul_mem_faceShiftLattice_singleton τ i k) ?_
    rw [htopEq]
    exact h.symm
  · have hkmem := natCast_mul_mem_faceShiftLattice_singleton τ i k
    have hlmem := natCast_mul_mem_faceShiftLattice_singleton τ j l
    by_cases hij : i = j
    · subst hij
      obtain ⟨a, b, haJ, hbJ, hab, hJ⟩ := orderTwoStructuralSurvivors i
      have hperiods :=
        linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hab
      have hshift := faceShiftLattice_translate_injective_bottom τ hτ hQ ({i} : Finset (Fin 3))
        haJ hbJ hab hJ hperiods hkmem hlmem h
      have hτi : τ i ≠ 0 := by
        intro h0
        have him := hτ i
        rw [h0] at him
        simp at him
      have hkl : (k : ℂ) = (l : ℂ) := mul_right_cancel₀ hτi hshift
      have hklnat : k = l := by exact_mod_cast hkl
      rw [hklnat]
    · exfalso
      exact multipleEllipticGammaFace_translate_ne_of_ne τ hτ hQ {i} {j}
        (by simpa using hij) (hsinglecard i) (hsinglecard j) hkmem hlmem h

/-! ## Structural translates reduce to the coordinate packet -/

theorem orderTwoFaceBranch_eq_coordinateSum (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (i : Fin 3) (m : ℕ) :
    orderTwoFaceBranch τ hτ i m =
      ∑ k ∈ Finset.range m, orderTwoStructuralCoordinate τ hτ (some (i, k)) := rfl

/-- **Squarefree reduction of a structural translate.**  Every structural translate of the
order-two primitive equals the top coordinate plus a finite sum of translated codimension-one face
coordinates, up to a differentially algebraic error.  This is the relation `xᵢxⱼ ≡ 0` realized on
the actual kernels. -/
theorem orderTwoStructuralTranslate_eq_coordinateSum_add_differentialAlgebraic
    (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (n : Fin 3 → ℕ) :
    ∃ d : meroField (Set.univ : Set ℂ), DifferentialAlgebraicOver ℂ d ∧
      addTranslationMeroEquiv (∑ i, (n i : ℂ) * τ i)
          (multipleEllipticGammaLogDerivMero τ hτ) =
        orderTwoStructuralCoordinate τ hτ none +
          (∑ i, ∑ k ∈ Finset.range (n i), orderTwoStructuralCoordinate τ hτ (some (i, k))) + d := by
  refine ⟨addTranslationMeroEquiv (∑ i, (n i : ℂ) * τ i)
        (multipleEllipticGammaLogDerivMero τ hτ) - multipleEllipticGammaLogDerivMero τ hτ -
        ∑ i, orderTwoFaceBranch τ hτ i (n i),
    orderTwoStructuralTranslate_sub_branches_differentialAlgebraic τ hτ hQ n, ?_⟩
  have hbranch : ∑ i, orderTwoFaceBranch τ hτ i (n i) =
      ∑ i, ∑ k ∈ Finset.range (n i), orderTwoStructuralCoordinate τ hτ (some (i, k)) :=
    Finset.sum_congr rfl fun i _ => orderTwoFaceBranch_eq_coordinateSum τ hτ i (n i)
  rw [← hbranch]
  show _ = multipleEllipticGammaLogDerivMero τ hτ + _ + _
  abel

/-! ## The complete order-two structural matroid -/

/-- **Order-two structural operator matroid.**  For every finite injective selection from the
squarefree coordinate packet and every finite family of constant-coefficient differential-operator
rows, the nonlinear differential matroid of the outputs is exactly the localized operator-row
matroid.  All differential dependence among structural translates is linear and visible in the
rows. -/
theorem orderTwoStructural_completeDifferentialMatroid
    (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {ρ κ : Type} [Fintype ρ] [Fintype κ] [DecidableEq ρ] [DecidableEq κ]
    (e : κ → OrderTwoStructuralIndex) (he : Function.Injective e)
    (L : ρ → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L (orderTwoStructuralCoordinate τ hτ ∘ e)) =
      differentialOperatorRowMatroid L :=
  multipleEllipticGammaCompleteDifferentialMatroid τ hτ hQ (by simp) _
    (fun k => orderTwoStructuralCoordinate_mem τ hτ (e k))
    ((orderTwoStructuralCoordinate_injective τ hτ hQ).comp he) L

/-- Numerical form: the differential transcendence rank of a finite operator family on the
squarefree coordinate packet equals the localized row rank. -/
theorem orderTwoStructural_completeDifferentialRank
    (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {ρ κ : Type} [Fintype ρ] [Fintype κ] [DecidableEq ρ] [DecidableEq κ]
    (e : κ → OrderTwoStructuralIndex) (he : Function.Injective e)
    (L : ρ → κ → Polynomial ℂ) (I : Finset ρ) :
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L (orderTwoStructuralCoordinate τ hτ ∘ e))).eRk
        (↑I : Set ρ) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ρ))) : ℕ∞) :=
  multipleEllipticGammaCompleteDifferentialRank τ hτ hQ (by simp) _
    (fun k => orderTwoStructuralCoordinate_mem τ hτ (e k))
    ((orderTwoStructuralCoordinate_injective τ hτ hQ).comp he) L I

end

end GaloisForLFunctions
