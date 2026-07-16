import GaloisForLFunctions.HTGeometry.NoetherianRegularStratification
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.Complex.Basic

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A subset of complex affine space cut out by an ideal of multivariate polynomials. -/
def IsComplexAffineAlgebraic {n : ℕ} (S : Set (Fin n → ℂ)) : Prop :=
  ∃ I : Ideal (MvPolynomial (Fin n) ℂ), S = MvPolynomial.zeroLocus ℂ I

/-- Taking the zero locus of the vanishing ideal recovers every complex affine algebraic set. -/
theorem IsComplexAffineAlgebraic.zeroLocus_vanishingIdeal_eq
    {n : ℕ} {S : Set (Fin n → ℂ)} (hS : IsComplexAffineAlgebraic S) :
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ S) = S := by
  obtain ⟨I, rfl⟩ := hS
  apply le_antisymm
  · exact MvPolynomial.zeroLocus_anti_mono
      (MvPolynomial.le_vanishingIdeal_zeroLocus I)
  · exact MvPolynomial.zeroLocus_vanishingIdeal_le _

/-- Strict containment of algebraic sets reverses to strict containment of vanishing ideals. -/
theorem IsComplexAffineAlgebraic.vanishingIdeal_strictMono
    {n : ℕ} {S T : Set (Fin n → ℂ)}
    (hS : IsComplexAffineAlgebraic S) (hT : IsComplexAffineAlgebraic T)
    (hTS : T ⊂ S) :
    MvPolynomial.vanishingIdeal ℂ S < MvPolynomial.vanishingIdeal ℂ T := by
  rw [lt_iff_le_and_ne]
  refine ⟨MvPolynomial.vanishingIdeal_anti_mono hTS.le, ?_⟩
  intro heq
  apply hTS.ne
  calc
    T = MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ T) :=
      hT.zeroLocus_vanishingIdeal_eq.symm
    _ = MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ S) := by rw [heq]
    _ = S := hS.zeroLocus_vanishingIdeal_eq

/-- Complex affine algebraic subsets satisfy the descending-chain condition. -/
theorem wellFounded_ssubset_complexAffineAlgebraic {n : ℕ} :
    WellFounded (fun T S : {Z : Set (Fin n → ℂ) // IsComplexAffineAlgebraic Z} =>
      T.1 ⊂ S.1) := by
  let v : {Z : Set (Fin n → ℂ) // IsComplexAffineAlgebraic Z} →
      Ideal (MvPolynomial (Fin n) ℂ) :=
    fun Z => MvPolynomial.vanishingIdeal ℂ Z.1
  have hwf : WellFounded ((· > ·) : Ideal (MvPolynomial (Fin n) ℂ) →
      Ideal (MvPolynomial (Fin n) ℂ) → Prop) :=
    (inferInstance : IsNoetherianRing (MvPolynomial (Fin n) ℂ)).wf
  refine (hwf.onFun (f := v)).mono ?_
  intro T S hTS
  exact IsComplexAffineAlgebraic.vanishingIdeal_strictMono S.2 T.2 hTS

/-! ## Arbitrary finite coordinate types -/

/-- A complex affine algebraic set with an arbitrary coordinate index type. -/
def IsComplexAffineAlgebraicSet {σ : Type*} (S : Set (σ → ℂ)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ ℂ), S = MvPolynomial.zeroLocus ℂ I

theorem IsComplexAffineAlgebraicSet.zeroLocus_vanishingIdeal_eq
    {σ : Type*} {S : Set (σ → ℂ)} (hS : IsComplexAffineAlgebraicSet S) :
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ S) = S := by
  obtain ⟨I, rfl⟩ := hS
  apply le_antisymm
  · exact MvPolynomial.zeroLocus_anti_mono
      (MvPolynomial.le_vanishingIdeal_zeroLocus I)
  · exact MvPolynomial.zeroLocus_vanishingIdeal_le _

theorem IsComplexAffineAlgebraicSet.vanishingIdeal_strictMono
    {σ : Type*} {S T : Set (σ → ℂ)}
    (hS : IsComplexAffineAlgebraicSet S) (hT : IsComplexAffineAlgebraicSet T)
    (hTS : T ⊂ S) :
    MvPolynomial.vanishingIdeal ℂ S < MvPolynomial.vanishingIdeal ℂ T := by
  rw [lt_iff_le_and_ne]
  refine ⟨MvPolynomial.vanishingIdeal_anti_mono hTS.le, ?_⟩
  intro heq
  apply hTS.ne
  calc
    T = MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ T) :=
      hT.zeroLocus_vanishingIdeal_eq.symm
    _ = MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ S) := by rw [heq]
    _ = S := hS.zeroLocus_vanishingIdeal_eq

/-- Noetherian descent for affine algebraic sets in any finite coordinate type. -/
theorem wellFounded_ssubset_complexAffineAlgebraicSet
    {σ : Type*} [Finite σ] :
    WellFounded (fun T S : {Z : Set (σ → ℂ) // IsComplexAffineAlgebraicSet Z} =>
      T.1 ⊂ S.1) := by
  let v : {Z : Set (σ → ℂ) // IsComplexAffineAlgebraicSet Z} →
      Ideal (MvPolynomial σ ℂ) :=
    fun Z => MvPolynomial.vanishingIdeal ℂ Z.1
  have hwf : WellFounded ((· > ·) : Ideal (MvPolynomial σ ℂ) →
      Ideal (MvPolynomial σ ℂ) → Prop) :=
    (inferInstance : IsNoetherianRing (MvPolynomial σ ℂ)).wf
  refine (hwf.onFun (f := v)).mono ?_
  intro T S hTS
  exact IsComplexAffineAlgebraicSet.vanishingIdeal_strictMono S.2 T.2 hTS

end

end GaloisForLFunctions.HTGeometry
