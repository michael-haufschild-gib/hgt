/-
# Chen--Gupta--Li primitive-character family packets

Chen--Gupta--Li's zero-density argument works at one fixed modulus while
summing its packets over every primitive nonprincipal character.  Existing
corpus layers construct the actual selected zero rows separately for each
primitive character.  This module supplies the missing finite family carrier
and reindexes both the literal primitive zero count and the Class-I/Class-II
partition over that carrier.

No RH, GRH, zero-density, large-value, local-capacity, or asymptotic premise
is supplied by a caller.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalPartition

noncomputable section

namespace RHTower

/-- The canonical finite family of primitive nonprincipal characters at the
literal modulus `n + 1`. -/
noncomputable def cglPrimitiveNonprincipalCharacterFamily (n : ℕ) :
    Finset (NonprincipalDirichletCharacter n) := by
  classical
  exact Finset.univ.filter (fun χ => DirichletCharacter.IsPrimitive χ.1)

/-- A member of the finite primitive nonprincipal character family. -/
abbrev CGLPrimitiveNonprincipalCharacterFamily (n : ℕ) :=
  ↑(cglPrimitiveNonprincipalCharacterFamily n)

/-- The finite family membership certificate supplies the existing primitive
character datum, with no primitivity premise requested from callers. -/
def cglPrimitiveNonprincipalCharacterFamily_asPrimitive
    {n : ℕ} (χ : CGLPrimitiveNonprincipalCharacterFamily n) :
    PrimitiveNonprincipalDirichletCharacter n := by
  classical
  exact ⟨χ.1, (Finset.mem_filter.mp χ.2).2⟩

/-- Forgetting the family membership certificate recovers the original
nonprincipal character exactly. -/
theorem cglPrimitiveNonprincipalCharacterFamily_asPrimitive_coe
    {n : ℕ} (χ : CGLPrimitiveNonprincipalCharacterFamily n) :
    (cglPrimitiveNonprincipalCharacterFamily_asPrimitive χ).1 = χ.1 := rfl

/-- The literal primitive centered-window count written as a finite sum over
the canonical primitive-character carrier. -/
noncomputable def cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount
    (n : ℕ) (σ τ : ℝ) (H : NNReal) : ℝ :=
  ∑ χ : CGLPrimitiveNonprincipalCharacterFamily n,
    completedLFunctionZeroDensityVerticalWindowCount n χ.1 σ τ H

/-- Exact reindexing of the existing primitive centered-window count through
the canonical finite primitive-character family. -/
theorem cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount_eq
    (n : ℕ) (σ τ : ℝ) (H : NNReal) :
    cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount n σ τ H =
      completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount n σ τ H := by
  classical
  let S := cglPrimitiveNonprincipalCharacterFamily n
  let p : NonprincipalDirichletCharacter n → Prop :=
    fun χ => DirichletCharacter.IsPrimitive χ.1
  let f : NonprincipalDirichletCharacter n → ℝ :=
    fun χ => completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H
  have hS : ∀ χ : NonprincipalDirichletCharacter n, χ ∈ S ↔ p χ := by
    intro χ
    simp only [S, cglPrimitiveNonprincipalCharacterFamily, Finset.mem_filter,
      Finset.mem_univ, true_and, p]
  have hattach : S.attach = (Finset.univ : Finset (↑S)) := by
    ext χ
    simp
  have hSdef : S = (Finset.univ : Finset (NonprincipalDirichletCharacter n)).filter p := by
    ext χ
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hS χ
  change (∑ χ ∈ (Finset.univ : Finset (↑S)), f χ.1) =
    ∑ χ ∈ (Finset.univ : Finset (NonprincipalDirichletCharacter n)),
      if p χ then f χ else 0
  rw [← hattach, Finset.sum_attach, hSdef, Finset.sum_filter]

/-- Total number of selected natural-scale primitive zero rows, aggregated
over the finite family at one modulus. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedFamilyAllRowsCard
    (n : ℕ) (τ : ℝ) (H : NNReal) (K : ℕ) : ℕ :=
  ∑ χ : CGLPrimitiveNonprincipalCharacterFamily n,
    (cglPrimitiveClassINaturalWellSpacedAllRows n
      (cglPrimitiveNonprincipalCharacterFamily_asPrimitive χ) τ H K).card

/-- The aggregate finite Class-I packet over all primitive characters at one
modulus. -/
abbrev CGLPrimitiveClassINaturalWellSpacedFamilyClassIRow
    (X Y n : ℕ) (τ : ℝ) (H : NNReal) (K : ℕ) :=
  Sigma fun χ : CGLPrimitiveNonprincipalCharacterFamily n =>
    CGLPrimitiveClassINaturalWellSpacedClassIRow X Y n
      (cglPrimitiveNonprincipalCharacterFamily_asPrimitive χ) τ H K

/-- The aggregate finite Class-II packet over all primitive characters at one
modulus. -/
abbrev CGLPrimitiveClassINaturalWellSpacedFamilyClassIIRow
    (X Y n : ℕ) (τ : ℝ) (H : NNReal) (K : ℕ) :=
  Sigma fun χ : CGLPrimitiveNonprincipalCharacterFamily n =>
    CGLPrimitiveClassINaturalWellSpacedClassIIRow X Y n
      (cglPrimitiveNonprincipalCharacterFamily_asPrimitive χ) τ H K

/-- The CGL Class-I and Class-II aggregate packets partition every selected
primitive zero row at the fixed modulus. -/
theorem cglPrimitiveClassINaturalWellSpacedFamilyClass_rows_card
    (X Y n : ℕ) (τ : ℝ) (H : NNReal) (K : ℕ) :
    Fintype.card (CGLPrimitiveClassINaturalWellSpacedFamilyClassIRow X Y n τ H K) +
      Fintype.card (CGLPrimitiveClassINaturalWellSpacedFamilyClassIIRow X Y n τ H K) =
        cglPrimitiveClassINaturalWellSpacedFamilyAllRowsCard n τ H K := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ hχ
  simpa using cglPrimitiveClassINaturalWellSpacedClass_rows_card X Y n
    (cglPrimitiveNonprincipalCharacterFamily_asPrimitive χ) τ H K

end RHTower
