import GaloisForLFunctions.HTGeometry.SpectralCausality
import GaloisForLFunctions.HTGeometry.ObserverTemporalDimensionCascadeLaw

/-!
# Locality as a finite-resolution temporal constraint

Every vanishing two-site rectangle contrast is a projective spectral
character.  The standard rectangle family is independent even when every
spectator configuration is included.  Consequently, if locality forces all
such contrasts to vanish through a jet cutoff, their entire span lies in the
unresolved temporal constraint space.

For two `q`-level factors with `n - 2` spectator factors this gives
`(q - 1)^2 q^(n - 2)` independent unresolved characters, all already carried
by second-replica rectangles.  When this span is later released, exact
rank-nullity forces at least the same increase in temporal dimension.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A rational rectangle contrast, viewed as a zero-charge projective
spectral character. -/
noncomputable def rectangleProjectiveRationalCharacter
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B) (j : RectangleContrastIndex A B C a₀ b₀) :
    ProjectiveRationalCharacter (A × B × C) := by
  refine ⟨fun x => rectangleContrastRelation (R := ℚ) a₀ b₀ j x, ?_⟩
  change ∑ x, rectangleContrastRelation (R := ℚ) a₀ b₀ j x = 0
  rw [← Finsupp.sum_fintype
    (rectangleContrastRelation (R := ℚ) a₀ b₀ j) (fun _ x => x)
    (fun _ => rfl)]
  simp only [rectangleContrastRelation]
  rw [Finsupp.sum_sub_index (by intros; rfl),
    Finsupp.sum_sub_index (by intros; rfl),
    Finsupp.sum_add_index' (by intros; rfl) (by intros; rfl)]
  simp

theorem rectangleProjectiveRationalCharacter_apply_distinguished
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B)
    (j k : RectangleContrastIndex A B C a₀ b₀) :
    (rectangleProjectiveRationalCharacter a₀ b₀ k :
      (A × B × C) → ℚ) (rectangleDistinguished j) =
        if k = j then 1 else 0 := by
  exact rectangleContrastRelation_apply_distinguished a₀ b₀ j k

/-- Rectangle characters remain linearly independent inside projective
character space. -/
theorem rectangleProjectiveRationalCharacter_linearIndependent
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B) :
    LinearIndependent ℚ
      (rectangleProjectiveRationalCharacter a₀ b₀ :
        RectangleContrastIndex A B C a₀ b₀ →
          ProjectiveRationalCharacter (A × B × C)) := by
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro j
  have hj := congrArg
    (fun z : ProjectiveRationalCharacter (A × B × C) =>
      (z : (A × B × C) → ℚ) (rectangleDistinguished j)) hl
  change
    ((l.sum fun i a => a • rectangleProjectiveRationalCharacter a₀ b₀ i :
      ProjectiveRationalCharacter (A × B × C)) :
        (A × B × C) → ℚ) (rectangleDistinguished j) = 0 at hj
  unfold Finsupp.sum at hj
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
    Finset.sum_apply] at hj
  simpa [rectangleProjectiveRationalCharacter_apply_distinguished] using hj

theorem rectangleProjectiveRationalCharacter_mem_constraint
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B)
    (jet : ℕ → A × B × C → ℂ) (r : ℕ)
    (hvanish :
      ∀ (j : RectangleContrastIndex A B C a₀ b₀) (m : Fin r),
        ∑ x, ((rectangleContrastRelation (R := ℚ) a₀ b₀ j x : ℚ) : ℂ) *
          jet m x = 0)
    (j : RectangleContrastIndex A B C a₀ b₀) :
    rectangleProjectiveRationalCharacter a₀ b₀ j ∈
      rationalSpectralConstraintSpace jet r := by
  change projectiveJetMap jet r
    (rectangleProjectiveRationalCharacter a₀ b₀ j) = 0
  ext m
  exact hvanish j m

/-- **Exponential unresolved-character law.** If every endpoint rectangle
vanishes through order `r - 1`, then all rectangle characters lie in the
temporal constraint kernel, giving the exact combinatorial lower bound on its
rank. -/
theorem rectangleConstraint_finrank_lower_bound
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B)
    (jet : ℕ → A × B × C → ℂ) (r : ℕ)
    (hvanish :
      ∀ (j : RectangleContrastIndex A B C a₀ b₀) (m : Fin r),
        ∑ x, ((rectangleContrastRelation (R := ℚ) a₀ b₀ j x : ℚ) : ℂ) *
          jet m x = 0) :
    (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C ≤
      Module.finrank ℚ (rationalSpectralConstraintSpace jet r) := by
  let family :
      RectangleContrastIndex A B C a₀ b₀ →
        ProjectiveRationalCharacter (A × B × C) :=
    rectangleProjectiveRationalCharacter a₀ b₀
  have hspan :
      Submodule.span ℚ (Set.range family) ≤
        rationalSpectralConstraintSpace jet r := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact rectangleProjectiveRationalCharacter_mem_constraint
      a₀ b₀ jet r hvanish j
  calc
    (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C =
        Fintype.card (RectangleContrastIndex A B C a₀ b₀) := by
          symm
          exact rectangleContrastIndex_card a₀ b₀
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range family)) := by
          symm
          exact finrank_span_eq_card
            (rectangleProjectiveRationalCharacter_linearIndependent a₀ b₀)
    _ ≤ Module.finrank ℚ (rationalSpectralConstraintSpace jet r) :=
      Submodule.finrank_mono hspan

/-- Persistent rectangle constraints impose the dual upper bound on resolved
temporal dimension. -/
theorem rectangleTemporalDimension_add_lowerBound_le
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (a₀ : A) (b₀ : B)
    (jet : ℕ → A × B × C → ℂ) (r : ℕ)
    (hvanish :
      ∀ (j : RectangleContrastIndex A B C a₀ b₀) (m : Fin r),
        ∑ x, ((rectangleContrastRelation (R := ℚ) a₀ b₀ j x : ℚ) : ℂ) *
          jet m x = 0) :
    temporalDimension jet r +
        (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C ≤
      Fintype.card (A × B × C) - 1 := by
  have hlower :=
    rectangleConstraint_finrank_lower_bound a₀ b₀ jet r hvanish
  have hconservation :=
    temporalDimension_add_constraintFinrank jet r
  rw [finrank_projectiveRationalCharacter (A × B × C)] at hconservation
  omega

/-- **Constraint-release law.** If the previously unresolved rectangle span
becomes transverse to the later constraint kernel, temporal dimension grows
by at least the full rectangle rank. -/
theorem rectangleTemporalDimension_gain_lower_bound_of_release
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B)
    (jet : ℕ → A × B × C → ℂ) {r s : ℕ} (hrs : r ≤ s)
    (hvanish :
      ∀ (j : RectangleContrastIndex A B C a₀ b₀) (m : Fin r),
        ∑ x, ((rectangleContrastRelation (R := ℚ) a₀ b₀ j x : ℚ) : ℂ) *
          jet m x = 0)
    (hreleased :
      Submodule.span ℚ
          (Set.range
            (rectangleProjectiveRationalCharacter a₀ b₀ :
              RectangleContrastIndex A B C a₀ b₀ →
                ProjectiveRationalCharacter (A × B × C))) ⊓
        rationalSpectralConstraintSpace jet s = ⊥) :
    (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C ≤
      temporalDimension jet s - temporalDimension jet r := by
  let W : Submodule ℚ (ProjectiveRationalCharacter (A × B × C)) :=
    Submodule.span ℚ
      (Set.range
        (rectangleProjectiveRationalCharacter a₀ b₀ :
          RectangleContrastIndex A B C a₀ b₀ →
            ProjectiveRationalCharacter (A × B × C)))
  let Kr := rationalSpectralConstraintSpace jet r
  let Ks := rationalSpectralConstraintSpace jet s
  have hWKr : W ≤ Kr := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact rectangleProjectiveRationalCharacter_mem_constraint
      a₀ b₀ jet r hvanish j
  have hKsKr : Ks ≤ Kr :=
    rationalSpectralConstraintSpace_antitone jet hrs
  have hsup : W ⊔ Ks ≤ Kr := sup_le hWKr hKsKr
  have hsupRank :
      Module.finrank ℚ
          (W ⊔ Ks : Submodule ℚ (ProjectiveRationalCharacter (A × B × C))) ≤
        Module.finrank ℚ Kr :=
    Submodule.finrank_mono hsup
  have hadd :
      Module.finrank ℚ W + Module.finrank ℚ Ks =
        Module.finrank ℚ
          (W ⊔ Ks : Submodule ℚ
            (ProjectiveRationalCharacter (A × B × C))) := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq W Ks]
    change W ⊓ Ks = ⊥ at hreleased
    rw [hreleased]
    simp
  have hWrank :
      Module.finrank ℚ W =
        (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C := by
    change Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range
          (rectangleProjectiveRationalCharacter a₀ b₀ :
            RectangleContrastIndex A B C a₀ b₀ →
              ProjectiveRationalCharacter (A × B × C)))) = _
    rw [finrank_span_eq_card
      (rectangleProjectiveRationalCharacter_linearIndependent a₀ b₀)]
    exact rectangleContrastIndex_card a₀ b₀
  have hdrop :
      (Fintype.card A - 1) * (Fintype.card B - 1) * Fintype.card C ≤
        Module.finrank ℚ Kr - Module.finrank ℚ Ks := by
    rw [← hWrank]
    omega
  rw [temporalDimension_sub_eq_constraintFinrank_sub jet hrs]
  exact hdrop

/-- In an `n`-site `q`-level product spectrum, endpoint rectangle causality
leaves at least `(q - 1)^2 q^(n - 2)` unresolved rational characters. -/
theorem quditPair_constraint_finrank_lower_bound
    {q n : ℕ} (a₀ b₀ : Fin q)
    (jet : ℕ → Fin q × Fin q × (Fin (n - 2) → Fin q) → ℂ) (r : ℕ)
    (hvanish :
      ∀ (j : RectangleContrastIndex
          (Fin q) (Fin q) (Fin (n - 2) → Fin q) a₀ b₀) (m : Fin r),
        ∑ x, ((rectangleContrastRelation (R := ℚ) a₀ b₀ j x : ℚ) : ℂ) *
          jet m x = 0) :
    (q - 1) ^ 2 * q ^ (n - 2) ≤
      Module.finrank ℚ (rationalSpectralConstraintSpace jet r) := by
  simpa [pow_two] using
    rectangleConstraint_finrank_lower_bound a₀ b₀ jet r hvanish

end

end GaloisForLFunctions.HTGeometry
