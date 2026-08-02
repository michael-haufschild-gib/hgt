import GaloisForLFunctions.RHTower.DeningerQuotientSeminorm
import GaloisForLFunctions.RHTower.DeningerNuclearSubspaceCompleted

/-!
# The quotient projection of seminorm spaces

A quotient of modules induces a norm-decreasing surjection of the associated seminorm spaces, and
that surjection commutes with the comparison maps of dominating seminorms.  After completion the
square still commutes, both composites agreeing on the dense image.

If the completed projection admits a bounded right inverse, the comparison map downstairs is the
comparison map upstairs conjugated by bounded maps, hence nuclear: nuclearity descends to the
quotient.

* `deningerQuotientProjection`, `_mk` : the projection of seminorm spaces.
* `deningerQuotientProjectionC` : its completion.
* `deningerIsNuclearSpaceC_quotient_of_rightInverse` : **nuclearity of a quotient with a
  sectioned projection.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section QuotientProjection

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem deningerQuotientKer_le (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    deningerSeminormKer p
      ≤ LinearMap.ker ((deningerSeminormMk (deningerQuotientSeminorm N p)).comp N.mkQ) := by
  intro x hx
  have hp : p x = 0 := hx
  have hle : deningerQuotientSeminorm N p (Submodule.Quotient.mk x) ≤ 0 := by
    have h := deningerQuotientSeminorm_mk_le N p x
    rw [hp] at h
    exact h
  have hzero : deningerQuotientSeminorm N p (Submodule.Quotient.mk x) = 0 :=
    le_antisymm hle (apply_nonneg _ _)
  show (deningerSeminormMk (deningerQuotientSeminorm N p)) (Submodule.Quotient.mk x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr hzero

/-- **The projection of seminorm spaces induced by a quotient of modules.** -/
noncomputable def deningerQuotientProjection (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    DeningerSeminormSpace p →L[𝕜] DeningerSeminormSpace (deningerQuotientSeminorm N p) :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer p)
      ((deningerSeminormMk (deningerQuotientSeminorm N p)).comp N.mkQ)
      (deningerQuotientKer_le N p))
    1 (by
      rintro ⟨x⟩
      show ‖(deningerSeminormMk (deningerQuotientSeminorm N p)) (Submodule.Quotient.mk x)‖
        ≤ 1 * p x
      rw [deningerSeminormMk_norm, one_mul]
      exact deningerQuotientSeminorm_mk_le N p x)

@[simp] theorem deningerQuotientProjection_mk (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : E) :
    deningerQuotientProjection N p (deningerSeminormMk p x)
      = deningerSeminormMk (deningerQuotientSeminorm N p) (Submodule.Quotient.mk x) := rfl

theorem deningerQuotientProjection_surjective (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    Function.Surjective (deningerQuotientProjection N p) := by
  intro w
  obtain ⟨z, rfl⟩ := deningerSeminormMk_surjective (deningerQuotientSeminorm N p) w
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
  exact ⟨deningerSeminormMk p x, rfl⟩

/-- **The comparison square of a quotient**, before completion. -/
theorem deningerQuotientProjection_square {p q : Seminorm 𝕜 E} {C : ℝ} (N : Submodule 𝕜 E)
    (h : ∀ x, p x ≤ C * q x)
    (hN : ∀ z : E ⧸ N, deningerQuotientSeminorm N p z ≤ C * deningerQuotientSeminorm N q z) :
    (deningerQuotientProjection N p).comp (deningerSeminormComparison h)
      = (deningerSeminormComparison hN).comp (deningerQuotientProjection N q) := by
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective q w
  rfl

/-- **The completed projection of seminorm spaces.** -/
noncomputable def deningerQuotientProjectionC (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    DeningerSeminormCompletion p →L[𝕜]
      DeningerSeminormCompletion (deningerQuotientSeminorm N p) :=
  ((Completion.toComplL (𝕜 := 𝕜)
      (E := DeningerSeminormSpace (deningerQuotientSeminorm N p))).comp
    (deningerQuotientProjection N p)).extend
      (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))

theorem deningerQuotientProjectionC_coe (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E)
    (z : DeningerSeminormSpace p) :
    deningerQuotientProjectionC N p
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p) z)
      = Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerQuotientSeminorm N p))
        (deningerQuotientProjection N p z) :=
  ContinuousLinearMap.extend_eq
    (f := (Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerQuotientSeminorm N p))).comp
      (deningerQuotientProjection N p))
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))
    (deningerDenseRange_toComplL _) (deningerIsUniformInducing_toComplL _) z

/-- **The comparison square of a quotient, after completion.** -/
theorem deningerQuotientProjectionC_square {p q : Seminorm 𝕜 E} {C : ℝ} (N : Submodule 𝕜 E)
    (h : ∀ x, p x ≤ C * q x)
    (hN : ∀ z : E ⧸ N, deningerQuotientSeminorm N p z ≤ C * deningerQuotientSeminorm N q z) :
    (deningerQuotientProjectionC N p).comp (deningerSeminormComparisonC h)
      = (deningerSeminormComparisonC hN).comp (deningerQuotientProjectionC N q) := by
  refine DFunLike.coe_injective ?_
  refine (deningerDenseRange_toComplL q).equalizer
    ((deningerQuotientProjectionC N p).comp (deningerSeminormComparisonC h)).continuous
    ((deningerSeminormComparisonC hN).comp (deningerQuotientProjectionC N q)).continuous ?_
  funext w
  show deningerQuotientProjectionC N p (deningerSeminormComparisonC h (Completion.toComplL w))
    = deningerSeminormComparisonC hN (deningerQuotientProjectionC N q (Completion.toComplL w))
  rw [deningerSeminormComparisonC_coe, deningerQuotientProjectionC_coe,
    deningerQuotientProjectionC_coe, deningerSeminormComparisonC_coe]
  exact congrArg
    (Completion.toComplL (𝕜 := 𝕜)
      (E := DeningerSeminormSpace (deningerQuotientSeminorm N p)))
    (ContinuousLinearMap.ext_iff.mp (deningerQuotientProjection_square N h hN) w)

/-- **A quotient whose completed projections are sectioned is nuclear in the completed sense.**
The comparison map downstairs is the comparison map upstairs conjugated by the section and the
projection, hence nuclear. -/
theorem deningerIsNuclearSpaceC_quotient_of_rightInverse {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (N : Submodule 𝕜 E) (hP : DeningerIsNuclearSpaceC P)
    (hsec : ∀ i : ι, ∃ σ : DeningerSeminormCompletion (deningerQuotientSeminorm N (P i)) →L[𝕜]
        DeningerSeminormCompletion (P i),
      ∀ w, deningerQuotientProjectionC N (P i) (σ w) = w) :
    DeningerIsNuclearSpaceC (fun i => deningerQuotientSeminorm N (P i)) := by
  intro i
  obtain ⟨j, C, h, hnuc⟩ := hP i
  obtain ⟨σ, hσ⟩ := hsec j
  have habs : ∀ x, P i x ≤ |C| * P j x := deningerSeminorm_le_abs h
  have hN : ∀ z : E ⧸ N, deningerQuotientSeminorm N (P i) z
      ≤ |C| * deningerQuotientSeminorm N (P j) z := fun z =>
    deningerQuotientSeminorm_le_of_le N (abs_nonneg C) habs z
  refine ⟨j, |C|, hN, ?_⟩
  have hnuc' : DeningerIsNuclear (deningerSeminormComparisonC habs) := by
    refine hnuc.of_eq ?_
    refine DFunLike.coe_injective ?_
    refine (deningerDenseRange_toComplL (P j)).equalizer
      (deningerSeminormComparisonC h).continuous
      (deningerSeminormComparisonC habs).continuous ?_
    funext w
    show deningerSeminormComparisonC h (Completion.toComplL w)
      = deningerSeminormComparisonC habs (Completion.toComplL w)
    rw [deningerSeminormComparisonC_coe, deningerSeminormComparisonC_coe]
    rfl
  have hcomp : DeningerIsNuclear
      ((deningerQuotientProjectionC N (P i)).comp
        ((deningerSeminormComparisonC habs).comp σ)) :=
    (hnuc'.compR σ).compL (deningerQuotientProjectionC N (P i))
  refine hcomp.of_eq ?_
  refine ContinuousLinearMap.ext fun w => ?_
  have hsquare : deningerQuotientProjectionC N (P i) (deningerSeminormComparisonC habs (σ w))
      = deningerSeminormComparisonC hN (deningerQuotientProjectionC N (P j) (σ w)) :=
    ContinuousLinearMap.ext_iff.mp (deningerQuotientProjectionC_square N habs hN) (σ w)
  show deningerSeminormComparisonC hN w
    = deningerQuotientProjectionC N (P i) (deningerSeminormComparisonC habs (σ w))
  rw [hsquare, hσ w]

end QuotientProjection

end RHTower
