import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFlowNeverStalls
import GaloisForLFunctions.RHTower.PaperRestrictedWeilInertia
import GaloisForLFunctions.HTGeometry.NonpositiveSpacesAvoidingTheKernel

/-!
# Every null mode forces aperture index growth

At every energy, enlarging the aperture converts the smaller nonpositive
spectral dimension into a lower bound for the larger negative index.
Consequently resonant apertures are finite below each fixed upper aperture.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil HTGeometry

/-- Zero extension on the weighted Fourier form domains is linear and injective. -/
def apertureExtLinear {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    Space a →ₗ[ℂ] Space b where
  toFun := apertureExt hab
  map_add' := apertureExt_add hab
  map_smul' := apertureExt_smul hab

private theorem injective_of_subtype_val_eq {X : Type*} {p q : X → Prop}
    (F : Subtype p → Subtype q) (hF : ∀ x, (F x).1 = x.1) : Function.Injective F := by
  intro x y hxy
  apply Subtype.ext
  exact (hF x).symm.trans ((congrArg Subtype.val hxy).trans (hF y))

theorem apertureExtLinear_injective {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    Function.Injective (apertureExtLinear hab) :=
  injective_of_subtype_val_eq (apertureExtLinear hab) (fun u => apertureExt_val hab u)

private theorem operator_quadratic_apertureExt {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) (E : ℝ) (u : Space a) :
    (inner ℂ (operator b E (apertureExt hab u)) (apertureExt hab u)).re =
      (inner ℂ (operator a E u) u).re := by
  rw [operator_quadratic, operator_quadratic,
    ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab (apertureExt_val hab u),
    norm_embedding_apertureExt]

/-- The larger-aperture repair is injective on every smaller-aperture
nonpositive space, including its null directions. -/
theorem nonpositive_dimension_le_larger_negativeRank {a b : SuzukiPositiveAperture}
    (hab : a.1 < b.1) (E : ℝ) (W : Submodule ℂ (Space a))
    (hW : ∀ u ∈ W, (inner ℂ (operator a E u) u).re ≤ 0) :
    FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ negativeRank b E := by
  let T := apertureExtLinear hab.le
  have hmap := PaperNegativePart.nonpositive_subspace_dimension_le
    (operator b E) (operator_selfAdjoint b E) (W.map T)
    (by
      rintro _ ⟨u, hu, rfl⟩
      exact (operator_quadratic_apertureExt hab.le E u).le.trans (hW u hu))
    (by
      rintro _ ⟨u, _, rfl⟩ hzero
      have hu : u = 0 := by
        by_contra hu0
        have hJu : ccmArchimedeanFormToAperture a u ≠ 0 := by
          intro hz
          exact hu0 ((ccmArchimedeanFormToAperture_injective a)
            (by simpa only [map_zero] using hz))
        apply not_isFormEigen_apertureExt hab hJu E
        intro z
        change ccmRestrictedWeilForm b (apertureExt hab.le u) z -
          (E : ℂ) * inner ℂ (ccmArchimedeanFormToAperture b (apertureExt hab.le u))
            (ccmArchimedeanFormToAperture b z) = 0
        rw [← operator_mixed]
        change inner ℂ (operator b E (T u)) z = 0
        rw [hzero, inner_zero_left]
      rw [hu, map_zero])
  let e := Submodule.equivMapOfInjective T (apertureExtLinear_injective hab.le) W
  letI := hmap.1
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective, ?_⟩
  rw [e.finrank_eq]
  exact hmap.2

/-- Multiplicity of a null mode of the literal shifted Weil form. -/
def weilNullity (a : SuzukiPositiveAperture) (E : ℝ) : ℕ :=
  Module.finrank ℂ (operator a E).toLinearMap.ker

instance finiteDimensional_weilKernel (a : SuzukiPositiveAperture) (E : ℝ) :
    FiniteDimensional ℂ (operator a E).toLinearMap.ker :=
  PaperNegativePart.finiteDimensional_kernel_of_one_sub_compact
    (operator a E) (one_sub_operator_compact a E)

/-- Every null multiplicity is paid by negative-index growth on every
strict enlargement, at every real energy. -/
theorem negativeRank_add_nullity_le_of_aperture_lt {a b : SuzukiPositiveAperture}
    (hab : a.1 < b.1) (E : ℝ) :
    negativeRank a E + weilNullity a E ≤ negativeRank b E := by
  have hd := PaperNegativePart.negativeSpace_disjoint_ker
    (operator a E) (operator_selfAdjoint a E)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (negativeSpace a E) (operator a E).toLinearMap.ker
  rw [hd.eq_bot] at hdim
  simp only [finrank_bot, add_zero] at hdim
  rw [negativeRank, weilNullity, ← hdim]
  exact (nonpositive_dimension_le_larger_negativeRank hab E _
    (fun _ hu => PaperNegativePart.nonpositive_on_negativeSpace_sup_ker
      (operator a E) (operator_selfAdjoint a E) hu)).2

/-- Enlarging the aperture cannot decrease the negative index. -/
theorem negativeRank_mono_of_aperture_le {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) (E : ℝ) : negativeRank a E ≤ negativeRank b E := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · have h := negativeRank_add_nullity_le_of_aperture_lt hlt E
    omega
  · exact (congrArg (fun c => negativeRank c E) (Subtype.ext heq)).le

/-- Total null multiplicity on any finite collection of smaller apertures
is bounded by the negative rank at the upper aperture. -/
theorem sum_nullity_le_negativeRank (s : Finset SuzukiPositiveAperture)
    (b : SuzukiPositiveAperture) (E : ℝ) (hs : ∀ a ∈ s, a.1 < b.1) :
    ∑ a ∈ s, weilNullity a E ≤ negativeRank b E := by
  classical
  induction s using Finset.induction_on_max generalizing b with
  | empty => simp only [Finset.sum_empty, Nat.zero_le]
  | insert a s hmax ih =>
      have ha : a.1 < b.1 := hs a (Finset.mem_insert_self a s)
      have hsum := ih a (fun x hx => hmax x hx)
      have hstep := negativeRank_add_nullity_le_of_aperture_lt ha E
      have hnot : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
      rw [Finset.sum_insert hnot]
      omega

/-- At a fixed energy, only finitely many smaller apertures can be resonant. -/
theorem finite_resonant_apertures_below (b : SuzukiPositiveAperture) (E : ℝ) :
    Set.Finite {a : SuzukiPositiveAperture | a.1 < b.1 ∧ 0 < weilNullity a E} := by
  let S := {a : SuzukiPositiveAperture | a.1 < b.1 ∧ 0 < weilNullity a E}
  let f : S → Fin (negativeRank b E) := fun a =>
    ⟨negativeRank a.1 E, by
      have h := negativeRank_add_nullity_le_of_aperture_lt a.2.1 E
      have hp := a.2.2
      omega⟩
  have hinj : Function.Injective f := by
    intro a c heq
    have hn : negativeRank a.1 E = negativeRank c.1 E := congrArg Fin.val heq
    rcases lt_trichotomy a.1.1 c.1.1 with hlt | he | hgt
    · have h := negativeRank_add_nullity_le_of_aperture_lt hlt E
      have hp := a.2.2
      omega
    · exact Subtype.ext (Subtype.ext he)
    · have h := negativeRank_add_nullity_le_of_aperture_lt hgt E
      have hp := c.2.2
      omega
  letI : Finite S := Finite.of_injective f hinj
  exact Set.toFinite S

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
