import GaloisForLFunctions.HTGeometry.ConstitutiveCohomologicalDegreeLowering
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Canonical exact coinduced reporter

The algebraic exact reporter required by cohomological degree lowering always exists: quotient all
coinduced functions by the subgroup of constant functions.  Right translation descends to an
additive action, the quotient map kills exactly constants, and it is surjective.  This closes the
algebraic formation/recovery gate and isolates Hilbert/topological admission as the remaining gate.
-/

namespace GaloisForLFunctions.HTGeometry

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

/-- Constant coinduced histories as an additive subgroup. -/
def coinducedFormationConstantSubgroup : AddSubgroup (G → A) where
  carrier := {f | ∃ a, f = coinducedFormationConstant a}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f h ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    rfl
  neg_mem' := by
    rintro f ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    rfl

/-- Coinduced histories modulo constants. -/
abbrev CohomologicalCoinducedQuotient :=
  (G → A) ⧸ coinducedFormationConstantSubgroup (G := G) (A := A)

/-- Right translation as an additive equivalence before quotienting. -/
def coinducedFormationRightTranslateAddEquiv (g : G) : (G → A) ≃+ (G → A) where
  toFun := coinducedFormationRightTranslate g
  invFun := coinducedFormationRightTranslate (-g)
  left_inv f := by
    funext x
    simp [coinducedFormationRightTranslate, add_assoc]
  right_inv f := by
    funext x
    simp [coinducedFormationRightTranslate, add_assoc]
  map_add' _ _ := rfl

/-- Right translation preserves exactly the constant-history subgroup. -/
theorem coinducedFormationConstantSubgroup_comap_rightTranslate (g : G) :
    (coinducedFormationConstantSubgroup (G := G) (A := A)).comap
        (coinducedFormationRightTranslateAddEquiv (A := A) g).toAddMonoidHom =
      coinducedFormationConstantSubgroup (G := G) (A := A) := by
  ext f
  constructor
  · intro hf
    change ∃ a, coinducedFormationRightTranslate g f = coinducedFormationConstant a at hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨a, ?_⟩
    funext x
    have hx := congrFun ha (x - g)
    simpa [coinducedFormationRightTranslate, coinducedFormationConstant,
      sub_eq_add_neg, add_assoc] using hx
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rfl

/-- Right translation descended to the quotient by constants. -/
def coinducedQuotientRightTranslateHom (g : G) :
    CohomologicalCoinducedQuotient (G := G) (A := A) →+
      CohomologicalCoinducedQuotient (G := G) (A := A) :=
  QuotientAddGroup.map (coinducedFormationConstantSubgroup (G := G) (A := A))
    (coinducedFormationConstantSubgroup (G := G) (A := A))
    (coinducedFormationRightTranslateAddEquiv (A := A) g).toAddMonoidHom (by
      rw [coinducedFormationConstantSubgroup_comap_rightTranslate (A := A)])

@[simp] theorem coinducedQuotientRightTranslateHom_mk (g : G) (f : G → A) :
    coinducedQuotientRightTranslateHom (A := A) g (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk (coinducedFormationRightTranslate g f) := by
  rw [coinducedQuotientRightTranslateHom, QuotientAddGroup.map_mk]
  rfl

/-- Descended right translation is invertible, with inverse translation by `-g`. -/
noncomputable def coinducedQuotientRightTranslateEquiv (g : G) :
    CohomologicalCoinducedQuotient (G := G) (A := A) ≃+
      CohomologicalCoinducedQuotient (G := G) (A := A) where
  toFun := coinducedQuotientRightTranslateHom (A := A) g
  invFun := coinducedQuotientRightTranslateHom (A := A) (-g)
  left_inv q := by
    induction q using QuotientAddGroup.induction_on with
    | H f =>
        simp only [coinducedQuotientRightTranslateHom_mk]
        congr 1
        funext x
        simp [coinducedFormationRightTranslate, add_assoc]
  right_inv q := by
    induction q using QuotientAddGroup.induction_on with
    | H f =>
        simp only [coinducedQuotientRightTranslateHom_mk]
        congr 1
        funext x
        simp [coinducedFormationRightTranslate, add_assoc]
  map_add' := (coinducedQuotientRightTranslateHom (A := A) g).map_add

@[simp] theorem coinducedQuotientRightTranslateEquiv_mk (g : G) (f : G → A) :
    coinducedQuotientRightTranslateEquiv (A := A) g (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk (coinducedFormationRightTranslate g f) :=
  coinducedQuotientRightTranslateHom_mk g f

/-- Canonical algebraic exact reporter: quotient by constants with descended right translation. -/
noncomputable def canonicalCohomologicalExactReporter :
    CohomologicalExactReporter (G := G) (A := A)
      (H := CohomologicalCoinducedQuotient (G := G) (A := A)) where
  reporter :=
    QuotientAddGroup.mk' (coinducedFormationConstantSubgroup (G := G) (A := A))
  action := coinducedQuotientRightTranslateEquiv (A := A)
  action_zero v := by
    induction v using QuotientAddGroup.induction_on with
    | H f =>
        rw [coinducedQuotientRightTranslateEquiv_mk]
        congr 1
        funext x
        simp [coinducedFormationRightTranslate]
  action_add g h v := by
    induction v using QuotientAddGroup.induction_on with
    | H f =>
        rw [coinducedQuotientRightTranslateEquiv_mk,
          coinducedQuotientRightTranslateEquiv_mk,
          coinducedQuotientRightTranslateEquiv_mk]
        congr 1
        funext x
        simp [coinducedFormationRightTranslate, add_assoc]
  kills_constants a := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact ⟨a, rfl⟩
  intertwines g f := by
    change QuotientAddGroup.mk (coinducedFormationRightTranslate g f) =
      coinducedQuotientRightTranslateEquiv (A := A) g (QuotientAddGroup.mk f)
    exact (coinducedQuotientRightTranslateEquiv_mk g f).symm
  exact_kernel f hf := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hf
    exact hf
  surjective :=
    QuotientAddGroup.mk'_surjective
      (coinducedFormationConstantSubgroup (G := G) (A := A))

end GaloisForLFunctions.HTGeometry
