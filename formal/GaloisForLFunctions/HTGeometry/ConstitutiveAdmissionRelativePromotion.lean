import GaloisForLFunctions.HTGeometry.ConstitutivePromotionDifferential

/-!
# Admission-relative promotion

Algebraic exactness and admitted exactness are distinct mechanism tests.  The constant forward
difference has an algebraic primitive and exact bounded primitives on every finite horizon, but no
globally upper-bounded primitive.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

def AlgebraicallyExact {C : Type u} {R : Type v} (D : C → R) (ρ : R) : Prop :=
  ∃ c, D c = ρ

def AdmissiblyExact {C : Type u} {R : Type v}
    (D : C → R) (Adm : C → Prop) (ρ : R) : Prop :=
  ∃ c, Adm c ∧ D c = ρ

theorem admissiblyExact_implies_algebraicallyExact
    {C : Type u} {R : Type v} (D : C → R) (Adm : C → Prop) (ρ : R) :
    AdmissiblyExact D Adm ρ → AlgebraicallyExact D ρ := by
  rintro ⟨c, _, hc⟩
  exact ⟨c, hc⟩

/-- Every residual belongs to exactly one mechanism case: admitted repair, algebraic but singular
repair, or algebraic obstruction. -/
theorem admissionPromotion_trichotomy
    {C : Type u} {R : Type v} (D : C → R) (Adm : C → Prop) (ρ : R) :
    AdmissiblyExact D Adm ρ ∨
      (AlgebraicallyExact D ρ ∧ ¬ AdmissiblyExact D Adm ρ) ∨
      ¬ AlgebraicallyExact D ρ := by
  by_cases hadm : AdmissiblyExact D Adm ρ
  · exact Or.inl hadm
  · by_cases halg : AlgebraicallyExact D ρ
    · exact Or.inr (Or.inl ⟨halg, hadm⟩)
    · exact Or.inr (Or.inr halg)

def promotionForwardDifference (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  b (n + 1) - b n

def promotionConstantOne : ℕ → ℤ := fun _ => 1

def countingCalibration (n : ℕ) : ℤ := n

theorem countingCalibration_forwardDifference (n : ℕ) :
    promotionForwardDifference countingCalibration n = 1 := by
  simp [promotionForwardDifference, countingCalibration]

theorem constantOne_algebraicallyExact :
    AlgebraicallyExact promotionForwardDifference promotionConstantOne := by
  refine ⟨countingCalibration, ?_⟩
  funext n
  exact countingCalibration_forwardDifference n

/-- Every primitive of the constant-one forward residual is an affine counting calibration. -/
theorem forwardDifference_one_primitive_formula (b : ℕ → ℤ)
    (h : ∀ n, promotionForwardDifference b n = 1) :
    ∀ n, b n = b 0 + n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := h n
      simp only [promotionForwardDifference] at hn
      rw [ih] at hn
      push_cast
      omega

def UpperAdmittedCalibration (b : ℕ → ℤ) : Prop :=
  ∃ C : ℤ, ∀ n, b n ≤ C

theorem no_upperAdmitted_constantOne_primitive (b : ℕ → ℤ)
    (h : ∀ n, promotionForwardDifference b n = 1) :
    ¬ UpperAdmittedCalibration b := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (C - b 0 : ℤ)
  have hb := forwardDifference_one_primitive_formula b h n
  have hbound := hC n
  rw [hb] at hbound
  omega

theorem constantOne_not_admissiblyExact :
    ¬ AdmissiblyExact promotionForwardDifference
      UpperAdmittedCalibration promotionConstantOne := by
  rintro ⟨b, hb, hdiff⟩
  apply no_upperAdmitted_constantOne_primitive b
  · intro n
    exact congrFun hdiff n
  · exact hb

def cappedCountingCalibration (N n : ℕ) : ℤ :=
  Nat.min n N

theorem cappedCountingCalibration_upperAdmitted (N : ℕ) :
    UpperAdmittedCalibration (cappedCountingCalibration N) := by
  refine ⟨(N : ℤ), ?_⟩
  intro n
  dsimp [cappedCountingCalibration]
  exact_mod_cast Nat.min_le_right n N

theorem cappedCountingCalibration_forwardDifference_of_lt
    (N n : ℕ) (hn : n < N) :
    promotionForwardDifference (cappedCountingCalibration N) n = 1 := by
  simp only [promotionForwardDifference, cappedCountingCalibration]
  have hnle : n ≤ N := Nat.le_of_lt hn
  have hsnle : n + 1 ≤ N := Nat.succ_le_iff.mpr hn
  simp [Nat.min_eq_left hnle, Nat.min_eq_left hsnle]

/-- Every finite horizon admits an exact bounded repair of the globally singular residual. -/
theorem every_finiteHorizon_has_upperAdmitted_primitive (N : ℕ) :
    ∃ b : ℕ → ℤ,
      UpperAdmittedCalibration b ∧
        ∀ n < N, promotionForwardDifference b n = 1 := by
  exact ⟨cappedCountingCalibration N,
    cappedCountingCalibration_upperAdmitted N,
    cappedCountingCalibration_forwardDifference_of_lt N⟩

theorem constitutiveAdmissionRelativePromotionMechanism_closed :
    AlgebraicallyExact promotionForwardDifference promotionConstantOne ∧
    (¬ AdmissiblyExact promotionForwardDifference
      UpperAdmittedCalibration promotionConstantOne) ∧
    (∀ N, ∃ b : ℕ → ℤ,
      UpperAdmittedCalibration b ∧
        ∀ n < N, promotionForwardDifference b n = 1) := by
  exact ⟨constantOne_algebraicallyExact,
    constantOne_not_admissiblyExact,
    every_finiteHorizon_has_upperAdmitted_primitive⟩

end GaloisForLFunctions.HTGeometry
