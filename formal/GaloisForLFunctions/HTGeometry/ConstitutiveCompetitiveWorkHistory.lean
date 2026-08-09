import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Competitive work envelopes and selection-induced history

Every scalar potential supplies an exact directed work law.  The pointwise maximum of two such
laws enforces both lower work requirements.  Its two-cycle work is exactly the absolute difference
between the parent increments.  Consequently the maximum is scalar-integrable only when the two
potentials differ by a constant.  Pointwise mandatory selection can therefore create a positive
history cycle from individually exact laws, while the pointwise minimum remains integrable.
-/

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

/-- Exact directed work supplied by a scalar potential. -/
def constitutiveExactWork (A : ι → ℝ) (i j : ι) : ℝ := A j - A i

/-- Mandatory parallel composition: enforce both exact lower work requirements. -/
def constitutiveConjunctiveWork (A B : ι → ℝ) (i j : ι) : ℝ :=
  max (constitutiveExactWork A i j) (constitutiveExactWork B i j)

/-- Permissive parallel composition: either exact lower work requirement may be used. -/
def constitutiveDisjunctiveWork (A B : ι → ℝ) (i j : ι) : ℝ :=
  min (constitutiveExactWork A i j) (constitutiveExactWork B i j)

/-- A directed work law is scalar-integrable when one potential dominates every increment. -/
def ConstitutiveScalarIntegrable (ω : ι → ι → ℝ) : Prop :=
  ∃ H : ι → ℝ, ∀ i j, ω i j ≤ constitutiveExactWork H i j

/-- Reversing an exact transition negates its work. -/
theorem constitutiveExactWork_reverse (A : ι → ℝ) (i j : ι) :
    constitutiveExactWork A j i = -constitutiveExactWork A i j := by
  simp [constitutiveExactWork]

/-- Scalar normalization is invisible to exact work. -/
theorem constitutiveExactWork_add_const (A : ι → ℝ) (c : ℝ) (i j : ι) :
    constitutiveExactWork (fun x => A x + c) i j = constitutiveExactWork A i j := by
  simp [constitutiveExactWork]

/-- **Conservative dominance rigidity.** One exact directed work law cannot pointwise dominate
another unless the two laws are equal. Reversing every transition turns the proposed inequality
into its converse. -/
theorem constitutiveExactWork_dominance_rigidity (A H : ι → ℝ)
    (h : ∀ i j, constitutiveExactWork A i j ≤ constitutiveExactWork H i j) :
    ∀ i j, constitutiveExactWork A i j = constitutiveExactWork H i j := by
  intro i j
  apply le_antisymm (h i j)
  have hr := h j i
  simp only [constitutiveExactWork] at hr ⊢
  linarith

/-- **No strict scalar-integrable strengthening.** If a work law strengthens one exact law on
every directed transition, then it remains scalar-integrable exactly when it equals that law. -/
theorem constitutiveStrengthening_scalarIntegrable_iff_eq (A : ι → ℝ) (ω : ι → ι → ℝ)
    (hA : ∀ i j, constitutiveExactWork A i j ≤ ω i j) :
    ConstitutiveScalarIntegrable ω ↔ ∀ i j, ω i j = constitutiveExactWork A i j := by
  constructor
  · rintro ⟨H, hH⟩
    have hAH : ∀ i j, constitutiveExactWork A i j ≤ constitutiveExactWork H i j :=
      fun i j => le_trans (hA i j) (hH i j)
    have heq := constitutiveExactWork_dominance_rigidity A H hAH
    intro i j
    apply le_antisymm
    · calc
        ω i j ≤ constitutiveExactWork H i j := hH i j
        _ = constitutiveExactWork A i j := (heq i j).symm
    · exact hA i j
  · intro heq
    exact ⟨A, fun i j => le_of_eq (heq i j)⟩

/-- **Competitive two-cycle law.** Mandatory selection creates precisely the absolute discrepancy
between the two parent increments. -/
theorem constitutiveConjunctiveWork_twoCycle (A B : ι → ℝ) (i j : ι) :
    constitutiveConjunctiveWork A B i j + constitutiveConjunctiveWork A B j i =
      |constitutiveExactWork A i j - constitutiveExactWork B i j| := by
  change max (A j - A i) (B j - B i) + max (A i - A j) (B i - B j) =
    |(A j - A i) - (B j - B i)|
  have hA : A i - A j = -(A j - A i) := by ring
  have hB : B i - B j = -(B j - B i) := by ring
  rw [hA, hB, max_neg_neg]
  simpa [sub_eq_add_neg, max_comm, min_comm] using
    max_sub_min_eq_abs (B j - B i) (A j - A i)

/-- Any disagreement produces a strictly positive two-step work history. -/
theorem constitutiveConjunctiveWork_positive_twoCycle (A B : ι → ℝ) (i j : ι)
    (h : constitutiveExactWork A i j ≠ constitutiveExactWork B i j) :
    0 < constitutiveConjunctiveWork A B i j + constitutiveConjunctiveWork A B j i := by
  rw [constitutiveConjunctiveWork_twoCycle]
  exact abs_pos.mpr (sub_ne_zero.mpr h)

/-- **Scalar-integrability rigidity.** The mandatory envelope of two exact laws admits a scalar
action exactly when the parent exact work laws coincide. -/
theorem constitutiveConjunctiveWork_scalarIntegrable_iff (A B : ι → ℝ) :
    ConstitutiveScalarIntegrable (constitutiveConjunctiveWork A B) ↔
      ∀ i j, constitutiveExactWork A i j = constitutiveExactWork B i j := by
  constructor
  · rintro ⟨H, hH⟩ i j
    have hsum : constitutiveConjunctiveWork A B i j +
        constitutiveConjunctiveWork A B j i ≤ 0 := by
      calc
        constitutiveConjunctiveWork A B i j + constitutiveConjunctiveWork A B j i
            ≤ constitutiveExactWork H i j + constitutiveExactWork H j i :=
          add_le_add (hH i j) (hH j i)
        _ = 0 := by simp [constitutiveExactWork]
    rw [constitutiveConjunctiveWork_twoCycle] at hsum
    have hz : |constitutiveExactWork A i j - constitutiveExactWork B i j| = 0 :=
      le_antisymm hsum (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  · intro h
    refine ⟨A, fun i j => ?_⟩
    rw [constitutiveConjunctiveWork, h i j, max_self]

/-- One disagreeing transition rules out every scalar action for the mandatory envelope. -/
theorem constitutiveConjunctiveWork_not_scalarIntegrable (A B : ι → ℝ) (i j : ι)
    (h : constitutiveExactWork A i j ≠ constitutiveExactWork B i j) :
    ¬ ConstitutiveScalarIntegrable (constitutiveConjunctiveWork A B) := by
  rw [constitutiveConjunctiveWork_scalarIntegrable_iff]
  exact fun hall => h (hall i j)

/-- Equality of exact work is equivalently equality of potentials modulo one marked scalar gauge. -/
theorem constitutiveExactWork_eq_iff_gaugeAt (A B : ι → ℝ) (b : ι) :
    (∀ i j, constitutiveExactWork A i j = constitutiveExactWork B i j) ↔
      ∀ i, A i - B i = A b - B b := by
  constructor
  · intro h i
    have hi := h b i
    simp only [constitutiveExactWork] at hi
    linarith
  · intro h i j
    have hi := h i
    have hj := h j
    simp only [constitutiveExactWork]
    linarith

/-- Marked-gauge form of scalar-integrability rigidity. -/
theorem constitutiveConjunctiveWork_scalarIntegrable_iff_gaugeAt
    (A B : ι → ℝ) (b : ι) :
    ConstitutiveScalarIntegrable (constitutiveConjunctiveWork A B) ↔
      ∀ i, A i - B i = A b - B b := by
  rw [constitutiveConjunctiveWork_scalarIntegrable_iff,
    constitutiveExactWork_eq_iff_gaugeAt A B b]

/-- The permissive envelope is always integrable by the left parent action. -/
theorem constitutiveDisjunctiveWork_scalarIntegrable_left (A B : ι → ℝ) :
    ConstitutiveScalarIntegrable (constitutiveDisjunctiveWork A B) := by
  exact ⟨A, fun i j => min_le_left _ _⟩

/-- The permissive envelope is also always integrable by the right parent action. -/
theorem constitutiveDisjunctiveWork_scalarIntegrable_right (A B : ι → ℝ) :
    ConstitutiveScalarIntegrable (constitutiveDisjunctiveWork A B) := by
  exact ⟨B, fun i j => min_le_right _ _⟩

/-- Closed capstone: mandatory pointwise selection creates a non-scalar history sector unless the
two parent exact laws were already the same law up to additive gauge. -/
theorem constitutiveMandatorySelectionCreatesHistory_iff (A B : ι → ℝ) (b : ι) :
    ConstitutiveScalarIntegrable (constitutiveConjunctiveWork A B) ↔
      ∀ i, A i - B i = A b - B b :=
  constitutiveConjunctiveWork_scalarIntegrable_iff_gaugeAt A B b

end GaloisForLFunctions.HTGeometry
