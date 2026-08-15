import GaloisForLFunctions.RHTower.SourceRecession
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Source-normalization fixed-budget gates

This module closes the form-level cone algebra behind two source-transfer
guardrails.  A positive-scale-invariant class of residual forms cannot stay
under one fixed positive-semidefinite budget unless each residual is itself
positive semidefinite.  Likewise, exact linear normalizations leave only
zero two-sided recession directions when the budget holds on their whole
affine class.

The statements use real bilinear forms.  This is the common real quadratic
cone for real symmetric forms and, after realification, complex Hermitian
forms; no finite-dimensionality assumption is needed by the algebra.
-/

namespace GaloisForLFunctions

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A source-orientation class which cannot distinguish a form from a positive
real rescaling of that form. -/
def sourceOrientationScaleInvariant
    (C : Set (LinearMap.BilinForm ℝ V)) : Prop :=
  ∀ ⦃R : LinearMap.BilinForm ℝ V⦄, R ∈ C →
    ∀ ⦃t : ℝ⦄, 0 < t → t • R ∈ C

/-- **Scale-invariant orientation cannot pay a fixed budget.** If every form
selected by a positive-scale-invariant source predicate satisfies `B + R ≥ 0`,
then every selected residual `R` is positive semidefinite. -/
theorem source_orientation_fixed_budget_forces_posSemidef
    (B : LinearMap.BilinForm ℝ V) (C : Set (LinearMap.BilinForm ℝ V))
    (hscale : sourceOrientationScaleInvariant C)
    (hbudget : ∀ ⦃R : LinearMap.BilinForm ℝ V⦄, R ∈ C → (B + R).IsPosSemidef) :
    ∀ ⦃R : LinearMap.BilinForm ℝ V⦄, R ∈ C → R.IsPosSemidef := by
  intro R hR
  have hdiag : ∀ v : V, 0 ≤ R v v :=
    source_budget_one_sided_recession_nonnegative (fun v => (B + R) v v) (fun _ => 0)
      (fun v => R v v) (by
        intro t ht v
        have hpos : 0 < 1 + t := by linarith
        have hmember : (1 + t) • R ∈ C := hscale hR hpos
        have h := hbudget hmember
        have hnonneg := h.isNonneg.nonneg v
        change 0 ≤ (B + (1 + t) • R) v v at hnonneg
        change 0 ≤ B v v + (1 + t) * R v v at hnonneg
        calc
          0 ≤ B v v + (1 + t) * R v v := hnonneg
          _ = (B v v + R v v) + 0 + t * R v v := by ring)
  have h1 := (hbudget hR).isSymm
  have h2 := (hbudget (hscale hR (by norm_num : 0 < (2 : ℝ)))).isSymm
  refine ⟨?_, ⟨hdiag⟩⟩
  refine ⟨fun x y => ?_⟩
  have h1eq := h1.eq x y
  have h2eq := h2.eq x y
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h2eq
  change B x y + R x y = B y x + R y x at h1eq
  linarith

/-- A one-sided affine ray of real bilinear forms can remain under a fixed
budget only when its direction is positive semidefinite. -/
theorem source_budget_one_sided_recession_posSemidef
    (B R D : LinearMap.BilinForm ℝ V)
    (hbudget : ∀ t : ℝ, 0 ≤ t → (B + R + t • D).IsPosSemidef) :
    D.IsPosSemidef := by
  have hdiag : ∀ v : V, 0 ≤ D v v :=
    source_budget_one_sided_recession_nonnegative (fun v => B v v) (fun v => R v v)
      (fun v => D v v) (by
        intro t ht v
        have h := hbudget t ht
        have hnonneg := h.isNonneg.nonneg v
        change 0 ≤ (B + R + t • D) v v at hnonneg
        change 0 ≤ B v v + R v v + t * D v v at hnonneg
        exact hnonneg)
  have hzero := hbudget 0 le_rfl
  have hone := hbudget 1 zero_le_one
  refine ⟨?_, ⟨hdiag⟩⟩
  refine ⟨fun x y => ?_⟩
  have hzeroeq := hzero.isSymm.eq x y
  have honeeq := hone.isSymm.eq x y
  simp only [LinearMap.add_apply, zero_smul, add_zero] at hzeroeq
  simp only [LinearMap.add_apply, one_smul] at honeeq
  change B x y + R x y = B y x + R y x at hzeroeq
  change B x y + R x y + D x y = B y x + R y x + D y x at honeeq
  linarith

/-- A two-sided affine line of real bilinear forms can remain under a fixed
budget only when its direction vanishes. -/
theorem source_budget_two_sided_recession_zero_form
    (B R D : LinearMap.BilinForm ℝ V)
    (hbudget : ∀ t : ℝ, (B + R + t • D).IsPosSemidef) :
    D = 0 := by
  have hdiag : ∀ v : V, D v v = 0 :=
    source_budget_two_sided_recession_zero (fun v => B v v) (fun v => R v v)
      (fun v => D v v) (by
        intro t v
        have h := hbudget t
        have hnonneg := h.isNonneg.nonneg v
        change 0 ≤ (B + R + t • D) v v at hnonneg
        change 0 ≤ B v v + R v v + t * D v v at hnonneg
        exact hnonneg)
  have hzero := hbudget 0
  have hone := hbudget 1
  have hsym : D.IsSymm := by
    refine ⟨fun x y => ?_⟩
    have hzeroeq := hzero.isSymm.eq x y
    have honeeq := hone.isSymm.eq x y
    simp only [LinearMap.add_apply, zero_smul, add_zero] at hzeroeq
    simp only [LinearMap.add_apply, one_smul] at honeeq
    change B x y + R x y = B y x + R y x at hzeroeq
    change B x y + R x y + D x y = B y x + R y x + D y x at honeeq
    linarith
  apply LinearMap.BilinForm.ext_of_isSymm hsym LinearMap.BilinForm.isSymm_zero
  intro v
  simpa using hdiag v

/-- Residual forms satisfying a prescribed family of linear source normalizations. -/
def sourceNormalizationAffine {ι : Type*}
    (L : ι → LinearMap.BilinForm ℝ V →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (R : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ j, L j R = c j

/-- Directions invisible to every prescribed linear source normalization. -/
def sourceNormalizationRecession {ι : Type*}
    (L : ι → LinearMap.BilinForm ℝ V →ₗ[ℝ] ℝ)
    (D : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ j, L j D = 0

/-- Adding any real multiple of an invisible direction preserves every exact
linear source normalization. -/
theorem sourceNormalizationAffine_add_smul_recession {ι : Type*}
    (L : ι → LinearMap.BilinForm ℝ V →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (R D : LinearMap.BilinForm ℝ V)
    (hR : sourceNormalizationAffine L c R)
    (hD : sourceNormalizationRecession L D) (t : ℝ) :
    sourceNormalizationAffine L c (R + t • D) := by
  intro j
  simp only [LinearMap.map_add, LinearMap.map_smul,
    hR j, hD j, smul_eq_mul, mul_zero, add_zero]

/-- **Finite-normalization recession gate.** If an affine class of real
bilinear residual forms is cut out by linear source normalizations and every
member obeys a fixed positive-semidefinite budget, every remaining two-sided
recession direction is zero.  The theorem does not need finiteness of the
index type, so it strictly strengthens the finite-list statement. -/
theorem finite_source_normalizations_budget_force_recession_zero {ι : Type*}
    (B : LinearMap.BilinForm ℝ V)
    (L : ι → LinearMap.BilinForm ℝ V →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hnonempty : ∃ R : LinearMap.BilinForm ℝ V, sourceNormalizationAffine L c R)
    (hbudget : ∀ ⦃R : LinearMap.BilinForm ℝ V⦄,
      sourceNormalizationAffine L c R → (B + R).IsPosSemidef)
    (D : LinearMap.BilinForm ℝ V) (hD : sourceNormalizationRecession L D) :
    D = 0 := by
  obtain ⟨R, hR⟩ := hnonempty
  apply source_budget_two_sided_recession_zero_form B R D
  intro t
  have hmember := sourceNormalizationAffine_add_smul_recession L c R D hR hD t
  simpa only [add_assoc] using hbudget hmember

/-- The positive-semidefinite version of the finite-normalization recession
gate, matching the stated Loewner-cone conclusion. -/
theorem finite_source_normalizations_budget_force_recession_posSemidef {ι : Type*}
    (B : LinearMap.BilinForm ℝ V)
    (L : ι → LinearMap.BilinForm ℝ V →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (hnonempty : ∃ R : LinearMap.BilinForm ℝ V, sourceNormalizationAffine L c R)
    (hbudget : ∀ ⦃R : LinearMap.BilinForm ℝ V⦄,
      sourceNormalizationAffine L c R → (B + R).IsPosSemidef)
    (D : LinearMap.BilinForm ℝ V) (hD : sourceNormalizationRecession L D) :
    D.IsPosSemidef := by
  rw [finite_source_normalizations_budget_force_recession_zero B L c hnonempty hbudget D hD]
  exact LinearMap.BilinForm.isPosSemidef_zero

end

end GaloisForLFunctions
