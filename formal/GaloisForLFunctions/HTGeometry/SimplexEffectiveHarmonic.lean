import Mathlib.Analysis.Matrix.Order

/-!
# The effective harmonic line of unaugmented simplex descent

Augmented descent on a full simplex is exact.  Removing the augmentation retains one constant
degree-zero class.  This file constructs its finite harmonic projection explicitly, proves that
its range is exactly the constant-section line, and gives the positive Green equation for the
orthogonal complement.

The surviving class is in even degree, so its grading is positive.  This is the finite Hodge
model for a distinguished effective section.  No analytic source, zeta function, or target moment
sequence occurs here.
-/

open scoped BigOperators ComplexOrder

namespace HTGeometry

open Matrix

noncomputable section

section EffectiveLine

variable {ι : Type*} [Fintype ι]

/-- The constant rank-one kernel on the simplex vertices. -/
def simplexAllOnes : Matrix ι ι ℂ := fun _ _ => 1

/-- The normalized projection kernel onto the constant section. -/
def simplexEffectiveHarmonicProjection : Matrix ι ι ℂ :=
  fun _ _ => ((Fintype.card ι : ℂ))⁻¹

/-- The distinguished constant section retained by unaugmented simplex descent. -/
def simplexEffectiveSection : ι → ℂ := fun _ => 1

/-- Squaring the all-ones kernel multiplies it by the number of simplex vertices. -/
theorem simplexAllOnes_mul_self :
    simplexAllOnes (ι := ι) * simplexAllOnes =
      (Fintype.card ι : ℂ) • simplexAllOnes := by
  ext i j
  simp [simplexAllOnes, Matrix.mul_apply]

/-- The constant kernel is positive semidefinite. -/
theorem simplexAllOnes_posSemidef :
    (simplexAllOnes (ι := ι)).PosSemidef := by
  let B : Matrix ι (Fin 1) ℂ := fun _ _ => 1
  have hB : simplexAllOnes (ι := ι) = B * Bᴴ := by
    ext i j
    simp [simplexAllOnes, B, Matrix.mul_apply]
  rw [hB]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- On a nonempty simplex, the normalized constant kernel is idempotent. -/
theorem simplexEffectiveHarmonicProjection_sq [Nonempty ι] :
    simplexEffectiveHarmonicProjection (ι := ι) *
        simplexEffectiveHarmonicProjection =
      simplexEffectiveHarmonicProjection := by
  ext i j
  simp only [Matrix.mul_apply, simplexEffectiveHarmonicProjection]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The normalized constant kernel is Hermitian. -/
theorem simplexEffectiveHarmonicProjection_isHermitian :
    (simplexEffectiveHarmonicProjection (ι := ι)).IsHermitian := by
  ext i j
  simp [simplexEffectiveHarmonicProjection]

/-- The effective harmonic projection is positive semidefinite. -/
theorem simplexEffectiveHarmonicProjection_posSemidef [Nonempty ι] :
    (simplexEffectiveHarmonicProjection (ι := ι)).PosSemidef := by
  have heq : simplexEffectiveHarmonicProjection (ι := ι) =
      ((Fintype.card ι : ℂ))⁻¹ • simplexAllOnes := by
    ext i j
    simp [simplexEffectiveHarmonicProjection, simplexAllOnes]
  rw [heq]
  apply simplexAllOnes_posSemidef.smul
  have hcast : ((Fintype.card ι : ℂ))⁻¹ =
      ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.nonneg_iff]
  constructor
  · have hnR : 0 ≤ (Fintype.card ι : ℝ) := by positivity
    exact inv_nonneg.mpr hnR
  · simp

/-- The harmonic projection has trace one: exactly one effective class survives. -/
theorem trace_simplexEffectiveHarmonicProjection [Nonempty ι] :
    (simplexEffectiveHarmonicProjection (ι := ι)).trace = 1 := by
  change (∑ _ : ι, ((Fintype.card ι : ℂ))⁻¹) = 1
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_inv_cancel₀ hn

/-- The distinguished effective section is fixed by the harmonic projection. -/
theorem simplexEffectiveHarmonicProjection_mulVec_section [Nonempty ι] :
    simplexEffectiveHarmonicProjection (ι := ι) *ᵥ simplexEffectiveSection =
      simplexEffectiveSection := by
  ext i
  simp only [Matrix.mulVec, dotProduct, simplexEffectiveHarmonicProjection,
    simplexEffectiveSection]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul, mul_one]
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_inv_cancel₀ hn

/-- The harmonic range is exactly the one-dimensional constant-section line. -/
theorem simplexEffectiveHarmonicProjection_mulVec_eq_self_iff
    [Nonempty ι] (x : ι → ℂ) :
    simplexEffectiveHarmonicProjection (ι := ι) *ᵥ x = x ↔
      ∃ c : ℂ, x = fun _ => c := by
  constructor
  · intro hx
    let c : ℂ := ((Fintype.card ι : ℂ))⁻¹ * ∑ j, x j
    refine ⟨c, funext fun i => ?_⟩
    have hi := congrFun hx i
    simpa only [Matrix.mulVec, dotProduct, simplexEffectiveHarmonicProjection,
      ← Finset.mul_sum, c] using hi.symm
  · rintro ⟨c, rfl⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, simplexEffectiveHarmonicProjection]
    rw [Finset.sum_const]
    simp only [Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

end EffectiveLine

section HodgeGreen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degree-zero full-simplex Hodge Laplacian `n I - J`. -/
def simplexZeroLaplacian : Matrix ι ι ℂ :=
  (Fintype.card ι : ℂ) • (1 : Matrix ι ι ℂ) - simplexAllOnes

/-- The Green operator on the complement of the constant harmonic line. -/
def simplexZeroGreen : Matrix ι ι ℂ :=
  ((Fintype.card ι : ℂ))⁻¹ •
    (1 - simplexEffectiveHarmonicProjection)

/-- The complement of the effective harmonic line is positive semidefinite. -/
theorem one_sub_simplexEffectiveHarmonicProjection_posSemidef [Nonempty ι] :
    (1 - simplexEffectiveHarmonicProjection (ι := ι)).PosSemidef := by
  let P := simplexEffectiveHarmonicProjection (ι := ι)
  have hP : P * P = P := simplexEffectiveHarmonicProjection_sq
  have hPstar : Pᴴ = P :=
    simplexEffectiveHarmonicProjection_isHermitian.eq
  have heq : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar]
    noncomm_ring [hP]
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

/-- The zero-form Laplacian is the simplex cardinality times the harmonic complement. -/
theorem simplexZeroLaplacian_eq_card_smul_one_sub_projection [Nonempty ι] :
    simplexZeroLaplacian (ι := ι) =
      (Fintype.card ι : ℂ) •
        (1 - simplexEffectiveHarmonicProjection) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext i j
  by_cases hij : i = j
  · subst j
    simp [simplexZeroLaplacian, simplexAllOnes,
      simplexEffectiveHarmonicProjection]
    field_simp
  · simp [simplexZeroLaplacian, simplexAllOnes,
      simplexEffectiveHarmonicProjection, hij]

/-- The explicit Green operator solves the left Hodge equation. -/
theorem simplexZeroLaplacian_mul_green [Nonempty ι] :
    simplexZeroLaplacian (ι := ι) * simplexZeroGreen =
      1 - simplexEffectiveHarmonicProjection := by
  let P := simplexEffectiveHarmonicProjection (ι := ι)
  have hP : P * P = P := simplexEffectiveHarmonicProjection_sq
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [simplexZeroLaplacian_eq_card_smul_one_sub_projection]
  change ((Fintype.card ι : ℂ) • (1 - P)) *
      (((Fintype.card ι : ℂ))⁻¹ • (1 - P)) = 1 - P
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP]
  rw [hcomp, mul_inv_cancel₀ hn, one_smul]

/-- The same explicit Green operator solves the right Hodge equation. -/
theorem simplexZeroGreen_mul_laplacian [Nonempty ι] :
    simplexZeroGreen (ι := ι) * simplexZeroLaplacian =
      1 - simplexEffectiveHarmonicProjection := by
  let P := simplexEffectiveHarmonicProjection (ι := ι)
  have hP : P * P = P := simplexEffectiveHarmonicProjection_sq
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [simplexZeroLaplacian_eq_card_smul_one_sub_projection]
  change (((Fintype.card ι : ℂ))⁻¹ • (1 - P)) *
      ((Fintype.card ι : ℂ) • (1 - P)) = 1 - P
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP]
  rw [hcomp, inv_mul_cancel₀ hn, one_smul]

/-- The degree-zero simplex Laplacian is positive semidefinite. -/
theorem simplexZeroLaplacian_posSemidef [Nonempty ι] :
    (simplexZeroLaplacian (ι := ι)).PosSemidef := by
  rw [simplexZeroLaplacian_eq_card_smul_one_sub_projection]
  apply one_sub_simplexEffectiveHarmonicProjection_posSemidef.smul
  apply Complex.nonneg_iff.mpr
  simp

/-- The Green operator on the harmonic complement is positive semidefinite. -/
theorem simplexZeroGreen_posSemidef [Nonempty ι] :
    (simplexZeroGreen (ι := ι)).PosSemidef := by
  unfold simplexZeroGreen
  apply one_sub_simplexEffectiveHarmonicProjection_posSemidef.smul
  have hcast : ((Fintype.card ι : ℂ))⁻¹ =
      ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.nonneg_iff]
  constructor
  · have hnR : 0 ≤ (Fintype.card ι : ℝ) := by positivity
    exact inv_nonneg.mpr hnR
  · simp

/-- The effective constant section is harmonic. -/
theorem simplexZeroLaplacian_mulVec_section [Nonempty ι] :
    simplexZeroLaplacian (ι := ι) *ᵥ simplexEffectiveSection = 0 := by
  rw [simplexZeroLaplacian_eq_card_smul_one_sub_projection]
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    simplexEffectiveHarmonicProjection_mulVec_section, sub_self, smul_zero]

/-- The surviving degree-zero harmonic line has positive parity. -/
theorem simplexEffectiveHarmonicProjection_positiveParity [Nonempty ι] :
    (1 : Matrix ι ι ℂ) * simplexEffectiveHarmonicProjection =
      simplexEffectiveHarmonicProjection := by
  rw [Matrix.one_mul]

end HodgeGreen

end

end HTGeometry
