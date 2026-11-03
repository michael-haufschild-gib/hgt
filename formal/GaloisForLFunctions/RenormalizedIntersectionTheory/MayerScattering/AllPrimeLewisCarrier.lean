import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckePositiveWordReduction
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWordHarmonicTransport
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.BoundaryRestorationCarrier

/-!
# Positive-determinant Hecke transport of the complete Lewis carrier

Finite positive-word partitions transport the three-term equation through the actual
Hecke cones. Reversal of each basis preserves modular inversion.
-/

set_option autoImplicit false
noncomputable section
open Complex Set
open GaloisForLFunctions RenormalizedIntersectionTheory MayerScatteringCore MayerCoding

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


/-- Homogeneous two-variable form of the physical Lewis period. -/
def lewisHomogeneousValue (s : ℂ) (g : ℝ → ℂ) (x y : ℝ) : ℂ :=
  (y : ℂ) ^ (-(2 * s)) * g (x / y)

/-- Apply a nonnegative integral matrix before evaluating the homogeneous period. -/
def lewisMatrixValue (s : ℂ) (g : ℝ → ℂ) (x y : ℝ) (A : NatMatrix) : ℂ :=
  lewisHomogeneousValue s g ((A 0 0 : ℝ) * x + (A 0 1 : ℝ) * y)
    ((A 1 0 : ℝ) * x + (A 1 1 : ℝ) * y)

/-- Positive scaling gives the exact homogeneous weight of the Lewis period. -/
theorem lewisHomogeneousValue_scale (s : ℂ) (g : ℝ → ℂ)
    {c x y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    lewisHomogeneousValue s g (c * x) (c * y) =
      (c : ℂ) ^ (-(2 * s)) * lewisHomogeneousValue s g x y := by
  unfold lewisHomogeneousValue
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hy.le]
  rw [mul_div_mul_left _ _ hc.ne', mul_assoc]

/-- The physical three-term equation is exactly binary splitting in homogeneous coordinates. -/
theorem lewisHomogeneousValue_farey (s : ℂ) (g : ℝ → ℂ)
    (hg : ∀ a : ℝ, 0 < a → lewisFarey s g a = g a)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    lewisHomogeneousValue s g x y =
      lewisHomogeneousValue s g (x + y) y + lewisHomogeneousValue s g x (x + y) := by
  have h := congrArg (fun z : ℂ => (y : ℂ) ^ (-(2 * s)) * z) (hg (x / y) (div_pos hx hy))
  have h1 : x / y + 1 = (x + y) / y := by field_simp [hy.ne']
  have h2 : (x / y) / (x / y + 1) = x / (x + y) := by
    rw [h1]
    field_simp [hy.ne', (add_pos hx hy).ne']
  have h3 : y * (x / y + 1) = x + y := by field_simp [hy.ne']
  have hp : (y : ℂ) ^ (-(2 * s)) * ((x / y + 1 : ℝ) : ℂ) ^ (-(2 * s)) =
      ((x + y : ℝ) : ℂ) ^ (-(2 * s)) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hy.le (by positivity), ← Complex.ofReal_mul, h3]
  simp only [lewisFarey, lewisShift, lewisParabolic, mul_add, ← mul_assoc] at h
  rw [hp, h2, h1] at h
  exact h.symm

private theorem lewisMatrixValue_left_true (s : ℂ) (g : ℝ → ℂ) (x y : ℝ) (A : NatMatrix) :
    lewisMatrixValue s g x y (generator true * A) =
      lewisHomogeneousValue s g
        (((A 0 0 : ℝ) * x + (A 0 1 : ℝ) * y) + ((A 1 0 : ℝ) * x + (A 1 1 : ℝ) * y))
        ((A 1 0 : ℝ) * x + (A 1 1 : ℝ) * y) := by
  unfold lewisMatrixValue
  congr 1
  · simp [generator, Matrix.mul_apply, Fin.sum_univ_two, add_mul]
    ring
  · simp [generator, Matrix.mul_apply, Fin.sum_univ_two]

private theorem lewisMatrixValue_left_false (s : ℂ) (g : ℝ → ℂ) (x y : ℝ) (A : NatMatrix) :
    lewisMatrixValue s g x y (generator false * A) =
      lewisHomogeneousValue s g ((A 0 0 : ℝ) * x + (A 0 1 : ℝ) * y)
        (((A 0 0 : ℝ) * x + (A 0 1 : ℝ) * y) + ((A 1 0 : ℝ) * x + (A 1 1 : ℝ) * y)) := by
  unfold lewisMatrixValue
  congr 1
  · simp [generator, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [generator, Matrix.mul_apply, Fin.sum_univ_two, add_mul]
    ring

private theorem lewisMatrixValue_right_true (s : ℂ) (g : ℝ → ℂ) (x y : ℝ) (A : NatMatrix) :
    lewisMatrixValue s g x y (A * generator true) = lewisMatrixValue s g (x + y) y A := by
  unfold lewisMatrixValue
  congr 1 <;> simp [generator, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add] <;> ring

private theorem lewisMatrixValue_right_false (s : ℂ) (g : ℝ → ℂ) (x y : ℝ) (A : NatMatrix) :
    lewisMatrixValue s g x y (A * generator false) = lewisMatrixValue s g x (x + y) A := by
  unfold lewisMatrixValue
  congr 1 <;> simp [generator, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add] <;> ring

private theorem positive_matrix_coordinates {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < (A 0 0 : ℝ) * x + (A 0 1 : ℝ) * y ∧
      0 < (A 1 0 : ℝ) * x + (A 1 1 : ℝ) * y := by
  have ha : 0 < A 0 0 := by
    by_contra h
    have hz : A 0 0 = 0 := by omega
    simp only [HasHeckeDeterminant, hz, zero_mul] at hA
    omega
  have hd : 0 < A 1 1 := by
    by_contra h
    have hz : A 1 1 = 0 := by omega
    simp only [HasHeckeDeterminant, hz, mul_zero] at hA
    omega
  have haR : (0 : ℝ) < A 0 0 := by exact_mod_cast ha
  have hdR : (0 : ℝ) < A 1 1 := by exact_mod_cast hd
  constructor <;> positivity

/-- The actual one-variable source operator equals the finite homogeneous matrix sum. -/
theorem lewisHeckeOperator_eq_matrixSum (n : ℕ) (s : ℂ) (g : ℝ → ℂ) (a : ℝ) :
    lewisHeckeOperator n s g a = ∑ A ∈ naturalHeckeSet n, lewisMatrixValue s g a 1 A := by
  classical
  rw [naturalHeckeSet, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro M hM
    have he := heckeMatrixTuple_natMatrix hM
    have h00 : ((heckeNatMatrix M) 0 0 : ℝ) = (M.1 : ℝ) := by
      exact_mod_cast congrArg (fun T : ℤ × ℤ × ℤ × ℤ => T.1) he
    have h01 : ((heckeNatMatrix M) 0 1 : ℝ) = (M.2.1 : ℝ) := by
      exact_mod_cast congrArg (fun T : ℤ × ℤ × ℤ × ℤ => T.2.1) he
    have h10 : ((heckeNatMatrix M) 1 0 : ℝ) = (M.2.2.1 : ℝ) := by
      exact_mod_cast congrArg (fun T : ℤ × ℤ × ℤ × ℤ => T.2.2.1) he
    have h11 : ((heckeNatMatrix M) 1 1 : ℝ) = (M.2.2.2 : ℝ) := by
      exact_mod_cast congrArg (fun T : ℤ × ℤ × ℤ × ℤ => T.2.2.2) he
    simp only [lewisMatrixValue, lewisHomogeneousValue, h00, h01, h10, h11, mul_one]
  · intro M hM N hN he
    have h := congrArg heckeMatrixTuple he
    simpa only [heckeMatrixTuple_natMatrix hM, heckeMatrixTuple_natMatrix hN] using h

#print axioms lewisHeckeOperator_eq_matrixSum


private theorem lewisMatrixValue_scale {n : ℕ} (hn : 0 < n) (s : ℂ) (g : ℝ → ℂ)
    {A : NatMatrix} (hA : HasHeckeDeterminant n A) {c x y : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    lewisMatrixValue s g (c * x) (c * y) A =
      (c : ℂ) ^ (-(2 * s)) * lewisMatrixValue s g x y A := by
  have hp := positive_matrix_coordinates hn hA hx hy
  have h0 : (A 0 0 : ℝ) * (c * x) + (A 0 1 : ℝ) * (c * y) =
      c * ((A 0 0 : ℝ) * x + (A 0 1 : ℝ) * y) := by ring
  have h1 : (A 1 0 : ℝ) * (c * x) + (A 1 1 : ℝ) * (c * y) =
      c * ((A 1 0 : ℝ) * x + (A 1 1 : ℝ) * y) := by ring
  unfold lewisMatrixValue
  rw [h0, h1, lewisHomogeneousValue_scale s g hc hp.2]

/-- Every positive-determinant source Hecke correspondence preserves the Lewis
three-term equation on the full positive line. No eigenfunction equation is assumed. -/
theorem lewisFarey_heckeOperator_of_fixed {n : ℕ} (hn : 0 < n) (s : ℂ) (g : ℝ → ℂ)
    (hg : ∀ a : ℝ, 0 < a → lewisFarey s g a = g a) {a : ℝ} (ha : 0 < a) :
    lewisFarey s (lewisHeckeOperator n s g) a = lewisHeckeOperator n s g a := by
  classical
  let H : NatMatrix → ℂ := lewisMatrixValue s g a 1
  have hH : ∀ A, HasHeckeDeterminant n A →
      H A = H (generator true * A) + H (generator false * A) := by
    intro A hA
    have hp := positive_matrix_coordinates hn hA ha one_pos
    dsimp only [H]
    rw [lewisMatrixValue_left_true, lewisMatrixValue_left_false]
    exact lewisHomogeneousValue_farey s g hg hp.1 hp.2
  have hsum := hecke_sum_right_harmonic hn H hH
  have hc : 0 < a + 1 := by positivity
  have hr : ∀ A ∈ naturalHeckeSet n,
      lewisMatrixValue s g a 1 (A * generator false) =
        ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * lewisMatrixValue s g (a / (a + 1)) 1 A := by
    intro A hA
    rw [lewisMatrixValue_right_false]
    have hs := lewisMatrixValue_scale hn s g (mem_naturalHeckeSet_iff.mp hA).1
      hc (div_pos ha hc) one_pos
    simpa only [mul_div_cancel₀ _ hc.ne', mul_one] using hs
  simp only [lewisFarey, lewisShift, lewisParabolic]
  rw [lewisHeckeOperator_eq_matrixSum, lewisHeckeOperator_eq_matrixSum,
    lewisHeckeOperator_eq_matrixSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ A ∈ naturalHeckeSet n,
        (lewisMatrixValue s g (a + 1) 1 A +
          ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * lewisMatrixValue s g (a / (a + 1)) 1 A)) =
        ∑ A ∈ naturalHeckeSet n, (H (A * generator true) + H (A * generator false)) := by
      apply Finset.sum_congr rfl
      intro A hA
      dsimp only [H]
      rw [lewisMatrixValue_right_true, hr A hA]
    _ = ∑ A ∈ naturalHeckeSet n, lewisMatrixValue s g a 1 A := hsum

#print axioms lewisFarey_heckeOperator_of_fixed


private theorem lewisHomogeneousValue_symmetric (s : ℂ) (g : ℝ → ℂ)
    (hg : ∀ a : ℝ, 0 < a → lewisModularInversion s g a = g a)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    lewisHomogeneousValue s g x y = lewisHomogeneousValue s g y x := by
  have h := congrArg (fun z : ℂ => (y : ℂ) ^ (-(2 * s)) * z) (hg (x / y) (div_pos hx hy))
  have hp : (y : ℂ) ^ (-(2 * s)) * ((x / y : ℝ) : ℂ) ^ (-(2 * s)) =
      (x : ℂ) ^ (-(2 * s)) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hy.le (div_pos hx hy).le, ← Complex.ofReal_mul,
      mul_div_cancel₀ _ hy.ne']
  simp only [lewisModularInversion, ← mul_assoc, hp, inv_div] at h
  exact h.symm

private def heckeReverseMatrix (A : NatMatrix) : NatMatrix :=
  !![A 1 1, A 1 0; A 0 1, A 0 0]

private theorem heckeReverseMatrix_involutive (A : NatMatrix) :
    heckeReverseMatrix (heckeReverseMatrix A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeReverseMatrix]

private theorem heckeReverseMatrix_mem {n : ℕ} {A : NatMatrix}
    (hA : A ∈ naturalHeckeSet n) : heckeReverseMatrix A ∈ naturalHeckeSet n := by
  have h := mem_naturalHeckeSet_iff.mp hA
  apply mem_naturalHeckeSet_iff.mpr
  constructor
  · change A 1 1 * A 0 0 = A 1 0 * A 0 1 + n
    simpa only [HasHeckeDeterminant, mul_comm] using h.1
  · change A 0 1 < A 1 1 ∧ A 1 0 < A 0 0
    exact ⟨h.2.2, h.2.1⟩

private theorem lewisMatrixValue_reverse (s : ℂ) (g : ℝ → ℂ) (a : ℝ) (A : NatMatrix) :
    lewisMatrixValue s g a 1 (heckeReverseMatrix A) =
      lewisHomogeneousValue s g ((A 1 0 : ℝ) * 1 + (A 1 1 : ℝ) * a)
        ((A 0 0 : ℝ) * 1 + (A 0 1 : ℝ) * a) := by
  unfold lewisMatrixValue
  change lewisHomogeneousValue s g ((A 1 1 : ℝ) * a + (A 1 0 : ℝ) * 1)
    ((A 0 1 : ℝ) * a + (A 0 0 : ℝ) * 1) = _
  congr 1 <;> ring

/-- The literal involution of the finite Hecke basis set preserves modular inversion. -/
theorem lewisModularInversion_heckeOperator_of_fixed {n : ℕ} (hn : 0 < n)
    (s : ℂ) (g : ℝ → ℂ)
    (hg : ∀ a : ℝ, 0 < a → lewisModularInversion s g a = g a)
    {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (lewisHeckeOperator n s g) a = lewisHeckeOperator n s g a := by
  classical
  simp only [lewisModularInversion, lewisHeckeOperator_eq_matrixSum, Finset.mul_sum]
  apply Finset.sum_bij (fun A _ => heckeReverseMatrix A)
  · intro A hA
    exact heckeReverseMatrix_mem hA
  · intro A hA B hB he
    have h := congrArg heckeReverseMatrix he
    simpa only [heckeReverseMatrix_involutive] using h
  · intro A hA
    exact ⟨heckeReverseMatrix A, heckeReverseMatrix_mem hA, heckeReverseMatrix_involutive A⟩
  · intro A hA
    have hdet := (mem_naturalHeckeSet_iff.mp hA).1
    have hs := lewisMatrixValue_scale hn s g hdet ha (inv_pos.mpr ha) one_pos
    have hp := positive_matrix_coordinates hn hdet one_pos ha
    calc
      (a : ℂ) ^ (-(2 * s)) * lewisMatrixValue s g a⁻¹ 1 A =
          lewisMatrixValue s g 1 a A := by
        simpa only [mul_inv_cancel₀ ha.ne', mul_one] using hs.symm
      _ = lewisMatrixValue s g a 1 (heckeReverseMatrix A) := by
        rw [lewisMatrixValue_reverse]
        exact lewisHomogeneousValue_symmetric s g hg hp.1 hp.2

/-- Every positive-determinant Hecke correspondence preserves the full completed
Lewis carrier, uniformly in the complex parameter. -/
theorem mayerCompletedLewisCarrier_heckeOperator {n : ℕ} (hn : 0 < n)
    {s : ℂ} {g : ℝ → ℂ} (hg : g ∈ mayerCompletedLewisCarrier s) :
    lewisHeckeOperator n s g ∈ mayerCompletedLewisCarrier s := by
  exact ⟨fun a ha => lewisModularInversion_heckeOperator_of_fixed hn s g hg.1 ha,
    fun a ha => lewisFarey_heckeOperator_of_fixed hn s g hg.2 ha⟩

#print axioms lewisModularInversion_heckeOperator_of_fixed
#print axioms mayerCompletedLewisCarrier_heckeOperator

#print axioms lewisHomogeneousValue_scale
#print axioms lewisHomogeneousValue_farey

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
