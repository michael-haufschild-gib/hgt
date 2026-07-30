import GaloisForLFunctions.HTGeometry.NoOutsideQuadraticWitnessDescent
import GaloisForLFunctions.HTGeometry.EventSquarePolarization
import GaloisForLFunctions.HTGeometry.SourceOddPositivitySquareLaw
import Mathlib.Analysis.Matrix.Order

/-!
# Triangle-source Hermitian lift
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix MatrixOrder ComplexOrder

/-- Three-cycle on the two independent account coordinates. -/
def triangleAccountCycle (K : Type*) [Ring K] :
    Matrix (Fin 2) (Fin 2) K :=
  !![-1, -1; 1, 0]

/-- Source reflection on the two independent account coordinates. -/
def triangleAccountReflection (K : Type*) [Ring K] :
    Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Centered orientation-preserving source rotation. -/
def triangleAccountPhaseGenerator (K : Type*) [Ring K] :
    Matrix (Fin 2) (Fin 2) K :=
  2 • triangleAccountCycle K + 1

/-- Explicit centered rotation matrix. -/
theorem triangleAccountPhaseGenerator_eq
    (K : Type*) [Ring K] :
    triangleAccountPhaseGenerator K = !![-1, -2; 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountPhaseGenerator, triangleAccountCycle]
  all_goals norm_num

/-- Counting Gram matrix induced by `(x,y) ↦ (x,y,-x-y)`. -/
def triangleAccountCountingGram :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 2]

theorem triangleAccountCycle_cube
    (K : Type*) [Ring K] :
    triangleAccountCycle K ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountCycle, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem triangleAccountReflection_sq
    (K : Type*) [Ring K] :
    triangleAccountReflection K ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountReflection, pow_two, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem triangleAccountReflection_cycle_reflection
    (K : Type*) [Ring K] :
    triangleAccountReflection K * triangleAccountCycle K *
        triangleAccountReflection K =
      triangleAccountCycle K ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountReflection, triangleAccountCycle, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem triangleAccountPhaseGenerator_sq
    (K : Type*) [CommRing K] :
    triangleAccountPhaseGenerator K ^ 2 =
      (-3 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountPhaseGenerator_eq, pow_two, smul_eq_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem triangleAccountReflection_phase_reflection
    (K : Type*) [Ring K] :
    triangleAccountReflection K * triangleAccountPhaseGenerator K *
        triangleAccountReflection K =
      -triangleAccountPhaseGenerator K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountReflection, triangleAccountPhaseGenerator_eq,
      Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Source phase scalar represented without choosing a sign of the imaginary direction. -/
def triangleAccountPhaseScalar
    {K : Type*} [Ring K] (a b : K) :
    Matrix (Fin 2) (Fin 2) K :=
  a • 1 + b • triangleAccountPhaseGenerator K

/-- Explicit matrix of a generated phase scalar. -/
theorem triangleAccountPhaseScalar_eq
    {K : Type*} [CommRing K] (a b : K) :
    triangleAccountPhaseScalar a b =
      !![a - b, -(2 * b); 2 * b, a + b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountPhaseScalar, triangleAccountPhaseGenerator_eq]
  all_goals ring

/-- Odd source relabeling acts as conjugation on the generated phase algebra. -/
theorem triangleAccountReflection_phaseScalar_reflection
    {K : Type*} [CommRing K] (a b : K) :
    triangleAccountReflection K * triangleAccountPhaseScalar a b *
        triangleAccountReflection K =
      triangleAccountPhaseScalar a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountReflection, triangleAccountPhaseScalar_eq,
      Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals ring

theorem triangleAccountPhaseScalar_mul
    {K : Type*} [CommRing K] (a b c d : K) :
    triangleAccountPhaseScalar a b * triangleAccountPhaseScalar c d =
      triangleAccountPhaseScalar (a * c - 3 * b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleAccountPhaseScalar, triangleAccountPhaseGenerator,
      triangleAccountCycle, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem commutes_triangleAccountCycle_iff
    {K : Type*} [Field K] [CharZero K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    A * triangleAccountCycle K = triangleAccountCycle K * A ↔
      ∃ a b : K, A = triangleAccountPhaseScalar a b := by
  constructor
  · intro h
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
    have hr : A 1 0 = -A 0 1 := by
      simp [triangleAccountCycle, Matrix.mul_apply, Fin.sum_univ_two] at h00
      linear_combination h00
    have hs : A 1 1 = A 0 0 - A 0 1 := by
      simp [triangleAccountCycle, Matrix.mul_apply, Fin.sum_univ_two] at h01
      linear_combination h01
    refine ⟨A 0 0 - A 0 1 / 2, -A 0 1 / 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triangleAccountPhaseScalar, triangleAccountPhaseGenerator_eq,
        hr, hs] <;>
      ring
  · rintro ⟨a, b, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triangleAccountPhaseScalar, triangleAccountPhaseGenerator,
        triangleAccountCycle, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

theorem commutes_triangleAccountCycle_reflection_iff
    {K : Type*} [Field K] [CharZero K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    (A * triangleAccountCycle K = triangleAccountCycle K * A ∧
      A * triangleAccountReflection K = triangleAccountReflection K * A) ↔
      ∃ a : K, A = a • 1 := by
  constructor
  · rintro ⟨hR, hT⟩
    rcases (commutes_triangleAccountCycle_iff A).mp hR with ⟨a, b, rfl⟩
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hT
    have hb : b = 0 := by
      simpa [triangleAccountPhaseScalar, triangleAccountPhaseGenerator,
        triangleAccountCycle, triangleAccountReflection, Matrix.mul_apply,
        Fin.sum_univ_two] using h01
    refine ⟨a, ?_⟩
    simp [triangleAccountPhaseScalar, hb]
  · rintro ⟨a, rfl⟩
    constructor <;>
      simp

/-- Full unlabeled-source symmetry has no nontrivial invariant projector on the account doublet. -/
theorem triangleAccount_sourceInvariant_idempotent_eq_zero_or_one
    {K : Type*} [Field K] [CharZero K]
    (P : Matrix (Fin 2) (Fin 2) K)
    (hR : P * triangleAccountCycle K = triangleAccountCycle K * P)
    (hT : P * triangleAccountReflection K = triangleAccountReflection K * P)
    (hP : P * P = P) :
    P = 0 ∨ P = 1 := by
  rcases (commutes_triangleAccountCycle_reflection_iff P).mp ⟨hR, hT⟩ with
    ⟨a, rfl⟩
  have ha : a * a = a := by
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hP
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
  have hz : a = 0 ∨ a = 1 := by
    have hfactor : a * (a - 1) = 0 := by
      linear_combination ha
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  rcases hz with rfl | rfl
  · simp
  · simp

theorem triangleAccountCountingGram_cycle_invariant :
    (triangleAccountCycle ℝ)ᵀ * triangleAccountCountingGram *
        triangleAccountCycle ℝ =
      triangleAccountCountingGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleAccountCycle, triangleAccountCountingGram,
      Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two]

theorem triangleAccountCountingGram_reflection_invariant :
    (triangleAccountReflection ℝ)ᵀ * triangleAccountCountingGram *
        triangleAccountReflection ℝ =
      triangleAccountCountingGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleAccountReflection, triangleAccountCountingGram,
      Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two]

theorem triangleAccountPhaseGenerator_counting_skew :
    (triangleAccountPhaseGenerator ℝ)ᵀ * triangleAccountCountingGram =
      -(triangleAccountCountingGram * triangleAccountPhaseGenerator ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleAccountPhaseGenerator_eq,
      triangleAccountCountingGram, Matrix.mul_apply, Matrix.vecMul,
      Fin.sum_univ_two]

theorem triangleAccountCountingGram_posDef :
    triangleAccountCountingGram.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [triangleAccountCountingGram, Matrix.IsHermitian]
  · intro x hx
    have hcoord : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h]
    have henergy :
        star x ⬝ᵥ (triangleAccountCountingGram *ᵥ x) =
          2 * x 0 ^ 2 + 2 * x 0 * x 1 + 2 * x 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, triangleAccountCountingGram,
        Fin.sum_univ_two]
      ring
    rw [henergy]
    rcases hcoord with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0]
    · nlinarith [sq_pos_of_ne_zero h1]

theorem triangleAccount_invariant_symmetricForm_eq_smul_countingGram
    (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hsymm : Hᵀ = H)
    (hR : (triangleAccountCycle ℝ)ᵀ * H * triangleAccountCycle ℝ = H)
    (hT : (triangleAccountReflection ℝ)ᵀ * H *
      triangleAccountReflection ℝ = H) :
    H = (H 0 1) • triangleAccountCountingGram := by
  have hsymm01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hsymm
  have hT00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hT
  have hR00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hR
  have hs : H 1 0 = H 0 1 := by
    simpa using hsymm01
  have ht : H 1 1 = H 0 0 := by
    simpa [triangleAccountReflection, Matrix.mul_apply, Matrix.vecMul,
      Fin.sum_univ_two] using hT00
  have hr : H 1 1 = H 1 0 + H 0 1 := by
    simp [triangleAccountCycle, Matrix.mul_apply,
      Fin.sum_univ_two] at hR00
    linear_combination hR00
  have hp : H 0 0 = 2 * H 0 1 := by
    rw [← ht, hr, hs]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [triangleAccountCountingGram, hp]
    ring
  · simp [triangleAccountCountingGram]
  · simp [triangleAccountCountingGram, hs]
  · simp [triangleAccountCountingGram, ht, hp]
    ring

/-- Positive full-source invariant account metrics form exactly one positive ray. -/
theorem triangleAccount_invariant_posDef_eq_pos_smul_countingGram
    (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hpos : H.PosDef)
    (hR : (triangleAccountCycle ℝ)ᵀ * H * triangleAccountCycle ℝ = H)
    (hT : (triangleAccountReflection ℝ)ᵀ * H *
      triangleAccountReflection ℝ = H) :
    ∃ c : ℝ, 0 < c ∧ H = c • triangleAccountCountingGram := by
  have hEq := triangleAccount_invariant_symmetricForm_eq_smul_countingGram
    H hpos.isHermitian hR hT
  refine ⟨H 0 1, ?_, hEq⟩
  have hx : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num at h0
  have hp := hpos.dotProduct_mulVec_pos hx
  rw [hEq] at hp
  simp [dotProduct, Matrix.mulVec, triangleAccountCountingGram,
    Fin.sum_univ_two] at hp
  linarith

theorem triangleAccountPhaseScalar_star_mul_self
    (a b : ℝ) :
    triangleAccountPhaseScalar a (-b) *
        triangleAccountPhaseScalar a b =
      (a ^ 2 + 3 * b ^ 2) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [triangleAccountPhaseScalar_mul]
  ring_nf
  simp [triangleAccountPhaseScalar]

theorem triangleAccountPhaseScalar_norm_pos
    {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 + 3 * b ^ 2 := by
  rcases h with ha | hb
  · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
  · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]

/-! ### Free complex exact lift and Hermitian public record -/

/-- Complex deformation carrier of the `3 → 2` triangle comparison interface. -/
abbrev TriangleWitnessEvent :=
  Matrix (Fin 3) (Fin 2) ℂ

/-- Positive Hermitian public record of a triangle witness deformation. -/
def triangleWitnessGram (X : TriangleWitnessEvent) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Xᴴ * X

/-- Complex scalar extension preserves exactness at the edge layer. -/
theorem triangleComplexEdgeBoundary_eq_zero_iff
    (x : Fin 3 → ℂ) :
    triangleEdgeBoundary x = 0 ↔
      ∃ a : ℂ, x = triangleFillerBoundary ℂ a :=
  triangleEdgeBoundary_eq_zero_iff x

/-- Complex scalar extension preserves exactness at the account layer. -/
theorem triangleComplexVertexAugmentation_eq_zero_iff
    (v : Fin 3 → ℂ) :
    triangleVertexAugmentation v = 0 ↔
      ∃ x : Fin 3 → ℂ, triangleEdgeBoundary x = v :=
  triangleVertexAugmentation_eq_zero_iff v

/-- Every source-completed triangle event has a positive-semidefinite Hermitian public record. -/
theorem triangleWitnessGram_posSemidef (X : TriangleWitnessEvent) :
    (triangleWitnessGram X).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self X

end

end GaloisForLFunctions.HTGeometry
