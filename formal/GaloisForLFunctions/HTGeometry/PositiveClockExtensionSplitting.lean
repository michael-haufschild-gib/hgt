import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Positive-clock extension splitting: first versus powered defect

For diagonal clocks `A = diag(a_i)` on `ℂ^r`, `B = diag(b_j)` on `ℂ^s` and a coupling `K`, the
extension clock `D = [[A, K], [0, B]]` has cube `[[A³, K₃], [0, B³]]` with
`K₃ = A²K + AKB + KB²`.  A lift `F_H(x) = (Hx, x)` has first defect `K + AH - HB` and powered
defect `K₃ + A³H - HB³`, and entrywise

`(K₃ + A³H - HB³)_{ij} = m_{ij} (K + AH - HB)_{ij}`,  `m_{ij} = a_i² + a_i b_j + b_j²`.

For positive clocks `m_{ij} > 0`, so both defects vanish for exactly the same lifts, the Schur map
`Y ↦ (m_{ij} Y_{ij})` is invertible, carries the first coboundary range onto the powered one and
`K` to `K₃`, and induces an isomorphism of cokernels.  A complex cube root of unity makes
`m_{ij} = 0` and breaks the equivalence.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r s : ℕ}

/-- The extension clock `D = [[A, K], [0, B]]`. -/
def extensionClock (A : Matrix (Fin r) (Fin r) ℂ) (K : Matrix (Fin r) (Fin s) ℂ)
    (B : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
  fromBlocks A K 0 B

/-- The lift `F_H(x) = (Hx, x)`. -/
def extensionLift (H : Matrix (Fin r) (Fin s) ℂ) : Matrix (Fin r ⊕ Fin s) (Fin s) ℂ :=
  fromRows H 1

/-- The powered-clock coupling `K₃ = A²K + AKB + KB²`. -/
def cubeCoupling (A : Matrix (Fin r) (Fin r) ℂ) (K : Matrix (Fin r) (Fin s) ℂ)
    (B : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin r) (Fin s) ℂ :=
  A ^ 2 * K + A * K * B + K * B ^ 2

/-- The cube of the extension clock is the extension of the cubed clocks by `K₃`. -/
theorem extensionClock_pow_three (A : Matrix (Fin r) (Fin r) ℂ) (K : Matrix (Fin r) (Fin s) ℂ)
    (B : Matrix (Fin s) (Fin s) ℂ) :
    extensionClock A K B ^ 3 = extensionClock (A ^ 3) (cubeCoupling A K B) (B ^ 3) := by
  simp only [extensionClock, cubeCoupling, pow_succ, pow_zero, Matrix.one_mul,
    fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.add_mul, Matrix.mul_assoc]
  congr 1
  abel

/-- First extension defect of a lift: `D F_H - F_H B = (K + AH - HB, 0)`. -/
theorem extensionClock_lift_defect (A : Matrix (Fin r) (Fin r) ℂ) (K : Matrix (Fin r) (Fin s) ℂ)
    (B : Matrix (Fin s) (Fin s) ℂ) (H : Matrix (Fin r) (Fin s) ℂ) :
    extensionClock A K B * extensionLift H - extensionLift H * B =
      fromRows (K + A * H - H * B) 0 := by
  simp only [extensionClock, extensionLift, fromBlocks_mul_fromRows, fromRows_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, zero_add]
  ext (i | i) j
  · simp only [fromRows_apply_inl, Matrix.sub_apply, Matrix.add_apply]
    ring
  · simp [fromRows_apply_inr]

/-- Powered extension defect of a lift: `D³ F_H - F_H B³ = (K₃ + A³H - HB³, 0)`. -/
theorem extensionClock_cube_lift_defect (A : Matrix (Fin r) (Fin r) ℂ)
    (K : Matrix (Fin r) (Fin s) ℂ) (B : Matrix (Fin s) (Fin s) ℂ) (H : Matrix (Fin r) (Fin s) ℂ) :
    extensionClock A K B ^ 3 * extensionLift H - extensionLift H * B ^ 3 =
      fromRows (cubeCoupling A K B + A ^ 3 * H - H * B ^ 3) 0 := by
  rw [extensionClock_pow_three, extensionClock_lift_defect]

/-- The first extension defect of the zero lift `F_0` is `K`; its powered defect is `K₃`. -/
theorem extensionClock_zero_lift_defects (A : Matrix (Fin r) (Fin r) ℂ)
    (K : Matrix (Fin r) (Fin s) ℂ) (B : Matrix (Fin s) (Fin s) ℂ) :
    extensionClock A K B * extensionLift 0 - extensionLift 0 * B = fromRows K 0 ∧
      extensionClock A K B ^ 3 * extensionLift 0 - extensionLift 0 * B ^ 3 =
        fromRows (cubeCoupling A K B) 0 := by
  rw [extensionClock_lift_defect, extensionClock_cube_lift_defect]
  simp

/-- The clock multiplier `m(x, y) = x² + x y + y²`. -/
def clockCubeMultiplier (x y : ℂ) : ℂ := x ^ 2 + x * y + y ^ 2

theorem cube_sub_cube_eq_multiplier (x y : ℂ) :
    x ^ 3 - y ^ 3 = (x - y) * clockCubeMultiplier x y := by
  unfold clockCubeMultiplier; ring

/-- **(4)** Entrywise, the powered defect is the multiplier times the first defect. -/
theorem cubeDefect_entry (a : Fin r → ℂ) (b : Fin s → ℂ) (K H : Matrix (Fin r) (Fin s) ℂ)
    (i : Fin r) (j : Fin s) :
    (cubeCoupling (diagonal a) K (diagonal b) + diagonal a ^ 3 * H - H * diagonal b ^ 3 :
        Matrix (Fin r) (Fin s) ℂ) i j =
      clockCubeMultiplier (a i) (b j) *
        (K + diagonal a * H - H * diagonal b : Matrix (Fin r) (Fin s) ℂ) i j := by
  simp only [cubeCoupling, diagonal_pow, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_assoc,
    diagonal_mul, mul_diagonal, Pi.pow_apply, clockCubeMultiplier]
  ring

/-- Positive clocks have strictly positive, hence nonzero, multipliers (including resonance
`a_i = b_j`, where the multiplier is `3 a_i²`). -/
theorem clockCubeMultiplier_ne_zero {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    clockCubeMultiplier x y ≠ 0 := by
  unfold clockCubeMultiplier
  have : (0 : ℝ) < x ^ 2 + x * y + y ^ 2 := by positivity
  exact_mod_cast this.ne'

theorem clockCubeMultiplier_self (x : ℂ) : clockCubeMultiplier x x = 3 * x ^ 2 := by
  unfold clockCubeMultiplier; ring

/-- **Same splitting lifts.**  For positive clocks the first and the powered defect of a lift
vanish for exactly the same `H`. -/
theorem cubeDefect_eq_zero_iff {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (K H : Matrix (Fin r) (Fin s) ℂ) :
    cubeCoupling (diagonal fun i => (a i : ℂ)) K (diagonal fun j => (b j : ℂ)) +
        (diagonal fun i => (a i : ℂ)) ^ 3 * H - H * (diagonal fun j => (b j : ℂ)) ^ 3 = 0 ↔
      K + (diagonal fun i => (a i : ℂ)) * H - H * (diagonal fun j => (b j : ℂ)) = 0 := by
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [cubeDefect_entry] at this
    exact (mul_eq_zero.mp this).resolve_left (clockCubeMultiplier_ne_zero (ha i) (hb j))
  · intro h
    ext i j
    rw [cubeDefect_entry, h]
    simp

/-- The first coboundary `δ₁ H = AH - HB`. -/
def clockCoboundary (A : Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin s) (Fin s) ℂ) :
    Matrix (Fin r) (Fin s) ℂ →ₗ[ℂ] Matrix (Fin r) (Fin s) ℂ where
  toFun H := A * H - H * B
  map_add' H H' := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c H := by simp [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- The Schur multiplier map `Y ↦ (m_{ij} Y_{ij})` of positive clocks, as a linear equivalence. -/
def clockSchurEquiv {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    Matrix (Fin r) (Fin s) ℂ ≃ₗ[ℂ] Matrix (Fin r) (Fin s) ℂ where
  toFun Y := Matrix.of fun i j => clockCubeMultiplier (a i) (b j) * Y i j
  invFun Y := Matrix.of fun i j => Y i j / clockCubeMultiplier (a i) (b j)
  map_add' Y Y' := by ext i j; simp [mul_add]
  map_smul' c Y := by ext i j; simp; ring
  left_inv Y := by
    ext i j
    simp [mul_div_cancel_left₀ _ (clockCubeMultiplier_ne_zero (ha i) (hb j))]
  right_inv Y := by
    ext i j
    simp [mul_div_cancel₀ _ (clockCubeMultiplier_ne_zero (ha i) (hb j))]

theorem clockSchurEquiv_apply {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (Y : Matrix (Fin r) (Fin s) ℂ) (i : Fin r) (j : Fin s) :
    clockSchurEquiv ha hb Y i j = clockCubeMultiplier (a i) (b j) * Y i j := rfl

/-- The Schur map intertwines the first and the powered coboundary. -/
theorem clockSchurEquiv_comp_coboundary {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    (clockSchurEquiv ha hb : Matrix (Fin r) (Fin s) ℂ →ₗ[ℂ] _) ∘ₗ
        clockCoboundary (diagonal fun i => (a i : ℂ)) (diagonal fun j => (b j : ℂ)) =
      clockCoboundary ((diagonal fun i => (a i : ℂ)) ^ 3) ((diagonal fun j => (b j : ℂ)) ^ 3) := by
  apply LinearMap.ext
  intro H
  ext i j
  have h := cubeDefect_entry (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) 0 H i j
  simp only [cubeCoupling, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, clockSchurEquiv_apply,
    clockCoboundary, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h]

/-- The Schur map sends the extension class `K` to the powered class `K₃`. -/
theorem clockSchurEquiv_coupling {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (K : Matrix (Fin r) (Fin s) ℂ) :
    clockSchurEquiv ha hb K = cubeCoupling (diagonal fun i => (a i : ℂ)) K
      (diagonal fun j => (b j : ℂ)) := by
  ext i j
  have h := cubeDefect_entry (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) K 0 i j
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, sub_zero] at h
  rw [clockSchurEquiv_apply, ← h]

/-- The Schur map carries the first coboundary range onto the powered coboundary range. -/
theorem map_range_clockCoboundary {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    Submodule.map (clockSchurEquiv ha hb : Matrix (Fin r) (Fin s) ℂ →ₗ[ℂ] _)
        (LinearMap.range (clockCoboundary (diagonal fun i => (a i : ℂ))
          (diagonal fun j => (b j : ℂ)))) =
      LinearMap.range (clockCoboundary ((diagonal fun i => (a i : ℂ)) ^ 3)
        ((diagonal fun j => (b j : ℂ)) ^ 3)) := by
  rw [← LinearMap.range_comp, clockSchurEquiv_comp_coboundary]

/-- **Cokernel isomorphism** induced by the Schur map. -/
def clockCokernelEquiv {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    (Matrix (Fin r) (Fin s) ℂ ⧸ LinearMap.range (clockCoboundary (diagonal fun i => (a i : ℂ))
        (diagonal fun j => (b j : ℂ)))) ≃ₗ[ℂ]
      (Matrix (Fin r) (Fin s) ℂ ⧸ LinearMap.range (clockCoboundary
        ((diagonal fun i => (a i : ℂ)) ^ 3) ((diagonal fun j => (b j : ℂ)) ^ 3))) :=
  Submodule.Quotient.equiv _ _ (clockSchurEquiv ha hb) (map_range_clockCoboundary ha hb)

/-- The cokernel isomorphism sends the first extension class to the powered extension class. -/
theorem clockCokernelEquiv_mk {a : Fin r → ℝ} {b : Fin s → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (K : Matrix (Fin r) (Fin s) ℂ) :
    clockCokernelEquiv ha hb (Submodule.Quotient.mk K) =
      Submodule.Quotient.mk (cubeCoupling (diagonal fun i => (a i : ℂ)) K
        (diagonal fun j => (b j : ℂ))) := by
  rw [clockCokernelEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_coe, clockSchurEquiv_coupling]

/-- **Positivity cannot be omitted.**  For a primitive cube root of unity `ω`, the clocks
`A = (ω)`, `B = (1)` with `K = (1)`: the first defect vanishes for some lift while the powered
defect vanishes for every lift. -/
theorem cubeRoot_splitting_counterexample {ω : ℂ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (∃ H : Matrix (Fin 1) (Fin 1) ℂ,
        (1 : Matrix (Fin 1) (Fin 1) ℂ) + diagonal (fun _ => ω) * H - H * diagonal (fun _ => 1) = 0) ∧
      (∀ H : Matrix (Fin 1) (Fin 1) ℂ,
        cubeCoupling (diagonal fun _ => ω) 1 (diagonal fun _ => 1) +
          diagonal (fun _ => ω) ^ 3 * H - H * diagonal (fun _ => 1) ^ 3 = 0) ∧
      ¬ ((1 : Matrix (Fin 1) (Fin 1) ℂ) + diagonal (fun _ => ω) * 0 -
          0 * diagonal (fun _ => 1) = 0) := by
  have hm : clockCubeMultiplier ω 1 = 0 := by
    have h := cube_sub_cube_eq_multiplier ω 1
    rw [hω3, one_pow, sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr hω1)
  have hω1' : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  refine ⟨⟨of fun _ _ => (1 - ω)⁻¹, ?_⟩, fun H => ?_, ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp [diagonal_mul]
    have : (1 - ω) ≠ 0 := by rwa [← neg_sub, neg_ne_zero]
    field_simp
    ring
  · ext i j
    rw [cubeDefect_entry]
    fin_cases i; fin_cases j
    simp [hm]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this

end

end GaloisForLFunctions.HTGeometry
