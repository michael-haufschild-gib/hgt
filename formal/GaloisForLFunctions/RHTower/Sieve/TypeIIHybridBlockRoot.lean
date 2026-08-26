import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridBlockPower

/-!
# Root-form hybrid Type II block estimate

The square estimate is split into its four nonnegative power contributions.  This preserves the
diagonal, hybrid derivative, reciprocal-correlation, and terminal diagonal terms separately for
the Vaughan parameter optimization.
-/

namespace RHTower.Sieve

noncomputable section

theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hsxy := Real.sq_sqrt hxy
  have hcross : 0 ≤ Real.sqrt x * Real.sqrt y :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  have hrhs : 0 ≤ Real.sqrt x + Real.sqrt y :=
    add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  have hlhs := Real.sqrt_nonneg (x + y)
  nlinarith

def typeIIHybridBlockComponents (T r : ℝ) (A B P : ℕ) : ℝ :=
  (B : ℝ) * P
    + 1000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B / ((A : ℝ) * P)
    + 20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B
    + (B : ℝ) ^ 2 / P

def typeIIHybridBlockRootEnvelope (T r : ℝ) (A B P : ℕ) : ℝ :=
  Real.sqrt ((B : ℝ) * P)
    + Real.sqrt (1000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B /
        ((A : ℝ) * P))
    + Real.sqrt (20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B)
    + Real.sqrt ((B : ℝ) ^ 2 / P)

theorem typeIIHybridBlockComponents_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (A B P : ℕ) : 0 ≤ typeIIHybridBlockComponents T r A B P := by
  rw [typeIIHybridBlockComponents]
  have := invSum_nonneg B
  positivity

theorem mul_add_typeIIHybridGapPowerEnvelope_eq_components {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B P : ℕ} (hA : 1 ≤ A) (hP : 1 ≤ P) :
    (B : ℝ) * ((P : ℝ) + typeIIHybridGapPowerEnvelope T r A B P) =
      typeIIHybridBlockComponents T r A B P := by
  have hTr0 : T * r ≠ 0 := mul_ne_zero hT.ne' hr.ne'
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hA)
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hP)
  rw [typeIIHybridGapPowerEnvelope, typeIIHybridBlockComponents]
  field_simp
  ring

theorem sqrt_typeIIHybridBlockComponents_le_rootEnvelope {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B P : ℕ} (hA : 1 ≤ A) (hP : 1 ≤ P) :
    Real.sqrt (typeIIHybridBlockComponents T r A B P) ≤
      typeIIHybridBlockRootEnvelope T r A B P := by
  let x₁ : ℝ := (B : ℝ) * P
  let x₂ : ℝ := 1000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B /
    ((A : ℝ) * P)
  let x₃ : ℝ := 20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B
  let x₄ : ℝ := (B : ℝ) ^ 2 / P
  have hx₁ : 0 ≤ x₁ := by dsimp [x₁]; positivity
  have hx₂ : 0 ≤ x₂ := by dsimp [x₂]; positivity
  have hx₃ : 0 ≤ x₃ := by
    dsimp [x₃]
    have := invSum_nonneg B
    positivity
  have hx₄ : 0 ≤ x₄ := by dsimp [x₄]; positivity
  have h12 := sqrt_add_le_add_sqrt hx₁ hx₂
  have h123 := sqrt_add_le_add_sqrt (add_nonneg hx₁ hx₂) hx₃
  have h1234 := sqrt_add_le_add_sqrt (add_nonneg (add_nonneg hx₁ hx₂) hx₃) hx₄
  rw [typeIIHybridBlockComponents, typeIIHybridBlockRootEnvelope]
  dsimp [x₁, x₂, x₃, x₄] at h12 h123 h1234
  linarith

/-- Closed norm estimate for one actual Vaughan block, split into its four root contributions. -/
theorem exists_norm_maskedBlockSum_le_hybrid_root :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ P → 2 ≤ Q →
      Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖
        ≤ Real.sqrt (8 * C * Real.log L * typeIIPolylogEnvelope B) *
          typeIIHybridBlockRootEnvelope T r A B P := by
  obtain ⟨C, hC0, hmain⟩ := exists_norm_maskedBlockSum_le_hybrid_power
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hP hQ hQ2P hQL h8
  have hbase := hmain (U := U) (V := V) hT hr hA hB hL hP hQ hQ2P hQL h8
  have hfact := mul_add_typeIIHybridGapPowerEnvelope_eq_components (B := B) hT hr hA hP
  have hK0 : 0 ≤ 8 * C * Real.log L * typeIIPolylogEnvelope B := by
    have hlog : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
    have hpoly := typeIIPolylogEnvelope_nonneg B
    positivity
  have hcomp0 := typeIIHybridBlockComponents_nonneg hT hr A B P
  have hroot := sqrt_typeIIHybridBlockComponents_le_rootEnvelope (B := B) hT hr hA hP
  calc
    ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
        (fun m => typeIIShort V m)‖
        ≤ Real.sqrt
          (8 * C * (B : ℝ) * Real.log L * typeIIPolylogEnvelope B *
            ((P : ℝ) + typeIIHybridGapPowerEnvelope T r A B P)) := hbase
    _ = Real.sqrt ((8 * C * Real.log L * typeIIPolylogEnvelope B) *
          typeIIHybridBlockComponents T r A B P) := by rw [← hfact]; congr 1 <;> ring
    _ = Real.sqrt (8 * C * Real.log L * typeIIPolylogEnvelope B) *
          Real.sqrt (typeIIHybridBlockComponents T r A B P) := Real.sqrt_mul hK0 _
    _ ≤ Real.sqrt (8 * C * Real.log L * typeIIPolylogEnvelope B) *
          typeIIHybridBlockRootEnvelope T r A B P :=
      mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)

end

end RHTower.Sieve
