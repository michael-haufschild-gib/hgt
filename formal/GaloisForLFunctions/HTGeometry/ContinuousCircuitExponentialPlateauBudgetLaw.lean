import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap

/-! Quantitative budget for exponentially wide continuous-circuit plateaux. -/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exponential backward width used for the continuous-circuit plateau. -/
def continuousCircuitPlateauWidth (L : ℕ) : ℕ := 2 ^ (L / 2)

def continuousCircuitPlateauLabelCount (L : ℕ) : ℕ :=
  Fintype.card (PauliTracelessLabel (L * 2) 2)

/-- One uniform product-formula repetition count for every increment up to
the target exponential width. -/
def continuousCircuitPlateauRepetitions (L : ℕ) : ℕ :=
  let m := continuousCircuitPlateauLabelCount L
  let W := continuousCircuitPlateauWidth L
  300 * m ^ (3 : ℕ) * (L + 2) ^ (2 : ℕ) * W ^ (2 : ℕ) + W * m * (L + 2) + 1

def continuousCircuitPlateauCompilerCost (L : ℕ) : ℕ :=
  continuousCircuitPlateauRepetitions L *
    continuousCircuitPlateauLabelCount L

private def continuousCircuitPlateauMajorant (L : ℕ) : ℕ :=
  let M := 72 * (L + 2) ^ (2 : ℕ)
  M * (300 * M ^ (3 : ℕ) * (L + 2) ^ (2 : ℕ) * 2 ^ L +
    2 ^ L * M * (L + 2) + 1)

theorem continuousCircuitPlateauLabelCount_le {L : ℕ} (hL : 1 ≤ L) :
    continuousCircuitPlateauLabelCount L ≤ 72 * (L + 2) ^ (2 : ℕ) := by
  have hcard : Fintype.card (PauliTracelessLabel (L * 2) 2) ≤
      18 * (L * 2) ^ (2 : ℕ) := by
    rw [card_pauliTracelessLabel]
    exact Quantum.nonidentityPauliWeightCount_le (L * 2) 2 (by omega)
  unfold continuousCircuitPlateauLabelCount
  calc
    Fintype.card (PauliTracelessLabel (L * 2) 2) ≤
        18 * (L * 2) ^ (2 : ℕ) := hcard
    _ = 72 * L ^ (2 : ℕ) := by ring
    _ ≤ 72 * (L + 2) ^ (2 : ℕ) := by
      gcongr
      omega

theorem continuousCircuitPlateauWidth_sq_le_twoPow (L : ℕ) :
    continuousCircuitPlateauWidth L ^ (2 : ℕ) ≤ 2 ^ L := by
  rw [continuousCircuitPlateauWidth, ← pow_mul]
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem continuousCircuitPlateauWidth_le_twoPow (L : ℕ) :
    continuousCircuitPlateauWidth L ≤ 2 ^ L := by
  unfold continuousCircuitPlateauWidth
  exact Nat.pow_le_pow_right (by omega) (Nat.div_le_self L 2)

theorem continuousCircuitPlateauCompilerCost_le_majorant {L : ℕ} (hL : 1 ≤ L) :
    continuousCircuitPlateauCompilerCost L ≤
      continuousCircuitPlateauMajorant L := by
  let m := continuousCircuitPlateauLabelCount L
  let W := continuousCircuitPlateauWidth L
  let M := 72 * (L + 2) ^ (2 : ℕ)
  have hm : m ≤ M := continuousCircuitPlateauLabelCount_le hL
  have hW : W ≤ 2 ^ L := continuousCircuitPlateauWidth_le_twoPow L
  have hW2 : W ^ (2 : ℕ) ≤ 2 ^ L := continuousCircuitPlateauWidth_sq_le_twoPow L
  let R := 300 * M ^ (3 : ℕ) * (L + 2) ^ (2 : ℕ) * 2 ^ L +
    2 ^ L * M * (L + 2) + 1
  have hr : continuousCircuitPlateauRepetitions L ≤ R := by
    unfold continuousCircuitPlateauRepetitions
    dsimp [m, W]
    dsimp [R]
    gcongr
  calc
    continuousCircuitPlateauCompilerCost L =
        continuousCircuitPlateauRepetitions L * m := rfl
    _ ≤ R * m := Nat.mul_le_mul_right m hr
    _ ≤ R * M := Nat.mul_le_mul_left R hm
    _ = continuousCircuitPlateauMajorant L := by
      simp [continuousCircuitPlateauMajorant, R, M]
      ring

set_option maxRecDepth 4000 in
theorem continuousCircuitPlateauMajorant_le_closedForm (L : ℕ) :
    continuousCircuitPlateauMajorant L ≤
      302 * 72 ^ (4 : ℕ) * (L + 2) ^ (10 : ℕ) * 2 ^ L := by
  let X := L + 2
  let M := 72 * X ^ (2 : ℕ)
  let q := 2 ^ L
  have hX : 1 ≤ X := by omega
  have hM : 1 ≤ M := by
    have hX2 : 1 ≤ X ^ (2 : ℕ) := Nat.one_le_pow 2 X hX
    dsimp [M]
    omega
  have hq : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hsmall1 : q * M * X ≤ M ^ (3 : ℕ) * X ^ (2 : ℕ) * q := by
    calc
      q * M * X ≤ q * M ^ (3 : ℕ) * X ^ (2 : ℕ) := by
        gcongr
        · simpa using Nat.pow_le_pow_right hM (by omega : 1 ≤ 3)
        · simpa using Nat.pow_le_pow_right hX (by omega : 1 ≤ 2)
      _ = M ^ (3 : ℕ) * X ^ (2 : ℕ) * q := by ring
  have hsmall2 : 1 ≤ M ^ (3 : ℕ) * X ^ (2 : ℕ) * q := by
    exact one_le_mul (one_le_mul (Nat.one_le_pow 3 M hM)
      (Nat.one_le_pow 2 X hX)) hq
  unfold continuousCircuitPlateauMajorant
  dsimp [X, M, q] at hsmall1 hsmall2 ⊢
  calc
    (72 * (L + 2) ^ (2 : ℕ)) *
        (300 * (72 * (L + 2) ^ (2 : ℕ)) ^ (3 : ℕ) * (L + 2) ^ (2 : ℕ) * 2 ^ L +
          2 ^ L * (72 * (L + 2) ^ (2 : ℕ)) * (L + 2) + 1) ≤
      (72 * (L + 2) ^ (2 : ℕ)) *
        (302 * (72 * (L + 2) ^ (2 : ℕ)) ^ (3 : ℕ) * (L + 2) ^ (2 : ℕ) * 2 ^ L) := by
          gcongr
          let A := (72 * (L + 2) ^ (2 : ℕ)) ^ (3 : ℕ) * (L + 2) ^ (2 : ℕ) * 2 ^ L
          let B := 2 ^ L * (72 * (L + 2) ^ (2 : ℕ)) * (L + 2)
          have hB : 2 ^ L * (72 * (L + 2) ^ (2 : ℕ)) * (L + 2) ≤ A := by
            simpa [A] using hsmall1
          have hA : 1 ≤ A := by simpa [A] using hsmall2
          have hBA : B ≤ A := by simpa [B] using hB
          have : 300 * A + B + 1 ≤ 302 * A := by omega
          simpa only [A, B, mul_assoc] using this
    _ = 302 * 72 ^ (4 : ℕ) * (L + 2) ^ (10 : ℕ) * 2 ^ L := by ring

private def continuousCircuitPlateauAsymptoticConstant : ℕ :=
  256 * 302 * 72 ^ (4 : ℕ) * 3 ^ (11 : ℕ)

private theorem eventually_continuousCircuitPlateau_polynomial_le_twoPow :
    ∀ᶠ L : ℕ in atTop,
      continuousCircuitPlateauAsymptoticConstant * L ^ (11 : ℕ) ≤ 2 ^ L := by
  have hK : (0 : ℝ) < continuousCircuitPlateauAsymptoticConstant := by
    norm_num [continuousCircuitPlateauAsymptoticConstant]
  have hlo := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 11
    (by norm_num : (1 : ℝ) < 2)).bound (one_div_pos.mpr hK)
  filter_upwards [hlo] with L hL
  have hraw : (L : ℝ) ^ (11 : ℕ) ≤
      (1 / (continuousCircuitPlateauAsymptoticConstant : ℝ)) *
        (2 : ℝ) ^ L := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ (11 : ℕ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ L)] using hL
  have hreal : (continuousCircuitPlateauAsymptoticConstant : ℝ) *
      (L : ℝ) ^ (11 : ℕ) ≤ (2 : ℝ) ^ L := by
    calc
      (continuousCircuitPlateauAsymptoticConstant : ℝ) * (L : ℝ) ^ (11 : ℕ) ≤
          (continuousCircuitPlateauAsymptoticConstant : ℝ) *
            ((1 / (continuousCircuitPlateauAsymptoticConstant : ℝ)) *
              (2 : ℝ) ^ L) := by gcongr
      _ = (2 : ℝ) ^ L := by field_simp
  exact_mod_cast hreal

/-- The exponential-width increment compiler eventually consumes at most
half of the near-Hilbert continuous-circuit gate budget. -/
theorem eventually_two_mul_continuousCircuitPlateauCompilerCost_le_nearHilbert :
    ∀ᶠ L : ℕ in atTop,
      2 * continuousCircuitPlateauCompilerCost L ≤
        nearHilbertContinuousCircuitBudget (L * 2) := by
  filter_upwards [eventually_continuousCircuitPlateau_polynomial_le_twoPow,
    Filter.eventually_ge_atTop 1] with L hpoly hL
  have hcost := continuousCircuitPlateauCompilerCost_le_majorant hL
  have hmajor := continuousCircuitPlateauMajorant_le_closedForm L
  have hLshift : L + 2 ≤ 3 * L := by omega
  have hpowshift : (L + 2) ^ (11 : ℕ) ≤ (3 * L) ^ (11 : ℕ) :=
    Nat.pow_le_pow_left hLshift 11
  have hlin : L * 2 + 1 ≤ 2 * (L + 2) := by omega
  have hclosed :
      (2 * continuousCircuitPlateauCompilerCost L) *
          (64 * (L * 2 + 1)) ≤ 2 ^ (L * 2) := by
    calc
      (2 * continuousCircuitPlateauCompilerCost L) * (64 * (L * 2 + 1)) ≤
          (2 * (302 * 72 ^ (4 : ℕ) * (L + 2) ^ (10 : ℕ) * 2 ^ L)) *
            (64 * (L * 2 + 1)) := by gcongr; exact hcost.trans hmajor
      _ = (128 * 302 * 72 ^ (4 : ℕ)) * (L + 2) ^ (10 : ℕ) * 2 ^ L *
          (L * 2 + 1) := by ring
      _ ≤ (128 * 302 * 72 ^ (4 : ℕ)) * (L + 2) ^ (10 : ℕ) * 2 ^ L *
          (2 * (L + 2)) := by gcongr
      _ = (256 * 302 * 72 ^ (4 : ℕ)) * (L + 2) ^ (11 : ℕ) * 2 ^ L := by ring
      _ ≤ continuousCircuitPlateauAsymptoticConstant * L ^ (11 : ℕ) * 2 ^ L := by
        unfold continuousCircuitPlateauAsymptoticConstant
        calc
          (256 * 302 * 72 ^ (4 : ℕ)) * (L + 2) ^ (11 : ℕ) * 2 ^ L ≤
              (256 * 302 * 72 ^ (4 : ℕ)) * (3 * L) ^ (11 : ℕ) * 2 ^ L := by gcongr
          _ = (256 * 302 * 72 ^ (4 : ℕ) * 3 ^ (11 : ℕ)) * L ^ (11 : ℕ) * 2 ^ L := by ring
      _ ≤ 2 ^ L * 2 ^ L := by gcongr
      _ = 2 ^ (L * 2) := by rw [← pow_add]; congr 1; omega
  unfold nearHilbertContinuousCircuitBudget
  rw [Nat.le_div_iff_mul_le (by positivity)]
  exact hclosed

theorem continuousCircuitPlateauRepetitions_pos (L : ℕ) :
    0 < continuousCircuitPlateauRepetitions L := by
  simp only [continuousCircuitPlateauRepetitions]
  omega

private theorem continuousCircuitPlateauRepetitions_ge_smallTerm (L : ℕ) :
    continuousCircuitPlateauWidth L * continuousCircuitPlateauLabelCount L *
        (L + 2) ≤ continuousCircuitPlateauRepetitions L := by
  simp only [continuousCircuitPlateauRepetitions]
  omega

private theorem continuousCircuitPlateauRepetitions_ge_errorTerm (L : ℕ) :
    300 * continuousCircuitPlateauLabelCount L ^ (3 : ℕ) * (L + 2) ^ (2 : ℕ) *
        continuousCircuitPlateauWidth L ^ (2 : ℕ) ≤
      continuousCircuitPlateauRepetitions L := by
  simp only [continuousCircuitPlateauRepetitions]
  omega

/-- One repetition count works uniformly for every time increment in the
exponential plateau and every Hamiltonian with norm at most `L + 2`. -/
theorem continuousCircuitPlateau_compiler_small
    {L : ℕ} {τ B : ℝ}
    (hτ : |τ| ≤ continuousCircuitPlateauWidth L)
    (hB0 : 0 ≤ B) (hB : B ≤ L + 2) :
    |τ / (continuousCircuitPlateauRepetitions L : ℝ)| *
        (continuousCircuitPlateauLabelCount L : ℝ) * B ≤ 1 := by
  let r := continuousCircuitPlateauRepetitions L
  let m := continuousCircuitPlateauLabelCount L
  let W := continuousCircuitPlateauWidth L
  have hr : (0 : ℝ) < r := by
    exact_mod_cast continuousCircuitPlateauRepetitions_pos L
  have hbudgetNat := continuousCircuitPlateauRepetitions_ge_smallTerm L
  have hbudget : (W : ℝ) * (m : ℝ) * (L + 2 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hbudgetNat
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hnum : |τ| * (m : ℝ) * B ≤ (r : ℝ) := by
    calc
      |τ| * (m : ℝ) * B ≤ (W : ℝ) * (m : ℝ) * (L + 2 : ℝ) := by gcongr
      _ ≤ (r : ℝ) := hbudget
  rw [abs_div, abs_of_pos hr]
  change |τ| / (r : ℝ) * (m : ℝ) * B ≤ 1
  rw [show |τ| / (r : ℝ) * (m : ℝ) * B =
      (|τ| * (m : ℝ) * B) / (r : ℝ) by ring]
  exact (div_le_one hr).2 hnum

/-- Uniform fixed-error estimate for the same exponential increment
compiler. -/
theorem continuousCircuitPlateau_compiler_error
    {L : ℕ} {τ B : ℝ}
    (hτ : |τ| ≤ continuousCircuitPlateauWidth L)
    (hB0 : 0 ≤ B) (hB : B ≤ L + 2) :
    3 * (continuousCircuitPlateauLabelCount L : ℝ) ^ (3 : ℕ) * B ^ (2 : ℕ) * |τ| ^ (2 : ℕ) /
        continuousCircuitPlateauRepetitions L ≤ (1 : ℝ) / 100 := by
  let r := continuousCircuitPlateauRepetitions L
  let m := continuousCircuitPlateauLabelCount L
  let W := continuousCircuitPlateauWidth L
  have hr : (0 : ℝ) < r := by
    exact_mod_cast continuousCircuitPlateauRepetitions_pos L
  have hbudgetNat := continuousCircuitPlateauRepetitions_ge_errorTerm L
  have hbudget : 300 * (m : ℝ) ^ (3 : ℕ) * (L + 2 : ℝ) ^ (2 : ℕ) * (W : ℝ) ^ (2 : ℕ) ≤
      (r : ℝ) := by
    exact_mod_cast hbudgetNat
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hτ0 : 0 ≤ |τ| := abs_nonneg _
  have hlarge : 300 * (m : ℝ) ^ (3 : ℕ) * B ^ (2 : ℕ) * |τ| ^ (2 : ℕ) ≤ (r : ℝ) := by
    calc
      300 * (m : ℝ) ^ (3 : ℕ) * B ^ (2 : ℕ) * |τ| ^ (2 : ℕ) ≤
          300 * (m : ℝ) ^ (3 : ℕ) * (L + 2 : ℝ) ^ (2 : ℕ) * (W : ℝ) ^ (2 : ℕ) := by
            gcongr
      _ ≤ (r : ℝ) := hbudget
  apply (div_le_iff₀ hr).2
  nlinarith

end

end GaloisForLFunctions.HTGeometry
