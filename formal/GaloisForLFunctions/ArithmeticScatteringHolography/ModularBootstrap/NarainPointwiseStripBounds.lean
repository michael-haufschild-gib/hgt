import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanStripBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPoleClearing

/-!
# Uniform strip bounds for Narain numerators

The sharp Fourier-tail envelope extends the filled mean numerator bound uniformly over every target horocycle.
-/

open Complex RHTower Set
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The full filled Eisenstein numerator has one exponential envelope on each target horocycle. -/
theorem exists_filledEisensteinNumerator_uniform_strip_bound
    (Y : Height) {B : ℝ} (hB : 0 ≤ B) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : ℝ, ∀ u : ℂ, |u.re| ≤ B → 1 ≤ |u.im| →
      ‖filledEisensteinNumerator ⟨x, Y.val, Y.property⟩ u‖ ≤
        C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) := by
  obtain ⟨CM, NM, hCM, hmean⟩ := exists_filledNumeratorMean_strip_bound ⟨Y.val, Y.property⟩ hB
  obtain ⟨CT, NT, hCT, htail⟩ := exists_weightedTail_jets_le_sharp Y.property hB
  let N : ℕ := max NM (NT + 3)
  let C : ℝ := CM + 16 * (1 + B) ^ 3 * CT
  refine ⟨C, N, by dsimp only [C]; positivity, ?_⟩
  intro x u hu ht
  have hY : Y.val ∈ Icc (Y.val / 2) (2 * Y.val) := by
    have hpos : 0 < Y.val := Y.property
    constructor <;> linarith only [hpos]
  have hM := hmean u hu ht
  have hT := (eisTail_jets_le (htail u false x Y.val hu hY)
    (htail u true x Y.val hu hY)).1
  obtain ⟨hplus, htwo, _, hminus, _⟩ := norm_one_add_two_mul_le hu hB
  have hlin : ‖2 * u - 1‖ ≤ 2 * (1 + B) * (1 + |u.im|) := by
    rw [show 2 * u - 1 = -(2 * (1 / 2 - u)) by ring, norm_neg,
      norm_mul, Complex.norm_ofNat]
    nlinarith only [hminus]
  have hp1 : 1 ≤ 1 + |u.im| := le_add_of_nonneg_right (abs_nonneg _)
  have hpM : (1 + |u.im|) ^ NM ≤ (1 + |u.im|) ^ N :=
    pow_le_pow_right₀ hp1 (le_max_left _ _)
  have hpT : (1 + |u.im|) ^ (NT + 3) ≤ (1 + |u.im|) ^ N :=
    pow_le_pow_right₀ hp1 (le_max_right _ _)
  have hproduct : ‖2 * u - 1‖ * ‖1 + 2 * u‖ * ‖2 * u‖ * ‖eisTail u x Y.val‖ ≤
      (16 * (1 + B) ^ 3 * CT) * (1 + |u.im|) ^ (NT + 3) *
        Real.exp (-(Real.pi * |u.im| / 2)) := by
    calc
      _ ≤ (2 * (1 + B) * (1 + |u.im|)) * (2 * (1 + B) * (1 + |u.im|)) *
          (2 * (1 + B) * (1 + |u.im|)) *
          (2 * (CT * (1 + |u.im|) ^ NT * Real.exp (-(Real.pi * |u.im| / 2)))) := by gcongr
      _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ ‖filledNumeratorMean ⟨Y.val, Y.property⟩ u‖ +
        ‖2 * u - 1‖ * ‖1 + 2 * u‖ * ‖2 * u‖ * ‖eisTail u x Y.val‖ := by
      simpa only [filledEisensteinNumerator, filledNumeratorMean, norm_mul] using
        norm_add_le (filledNumeratorMean ⟨Y.val, Y.property⟩ u)
          ((2 * u - 1) * (1 + 2 * u) * (2 * u) * eisTail u x Y.val)
    _ ≤ CM * (1 + |u.im|) ^ NM * Real.exp (-(Real.pi * |u.im| / 2)) +
        (16 * (1 + B) ^ 3 * CT) * (1 + |u.im|) ^ (NT + 3) *
          Real.exp (-(Real.pi * |u.im| / 2)) := add_le_add hM hproduct
    _ ≤ CM * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) +
        (16 * (1 + B) ^ 3 * CT) * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) := by gcongr
    _ = _ := by dsimp only [C]; ring


/-- Every target modulus inherits the uniform horocycle envelope. -/
theorem exists_filledEisensteinNumerator_strip_bound
    (z : D4BMUpperHalfPlaneCoordinate) {B : ℝ} (hB : 0 ≤ B) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ u : ℂ, |u.re| ≤ B → 1 ≤ |u.im| →
      ‖filledEisensteinNumerator z u‖ ≤
        C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) := by
  obtain ⟨C, N, hC, hb⟩ := exists_filledEisensteinNumerator_uniform_strip_bound
    ⟨z.y, z.y_pos⟩ hB
  exact ⟨C, N, hC, hb z.x⟩

#print axioms exists_filledEisensteinNumerator_uniform_strip_bound

#print axioms exists_filledEisensteinNumerator_strip_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
