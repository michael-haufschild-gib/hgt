import GaloisForLFunctions.ArithmeticIncidencePositivity.ShiftedGroundStateAndFirstJetAtomPoleLaw

/-!
# Closed shift thresholds for fixed-support collars

The double-exponential collar ratio yields an explicit sufficient shift.
The positive midpoint gap then gives a concrete threshold for each actual
integer atom outside the five exceptional moduli.
-/

open MeasureTheory Set Real
open RHTower RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
noncomputable section
namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The pointwise collar estimates imply positivity under explicit scalar inequalities. -/
theorem shiftedGroundState_collar_integral_pos_of_bounds
    {g : ℝ → ℝ} {L δ m B a : ℝ}
    (hL : 0 < L) (hg : Continuous g) (hm : 0 < m) (hB0 : 0 < B)
    (hδ0 : 0 < δ) (hδL : δ ≤ L / 4)
    (hg_mid : ∀ x, |x - L / 2| ≤ δ → m ≤ g x)
    (hg_low : ∀ x ∈ Icc 0 L, -B ≤ g x)
    (ha3 : L + Real.log 3 / 2 ≤ a) (ha2 : L + Real.log 2 / 2 ≤ a)
    (hexp : Real.log 2 ≤ π * Real.exp (2 * (a - L)) * (L / 2))
    (hsmall : L * B * Real.exp (5 * L + 4 * π * L) *
      Real.exp (-(2 * π * Real.exp (2 * a - L) *
        (Real.cosh (2 * δ) - Real.cosh δ))) < δ * m * (1 / 4)) :
    0 < ∫ x in Ioo (0 : ℝ) L,
      shiftDifference a x * shiftDifference a (L - x) * g x := by
  rw [setIntegral_Ioo_eq_intervalIntegral hL.le]
  set F : ℝ → ℝ := fun x => shiftDifference a x * shiftDifference a (L - x) * g x
  have hF : Continuous F :=
    ((continuous_shiftDifference a).mul
      ((continuous_shiftDifference a).comp (continuous_const.sub continuous_id))).mul hg
  have hΦaL := riemannKernelReal_pos (a - L)
  set C₀ := riemannKernelReal (a - L) ^ 2 * Real.exp (2 * π * Real.exp (2 * (a - L)))
  have hC₀ : 0 < C₀ := by positivity
  set M_out := C₀ * Real.exp (5 * L - 2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ))
  set M_in := 1 / 4 * C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ)
  have hM_out : ∀ x ∈ Icc 0 L, δ ≤ |x - L / 2| →
      shiftDifference a x * shiftDifference a (L - x) ≤ M_out := fun x hx hxδ => by
    have h := shiftDifference_collar_le_of_abs_sub_ge ha3 hδ0.le hx hxδ
    have heq : M_out = riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) + 5 * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ)) := by
      dsimp [M_out, C₀]
      rw [mul_assoc, ← Real.exp_add]
      congr 2; ring
    rwa [heq]
  have hM_in : ∀ x, |x - L / 2| ≤ δ / 2 →
      M_in ≤ shiftDifference a x * shiftDifference a (L - x) := fun x hx => by
    have h := shiftDifference_collar_ge_of_abs_sub_le hL ha2 hexp hδ0.le (by linarith) hx
    have heq : M_in = 1 / 4 * riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh δ) := by
      dsimp [M_in, C₀]
      rw [show 1 / 4 * (riemannKernelReal (a - L) ^ 2 * Real.exp (2 * π * Real.exp (2 * (a - L)))) *
          Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) =
        1 / 4 * riemannKernelReal (a - L) ^ 2 *
          (Real.exp (2 * π * Real.exp (2 * (a - L))) *
            Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ)) by ring,
        ← Real.exp_add]
      congr 2; ring
    rwa [heq]
  have ha0 : 0 < a := by
    have : 0 < Real.log 2 := Real.log_pos one_lt_two
    linarith
  have hcoll_nn : ∀ x ∈ Icc 0 L, 0 ≤ shiftDifference a x * shiftDifference a (L - x) :=
    fun x hx => mul_nonneg (shiftDifference_nonneg_of_nonneg ha0.le hx.1)
      (shiftDifference_nonneg_of_nonneg ha0.le (by linarith [hx.2]))
  have hI1 : -(B * M_out) * (L / 2 - δ - 0) ≤ ∫ x in (0 : ℝ)..(L / 2 - δ), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨hx.1, by linarith [hx.2]⟩
    have hxδ : δ ≤ |x - L / 2| := by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]
    have h1 := hM_out x hxL hxδ
    have h2 := hg_low x hxL
    have h3 := hcoll_nn x hxL
    dsimp [F]
    nlinarith
  have hI2 : 0 * (L / 2 - δ / 2 - (L / 2 - δ)) ≤ ∫ x in (L / 2 - δ)..(L / 2 - δ / 2), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (hcoll_nn x hxL) (hm.le.trans (hg_mid x hxδ))
  have hI3 : (m * M_in) * (L / 2 + δ / 2 - (L / 2 - δ / 2)) ≤
      ∫ x in (L / 2 - δ / 2)..(L / 2 + δ / 2), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxδ2 : |x - L / 2| ≤ δ / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := hxδ2.trans (by linarith)
    have h1 := hM_in x hxδ2
    have h2 := hg_mid x hxδ
    dsimp [F]
    nlinarith [show 0 ≤ M_in by positivity]
  have hI4 : 0 * (L / 2 + δ - (L / 2 + δ / 2)) ≤ ∫ x in (L / 2 + δ / 2)..(L / 2 + δ), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (hcoll_nn x hxL) (hm.le.trans (hg_mid x hxδ))
  have hI5 : -(B * M_out) * (L - (L / 2 + δ)) ≤ ∫ x in (L / 2 + δ)..L, F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], hx.2⟩
    have hxδ : δ ≤ |x - L / 2| := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1]
    have h1 := hM_out x hxL hxδ
    have h2 := hg_low x hxL
    have h3 := hcoll_nn x hxL
    dsimp [F]
    nlinarith
  rw [intervalIntegral_five_split hF L δ]
  have hdiff_pos : 0 < δ * (m * M_in) - L * (B * M_out) := by
    have hrel : L * (B * M_out) =
        C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (L * B * Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) := by
      dsimp [M_out]
      rw [show C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (L * B * Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) =
          L * B * C₀ * (Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
            Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) by ring,
        ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hin_rel : δ * (m * M_in) =
        C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (δ * m * (1 / 4)) := by
      dsimp [M_in]
      ring
    rw [hin_rel, hrel, ← mul_sub]
    exact mul_pos (by positivity) (sub_pos.mpr hsmall)
  have hBM : 0 ≤ B * M_out := by positivity
  nlinarith


end GaloisForLFunctions.ArithmeticIncidencePositivity
