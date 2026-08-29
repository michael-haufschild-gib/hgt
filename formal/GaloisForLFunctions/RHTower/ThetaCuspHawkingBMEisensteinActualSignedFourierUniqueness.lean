import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient
import GaloisForLFunctions.RHTower.DeningerSmoothCoeffInjective

/-!
# Signed Fourier uniqueness for the actual completed Eisenstein Poincare series

Corpus search isolated a precise gap between the genuine coefficient computations and the
canonical cusp model.  The corpus proves the actual zero and positive Fourier coefficients, but
the canonical model is a signed two-sided Whittaker expansion.  This file supplies the missing
reflection involution on primitive integer pairs, proves horizontal evenness of the actual
Poincare sum, and derives equality of its positive and negative Fourier coefficients.

The intended downstream chain is

`all signed actual coefficients -> Fourier uniqueness -> actual Poincare = canonical cusp model ->
 literal truncated modular Green/Stokes -> balanced BM ++- source -> negative BM leg -> conserved
 left-QNM projection -> HC94 -> RH`.

All statements are unconditional in the existing absolute-convergence parameter.
-/

open Real MeasureTheory Set intervalIntegral Filter Topology Function
open scoped ENNReal FourierTransform

noncomputable section

namespace RHTower

/-- Reflection of a primitive bottom row across the vertical axis. -/
def d4BMPrimitiveIntegerPairReflect
    (p : D4BMPrimitiveIntegerPair) : D4BMPrimitiveIntegerPair where
  pair := (p.pair.1, -p.pair.2)
  primitive := by
    simpa using p.primitive

@[simp] theorem d4BMPrimitiveIntegerPairReflect_pair_fst
    (p : D4BMPrimitiveIntegerPair) :
    (d4BMPrimitiveIntegerPairReflect p).pair.1 = p.pair.1 := rfl

@[simp] theorem d4BMPrimitiveIntegerPairReflect_pair_snd
    (p : D4BMPrimitiveIntegerPair) :
    (d4BMPrimitiveIntegerPairReflect p).pair.2 = -p.pair.2 := rfl

@[simp] theorem d4BMPrimitiveIntegerPairReflect_involutive
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPrimitiveIntegerPairReflect (d4BMPrimitiveIntegerPairReflect p) = p := by
  cases p with
  | mk pair primitive =>
      cases pair
      simp [d4BMPrimitiveIntegerPairReflect]

/-- Reflection is a genuine equivalence of the primitive-pair index set. -/
def d4BMPrimitiveIntegerPairReflectEquiv :
    D4BMPrimitiveIntegerPair ≃ D4BMPrimitiveIntegerPair where
  toFun := d4BMPrimitiveIntegerPairReflect
  invFun := d4BMPrimitiveIntegerPairReflect
  left_inv := d4BMPrimitiveIntegerPairReflect_involutive
  right_inv := d4BMPrimitiveIntegerPairReflect_involutive

theorem d4BM_poincareQuadratic_horizontal_neg_reflect
    (z : D4BMUpperHalfPlaneCoordinate) (x : ℝ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareQuadratic (d4BMHorizontalCoordinate z (-x)) p.pair =
      d4BMPoincareQuadratic (d4BMHorizontalCoordinate z x)
        (d4BMPrimitiveIntegerPairReflect p).pair := by
  unfold d4BMPoincareQuadratic
  simp only [d4BMHorizontalCoordinate_y, d4BMHorizontalCoordinate_x,
    d4BMPrimitiveIntegerPairReflect_pair_fst,
    d4BMPrimitiveIntegerPairReflect_pair_snd]
  push_cast
  ring

theorem d4BM_poincareSeed_horizontal_neg_reflect
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (x : ℝ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed (d4BMHorizontalCoordinate z (-x)) s p =
      d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s
        (d4BMPrimitiveIntegerPairReflect p) := by
  unfold d4BMPoincareSeed
  rw [d4BM_poincareQuadratic_horizontal_neg_reflect]
  rfl

/-- The actual raw primitive-pair Poincare series is horizontally even. -/
theorem d4BM_rawEisensteinHorizontalFunction_even
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMRawEisensteinHorizontalFunction z P (-x) =
      d4BMRawEisensteinHorizontalFunction z P x := by
  unfold d4BMRawEisensteinHorizontalFunction d4BMRawEisensteinPoincareSeries
  congr 1
  calc
    (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeed (d4BMHorizontalCoordinate z (-x)) P.s p) =
        ∑' p : D4BMPrimitiveIntegerPair,
          d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s
            (d4BMPrimitiveIntegerPairReflect p) := by
      apply tsum_congr
      exact fun p => d4BM_poincareSeed_horizontal_neg_reflect z P.s x p
    _ = ∑' p : D4BMPrimitiveIntegerPair,
          d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p :=
      Equiv.tsum_eq d4BMPrimitiveIntegerPairReflectEquiv
        (fun p => d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p)

/-- Completion preserves horizontal evenness. -/
theorem d4BM_completedEisensteinHorizontalFunction_even
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCompletedEisensteinHorizontalFunction z P (-x) =
      d4BMCompletedEisensteinHorizontalFunction z P x := by
  rw [d4BM_completedEisensteinHorizontalFunction_eq_lambda_mul_raw,
    d4BM_completedEisensteinHorizontalFunction_eq_lambda_mul_raw,
    d4BM_rawEisensteinHorizontalFunction_even]

theorem d4BM_fourier_character_one_sub
    (m : ℤ) (x : ℝ) :
    fourier m ((1 - x : ℝ) : UnitAddCircle) =
      fourier (-m) (x : UnitAddCircle) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  norm_num
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (1 - (x : ℂ)) =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          -(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ)) by
    ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- Unit-cell Fourier coefficients of an even one-periodic function are sign-symmetric. -/
theorem d4BM_unitFourierCoefficient_neg_eq_of_even_periodic
    (f : ℝ → ℂ) (hper : Function.Periodic f 1)
    (heven : ∀ x, f (-x) = f x) (m : ℤ) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier m (x : UnitAddCircle) * f x) =
      ∫ x in Set.Ioc (0 : ℝ) 1,
        fourier (-m) (x : UnitAddCircle) * f x := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one]
  let g : ℝ → ℂ := fun x => fourier m (x : UnitAddCircle) * f x
  have hsub : (∫ x : ℝ in (0 : ℝ)..1, g (1 - x)) =
      ∫ x : ℝ in (0 : ℝ)..1, g x := by
    simpa using intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) g (1 : ℝ)
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [g]
  rw [d4BM_fourier_character_one_sub]
  have hf : f (1 - x) = f x := by
    calc
      f (1 - x) = f (-x) := by
        have hp := hper (-x)
        convert hp using 1 <;> ring
      _ = f x := heven x
  rw [hf]

/-- The genuine completed Poincare coefficients at opposite frequencies agree. -/
theorem d4BM_actualCompletedPoincare_negativeFourierCoefficient_eq_positive
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (F : D4BMPositiveFourierFrequency) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      fourier (F.value : ℤ) (x : UnitAddCircle) *
        d4BMCompletedEisensteinHorizontalFunction z P x) =
      ∫ x in Set.Ioc (0 : ℝ) 1,
        fourier (-(F.value : ℤ)) (x : UnitAddCircle) *
          d4BMCompletedEisensteinHorizontalFunction z P x := by
  apply d4BM_unitFourierCoefficient_neg_eq_of_even_periodic
  · intro x
    change d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate z (x + 1)) P =
      d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate z x) P
    exact d4BM_completedEisensteinPoincareSeries_translate
      (d4BMHorizontalCoordinate z x) P
  · exact d4BM_completedEisensteinHorizontalFunction_even z P

theorem d4BM_fourierCoeffOn_completedHorizontal_eq_actualIntegral
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (m : ℤ) :
    fourierCoeffOn (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one
        (d4BMCompletedEisensteinHorizontalFunction z P) m =
      ∫ x in Set.Ioc (0 : ℝ) 1,
        fourier (-m) (x : UnitAddCircle) *
          d4BMCompletedEisensteinHorizontalFunction z P x := by
  rw [fourierCoeffOn_eq_integral]
  norm_num [intervalIntegral.integral_of_le zero_le_one, smul_eq_mul]

/-- Common coefficient of the two signed modes with absolute frequency `N+1`. -/
def d4BMActualCanonicalSignedModeCoefficient
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (N : ℕ) : ℂ :=
  2 * d4BMCompletedEisensteinWhittakerCoefficient (P.s - 1 / 2)
      ⟨N + 1, by omega⟩ *
    (Real.sqrt z.y : ℂ) *
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
      (2 * Real.pi * z.y * (N + 1)) (P.s - 1 / 2)

theorem d4BM_actualCompletedPoincare_positiveSucc_fourierCoeffOn
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (N : ℕ) :
    fourierCoeffOn (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one
        (d4BMCompletedEisensteinHorizontalFunction z P) (N + 1 : ℤ) =
      d4BMActualCanonicalSignedModeCoefficient z P N := by
  rw [d4BM_fourierCoeffOn_completedHorizontal_eq_actualIntegral]
  simpa [d4BMActualCanonicalSignedModeCoefficient, Nat.cast_add, Nat.cast_one] using
    d4BM_actualCompletedPoincare_positiveFourierCoefficient_eq_canonicalWhittaker
      z P ⟨N + 1, by omega⟩

theorem d4BM_actualCompletedPoincare_negativeSucc_fourierCoeffOn
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (N : ℕ) :
    fourierCoeffOn (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one
        (d4BMCompletedEisensteinHorizontalFunction z P) (Int.negSucc N) =
      d4BMActualCanonicalSignedModeCoefficient z P N := by
  rw [d4BM_fourierCoeffOn_completedHorizontal_eq_actualIntegral]
  have hsym := d4BM_actualCompletedPoincare_negativeFourierCoefficient_eq_positive
    z P ⟨N + 1, by omega⟩
  have hpos :=
    d4BM_actualCompletedPoincare_positiveFourierCoefficient_eq_canonicalWhittaker
      z P ⟨N + 1, by omega⟩
  rw [show -(Int.negSucc N) = (N + 1 : ℤ) by omega]
  simpa [d4BMActualCanonicalSignedModeCoefficient, Nat.cast_add, Nat.cast_one] using
    hsym.trans hpos

theorem d4BM_actualCompletedPoincare_zero_fourierCoeffOn
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    fourierCoeffOn (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one
        (d4BMCompletedEisensteinHorizontalFunction z P) 0 =
      d4BMCompletedEisensteinCuspConstantPart .scalar
        (P.s - 1 / 2) z.y := by
  rw [d4BM_fourierCoeffOn_completedHorizontal_eq_actualIntegral]
  exact d4BM_actualCompletedPoincare_zeroFourierCoefficient_eq_canonicalConstantPart z P

/-- The actual horizontal second jet is continuous.  This is the local normal-convergence
regularity needed for classical pointwise Fourier inversion. -/
theorem continuous_d4BMCompletedPoincareHorizontalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Continuous (fun x : ℝ =>
      d4BMCompletedPoincareHorizontalSecondJet (d4BMHorizontalCoordinate z x) P) := by
  rw [continuous_iff_continuousAt]
  intro x
  let zx := d4BMHorizontalCoordinate z x
  let t : Set ℝ := Ioo (x - z.y) (x + z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedHorizontalSecondJet (d4BMHorizontalCoordinate z y) P.s p
  let M := d4BMHorizontalSecondJetLocalMajorant zx P
  have hM : Summable M := summable_d4BMHorizontalSecondJetLocalMajorant zx P
  have hterm : ∀ p, ContinuousOn (g p) t := by
    intro p
    apply Continuous.continuousOn
    dsimp only [g]
    fun_prop
  have hbound : ∀ p, ∀ y ∈ t, ‖g p y‖ ≤ M p := by
    intro p y hy
    have hK : 0 ≤
        (2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / zx.y ^ 2 := by
      apply div_nonneg
      · positivity
      · exact sq_nonneg _
    calc
      ‖g p y‖ ≤
          ((2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / zx.y ^ 2) *
            ‖d4BMPoincareSeed (d4BMHorizontalCoordinate z y) P.s p‖ := by
        dsimp only [g]
        simpa [zx, d4BMHorizontalCoordinate] using
          norm_d4BMPoincareSeedHorizontalSecondJet_le
            (d4BMHorizontalCoordinate z y) P.s p
      _ ≤ ((2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / zx.y ^ 2) *
          (3 ^ P.s.re * ‖d4BMPoincareSeed zx P.s p‖) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply norm_d4BMPoincareSeed_horizontal_le zx P p
        simpa [t, zx, d4BMHorizontalCoordinate] using hy
      _ = M p := by
        simp [M, d4BMHorizontalSecondJetLocalMajorant]
        ring
  have hsumCont : ContinuousOn (fun y => ∑' p, g p y) t :=
    continuousOn_tsum hterm hM hbound
  have hxmem : x ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hsumAt : ContinuousAt (fun y => ∑' p, g p y) x :=
    hsumCont.continuousAt (isOpen_Ioo.mem_nhds hxmem)
  have hscaled : ContinuousAt
      (fun y => reflectedCompletedLambda (2 * P.s) * (1 / 2 : ℂ) * ∑' p, g p y) x :=
    (continuousAt_const.mul (continuousAt_const.mul hsumAt))
  simpa [g, d4BMCompletedPoincareHorizontalSecondJet,
    d4BMRawPoincareHorizontalSecondJet, d4BMHorizontalCoordinate] using hscaled

end RHTower
