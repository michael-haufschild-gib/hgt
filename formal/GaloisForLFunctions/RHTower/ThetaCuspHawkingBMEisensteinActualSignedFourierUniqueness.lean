import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient
import GaloisForLFunctions.RHTower.DeningerSmoothCoeffInjective
import GaloisForLFunctions.RHTower.PeriodicFourierDecay
import GaloisForLFunctions.HTGeometry.KleinGordonEigenEnvelope

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
    have hseed : Continuous (fun y : ℝ =>
        d4BMPoincareSeed (d4BMHorizontalCoordinate z y) P.s p) := by
      rw [continuous_iff_continuousAt]
      intro y
      simpa [d4BMHorizontalCoordinate] using
        (hasDerivAt_d4BMPoincareSeed_horizontal
          (d4BMHorizontalCoordinate z y) P.s p).continuousAt
    have hqR : Continuous (fun y : ℝ =>
        d4BMPoincareQuadratic (d4BMHorizontalCoordinate z y) p.pair) := by
      unfold d4BMPoincareQuadratic
      fun_prop
    have hqC : Continuous (fun y : ℝ =>
        (d4BMPoincareQuadratic (d4BMHorizontalCoordinate z y) p.pair : ℂ)) :=
      Complex.continuous_ofReal.comp hqR
    have huR : Continuous (fun y : ℝ =>
        d4BMPoincareHorizontalLinear (d4BMHorizontalCoordinate z y) p) := by
      unfold d4BMPoincareHorizontalLinear
      fun_prop
    have huC : Continuous (fun y : ℝ =>
        (d4BMPoincareHorizontalLinear (d4BMHorizontalCoordinate z y) p : ℂ)) :=
      Complex.continuous_ofReal.comp huR
    have hqne : ∀ y : ℝ,
        (d4BMPoincareQuadratic (d4BMHorizontalCoordinate z y) p.pair : ℂ) ≠ 0 := by
      intro y
      exact_mod_cast (d4BMPoincareQuadratic_pos
        (d4BMHorizontalCoordinate z y) p.pair p.pair_ne_zero).ne'
    unfold d4BMPoincareSeedHorizontalSecondJet
    apply Continuous.mul
    · apply Continuous.add
      · exact continuous_const.div hqC hqne
      · apply Continuous.div
        · exact continuous_const.mul (huC.pow 2)
        · exact hqC.pow 2
        · intro y
          exact pow_ne_zero 2 (hqne y)
    · exact hseed
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
  have hhalf : ContinuousAt (fun y => (1 / 2 : ℂ) * ∑' p, g p y) x :=
    continuousAt_const.mul hsumAt
  have hscaled : ContinuousAt
      (fun y => reflectedCompletedLambda (2 * P.s) * ((1 / 2 : ℂ) * ∑' p, g p y)) x :=
    continuousAt_const.mul hhalf
  simpa [g, d4BMCompletedPoincareHorizontalSecondJet,
    d4BMRawPoincareHorizontalSecondJet, d4BMHorizontalCoordinate] using hscaled

theorem d4BM_completedPoincareHorizontalSecondJet_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalSecondJet
        (d4BMEisensteinTranslateCoordinate z) P =
      d4BMCompletedPoincareHorizontalSecondJet z P := by
  let f₁ : ℝ → ℂ := fun x =>
    d4BMCompletedPoincareHorizontalFirstJet (d4BMHorizontalCoordinate z x) P
  let f₂ : ℝ → ℂ := fun x =>
    d4BMCompletedPoincareHorizontalSecondJet (d4BMHorizontalCoordinate z x) P
  have hper₁ : Function.Periodic f₁ 1 := by
    intro x
    dsimp only [f₁]
    simpa [d4BMHorizontalCoordinate, d4BMEisensteinTranslateCoordinate] using
      d4BM_completedPoincareHorizontalFirstJet_translate
        (d4BMHorizontalCoordinate z x) P
  have hright : HasDerivAt f₁ (f₂ z.x) z.x := by
    simpa [f₁, f₂, d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal z P
  have hleftBase : HasDerivAt f₁ (f₂ (z.x + 1)) (z.x + 1) := by
    simpa [f₁, f₂, d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal
        (d4BMHorizontalCoordinate z (z.x + 1)) P
  have hshift : HasDerivAt (fun x : ℝ => x + 1) 1 z.x := by
    simpa using (hasDerivAt_id z.x).add_const 1
  have hleft := hleftBase.scomp z.x hshift
  have hfun : (fun x : ℝ => f₁ (x + 1)) = f₁ := funext hper₁
  have hleft' : HasDerivAt f₁ (f₂ (z.x + 1)) z.x := by
    rw [← hfun]
    simpa [Function.comp_def] using hleft
  have hvalue : f₂ (z.x + 1) = f₂ z.x := hleft'.unique hright
  simpa [f₂, d4BMHorizontalCoordinate, d4BMEisensteinTranslateCoordinate] using hvalue

/-- The completed second horizontal jet is one-periodic. -/
theorem d4BM_completedPoincareHorizontalSecondJet_periodic
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Function.Periodic (fun x : ℝ =>
      d4BMCompletedPoincareHorizontalSecondJet (d4BMHorizontalCoordinate z x) P) 1 := by
  intro x
  simpa [d4BMHorizontalCoordinate, d4BMEisensteinTranslateCoordinate] using
    d4BM_completedPoincareHorizontalSecondJet_translate
      (d4BMHorizontalCoordinate z x) P

/-- Pointwise Fourier inversion for the actual completed Poincare series on its unit cell. -/
theorem d4BM_actualCompletedPoincare_hasSum_fourierSeries
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    HasSum (fun m : ℤ =>
      fourierCoeffOn (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one
          (d4BMCompletedEisensteinHorizontalFunction z P) m *
        fourier m (x : UnitAddCircle))
      (d4BMCompletedEisensteinHorizontalFunction z P x) := by
  let f : ℝ → ℂ := d4BMCompletedEisensteinHorizontalFunction z P
  let f₁ : ℝ → ℂ := fun y =>
    d4BMCompletedPoincareHorizontalFirstJet (d4BMHorizontalCoordinate z y) P
  let f₂ : ℝ → ℂ := fun y =>
    d4BMCompletedPoincareHorizontalSecondJet (d4BMHorizontalCoordinate z y) P
  have hf : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt f (f₁ y) y := by
    intro y _hy
    change HasDerivAt
      (fun x : ℝ => d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate z x) P)
      (d4BMCompletedPoincareHorizontalFirstJet
        (d4BMHorizontalCoordinate z y) P) y
    simpa [d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal
        (d4BMHorizontalCoordinate z y) P
  have hf₁ : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt f₁ (f₂ y) y := by
    intro y _hy
    simpa [f₁, f₂, d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal
        (d4BMHorizontalCoordinate z y) P
  have hcont₁ : Continuous f₁ := by
    rw [continuous_iff_continuousAt]
    intro y
    simpa [f₁, f₂, d4BMHorizontalCoordinate] using
      (hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal
        (d4BMHorizontalCoordinate z y) P).continuousAt
  have hcont₂ : Continuous f₂ := by
    exact continuous_d4BMCompletedPoincareHorizontalSecondJet_horizontal z P
  have hper : Function.Periodic f 1 := by
    intro y
    change d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate z (y + 1)) P =
      d4BMCompletedEisensteinPoincareSeries (d4BMHorizontalCoordinate z y) P
    exact d4BM_completedEisensteinPoincareSeries_translate
      (d4BMHorizontalCoordinate z y) P
  have hper₁ : Function.Periodic f₁ 1 := by
    intro y
    dsimp only [f₁]
    simpa [d4BMHorizontalCoordinate, d4BMEisensteinTranslateCoordinate] using
      d4BM_completedPoincareHorizontalFirstJet_translate
        (d4BMHorizontalCoordinate z y) P
  have hper₂ : Function.Periodic f₂ 1 :=
    d4BM_completedPoincareHorizontalSecondJet_periodic z P
  obtain ⟨C, hC, hbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_of_periodic hcont₂ hper₂ zero_lt_one
  have hsum := GaloisForLFunctions.RHTower.hasSum_fourier_of_periodic_two
    zero_lt_one hf hf₁
    (hcont₁.intervalIntegrable 0 1) (hcont₂.intervalIntegrable 0 1) hbound
    (by simpa using hper 0) (by simpa using hper₁ 0) hx
  simpa [f] using hsum

/-- Constructor-level decomposition of the integer frequency lattice. -/
def d4BMNatSumNatEquivInt : ℕ ⊕ ℕ ≃ ℤ where
  toFun
    | Sum.inl n => Int.ofNat n
    | Sum.inr n => Int.negSucc n
  invFun
    | Int.ofNat n => Sum.inl n
    | Int.negSucc n => Sum.inr n
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

@[simp] theorem d4BMNatSumNatEquivInt_inl (N : ℕ) :
    d4BMNatSumNatEquivInt (Sum.inl N) = (N : ℤ) := rfl

@[simp] theorem d4BMNatSumNatEquivInt_inr (N : ℕ) :
    d4BMNatSumNatEquivInt (Sum.inr N) = Int.negSucc N := rfl

theorem d4BM_completedEisensteinFourierPhase_false_eq_fourier
    (N : ℕ) (x : ℝ) :
    d4BMCompletedEisensteinFourierPhase false N x =
      fourier (N + 1 : ℤ) (x : UnitAddCircle) := by
  rw [d4BMCompletedEisensteinFourierPhase, fourier_coe_apply]
  simp [d4BMFourierSign]
  congr 1
  push_cast
  ring

theorem d4BM_completedEisensteinFourierPhase_true_eq_fourier
    (N : ℕ) (x : ℝ) :
    d4BMCompletedEisensteinFourierPhase true N x =
      fourier (Int.negSucc N) (x : UnitAddCircle) := by
  rw [d4BMCompletedEisensteinFourierPhase, fourier_coe_apply]
  simp [d4BMFourierSign]
  congr 1
  push_cast
  ring

theorem d4BM_tsum_actualCanonicalSignedMode_positive_eq_signedTail
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    (∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
      fourier (N + 1 : ℤ) (x : UnitAddCircle)) =
      2 * d4BMCompletedEisensteinSignedSqrtWhittakerTail
        (P.s - 1 / 2) (P.s - 1 / 2) false x 0 0 z.y := by
  rw [d4BMCompletedEisensteinSignedSqrtWhittakerTail, ← tsum_mul_left]
  apply tsum_congr
  intro N
  rw [← d4BM_completedEisensteinFourierPhase_false_eq_fourier]
  simp only [pow_zero, mul_one]
  unfold d4BMActualCanonicalSignedModeCoefficient
  ring

theorem d4BM_tsum_actualCanonicalSignedMode_negative_eq_signedTail
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    (∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
      fourier (Int.negSucc N) (x : UnitAddCircle)) =
      2 * d4BMCompletedEisensteinSignedSqrtWhittakerTail
        (P.s - 1 / 2) (P.s - 1 / 2) true x 0 0 z.y := by
  rw [d4BMCompletedEisensteinSignedSqrtWhittakerTail, ← tsum_mul_left]
  apply tsum_congr
  intro N
  rw [← d4BM_completedEisensteinFourierPhase_true_eq_fourier]
  simp only [pow_zero, mul_one]
  unfold d4BMActualCanonicalSignedModeCoefficient
  ring

theorem d4BM_actualCanonicalSignedMode_twoSided_tsum_eq_cuspTailPart
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    (∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
        fourier (N + 1 : ℤ) (x : UnitAddCircle)) +
      (∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
        fourier (Int.negSucc N) (x : UnitAddCircle)) =
      d4BMCompletedEisensteinCuspTailPart .scalar
        (P.s - 1 / 2) x z.y := by
  rw [d4BM_tsum_actualCanonicalSignedMode_positive_eq_signedTail,
    d4BM_tsum_actualCanonicalSignedMode_negative_eq_signedTail]
  simp [d4BMCompletedEisensteinCuspTailPart,
    d4BMCompletedEisensteinFullSignedZeroWord]
  ring

/-- **Actual-to-canonical Fourier weld on a fundamental unit cell.**  The genuine completed
Poincare sum is exactly the corpus canonical completed Eisenstein cusp model. -/
theorem d4BM_actualCompletedPoincare_eq_canonicalCuspLeg_of_mem_Ioc
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    d4BMCompletedEisensteinHorizontalFunction z P x =
      d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) x z.y := by
  let a : ℤ → ℂ := fun m =>
    fourierCoeffOn (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one
        (d4BMCompletedEisensteinHorizontalFunction z P) m *
      fourier m (x : UnitAddCircle)
  have hsum : HasSum a (d4BMCompletedEisensteinHorizontalFunction z P x) := by
    simpa [a] using d4BM_actualCompletedPoincare_hasSum_fourierSeries z P hx
  have ha : Summable a := hsum.summable
  have hae : Summable (a ∘ d4BMNatSumNatEquivInt) :=
    ha.comp_injective d4BMNatSumNatEquivInt.injective
  have hpos : Summable ((a ∘ d4BMNatSumNatEquivInt) ∘ Sum.inl) :=
    hae.comp_injective Sum.inl_injective
  have hneg : Summable ((a ∘ d4BMNatSumNatEquivInt) ∘ Sum.inr) :=
    hae.comp_injective Sum.inr_injective
  have hsplit :
      (∑' q : ℕ ⊕ ℕ, a (d4BMNatSumNatEquivInt q)) =
        (∑' N : ℕ, a (N : ℤ)) + (∑' N : ℕ, a (Int.negSucc N)) := by
    simpa [Function.comp_def] using Summable.tsum_sum hpos hneg
  have hposSplit :
      a 0 + (∑' N : ℕ, a (N + 1 : ℤ)) = ∑' N : ℕ, a (N : ℤ) := by
    simpa using hpos.sum_add_tsum_nat_add 1
  have hzero : a 0 = d4BMCompletedEisensteinCuspConstantPart .scalar
      (P.s - 1 / 2) z.y := by
    dsimp only [a]
    rw [d4BM_actualCompletedPoincare_zero_fourierCoeffOn]
    simp
  have hpositive :
      (∑' N : ℕ, a (N + 1 : ℤ)) =
        ∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
          fourier (N + 1 : ℤ) (x : UnitAddCircle) := by
    apply tsum_congr
    intro N
    dsimp only [a]
    rw [d4BM_actualCompletedPoincare_positiveSucc_fourierCoeffOn]
  have hnegative :
      (∑' N : ℕ, a (Int.negSucc N)) =
        ∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
          fourier (Int.negSucc N) (x : UnitAddCircle) := by
    apply tsum_congr
    intro N
    dsimp only [a]
    rw [d4BM_actualCompletedPoincare_negativeSucc_fourierCoeffOn]
  calc
    d4BMCompletedEisensteinHorizontalFunction z P x = ∑' m : ℤ, a m :=
      hsum.tsum_eq.symm
    _ = ∑' q : ℕ ⊕ ℕ, a (d4BMNatSumNatEquivInt q) :=
      (Equiv.tsum_eq d4BMNatSumNatEquivInt a).symm
    _ = (∑' N : ℕ, a (N : ℤ)) + (∑' N : ℕ, a (Int.negSucc N)) := hsplit
    _ = (a 0 + ∑' N : ℕ, a (N + 1 : ℤ)) +
        ∑' N : ℕ, a (Int.negSucc N) := by rw [hposSplit]
    _ = d4BMCompletedEisensteinCuspConstantPart .scalar (P.s - 1 / 2) z.y +
        ((∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
            fourier (N + 1 : ℤ) (x : UnitAddCircle)) +
          ∑' N : ℕ, d4BMActualCanonicalSignedModeCoefficient z P N *
            fourier (Int.negSucc N) (x : UnitAddCircle)) := by
      rw [hzero, hpositive, hnegative]
      ring
    _ = d4BMCompletedEisensteinCuspConstantPart .scalar (P.s - 1 / 2) z.y +
        d4BMCompletedEisensteinCuspTailPart .scalar (P.s - 1 / 2) x z.y := by
      rw [d4BM_actualCanonicalSignedMode_twoSided_tsum_eq_cuspTailPart]
    _ = d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) x z.y := rfl

theorem d4BM_fourier_character_add_one
    (m : ℤ) (x : ℝ) :
    fourier m ((x + 1 : ℝ) : UnitAddCircle) =
      fourier m (x : UnitAddCircle) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  norm_num
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((x : ℂ) + 1) =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ) by ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

theorem d4BM_completedEisensteinFourierPhase_add_one
    (negative : Bool) (N : ℕ) (x : ℝ) :
    d4BMCompletedEisensteinFourierPhase negative N (x + 1) =
      d4BMCompletedEisensteinFourierPhase negative N x := by
  cases negative
  · rw [d4BM_completedEisensteinFourierPhase_false_eq_fourier,
      d4BM_completedEisensteinFourierPhase_false_eq_fourier,
      d4BM_fourier_character_add_one]
  · rw [d4BM_completedEisensteinFourierPhase_true_eq_fourier,
      d4BM_completedEisensteinFourierPhase_true_eq_fourier,
      d4BM_fourier_character_add_one]

theorem d4BM_completedEisensteinSignedSqrtWhittakerTail_add_one
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (indexDegree heightDegree : ℕ) (Y : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail
        u nu negative (x + 1) indexDegree heightDegree Y =
      d4BMCompletedEisensteinSignedSqrtWhittakerTail
        u nu negative x indexDegree heightDegree Y := by
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerTail
  apply tsum_congr
  intro N
  rw [d4BM_completedEisensteinFourierPhase_add_one]

/-- The canonical signed scalar cusp model is one-periodic. -/
theorem d4BM_completedEisensteinCuspLeg_scalar_periodic
    (u : ℂ) (Y : ℝ) :
    Function.Periodic (fun x : ℝ =>
      d4BMCompletedEisensteinCuspLeg .scalar u x Y) 1 := by
  intro x
  unfold d4BMCompletedEisensteinCuspLeg d4BMCompletedEisensteinCuspTailPart
    d4BMCompletedEisensteinFullSignedZeroWord
  change d4BMCompletedEisensteinCuspConstantPart .scalar u Y +
      2 * (d4BMCompletedEisensteinSignedSqrtWhittakerTail
          u u false (x + 1) 0 0 Y +
        d4BMCompletedEisensteinSignedSqrtWhittakerTail
          u u true (x + 1) 0 0 Y) =
    d4BMCompletedEisensteinCuspConstantPart .scalar u Y +
      2 * (d4BMCompletedEisensteinSignedSqrtWhittakerTail
          u u false x 0 0 Y +
        d4BMCompletedEisensteinSignedSqrtWhittakerTail
          u u true x 0 0 Y)
  rw [d4BM_completedEisensteinSignedSqrtWhittakerTail_add_one,
    d4BM_completedEisensteinSignedSqrtWhittakerTail_add_one]

/-- Actual-to-canonical equality on the closed unit cell. -/
theorem d4BM_actualCompletedPoincare_eq_canonicalCuspLeg_of_mem_Icc
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    d4BMCompletedEisensteinHorizontalFunction z P x =
      d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) x z.y := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hx0.eq_or_lt with rfl | hxpos
  · have hcell := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg_of_mem_Ioc
      z P (x := (1 : ℝ)) ⟨zero_lt_one, le_rfl⟩
    have hactual : d4BMCompletedEisensteinHorizontalFunction z P (0 + 1) =
        d4BMCompletedEisensteinHorizontalFunction z P 0 := by
      change d4BMCompletedEisensteinPoincareSeries
          (d4BMHorizontalCoordinate z (0 + 1)) P =
        d4BMCompletedEisensteinPoincareSeries (d4BMHorizontalCoordinate z 0) P
      exact d4BM_completedEisensteinPoincareSeries_translate
        (d4BMHorizontalCoordinate z 0) P
    have hcanonical := d4BM_completedEisensteinCuspLeg_scalar_periodic
      (P.s - 1 / 2) z.y 0
    have hcanonical' :
        d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) 1 z.y =
          d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) 0 z.y := by
      simpa using hcanonical
    have hactual' : d4BMCompletedEisensteinHorizontalFunction z P 1 =
        d4BMCompletedEisensteinHorizontalFunction z P 0 := by
      simpa using hactual
    exact hactual'.symm.trans (hcell.trans hcanonical')
  · exact d4BM_actualCompletedPoincare_eq_canonicalCuspLeg_of_mem_Ioc
      z P ⟨hxpos, hx1⟩

/-- **Global actual-to-canonical Fourier uniqueness.**  In the absolute-convergence chamber, the
actual completed primitive-pair Poincare series is the canonical signed scalar cusp model at every
horizontal coordinate. -/
theorem d4BM_actualCompletedPoincare_eq_canonicalCuspLeg
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCompletedEisensteinHorizontalFunction z P x =
      d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) x z.y := by
  let r : ℝ := Int.fract x
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hcell := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg_of_mem_Icc z P hr
  have hperActual : Function.Periodic
      (d4BMCompletedEisensteinHorizontalFunction z P) 1 := by
    intro y
    change d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate z (y + 1)) P =
      d4BMCompletedEisensteinPoincareSeries (d4BMHorizontalCoordinate z y) P
    exact d4BM_completedEisensteinPoincareSeries_translate
      (d4BMHorizontalCoordinate z y) P
  have hperCanonical := d4BM_completedEisensteinCuspLeg_scalar_periodic
    (P.s - 1 / 2) z.y
  have hxrep : r + (⌊x⌋ : ℝ) * 1 = x := by
    dsimp only [r]
    rw [mul_one, add_comm]
    exact Int.floor_add_fract x
  have hactual : d4BMCompletedEisensteinHorizontalFunction z P x =
      d4BMCompletedEisensteinHorizontalFunction z P r := by
    calc
      d4BMCompletedEisensteinHorizontalFunction z P x =
          d4BMCompletedEisensteinHorizontalFunction z P
            (r + (⌊x⌋ : ℝ) * 1) := by rw [hxrep]
      _ = d4BMCompletedEisensteinHorizontalFunction z P r :=
        (hperActual.int_mul ⌊x⌋) r
  have hcanonical :
      d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) x z.y =
        d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) r z.y := by
    calc
      d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) x z.y =
          d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2)
            (r + (⌊x⌋ : ℝ) * 1) z.y := by rw [hxrep]
      _ = d4BMCompletedEisensteinCuspLeg .scalar (P.s - 1 / 2) r z.y :=
        (hperCanonical.int_mul ⌊x⌋) r
  exact hactual.trans (hcell.trans hcanonical.symm)

end RHTower
