import GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorFiniteSchwarzPolarizedInfiniteRankNoGo
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDampingSemigroup

/-!
# HB pre-divisor finite-energy infinite-rank Gram no-go

The exact source-faithful HB cancellation kernel already has infinite diagonal energy at its
left hard edge.  Its susceptibility dominates `x⁻²` on `(0, 1/2)`, so no positive complex-Hilbert
Gram realization can have locally finite feature energy there, regardless of feature-space
dimension.

Combined with the finite-separation-rank obstruction, this closes finite-energy positive Hilbert
compensation.  A surviving HB incidence must have infinite hard-edge energy, be indefinite,
renormalized or distributional, exclude the hard-edge domain, change support or sheet, or leave
scalar Hilbert pairing.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- The exact HB pre-divisor susceptibility has at least inverse-square hard-edge growth. -/
theorem d4PreDivisorOpticalCancellationSusceptibility_rpow_neg_two_le
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    x ^ (-2 : ℝ) ≤ d4PreDivisorOpticalCancellationSusceptibility x := by
  let A : ℝ := x * (3 - x)
  let B : ℝ := (1 - x) * (2 + x)
  let N : ℝ := A ^ 2 * (2 - B) + B ^ 2 * (2 - A) + 2 * A * B
  have hx0 : 0 < x := hx.1
  have hxhalf : x < 1 / 2 := hx.2
  have hA0 : 0 < A := by
    dsimp [A]
    exact mul_pos hx0 (by linarith)
  have hA2 : A < 2 := by
    dsimp [A]
    nlinarith [sq_nonneg (x - 3 / 2)]
  have hB0 : 0 < B := by
    dsimp [B]
    exact mul_pos (by linarith) (by linarith)
  have hB2 : B < 2 := by
    dsimp [B]
    nlinarith [sq_nonneg x]
  have hN : B ^ 2 * (2 - A) ≤ N := by
    dsimp [N]
    have h1 : 0 ≤ A ^ 2 * (2 - B) := mul_nonneg (sq_nonneg _) (by linarith)
    have h2 : 0 ≤ 2 * A * B :=
      (mul_pos (mul_pos (by norm_num) hA0) hB0).le
    linarith
  have hAl : A ≤ 3 * x := by
    dsimp [A]
    nlinarith [sq_nonneg x]
  have hAsq : A ^ 2 ≤ 9 * x ^ 2 := by nlinarith [sq_nonneg (A - 3 * x)]
  have hAmargin : 1 / 2 ≤ 2 - A := by
    dsimp [A]
    nlinarith [sq_nonneg x]
  have hAmargin0 : 0 ≤ 2 - A := le_trans (by norm_num) hAmargin
  have hfactor : 3 / 2 ≤ (2 - x) * (x + 1) := by
    nlinarith [sq_nonneg x]
  have hAne : A ≠ 0 := ne_of_gt hA0
  have hBne : B ≠ 0 := ne_of_gt hB0
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hrpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
    rw [Real.rpow_neg (le_of_lt hx0)]
    norm_num [Real.rpow_two]
  rw [hrpow]
  have hformula :
      d4PreDivisorOpticalCancellationSusceptibility x =
        54 * N * (2 - x) * (x + 1) / (A ^ 2 * B ^ 2) := by
    dsimp [A, B, N]
    unfold d4PreDivisorOpticalCancellationSusceptibility
      d4PreDivisorEventHorizonThirdMassReflectionSusceptibility
      d4PreDivisorThetaMirrorAIMEDenominator
      d4PreDivisorHorizonAngularShift
      d4PreDivisorReflectedHorizonAngularShift
      d4EventHorizonThirdMassParityCrossNumerator
    field_simp [hxne]
    ring
  rw [hformula]
  rw [div_le_div_iff₀ (sq_pos_of_pos hx0)
    (mul_pos (sq_pos_of_pos hA0) (sq_pos_of_pos hB0))]
  have hmain :
      A ^ 2 * B ^ 2 ≤ x ^ 2 * (54 * N * (2 - x) * (x + 1)) := by
    calc
      A ^ 2 * B ^ 2 ≤ (9 * x ^ 2) * B ^ 2 :=
        mul_le_mul_of_nonneg_right hAsq (sq_nonneg B)
      _ = x ^ 2 * (9 * B ^ 2) := by ring
      _ ≤ x ^ 2 * (54 * (B ^ 2 * (2 - A)) * (2 - x) * (x + 1)) := by
        have hprod : (1 / 2 : ℝ) * (3 / 2 : ℝ) ≤
            (2 - A) * ((2 - x) * (x + 1)) := by
          exact mul_le_mul hAmargin hfactor (by norm_num) hAmargin0
        have h9 : (9 : ℝ) ≤ 54 * ((2 - A) * ((2 - x) * (x + 1))) := by
          nlinarith
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
        calc
          9 * B ^ 2 ≤ (54 * ((2 - A) * ((2 - x) * (x + 1)))) * B ^ 2 :=
            mul_le_mul_of_nonneg_right h9 (sq_nonneg B)
          _ = 54 * (B ^ 2 * (2 - A)) * (2 - x) * (x + 1) := by ring
      _ ≤ x ^ 2 * (54 * N * (2 - x) * (x + 1)) := by
        have h2minus : 0 ≤ 2 - x := by linarith
        have hxplus : 0 ≤ x + 1 := by linarith
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hN (by norm_num)) h2minus) hxplus)
          (sq_nonneg x)
  nlinarith

/-- The exact HB pre-divisor susceptibility has infinite energy at the left hard edge. -/
theorem not_integrableOn_d4PreDivisorOpticalCancellationSusceptibility :
    ¬ IntegrableOn d4PreDivisorOpticalCancellationSusceptibility
      (Ioo (0 : ℝ) (1 / 2)) := by
  intro hS
  have hsmall : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioo 0 (1 / 2)) := by
    refine Integrable.mono' hS ?_ ?_
    · exact ((measurable_id.pow_const _).aestronglyMeasurable.restrict)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.1.le _)]
      exact d4PreDivisorOpticalCancellationSusceptibility_rpow_neg_two_le hx
  have hexponent : (-1 : ℝ) < -2 :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff
      (show (0 : ℝ) < 1 / 2 by norm_num)).mp hsmall
  norm_num at hexponent

/-- Any positive Hilbert Gram realization of the exact HB kernel has infinite feature energy. -/
theorem not_integrableOn_normSq_of_d4PreDivisorOpticalCancellationGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Phi : ℝ → E)
    (hgram : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (Phi y) =
        d4PreDivisorOpticalCancellationPolarizedKernel x y) :
    ¬ IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2)) := by
  intro henergy
  apply not_integrableOn_d4PreDivisorOpticalCancellationSusceptibility
  refine IntegrableOn.congr_fun henergy ?_ measurableSet_Ioo
  intro x hx
  have hdiag := hgram x hx x hx
  rw [d4PreDivisorOpticalCancellationPolarizedKernel,
    show ((x + x) / 2 : ℝ) = x by ring,
    d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal] at hdiag
  calc
    ‖Phi x‖ ^ 2 = Complex.re (inner ℂ (Phi x) (Phi x)) :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) (Phi x)).symm
    _ = Complex.re (d4PreDivisorOpticalCancellationSusceptibility x : ℂ) :=
      congrArg Complex.re hdiag
    _ = d4PreDivisorOpticalCancellationSusceptibility x := by simp

/-- Closed route certificate: no positive finite-energy Hilbert feature field realizes the exact
source-faithful HB pre-divisor cancellation kernel on the physical hard-edge square. -/
def D4HBPreDivisorFiniteEnergyInfiniteRankGramRouteKilled : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (Phi : ℝ → E),
    (∀ x ∈ Ioo (0 : ℝ) (1 / 2), ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (Phi y) =
        d4PreDivisorOpticalCancellationPolarizedKernel x y) →
      ¬ IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2))

/-- The positive finite-energy infinite-rank HB Gram compensation route is killed. -/
theorem d4HBPreDivisorFiniteEnergyInfiniteRankGramRouteKilled :
    D4HBPreDivisorFiniteEnergyInfiniteRankGramRouteKilled := by
  intro E _ _ Phi hgram
  exact not_integrableOn_normSq_of_d4PreDivisorOpticalCancellationGram Phi hgram

end

end RHTower
