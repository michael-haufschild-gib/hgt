/-
# One-step Gaussian decoupling for Bourgain's normalized curve

This module discharges every geometric and Taylor hypothesis in the generic
Gaussian theorem for the exact normalized curve

`(t,t²,φ₃,q(t),φ₄,q(t))`.

The only scale condition is the explicit cubic smallness
`50331648000 H³ / D ≤ 1/24`.  Since `D²` is Bourgain's physical ball radius,
this is the quantitative form of `N = O(K^(3/2))` in (1.22).
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedScaledDistortion
import GaloisForLFunctions.RHTower.BourgainNormalizedTaylorRemainderBound

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The exact normalized curve satisfies sharp paired Gaussian decoupling on
every separated pair of arcs for which its cubic Taylor error is small. -/
theorem integral_bourgainNormalizedExactPaired_gaussian_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (hH : 0 < H)
        {q D a b : ℝ}
        (hq : 0 < q) (hq1 : q ≤ 1 / 2)
        (hD : 0 < D) (hHD : (H : ℝ) ≤ D)
        (ha0 : 0 ≤ a) (ha1 : a + (H : ℝ) / D ≤ 1)
        (hb0 : 0 ≤ b) (hb1 : b + (H : ℝ) / D ≤ 1)
        (hab : 1 / 4 ≤ b - a)
        (hsmall :
          50331648000 * (H : ℝ) ^ (3 : ℕ) / D ≤ 1 / 24),
      let hunit :=
        isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
          hq hq1
          (show a ∈ Set.Icc (0 : ℝ) 1 by
            constructor
            · exact ha0
            · have : 0 ≤ (H : ℝ) / D := by positivity
              linarith)
          (show b ∈ Set.Icc (0 : ℝ) 1 by
            constructor
            · exact hb0
            · have : 0 ≤ (H : ℝ) / D := by positivity
              linarith)
          hab
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let X := bourgainIndependentParabolaNaturalScale H
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand X
            (bourgainPairedTripleCloud
              (bourgainGenericExactLeftFrequency
                (bourgainNormalizedCubicRemainder q)
                (bourgainNormalizedQuarticRemainder q)
                hscale hunit D)
              (bourgainGenericExactRightFrequency
                (bourgainNormalizedCubicRemainder q)
                (bourgainNormalizedQuarticRemainder q)
                hscale hunit D))
            (bourgainPairedTripleWeight c₁ c₂) x) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hgeneric⟩ :=
    integral_bourgainGenericExactPaired_gaussian_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH q D a b hq hq1 hD hHD ha0 ha1 hb0 hb1 hab hsmall
  dsimp only
  let Δ : ℝ := (H : ℝ) / D
  let ρ : ℝ := 12 * Δ ^ (3 : ℕ)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    positivity
  have haIcc : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hbIcc : b ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  let hunit :=
    isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
      hq hq1 haIcc hbIcc hab
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hsample (n : Fin H) :
      0 ≤ (bourgainIndex n : ℝ) / D ∧
        (bourgainIndex n : ℝ) / D ≤ Δ := by
    constructor
    · positivity
    · dsimp [Δ]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast bourgainIndex_le n) hD.le
  have hleft (n : Fin H) :
      ‖bourgainGenericFourCurve
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q)
            (a + (bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurveQuadraticModel
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) a
            ((bourgainIndex n : ℝ) / D)‖ ≤ ρ := by
    exact norm_bourgainNormalizedTaylorCurve_sub_quadratic_le
      hq ha0 ha1 hΔ (hsample n).1 (hsample n).2
  have hright (n : Fin H) :
      ‖bourgainGenericFourCurve
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q)
            (b + (bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurveQuadraticModel
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q) b
            ((bourgainIndex n : ℝ) / D)‖ ≤ ρ := by
    exact norm_bourgainNormalizedTaylorCurve_sub_quadratic_le
      hq hb0 hb1 hΔ (hsample n).1 (hsample n).2
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) hscale hunit
  let X := bourgainIndependentParabolaNaturalScale H
  let δ :=
    bourgainGenericFrequencyPerturbationSize X
      ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ρ
  have hδphysical :
      δ ≤ 4194304000 * D ^ (2 : ℕ) * ρ := by
    exact bourgainNormalizedFrequencyPerturbationSize_le
      hH hq hq1 hD hHD hρ haIcc hbIcc hab
  have hphysical :
      4194304000 * D ^ (2 : ℕ) * ρ =
        50331648000 * (H : ℝ) ^ (3 : ℕ) / D := by
    dsimp [ρ, Δ]
    field_simp
    ring
  have hδsmall : δ ≤ 1 / 24 := by
    exact hδphysical.trans (hphysical.le.trans hsmall)
  exact hgeneric H hH
    (bourgainNormalizedCubicRemainder q)
    (bourgainNormalizedQuarticRemainder q)
    hD hρ hunit hleft hright hδsmall

end

end RHTower
