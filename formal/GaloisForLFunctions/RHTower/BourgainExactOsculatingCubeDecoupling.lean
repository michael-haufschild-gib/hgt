/-
# Exact osculating decoupling on the normalized cube

The paired-triple Fourier identity turns the perturbation-stable Gaussian
estimate into Bourgain's exact bilinear sixth moment on one normalized
osculating coordinate cube.  No additive Taylor-error term occurs.
-/
import GaloisForLFunctions.RHTower.BourgainPairedTripleFourierIdentity

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp exact-curve bilinear sixth-moment estimate on the normalized
four-cube.  The sole scale condition is the explicit cubic frequency
perturbation bound. -/
theorem integral_bourgainExactLocalSum_scaledOsculating_fourCube_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (hH : 0 < H),
      ∀ {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (hab : a < b),
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let E :=
        bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale ha hab
      let X := bourgainIndependentParabolaNaturalScale H
      let δ :=
        bourgainOsculatingFrequencyPerturbationSize X
          ‖(E.symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
          a b ((H : ℝ) / D)
      δ ≤ 1 / 24 →
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫ x in bourgainFourCube,
          ‖bourgainSquareRootExactLocalSum H D a c₁
              (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b c₂
              (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ)) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀, hgaussian⟩ :=
    integral_bourgainExactOsculatingPaired_gaussian_subpower hε
  refine ⟨Real.exp (4 * Real.pi) * C₀,
    mul_pos (Real.exp_pos _) hC₀, ?_⟩
  intro H hH D a b hD ha hab
  dsimp only
  intro hsmall c₁ c₂
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv hscale ha hab
  let X := bourgainIndependentParabolaNaturalScale H
  let p : Fin H → BourgainPhaseSpace :=
    bourgainExactLeftOsculatingFrequency hscale ha hab D
  let q : Fin H → BourgainPhaseSpace :=
    bourgainExactRightOsculatingFrequency hscale ha hab D
  let w : (Fin 3 → Fin H) × (Fin 3 → Fin H) → ℂ :=
    bourgainPairedTripleWeight c₁ c₂
  have hpoint :
      (fun x : BourgainPhaseSpace =>
        ‖bourgainSquareRootExactLocalSum H D a c₁
            (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ) *
          ‖bourgainSquareRootExactLocalSum H D b c₂
            (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ)) =
        fun x =>
          ‖bourgainWeightedFourierSum X
            (bourgainPairedTripleCloud p q) w x‖ ^ (2 : ℕ) := by
    funext x
    symm
    exact
      norm_sq_bourgainWeightedFourierSum_pairedTripleCloud_eq_exact
        hscale ha hab X c₁ c₂ x
  calc
    (∫ x in bourgainFourCube,
        ‖bourgainSquareRootExactLocalSum H D a c₁
            (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ) *
          ‖bourgainSquareRootExactLocalSum H D b c₂
            (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ)) =
      ∫ x in bourgainFourCube,
        ‖bourgainWeightedFourierSum X
          (bourgainPairedTripleCloud p q) w x‖ ^ (2 : ℕ) := by
        rw [hpoint]
    _ ≤ Real.exp (4 * Real.pi) *
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand X
            (bourgainPairedTripleCloud p q) w x) :=
      integral_bourgainFourCube_l2_le_gaussian
        X (bourgainPairedTripleCloud p q) w
    _ ≤ Real.exp (4 * Real.pi) *
        (C₀ * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
      gcongr
      exact hgaussian H hH hD ha hab hsmall c₁ c₂
    _ = (Real.exp (4 * Real.pi) * C₀) * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
      ring

end

end RHTower
