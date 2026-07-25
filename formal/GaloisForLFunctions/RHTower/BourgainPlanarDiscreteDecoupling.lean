/-
# Discrete planar `L⁶` decoupling input

This module packages the arithmetic parabola theorem in the literal
`[0,1]²` exponential-integral convention used in Bourgain (1.5).  It proves
unconditionally

`∫_[0,1]² |Σ aₙ e(nu+n²v)|⁶ ≤ Cε H^ε (Σ|aₙ|²)³`.

The continuous weighted extension form of (1.5), and its wave-packet
localization, remain separate analytic steps.
-/
import GaloisForLFunctions.RHTower.BourgainPlanarBilinearL6
import GaloisForLFunctions.RHTower.BourgainUnitIntervalTorus

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Literal discrete parabola extension operator on `[0,1]²`. -/
def bourgainDiscreteParabolaExtension
    (H : ℕ) (a : Fin H → ℂ) (u v : ℝ) : ℂ :=
  ∑ n : Fin H,
    a n * bourgainUnitCharacter
      ((bourgainIndex n : ℝ) * u +
        (bourgainIndex n : ℝ) ^ (2 : ℕ) * v)

/-- Exact identification with the internal two-torus polynomial. -/
theorem bourgainDiscreteParabolaExtension_eq_twoTorus
    (H : ℕ) (a : Fin H → ℂ) (u v : ℝ) :
    bourgainDiscreteParabolaExtension H a u v =
      bourgainParabolaTwoTorusSum H a
        (bourgainUnitCharacter u) (bourgainUnitCharacter v) := by
  unfold bourgainDiscreteParabolaExtension
    bourgainParabolaTwoTorusSum bourgainUnitCharacter
  apply Fintype.sum_congr
  intro n
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  let E₁ : ℂ :=
    (bourgainIndex n : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))
  let E₂ : ℂ :=
    (bourgainIndex n ^ (2 : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (v : ℂ))
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I *
          (((bourgainIndex n : ℝ) * u +
            (bourgainIndex n : ℝ) ^ (2 : ℕ) * v : ℝ) : ℂ) =
        E₁ + E₂ := by
    dsimp only [E₁, E₂]
    push_cast
    ring
  rw [hphase, Complex.exp_add]
  dsimp only [E₁, E₂]
  push_cast
  ring

/-- Literal unit-square sixth moment equals the exact two-torus moment. -/
theorem integral_unitSquare_discreteParabola_norm_pow_six_eq
    (H : ℕ) (a : Fin H → ℂ) :
    (∫ v in (0 : ℝ)..1,
      ∫ u in (0 : ℝ)..1,
        ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ)) =
      Real.circleAverage
        (fun z₂ =>
          Real.circleAverage
            (fun z₁ =>
              ‖bourgainParabolaTwoTorusSum H a z₁ z₂‖ ^ (6 : ℕ))
            0 1)
        0 1 := by
  rw [circleAverage_circleAverage_zero_one_eq_unitSquare]
  apply intervalIntegral.integral_congr
  intro v _
  apply intervalIntegral.integral_congr
  intro u _
  dsimp
  rw [bourgainDiscreteParabolaExtension_eq_twoTorus]

/-- **Unconditional discrete form of the planar decoupling input (1.5).** -/
theorem integral_unitSquare_discreteParabola_norm_pow_six_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a : Fin H → ℂ),
        (∫ v in (0 : ℝ)..1,
          ∫ u in (0 : ℝ)..1,
            ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ)) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ :=
    circleAverage_circleAverage_parabola_norm_pow_six_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a
  rw [integral_unitSquare_discreteParabola_norm_pow_six_eq]
  exact hbound H a

end

end RHTower
