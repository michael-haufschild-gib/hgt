/-
# Unconditional local-ball estimate for separated `A₆` blocks

This module specializes the translated quadratic local-moment theorem to
literal unit-coefficient `A₆` blocks on the radius `M² / 12` ball.  The
Taylor remainder is discharged by the explicit `O(M⁶)` estimate rather than
being retained as a hypothesis or unresolved error term.
-/
import GaloisForLFunctions.RHTower.BourgainA6TaylorErrorAbsorption

open MeasureTheory

namespace RHTower

noncomputable section

/-- Absolute constant controlling the two unit-block Taylor errors. -/
def bourgainA6UnitTaylorErrorConstant : ℝ :=
  2 * (5 * Real.pi / 4) ^ (6 : ℕ) +
    (5 * Real.pi / 4) ^ (12 : ℕ)

/-- Uniform translated local-ball estimate for two separated literal `A₆`
blocks.  Every analytic input is unconditional; the cubic Taylor error has
already been absorbed into the explicit final term. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_localBall_unit_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq : q₁ < q₂) →
        (ha : (1 / 2 : ℝ) ≤ Real.sqrt ((q₁ : ℝ) / (N : ℝ))) →
        (hb : Real.sqrt ((q₂ : ℝ) / (N : ℝ)) ≤ 1) →
      ∀ y : BourgainPhaseSpace,
      let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
      let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
      let R : ℝ := (M : ℝ) ^ (2 : ℕ) / 12
      (∫⁻ x in {x : BourgainPhaseSpace | ‖x‖ ≤ R},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) (x + y)‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (ENNReal.ofReal
                |(3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| *
              ENNReal.ofReal
                |(((M : ℝ) / (N : ℝ)) ^ (6 : ℕ))⁻¹| *
              ENNReal.ofReal
                ((M : ℝ) ^ (8 : ℕ) *
                  (C * (M : ℝ) ^ ε *
                    (M : ℝ) ^ (3 : ℕ) * (M : ℝ) ^ (3 : ℕ))) +
            ENNReal.ofReal
                (bourgainA6UnitTaylorErrorConstant *
                  (M : ℝ) ^ (6 : ℕ)) *
              ENNReal.ofReal ((2 * R) ^ (4 : ℕ))) := by
  obtain ⟨C, hC, hlocal⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_bilinear_translate hε
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hMN hM2N hq ha hb y
  dsimp only
  let a : ℝ := Real.sqrt ((q₁ : ℝ) / (N : ℝ))
  let b : ℝ := Real.sqrt ((q₂ : ℝ) / (N : ℝ))
  let R : ℝ := (M : ℝ) ^ (2 : ℕ) / 12
  have hab : a < b := by
    exact sqrt_natCast_div_lt hN hq
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hphysical : 12 * R ≤ (M : ℝ) ^ (2 : ℕ) := by
    dsimp [R]
    ring_nf
    exact le_rfl
  have hraw :=
    hlocal ha hab hb (by positivity : 0 ≤ R) hNr M hM hMN'
      (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) y hphysical
  have herror :
      bourgainSquareRootBilinearTaylorError
          R a b ((M : ℝ) / (N : ℝ))
          (fun _ : Fin M => (1 : ℂ)) (fun _ : Fin M => (1 : ℂ)) ≤
        bourgainA6UnitTaylorErrorConstant * (M : ℝ) ^ (6 : ℕ) := by
    have hbLower : (1 / 2 : ℝ) ≤ b := ha.trans hab.le
    exact bourgainSquareRootBilinearTaylorError_unit_le_mul
      hN hM hM2N ha hbLower
  calc
    (∫⁻ x in {x : BourgainPhaseSpace | ‖x‖ ≤ R},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) (x + y)‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (ENNReal.ofReal
                |(3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ)))⁻¹| *
              ENNReal.ofReal
                |(((M : ℝ) / (N : ℝ)) ^ (6 : ℕ))⁻¹| *
              ENNReal.ofReal
                ((M : ℝ) ^ (8 : ℕ) *
                  (C * (M : ℝ) ^ ε *
                    (M : ℝ) ^ (3 : ℕ) * (M : ℝ) ^ (3 : ℕ))) +
            ENNReal.ofReal
                (bourgainSquareRootBilinearTaylorError
                  R a b ((M : ℝ) / (N : ℝ))
                  (fun _ : Fin M => (1 : ℂ))
                  (fun _ : Fin M => (1 : ℂ))) *
              ENNReal.ofReal ((2 * R) ^ (4 : ℕ))) := by
      simpa only [a, b, R,
        bourgainA6PhysicalBlockSum_eq_exactLocalSum,
        norm_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, one_pow] using hraw
    _ ≤ _ := by
      gcongr

end

end RHTower
