/-
# Translation invariance for exact localized square-root sums

Translating a physical phase cube twists each coefficient by a unit
character.  Hence all coefficient norms and the explicit Taylor-error term
are unchanged, making the exact local bilinear estimate uniform over cube
centers.
-/
import GaloisForLFunctions.RHTower.BourgainExactLocalMomentTransfer

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

def bourgainSquareRootExactLocalTranslateCoefficients
    (H : ℕ) (D a : ℝ) (c : Fin H → ℂ)
    (y : BourgainPhaseSpace) : Fin H → ℂ :=
  fun n =>
    c n * bourgainUnitCharacter
      (bourgainSquareRootCurvePhase y
        (a ^ 2 + (bourgainIndex n : ℝ) / D))

@[simp] theorem norm_bourgainSquareRootExactLocalTranslateCoefficients
    (H : ℕ) (D a : ℝ) (c : Fin H → ℂ)
    (y : BourgainPhaseSpace) (n : Fin H) :
    ‖bourgainSquareRootExactLocalTranslateCoefficients H D a c y n‖ =
      ‖c n‖ := by
  rw [bourgainSquareRootExactLocalTranslateCoefficients, norm_mul,
    norm_bourgainUnitCharacter, mul_one]

theorem bourgainSquareRootCurvePhase_add
    (x y : BourgainPhaseSpace) (t : ℝ) :
    bourgainSquareRootCurvePhase (x + y) t =
      bourgainSquareRootCurvePhase x t +
        bourgainSquareRootCurvePhase y t := by
  unfold bourgainSquareRootCurvePhase bourgainDot
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem bourgainSquareRootExactLocalSum_add
    (H : ℕ) (D a : ℝ) (c : Fin H → ℂ)
    (x y : BourgainPhaseSpace) :
    bourgainSquareRootExactLocalSum H D a c (x + y) =
      bourgainSquareRootExactLocalSum H D a
        (bourgainSquareRootExactLocalTranslateCoefficients H D a c y) x := by
  unfold bourgainSquareRootExactLocalSum
  apply Fintype.sum_congr
  intro n
  rw [bourgainSquareRootCurvePhase_add, bourgainUnitCharacter_add]
  unfold bourgainSquareRootExactLocalTranslateCoefficients
  ring

theorem bourgainSquareRootLocalTaylorError_translateCoefficients
    (H : ℕ) (N D a δ : ℝ) (c : Fin H → ℂ)
    (y : BourgainPhaseSpace) :
    bourgainSquareRootLocalTaylorError N a δ
        (bourgainSquareRootExactLocalTranslateCoefficients H D a c y) =
      bourgainSquareRootLocalTaylorError N a δ c := by
  unfold bourgainSquareRootLocalTaylorError
  congr 1
  apply Fintype.sum_congr
  intro n
  exact norm_bourgainSquareRootExactLocalTranslateCoefficients
    H D a c y n

theorem bourgainSquareRootBilinearTaylorError_translateCoefficients
    (H : ℕ) (N D a b δ : ℝ) (c₁ c₂ : Fin H → ℂ)
    (y : BourgainPhaseSpace) :
    bourgainSquareRootBilinearTaylorError N a b δ
        (bourgainSquareRootExactLocalTranslateCoefficients H D a c₁ y)
        (bourgainSquareRootExactLocalTranslateCoefficients H D b c₂ y) =
      bourgainSquareRootBilinearTaylorError N a b δ c₁ c₂ := by
  have hS₁ :
      (∑ n : Fin H,
        ‖bourgainSquareRootExactLocalTranslateCoefficients H D a c₁ y n‖) =
        ∑ n : Fin H, ‖c₁ n‖ := by
    apply Fintype.sum_congr
    intro n
    exact norm_bourgainSquareRootExactLocalTranslateCoefficients
      H D a c₁ y n
  have hS₂ :
      (∑ n : Fin H,
        ‖bourgainSquareRootExactLocalTranslateCoefficients H D b c₂ y n‖) =
        ∑ n : Fin H, ‖c₂ n‖ := by
    apply Fintype.sum_congr
    intro n
    exact norm_bourgainSquareRootExactLocalTranslateCoefficients
      H D b c₂ y n
  simp only [bourgainSquareRootBilinearTaylorError]
  rw [hS₁, hS₂,
    bourgainSquareRootLocalTaylorError_translateCoefficients,
    bourgainSquareRootLocalTaylorError_translateCoefficients]

/-- The application-range local estimate is uniform over translations of
the physical phase cube. -/
theorem setLIntegral_bourgainSquareRootExactLocalSum_bilinear_translate
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a₀ b₀ N D : ℝ},
        (ha₀ : 1 / 2 ≤ a₀) → (ha₀b₀ : a₀ < b₀) →
        (hb₀ : b₀ ≤ 1) → (hN : 0 ≤ N) → (hD : 0 < D) →
      ∀ (H : ℕ), (hH : 0 < H) →
      (hHD : (H : ℝ) ≤ D) → ∀ (c₁ c₂ : Fin H → ℂ)
        (y : BourgainPhaseSpace),
      12 * N ≤ (H : ℝ) ^ (2 : ℕ) →
      (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootExactLocalSum H D a₀ c₁ (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b₀ c₂ (x + y)‖ ^
              (6 : ℕ))) ≤
        (1024 : ENNReal) *
          (ENNReal.ofReal
              |(3 * (b₀ - a₀) ^ (4 : ℕ) /
                (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
            ENNReal.ofReal |(((H : ℝ) / D) ^ (6 : ℕ))⁻¹| *
            ENNReal.ofReal
              ((H : ℝ) ^ (8 : ℕ) *
                (C * (H : ℝ) ^ ε *
                  (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                  (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) +
            ENNReal.ofReal
                (bourgainSquareRootBilinearTaylorError
                  N a₀ b₀ ((H : ℝ) / D) c₁ c₂) *
              ENNReal.ofReal ((2 * N) ^ (4 : ℕ))) := by
  obtain ⟨C, hC, hlocal⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_bilinear_application hε
  refine ⟨C, hC, ?_⟩
  intro a₀ b₀ N D ha₀ ha₀b₀ hb₀ hN hD H hH hHD c₁ c₂ y hphysical
  let c₁' :=
    bourgainSquareRootExactLocalTranslateCoefficients H D a₀ c₁ y
  let c₂' :=
    bourgainSquareRootExactLocalTranslateCoefficients H D b₀ c₂ y
  have hbound :=
    hlocal ha₀ ha₀b₀ hb₀ hN hD H hH hHD c₁' c₂' hphysical
  calc
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootExactLocalSum H D a₀ c₁ (x + y)‖ ^
                (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b₀ c₂ (x + y)‖ ^
              (6 : ℕ))) =
      ∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (‖bourgainSquareRootExactLocalSum H D a₀ c₁' x‖ ^ (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b₀ c₂' x‖ ^
              (6 : ℕ)) := by
      apply lintegral_congr
      intro x
      rw [bourgainSquareRootExactLocalSum_add,
        bourgainSquareRootExactLocalSum_add]
    _ ≤ _ := by
      simpa [c₁', c₂',
        bourgainSquareRootBilinearTaylorError_translateCoefficients] using
        hbound

end

end RHTower
