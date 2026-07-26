/-
# One-step local recurrence for the `A₆` block family

This file integrates the exact three-color pointwise decomposition on the
recurrence-scale local ball.  Diagonal twelfth moments remain explicit;
all separated off-diagonal terms are collected in the previously bounded
local pair majorant.
-/
import GaloisForLFunctions.RHTower.BourgainA6LocalMajorant

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Local translated twelfth moment of one block in an `A₆` family. -/
def bourgainA6SingleBlockLocalMoment
    (Λ N K M q₀ : ℕ) (i : Fin K)
    (y : BourgainPhaseSpace) : ENNReal :=
  ∫⁻ x in
    {x : BourgainPhaseSpace |
      ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
    ENNReal.ofReal
      (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
          (fun _ => 1) (x + y)‖ ^ (12 : ℕ))

/-- Weighted diagonal part of the integrated three-color majorant. -/
def bourgainA6ThreeColorDiagonalLocalMoment
    (Λ N K M q₀ : ℕ) (y : BourgainPhaseSpace) : ENNReal :=
  ∑ c : Fin 3,
    (2 : ENNReal) ^ (12 : ℕ) *
      ∑ i ∈ bourgainColorBlockFinset K c,
        bourgainA6SingleBlockLocalMoment Λ N K M q₀ i y

/-- Local translated twelfth moment of the complete block family. -/
def bourgainA6BlockFamilyLocalMoment
    (Λ N K M q₀ : ℕ) (y : BourgainPhaseSpace) : ENNReal :=
  ∫⁻ x in
    {x : BourgainPhaseSpace |
      ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
    ENNReal.ofReal
      (‖bourgainA6BlockFamilySum N K M q₀ (x + y)‖ ^ (12 : ℕ))

/-- `ENNReal` form of the three-color majorant for a translated physical
block family. -/
def bourgainA6LocalMajorantENN
    (N K M q₀ : ℕ) (y x : BourgainPhaseSpace) : ENNReal :=
  (3 : ENNReal) ^ (11 : ℕ) *
    ∑ c : Fin 3,
      ((2 : ENNReal) ^ (12 : ℕ) *
          ∑ i ∈ bourgainColorBlockFinset K c,
            ENNReal.ofReal
              (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
                  (fun _ => 1) (x + y)‖ ^ (12 : ℕ)) +
        (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^
            (18 : ℕ) *
          ∑ i ∈ bourgainColorBlockFinset K c,
            ∑ j ∈ (bourgainColorBlockFinset K c).filter
                (fun j => j ≠ i),
              ENNReal.ofReal
                (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
                    (fun _ => 1) (x + y)‖ ^ (6 : ℕ) *
                  ‖bourgainA6PhysicalBlockSum N M (q₀ + M * j.1)
                    (fun _ => 1) (x + y)‖ ^ (6 : ℕ)))

/-- `ENNReal.ofReal` turns the real three-color majorant into its exact
nonnegative finite-sum expression. -/
theorem ofReal_bourgainThreeColorBilinearMajorant_eq
    {Ω : Type*} (K : ℕ) (f : Fin K → Ω → ℂ) (x : Ω) :
    ENNReal.ofReal (bourgainThreeColorBilinearMajorant K f x) =
      (3 : ENNReal) ^ (11 : ℕ) *
        ∑ c : Fin 3,
          ((2 : ENNReal) ^ (12 : ℕ) *
              ∑ i ∈ bourgainColorBlockFinset K c,
                ENNReal.ofReal (‖f i x‖ ^ (12 : ℕ)) +
            (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^
                (18 : ℕ) *
              ∑ i ∈ bourgainColorBlockFinset K c,
                ∑ j ∈ (bourgainColorBlockFinset K c).filter
                    (fun j => j ≠ i),
                  ENNReal.ofReal
                    (‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ))) := by
  unfold bourgainThreeColorBilinearMajorant
  have hpow : ∀ (a : ℝ) (n : ℕ), 0 ≤ a → ENNReal.ofReal (a ^ n) = ENNReal.ofReal a ^ n :=
    fun a n ha => ENNReal.ofReal_pow ha n
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)]
  congr 1
  · norm_num
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  have h1 : ENNReal.ofReal ((2 : ℝ) ^ (12 : ℕ)) = (2 : ENNReal) ^ (12 : ℕ) := by
    norm_num
  have h2 : ENNReal.ofReal
      (((bourgainColorBlockFinset K c).card : ℝ) ^ (18 : ℕ))
      = (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^ (18 : ℕ) := by
    rw [hpow _ _ (by positivity)]
    simp
  rw [h1, h2]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)

/-- Pointwise `ENNReal` three-color decomposition for a translated `A₆`
block family. -/
theorem ofReal_norm_bourgainA6BlockFamilySum_pow_twelve_le_localMajorant
    (N K M q₀ : ℕ) (y x : BourgainPhaseSpace) :
    ENNReal.ofReal
        (‖bourgainA6BlockFamilySum N K M q₀ (x + y)‖ ^ (12 : ℕ)) ≤
      bourgainA6LocalMajorantENN N K M q₀ y x := by
  let f : Fin K → BourgainPhaseSpace → ℂ :=
    fun i z =>
      bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
        (fun _ => 1) z
  have hreal :=
    norm_bourgainA6BlockFamilySum_pow_twelve_le_majorant
      N K M q₀ (x + y)
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ofReal_bourgainThreeColorBilinearMajorant_eq K f (x + y)] at h
  simpa only [f, bourgainA6LocalMajorantENN] using h

end

end RHTower
