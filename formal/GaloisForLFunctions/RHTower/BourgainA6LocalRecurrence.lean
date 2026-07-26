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
  have hin : ∀ c : Fin 3,
      (0 : ℝ) ≤ (2 : ℝ) ^ (12 : ℕ) *
          ∑ i ∈ bourgainColorBlockFinset K c, ‖f i x‖ ^ (12 : ℕ) +
        ((bourgainColorBlockFinset K c).card : ℝ) ^ (18 : ℕ) *
          ∑ i ∈ bourgainColorBlockFinset K c,
            ∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
              ‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ) := by
    intro c; positivity
  have hsum1 : ∀ c : Fin 3,
      ENNReal.ofReal (∑ i ∈ bourgainColorBlockFinset K c, ‖f i x‖ ^ (12 : ℕ))
        = ∑ i ∈ bourgainColorBlockFinset K c, ENNReal.ofReal (‖f i x‖ ^ (12 : ℕ)) :=
    fun c => ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)
  have hsum2 : ∀ (c : Fin 3) (i : Fin K),
      ENNReal.ofReal
          (∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
            ‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ))
        = ∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
            ENNReal.ofReal (‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ)) :=
    fun c i => ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)
  have hsum3 : ∀ c : Fin 3,
      ENNReal.ofReal
          (∑ i ∈ bourgainColorBlockFinset K c,
            ∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
              ‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ))
        = ∑ i ∈ bourgainColorBlockFinset K c,
            ∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
              ENNReal.ofReal (‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ)) := by
    intro c
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    exact Finset.sum_congr rfl fun i _ => hsum2 c i
  have hcard : ∀ c : Fin 3,
      ENNReal.ofReal (((bourgainColorBlockFinset K c).card : ℝ) ^ (18 : ℕ))
        = (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^ (18 : ℕ) := by
    intro c
    rw [ENNReal.ofReal_pow (by positivity)]
    simp
  unfold bourgainThreeColorBilinearMajorant
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun c _ => hin c)]
  congr 1
  · norm_num
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    hsum1 c, hsum3 c, hcard c]
  norm_num

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

/-- Exact evaluation of the integrated `ENNReal` majorant as its diagonal
and separated-pair local moments. -/
theorem setLIntegral_bourgainA6LocalMajorantENN_eq
    (Λ N K M q₀ : ℕ) (y : BourgainPhaseSpace) :
    (∫⁻ x in
      {x : BourgainPhaseSpace |
        ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
      bourgainA6LocalMajorantENN N K M q₀ y x) =
      (3 : ENNReal) ^ (11 : ℕ) *
        (bourgainA6ThreeColorDiagonalLocalMoment Λ N K M q₀ y +
          bourgainA6ThreeColorPairLocalMoment Λ N K M q₀ y) := by
  let μ : Measure BourgainPhaseSpace :=
    volume.restrict
      {x : BourgainPhaseSpace |
        ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M}
  have hblock (i : Fin K) :
      Continuous
        (fun x : BourgainPhaseSpace =>
          bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
            (fun _ => 1) (x + y)) :=
    (continuous_bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
      (fun _ => 1)).comp (continuous_id.add continuous_const)
  have hdiag (i : Fin K) :
      AEMeasurable
        (fun x : BourgainPhaseSpace =>
          ENNReal.ofReal
            (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
                (fun _ => 1) (x + y)‖ ^ (12 : ℕ))) μ :=
    (ENNReal.continuous_ofReal.comp ((hblock i).norm.pow 12)).aemeasurable
  have hpair (i j : Fin K) :
      AEMeasurable
        (fun x : BourgainPhaseSpace =>
          ENNReal.ofReal
            (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
                (fun _ => 1) (x + y)‖ ^ (6 : ℕ) *
              ‖bourgainA6PhysicalBlockSum N M (q₀ + M * j.1)
                (fun _ => 1) (x + y)‖ ^ (6 : ℕ))) μ :=
    (ENNReal.continuous_ofReal.comp
      (((hblock i).norm.pow 6).mul ((hblock j).norm.pow 6))).aemeasurable
  have hdiagSum (c : Fin 3) :
      AEMeasurable
        (fun x : BourgainPhaseSpace =>
          ∑ i ∈ bourgainColorBlockFinset K c,
            ENNReal.ofReal
              (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
                  (fun _ => 1) (x + y)‖ ^ (12 : ℕ))) μ :=
    Finset.aemeasurable_fun_sum _ fun i _ => hdiag i
  have hpairInner (c : Fin 3) (i : Fin K) :
      AEMeasurable
        (fun x : BourgainPhaseSpace =>
          ∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
            ENNReal.ofReal
              (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
                  (fun _ => 1) (x + y)‖ ^ (6 : ℕ) *
                ‖bourgainA6PhysicalBlockSum N M (q₀ + M * j.1)
                  (fun _ => 1) (x + y)‖ ^ (6 : ℕ))) μ :=
    Finset.aemeasurable_fun_sum _ fun j _ => hpair i j
  have hpairSum (c : Fin 3) :
      AEMeasurable
        (fun x : BourgainPhaseSpace =>
          ∑ i ∈ bourgainColorBlockFinset K c,
            ∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
              ENNReal.ofReal
                (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
                    (fun _ => 1) (x + y)‖ ^ (6 : ℕ) *
                  ‖bourgainA6PhysicalBlockSum N M (q₀ + M * j.1)
                    (fun _ => 1) (x + y)‖ ^ (6 : ℕ))) μ :=
    Finset.aemeasurable_fun_sum _ fun i _ => hpairInner c i
  have hcolor (c : Fin 3) :
      AEMeasurable
        (fun x : BourgainPhaseSpace =>
          (2 : ENNReal) ^ (12 : ℕ) *
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
                        (fun _ => 1) (x + y)‖ ^ (6 : ℕ))) μ :=
    ((hdiagSum c).const_mul ((2 : ENNReal) ^ (12 : ℕ))).add
      ((hpairSum c).const_mul
        ((((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^
          (18 : ℕ)))
  change (∫⁻ x, bourgainA6LocalMajorantENN N K M q₀ y x ∂μ) = _
  unfold bourgainA6LocalMajorantENN
  rw [lintegral_const_mul' _ _ (by finiteness)]
  rw [lintegral_finsetSum' Finset.univ (fun c _ => hcolor c)]
  congr 1
  unfold bourgainA6ThreeColorDiagonalLocalMoment
    bourgainA6ThreeColorPairLocalMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [lintegral_add_left'
    ((hdiagSum c).const_mul ((2 : ENNReal) ^ (12 : ℕ)))]
  congr 1
  · rw [lintegral_const_mul' _ _ (by finiteness)]
    rw [lintegral_finsetSum'
      (bourgainColorBlockFinset K c) (fun i _ => hdiag i)]
    rfl
  · rw [lintegral_const_mul' _ _ (by finiteness)]
    rw [lintegral_finsetSum'
      (bourgainColorBlockFinset K c) (fun i _ => hpairInner c i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_finsetSum'
      ((bourgainColorBlockFinset K c).filter (fun j => j ≠ i))
      (fun j _ => hpair i j)]
    rfl

/-- Integrated one-step three-color recurrence: complete local family
moment is bounded by diagonal block moments plus separated pair moments. -/
theorem bourgainA6BlockFamilyLocalMoment_le_diagonal_add_pair
    (Λ N K M q₀ : ℕ) (y : BourgainPhaseSpace) :
    bourgainA6BlockFamilyLocalMoment Λ N K M q₀ y ≤
      (3 : ENNReal) ^ (11 : ℕ) *
        (bourgainA6ThreeColorDiagonalLocalMoment Λ N K M q₀ y +
          bourgainA6ThreeColorPairLocalMoment Λ N K M q₀ y) := by
  unfold bourgainA6BlockFamilyLocalMoment
  calc
    (∫⁻ x in
      {x : BourgainPhaseSpace |
        ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
      ENNReal.ofReal
        (‖bourgainA6BlockFamilySum N K M q₀ (x + y)‖ ^
          (12 : ℕ))) ≤
        ∫⁻ x in
          {x : BourgainPhaseSpace |
            ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
          bourgainA6LocalMajorantENN N K M q₀ y x := by
            apply lintegral_mono
            exact fun x =>
              ofReal_norm_bourgainA6BlockFamilySum_pow_twelve_le_localMajorant
                N K M q₀ y x
    _ = _ := setLIntegral_bourgainA6LocalMajorantENN_eq Λ N K M q₀ y

/-- Recurrence-ready form with every off-diagonal term replaced by the
uniform local power estimate.  Only diagonal smaller-block moments remain
to be closed by multiscale iteration. -/
theorem bourgainA6BlockFamilyLocalMoment_le_diagonal_add_power
    {ε : ℝ} (hε : 0 < ε) :
    ∀ Λ : ℕ, 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K M q₀ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₀ : 0 < q₀) → (hinside : q₀ + M * K ≤ N) →
        (hstart : N ≤ Λ * q₀) →
      ∀ y : BourgainPhaseSpace,
      bourgainA6BlockFamilyLocalMoment Λ N K M q₀ y ≤
        (3 : ENNReal) ^ (11 : ℕ) *
          (bourgainA6ThreeColorDiagonalLocalMoment Λ N K M q₀ y +
            (3 : ENNReal) * (K : ENNReal) ^ (20 : ℕ) *
              ENNReal.ofReal
                (C * (N : ℝ) ^ (10 : ℕ) *
                  (M : ℝ) ^ (4 + ε))) := by
  intro Λ hΛ
  obtain ⟨C, hC, hpair⟩ :=
    bourgainA6ThreeColorPairLocalMoment_power hε Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro N K M q₀ hN hM hMN hM2N hq₀ hinside hstart y
  refine (bourgainA6BlockFamilyLocalMoment_le_diagonal_add_pair
    Λ N K M q₀ y).trans ?_
  gcongr
  exact hpair N K M q₀ hN hM hMN hM2N hq₀ hinside hstart y

end

end RHTower
