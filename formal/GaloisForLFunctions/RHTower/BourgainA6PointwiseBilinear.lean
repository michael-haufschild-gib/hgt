/-
# Pointwise separated bilinear decomposition for `A₆` blocks

This module connects the exact normalized-curve block sums to the
Bourgain--Guth three-color decomposition.  Every off-diagonal pair in a
color class has the quantitative determinant bound from block geometry.
-/
import GaloisForLFunctions.RHTower.BourgainA6BlockLocalization
import GaloisForLFunctions.RHTower.BourgainIntegratedBilinearDecomposition

open MeasureTheory

namespace RHTower

noncomputable section

/-- Sum of `K` consecutive length-`M` blocks beginning at the positive
integer offset `q₀`. -/
def bourgainA6BlockFamilySum
    (N K M q₀ : ℕ) (x : BourgainPhaseSpace) : ℂ :=
  ∑ i : Fin K,
    bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
      (fun _ => 1) x

/-- Every finite exact block sum is continuous in physical phase space. -/
theorem continuous_bourgainA6PhysicalBlockSum
    (N M q : ℕ) (c : Fin M → ℂ) :
    Continuous (bourgainA6PhysicalBlockSum N M q c) := by
  unfold bourgainA6PhysicalBlockSum bourgainSquareRootCurvePhase
    bourgainSquareRootCurve bourgainDot bourgainUnitCharacter
  fun_prop

/-- A finite consecutive block family is continuous. -/
theorem continuous_bourgainA6BlockFamilySum
    (N K M q₀ : ℕ) :
    Continuous (bourgainA6BlockFamilySum N K M q₀) := by
  unfold bourgainA6BlockFamilySum
  fun_prop [continuous_bourgainA6PhysicalBlockSum]

/-- Literal three-color pointwise decomposition of a consecutive `A₆` block
family. -/
theorem norm_bourgainA6BlockFamilySum_pow_twelve_le_majorant
    (N K M q₀ : ℕ) (x : BourgainPhaseSpace) :
    ‖bourgainA6BlockFamilySum N K M q₀ x‖ ^ (12 : ℕ) ≤
      bourgainThreeColorBilinearMajorant K
        (fun i x =>
          bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
            (fun _ => 1) x) x := by
  exact norm_sum_pow_twelve_le_bourgainThreeColorBilinearMajorant
    K
    (fun i x =>
      bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
        (fun _ => 1) x)
    x

/-- Integrated three-color decomposition on a physical norm ball.  All
integrability hypotheses are discharged by continuity and compactness. -/
theorem integral_bourgainA6BlockFamilySum_pow_twelve_le_majorant
    (N K M q₀ : ℕ) (R : ℝ) :
    (∫ x in Metric.closedBall (0 : BourgainPhaseSpace) R,
        ‖bourgainA6BlockFamilySum N K M q₀ x‖ ^ (12 : ℕ)) ≤
      ∫ x in Metric.closedBall (0 : BourgainPhaseSpace) R,
        bourgainThreeColorBilinearMajorant K
          (fun i x =>
            bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
              (fun _ => 1) x) x := by
  let f : Fin K → BourgainPhaseSpace → ℂ :=
    fun i x =>
      bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
        (fun _ => 1) x
  have hf (i : Fin K) : Continuous (f i) := by
    dsimp only [f]
    exact continuous_bourgainA6PhysicalBlockSum _ _ _ _
  have hleft :
      Integrable
        (fun x : BourgainPhaseSpace =>
          ‖∑ i : Fin K, f i x‖ ^ (12 : ℕ))
        (volume.restrict
          (Metric.closedBall (0 : BourgainPhaseSpace) R)) := by
    apply ContinuousOn.integrableOn_compact isCompact_closedBall
    fun_prop
  have hdiag :
      ∀ i : Fin K,
        Integrable (fun x => ‖f i x‖ ^ (12 : ℕ))
          (volume.restrict
            (Metric.closedBall (0 : BourgainPhaseSpace) R)) := by
    intro i
    apply ContinuousOn.integrableOn_compact isCompact_closedBall
    exact (hf i).norm.pow 12 |>.continuousOn
  have hpair :
      ∀ (c : Fin 3) (i : Fin K),
        i ∈ bourgainColorBlockFinset K c →
        ∀ j : Fin K,
          j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i) →
          Integrable
            (fun x => ‖f i x‖ ^ (6 : ℕ) * ‖f j x‖ ^ (6 : ℕ))
            (volume.restrict
              (Metric.closedBall (0 : BourgainPhaseSpace) R)) := by
    intro c i hi j hj
    apply ContinuousOn.integrableOn_compact isCompact_closedBall
    exact (((hf i).norm.pow 6).mul ((hf j).norm.pow 6)).continuousOn
  have h :=
    integral_norm_sum_pow_twelve_le_bourgainThreeColorBilinearMajorant
      (volume.restrict
        (Metric.closedBall (0 : BourgainPhaseSpace) R))
      K f hleft hdiag hpair
  simpa only [f, bourgainA6BlockFamilySum] using h

/-- Low start of an unordered block pair. -/
def bourgainA6PairLowStart
    (M q₀ : ℕ) {K : ℕ} (i j : Fin K) : ℕ :=
  q₀ + M * min i.1 j.1

/-- High start of an unordered block pair. -/
def bourgainA6PairHighStart
    (M q₀ : ℕ) {K : ℕ} (i j : Fin K) : ℕ :=
  q₀ + M * max i.1 j.1

/-- A separated pair has at least one block-length gap between its ordered
starts. -/
theorem bourgainA6PairLowStart_add_le_highStart
    {K M q₀ : ℕ} {i j : Fin K}
    (hsep : BourgainSeparatedBlocks i j) :
    bourgainA6PairLowStart M q₀ i j + M ≤
      bourgainA6PairHighStart M q₀ i j := by
  unfold bourgainA6PairLowStart bourgainA6PairHighStart
  rcases hsep with hij | hji
  · rw [Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
    nlinarith
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega)]
    nlinarith

/-- Starts of every block in a family contained in `[q₀,N]` are at most
`N`. -/
theorem bourgainA6PairHighStart_le
    {N K M q₀ : ℕ} {i j : Fin K}
    (hinside : q₀ + M * K ≤ N) :
    bourgainA6PairHighStart M q₀ i j ≤ N := by
  unfold bourgainA6PairHighStart
  have hi : i.1 < K := i.2
  have hj : j.1 < K := j.2
  have hmax : max i.1 j.1 < K := by omega
  have hmul : M * max i.1 j.1 ≤ M * K :=
    Nat.mul_le_mul_left M hmax.le
  omega

/-- Every separated pair in a positive block family has the sharp reciprocal
phase-Jacobian bound, independent of pair location. -/
theorem abs_inv_bourgainA6PairPhaseDeterminant_le
    {N K M q₀ : ℕ} (hN : 0 < N) (hM : 0 < M) (hq₀ : 0 < q₀)
    (hinside : q₀ + M * K ≤ N)
    {i j : Fin K} (hsep : BourgainSeparatedBlocks i j) :
    |(bourgainA6BlockPhaseDeterminant N M
        (bourgainA6PairLowStart M q₀ i j)
        (bourgainA6PairHighStart M q₀ i j))⁻¹| ≤
      (512 / 3 : ℝ) * ((N : ℝ) / (M : ℝ)) ^ (10 : ℕ) := by
  apply abs_inv_bourgainA6BlockPhaseDeterminant_le hN hM
  · unfold bourgainA6PairLowStart
    omega
  · exact bourgainA6PairLowStart_add_le_highStart hsep
  · exact bourgainA6PairHighStart_le hinside

/-- Off-diagonal pairs produced by one color class automatically satisfy the
uniform reciprocal-Jacobian estimate. -/
theorem abs_inv_bourgainA6PairPhaseDeterminant_le_of_color
    {N K M q₀ : ℕ} (hN : 0 < N) (hM : 0 < M) (hq₀ : 0 < q₀)
    (hinside : q₀ + M * K ≤ N)
    {c : Fin 3} {i j : Fin K}
    (hi : i ∈ bourgainColorBlockFinset K c)
    (hj : j ∈
      (bourgainColorBlockFinset K c).filter (fun j => j ≠ i)) :
    |(bourgainA6BlockPhaseDeterminant N M
        (bourgainA6PairLowStart M q₀ i j)
        (bourgainA6PairHighStart M q₀ i j))⁻¹| ≤
      (512 / 3 : ℝ) * ((N : ℝ) / (M : ℝ)) ^ (10 : ℕ) := by
  exact abs_inv_bourgainA6PairPhaseDeterminant_le
    hN hM hq₀ hinside
    (separated_of_mem_colorBlock_filter_ne hi hj)

end

end RHTower
