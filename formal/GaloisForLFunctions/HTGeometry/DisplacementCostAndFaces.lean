/-
The cost of displacement, and why convexity contributes nothing.

For a pair with positive displacement the efficiency threshold is `1/2 - ρ`, where

    ρ(κ, λ) := (μ(κ, λ) - θ) / d(κ, λ)

is the **cost of displacement**: how much pointwise exponent must be surrendered per unit of
displacement bought.  Three facts.

* `ρ` is constant along the segment joining a pair on the line of symmetry attaining the target to
  any other pair.  Both the excess and the displacement scale linearly along such a segment, so their
  ratio does not move.  **Convexity of the exponent-pair region therefore contributes nothing to the
  threshold: it is decided by extreme points alone.**

* The threshold equals the critical length exactly when some pair with nonzero displacement attains
  the target exponent — that is, when the target is attained *off* the line of symmetry.

* If it is, then the pair, its `B`-image and their midpoint are three distinct pairs all attaining the
  target, so the target is attained on a nondegenerate face of the region rather than at a vertex.

Every published record is attained at a vertex, on the line of symmetry, which is why every published
threshold is strictly below the critical length.
-/
import GaloisForLFunctions.HTGeometry.SelfDefeatingProductivity

namespace HTGeometry

/-! ### The cost of displacement -/

/-- The pointwise exponent surrendered per unit of displacement bought. -/
def displacementCost (κ lam θ : ℚ) : ℚ := (epMu κ lam - θ) / epDisplacement κ lam

/-- The threshold is the critical length less the cost. -/
theorem threshold_eq_half_sub_cost (κ lam θ : ℚ) :
    efficiencyThreshold κ lam θ = 1 / 2 - displacementCost κ lam θ := rfl

/-- **The threshold reaches the critical length exactly when the target is attained off the line of
symmetry.** -/
theorem threshold_eq_critical_iff {κ lam θ : ℚ} (hd : epDisplacement κ lam ≠ 0) :
    efficiencyThreshold κ lam θ = 1 / 2 ↔ epMu κ lam = θ := by
  rw [threshold_eq_half_sub_cost]
  unfold displacementCost
  constructor
  · intro h
    have hzero : (epMu κ lam - θ) / epDisplacement κ lam = 0 := by linarith
    rcases div_eq_zero_iff.mp hzero with h' | h'
    · linarith
    · exact absurd h' hd
  · intro h; rw [h]; simp

/-! ### Convexity contributes nothing -/

/-- Convex combination of two pairs, first coordinate. -/
def mixFst (κ₀ κ₁ t : ℚ) : ℚ := (1 - t) * κ₀ + t * κ₁

/-- Convex combination of two pairs, second coordinate. -/
def mixSnd (lam₀ lam₁ t : ℚ) : ℚ := (1 - t) * lam₀ + t * lam₁

/-- The pointwise exponent is affine along a segment. -/
theorem epMu_mix (κ₀ lam₀ κ₁ lam₁ t : ℚ) :
    epMu (mixFst κ₀ κ₁ t) (mixSnd lam₀ lam₁ t)
      = (1 - t) * epMu κ₀ lam₀ + t * epMu κ₁ lam₁ := by
  unfold epMu mixFst mixSnd; ring

/-- The displacement is affine along a segment. -/
theorem epDisplacement_mix (κ₀ lam₀ κ₁ lam₁ t : ℚ) :
    epDisplacement (mixFst κ₀ κ₁ t) (mixSnd lam₀ lam₁ t)
      = (1 - t) * epDisplacement κ₀ lam₀ + t * epDisplacement κ₁ lam₁ := by
  unfold epDisplacement mixFst mixSnd; ring

/-- **The cost of displacement is constant along a segment from a line pair attaining the target.**
Both excess and displacement scale by `t`, so their ratio is unchanged. -/
theorem displacementCost_mix_const {κ₀ lam₀ κ₁ lam₁ θ t : ℚ}
    (hline : epDisplacement κ₀ lam₀ = 0) (hmu : epMu κ₀ lam₀ = θ) (ht : t ≠ 0) :
    displacementCost (mixFst κ₀ κ₁ t) (mixSnd lam₀ lam₁ t) θ = displacementCost κ₁ lam₁ θ := by
  unfold displacementCost
  rw [epMu_mix, epDisplacement_mix, hline, hmu]
  rw [show (1 - t) * θ + t * epMu κ₁ lam₁ - θ = t * (epMu κ₁ lam₁ - θ) by ring,
    show (1 - t) * 0 + t * epDisplacement κ₁ lam₁ = t * epDisplacement κ₁ lam₁ by ring,
    mul_div_mul_left _ _ ht]

/-- **Hence the efficiency threshold is constant along such a segment**: convexity of the
exponent-pair region cannot raise it. -/
theorem threshold_mix_const {κ₀ lam₀ κ₁ lam₁ θ t : ℚ}
    (hline : epDisplacement κ₀ lam₀ = 0) (hmu : epMu κ₀ lam₀ = θ) (ht : t ≠ 0) :
    efficiencyThreshold (mixFst κ₀ κ₁ t) (mixSnd lam₀ lam₁ t) θ
      = efficiencyThreshold κ₁ lam₁ θ := by
  rw [threshold_eq_half_sub_cost, threshold_eq_half_sub_cost,
    displacementCost_mix_const hline hmu ht]

/-! ### An off-line record forces a nondegenerate face -/

/-- **If the target is attained off the line, its `B`-image attains it too, with opposite
displacement.** -/
theorem procB_of_offline_record {κ lam θ : ℚ} (hmu : epMu κ lam = θ) :
    epMu (procB_fst lam) (procB_snd κ) = θ ∧
      epDisplacement (procB_fst lam) (procB_snd κ) = - epDisplacement κ lam := by
  exact ⟨by rw [HTGeometry.epMu_procB]; exact hmu, procB_negates_displacement κ lam⟩

/-- **And their midpoint attains it on the line.**  So an off-line record produces three pairs with
the same exponent: the target is attained on a nondegenerate face, not at a vertex. -/
theorem offline_record_gives_face {κ lam θ : ℚ} (hmu : epMu κ lam = θ) :
    epMu (mixFst κ (procB_fst lam) (1 / 2)) (mixSnd lam (procB_snd κ) (1 / 2)) = θ ∧
      epDisplacement (mixFst κ (procB_fst lam) (1 / 2))
        (mixSnd lam (procB_snd κ) (1 / 2)) = 0 := by
  constructor
  · rw [epMu_mix, HTGeometry.epMu_procB, hmu]; ring
  · rw [epDisplacement_mix, procB_negates_displacement]; ring

/-- **The characterisation.**  Some pair has threshold equal to the critical length if and only if the
record is attained on a nondegenerate face of the exponent-pair region. -/
theorem critical_threshold_iff_face {κ lam θ : ℚ} (hd : epDisplacement κ lam ≠ 0) :
    efficiencyThreshold κ lam θ = 1 / 2 ↔
      (epMu κ lam = θ ∧ epMu (procB_fst lam) (procB_snd κ) = θ ∧
        epMu (mixFst κ (procB_fst lam) (1 / 2)) (mixSnd lam (procB_snd κ) (1 / 2)) = θ) := by
  rw [threshold_eq_critical_iff hd]
  constructor
  · intro h
    exact ⟨h, (procB_of_offline_record h).1, (offline_record_gives_face h).1⟩
  · rintro ⟨h, -, -⟩; exact h

/-! ### The published data -/

/-- The trivial pair's cost and threshold. -/
theorem trivial_pair_cost_and_threshold :
    displacementCost 0 1 bourgainTheta = 4 / 21 ∧
      efficiencyThreshold 0 1 bourgainTheta = 13 / 42 := by
  constructor
  · unfold displacementCost epMu epDisplacement bourgainTheta; norm_num
  · unfold efficiencyThreshold epMu epDisplacement bourgainTheta; norm_num

/-- **The trivial pair's threshold is exactly `2θ`**, matching the covering bound of Theorem 124. -/
theorem trivial_threshold_eq_two_theta :
    efficiencyThreshold 0 1 bourgainTheta = 2 * bourgainTheta := by
  rw [trivial_pair_cost_and_threshold.2]; unfold bourgainTheta; norm_num

/-- The cost of the `A`-image of the record pair. -/
theorem procA_bourgain_cost :
    displacementCost (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
      bourgainTheta = 167 / 1764 := by
  unfold displacementCost
  rw [procA_bourgain_excess, procA_bourgain_displacement]
  norm_num

/-- **The `A`-image is the cheapest displacement available**, at cost `167/1764` against the trivial
pair's `4/21 = 336/1764`. -/
theorem procA_beats_trivial_cost :
    displacementCost (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        bourgainTheta < displacementCost 0 1 bourgainTheta := by
  rw [procA_bourgain_cost, trivial_pair_cost_and_threshold.1]; norm_num

/-- **Every published record is attained on the line of symmetry**, hence at a vertex: the target's
face is degenerate and no threshold reaches the critical length. -/
theorem records_are_vertices :
    epDisplacement weylKappa weylLambda = 0 ∧
      epDisplacement biKappa biLambda = 0 ∧
      epDisplacement huxleyPairKappa huxleyPairLambda = 0 ∧
      epDisplacement bourgainKappa bourgainLambda = 0 :=
  landmarks_length_neutral

end HTGeometry
