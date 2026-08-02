import GaloisForLFunctions.HTGeometry.TorusBoxDimension
import GaloisForLFunctions.HTGeometry.BoxDimensionBiLipschitz

/-!
# Box dimension of a bi-Lipschitz image of a phase torus

Combining the two-sided covering estimate of a phase torus with the bi-Lipschitz transfer of box
dimension: every bi-Lipschitz image of a `k`-dimensional phase torus has box dimension `k`.

This is the geometric half of the completed-orbit dimension theorem: the completed reporter orbit
of a finite frequency packet is such an image, so its Minkowski dimension is the rank of the
visible gap module.
-/

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The phase torus has finite covering numbers at every resolution. -/
theorem externalCoveringNumber_torus_finite (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, Metric.externalCoveringNumber δ.toNNReal (Set.univ : Set (UnitAddTorus k))
      ≤ (n : ℕ∞) := by
  set m : ℕ := ⌈1 / δ⌉₊ with hm
  have hinvpos : (0 : ℝ) < 1 / δ := by positivity
  have hmpos : 0 < m := Nat.ceil_pos.mpr hinvpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hge : (1 : ℝ) / δ ≤ m := Nat.le_ceil _
  have hradius : (1 : ℝ) / (2 * m) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ δ * m := by
      rw [div_le_iff₀ hδ] at hge
      nlinarith [hge]
    nlinarith [hδ.le, hmR]
  have hle : Real.toNNReal (1 / (2 * m)) ≤ δ.toNNReal := Real.toNNReal_mono hradius
  exact ⟨m ^ Fintype.card k,
    le_trans (Metric.externalCoveringNumber_anti hle) (externalCoveringNumber_torus_le m hmpos)⟩

/-- **The box dimension of a bi-Lipschitz image of a phase torus.** -/
theorem hasBoxDim_range_of_biLipschitz {Y : Type*} [PseudoMetricSpace Y]
    {f : UnitAddTorus k → Y} {L K : ℝ≥0} (hL : 0 < (L : ℝ)) (hK : 0 < (K : ℝ))
    (hlip : LipschitzWith L f) (hanti : AntilipschitzWith K f) :
    HasBoxDim (Set.range f) (Fintype.card k) := by
  have himage : Set.range f = f '' (Set.univ : Set (UnitAddTorus k)) := (Set.image_univ).symm
  rw [himage]
  refine hasBoxDim_image_of_covering_bounds (c₁ := (1 / 4 : ℝ) ^ Fintype.card k)
    (c₂ := (2 : ℝ) ^ Fintype.card k) (ε₀ := 1 / 4) hL hK hlip hanti
    (by positivity) (by positivity) (by norm_num)
    (fun δ hδ => externalCoveringNumber_torus_finite δ hδ)
    (fun δ hδ hδ₀ => le_coveringCard_torus hδ (le_of_lt hδ₀))
    (fun δ hδ hδ₀ => coveringCard_torus_le hδ (by linarith))

end

end GaloisForLFunctions.HTGeometry
