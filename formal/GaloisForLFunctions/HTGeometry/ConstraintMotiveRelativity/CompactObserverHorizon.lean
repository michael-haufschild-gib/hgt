import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow

/-!
# The compact observer: local gauges and the cofinal horizon

A compact observer `K : H → Y` on an infinite-dimensional Hilbert source can be injective on every
member of a nested cofinal tower of finite-dimensional charts.  On each chart the observation floor

`σ(S) = min { ‖K x‖ : x ∈ S, ‖x‖ = 1 }`

is attained and positive, so the chart inverse exists with the exact reconstruction norm `σ(S)⁻¹`.
But the floors are antitone and tend to zero: a uniform floor would make `K` bounded below on the
whole space, and a compact operator bounded below has finite-dimensional domain.  Consequently no
bounded left inverse exists at all.

The positive Gram shadow `K*K` has the same floor, is invariant under output isometries, and the
observed image of every bounded source history has compact closure — while the source history
itself can be uniformly separated, as an orthonormal sequence is.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open Metric Set Filter Topology
open scoped InnerProductSpace

section CompactObserver

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]

/-- The unit sphere of a source chart, inside the ambient space. -/
def chartSphere (S : Submodule 𝕜 H) : Set H := {x : H | x ∈ S ∧ ‖x‖ = 1}

/-- **`(COH.3)`.**  The observation floor of a source chart. -/
noncomputable def obsFloor (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) : ℝ :=
  sInf ((fun x => ‖K x‖) '' chartSphere S)

theorem bddBelow_obsSet (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) :
    BddBelow ((fun x => ‖K x‖) '' chartSphere S) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, -, rfl⟩
  exact norm_nonneg _

theorem obsFloor_nonneg (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) : 0 ≤ obsFloor K S := by
  rw [obsFloor]
  rcases Set.eq_empty_or_nonempty ((fun x => ‖K x‖) '' chartSphere S) with h | h
  · rw [h]; simp
  · exact le_csInf h (by rintro y ⟨x, -, rfl⟩; exact norm_nonneg _)

theorem obsFloor_le_of_mem {K : H →L[𝕜] Y} {S : Submodule 𝕜 H} {x : H} (hx : x ∈ S)
    (hnx : ‖x‖ = 1) : obsFloor K S ≤ ‖K x‖ :=
  csInf_le (bddBelow_obsSet K S) ⟨x, ⟨hx, hnx⟩, rfl⟩

/-- The floor is the exact chart coercivity constant. -/
theorem obsFloor_mul_le {K : H →L[𝕜] Y} {S : Submodule 𝕜 H} {x : H} (hx : x ∈ S) :
    obsFloor K S * ‖x‖ ≤ ‖K x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
    have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
    set u : H := ((‖x‖ : 𝕜))⁻¹ • x with hu
    have huS : u ∈ S := S.smul_mem _ hx
    have hnu : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos,
        inv_mul_cancel₀ hnx]
    have hle := obsFloor_le_of_mem (K := K) huS hnu
    have hKu : ‖K u‖ = (‖x‖ : ℝ)⁻¹ * ‖K x‖ := by
      rw [hu, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos]
    rw [hKu] at hle
    rw [← le_div_iff₀ hpos, div_eq_inv_mul]
    calc obsFloor K S ≤ (‖x‖ : ℝ)⁻¹ * ‖K x‖ := hle
      _ = (‖x‖ : ℝ)⁻¹ * ‖K x‖ := rfl

theorem chartSphere_eq_image (S : Submodule 𝕜 H) :
    chartSphere S = (S.subtypeL) '' (Metric.sphere (0 : S) 1) := by
  ext x
  constructor
  · rintro ⟨hxS, hxn⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    simpa [mem_sphere_iff_norm] using hxn
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    simpa [mem_sphere_iff_norm] using hy

/-- **`(COH.3)`, attainment.**  On a nonzero finite-dimensional chart the floor is attained. -/
theorem exists_norm_eq_obsFloor (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) [FiniteDimensional 𝕜 S]
    [Nontrivial S] : ∃ x ∈ chartSphere S, ‖K x‖ = obsFloor K S := by
  have hcpt : IsCompact (chartSphere (𝕜 := 𝕜) S) := by
    rw [chartSphere_eq_image]
    exact (isCompact_sphere (0 : S) 1).image (S.subtypeL).continuous
  have hne : (chartSphere (𝕜 := 𝕜) S).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : S)
    have hv0 : (v : H) ≠ 0 := fun h => hv (Subtype.ext h)
    have hpos : (0 : ℝ) < ‖(v : H)‖ := norm_pos_iff.2 hv0
    refine ⟨((‖(v : H)‖ : 𝕜))⁻¹ • (v : H), S.smul_mem _ v.2, ?_⟩
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos,
      inv_mul_cancel₀ hpos.ne']
  obtain ⟨x, hx, hmin⟩ := hcpt.exists_isMinOn hne
    (Continuous.continuousOn (by continuity : Continuous fun x : H => ‖K x‖))
  refine ⟨x, hx, ?_⟩
  refine le_antisymm ?_ (obsFloor_le_of_mem hx.1 hx.2)
  refine le_csInf (hne.image _) ?_
  rintro y ⟨z, hz, rfl⟩
  exact hmin hz

/-- **`(COH.3)`, positivity.**  Injectivity on the chart makes the floor positive. -/
theorem obsFloor_pos (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) [FiniteDimensional 𝕜 S] [Nontrivial S]
    (hinj : ∀ x ∈ S, K x = 0 → x = 0) : 0 < obsFloor K S := by
  obtain ⟨x, hx, hval⟩ := exists_norm_eq_obsFloor K S
  have hx0 : x ≠ 0 := by
    intro h
    have := hx.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hKx : K x ≠ 0 := fun h => hx0 (hinj x hx.1 h)
  rw [← hval]
  exact norm_pos_iff.2 hKx

/-- **`(COH.3)`, monotonicity.**  A larger chart has a smaller floor, provided the smaller chart
carries a unit vector.  Nonemptiness is necessary: the floor of the zero chart is the infimum of
the empty set, namely `0`, which no positive floor of a larger chart can lie below. -/
theorem obsFloor_antitone (K : H →L[𝕜] Y) {S T : Submodule 𝕜 H} (hST : S ≤ T)
    (hS : (chartSphere (𝕜 := 𝕜) S).Nonempty) :
    obsFloor K T ≤ obsFloor K S := by
  obtain ⟨x₀, hx₀⟩ := hS
  refine le_csInf ⟨‖K x₀‖, ⟨x₀, hx₀, rfl⟩⟩ ?_
  rintro y ⟨x, hx, rfl⟩
  exact obsFloor_le_of_mem (hST hx.1) hx.2

/-- **`(COH.3a)`.**  On a chart with positive floor the reconstruction norm is exactly the inverse
floor: `σ(S)⁻¹` is the least constant bounding the source energy by the observed energy. -/
theorem isLeast_reconstruction_constant (K : H →L[𝕜] Y) (S : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 S] [Nontrivial S] (hpos : 0 < obsFloor K S) :
    IsLeast {c : ℝ | ∀ x ∈ S, ‖x‖ ≤ c * ‖K x‖} (obsFloor K S)⁻¹ := by
  constructor
  · intro x hx
    have h := obsFloor_mul_le (K := K) hx
    rw [← le_div_iff₀' hpos] at h
    rw [inv_mul_eq_div]
    exact h
  · intro c hc
    obtain ⟨x, hx, hval⟩ := exists_norm_eq_obsFloor K S
    have h := hc x hx.1
    rw [hx.2, hval] at h
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith

end CompactObserver

end HTGeometry.ConstraintMotiveRelativity
