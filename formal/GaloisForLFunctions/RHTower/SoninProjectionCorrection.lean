/-
Projection correction for a pair of Hilbert-space constraints.

For closed forbidden subspaces `A` and `B`, the common admissible space is
`Aᗮ ⊓ Bᗮ`.  If the forbidden-forbidden block `P_B P_A P_B` has norm below one,
then every vector already satisfying the first constraint can be corrected into the common
kernel, with a quantitative bound controlled by its violation of the second constraint.

This is the abstract projection step used for Sonin spaces: the two forbidden subspaces are the
physical and Fourier cutoff ranges.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace RHTower

open ContinuousLinearMap
open Filter Topology

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [Nontrivial H]

/-- The forbidden-forbidden compression associated to two orthogonal constraints. -/
def soninAlternatingBlock (A B : Submodule 𝕜 H)
    [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] : H →L[𝕜] H :=
  B.starProjection * A.starProjection * B.starProjection

/-- The orthogonal projection onto the common kernel of two constraints. -/
def soninIntersectionProjection (A B : Submodule 𝕜 H)
    [(Aᗮ ⊓ Bᗮ).HasOrthogonalProjection] : H →L[𝕜] H :=
  (Aᗮ ⊓ Bᗮ).starProjection

/-- A vector in the kernel of the first projection can be corrected into the intersection of both
kernels whenever the forbidden-forbidden compression is a strict contraction. -/
theorem exists_soninIntersection_correction
    (A B : Submodule 𝕜 H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1) {x : H} (hx : x ∈ Aᗮ) :
    ∃ z ∈ Aᗮ ⊓ Bᗮ,
      ‖x - z‖ ≤ (1 - ‖soninAlternatingBlock A B‖)⁻¹ * ‖B.starProjection x‖ := by
  let T : H →L[𝕜] H := soninAlternatingBlock A B
  let e : (H →L[𝕜] H)ˣ := Units.oneSub T (by simpa [T] using hT)
  let R : H →L[𝕜] H := (↑(e⁻¹) : H →L[𝕜] H)
  let u : H := R (B.starProjection x)
  let c : H := Aᗮ.starProjection u
  let z : H := x - c
  have hres : (1 - T) u = B.starProjection x := by
    change ((↑e : H →L[𝕜] H) * (↑(e⁻¹) : H →L[𝕜] H)) (B.starProjection x) =
      B.starProjection x
    rw [← Units.val_mul]
    simp
  have hres' : u - T u = B.starProjection x := by
    simpa using hres
  have hTu : T u ∈ B := by
    change B.starProjection (A.starProjection (B.starProjection u)) ∈ B
    exact B.starProjection_apply_mem _
  have huB : u ∈ B := by
    have hu : u = B.starProjection x + T u := sub_eq_iff_eq_add.mp hres'
    rw [hu]
    exact B.add_mem (B.starProjection_apply_mem _) hTu
  have hQu : B.starProjection u = u := B.starProjection_eq_self_iff.mpr huB
  have hTu_eq : T u = B.starProjection (A.starProjection u) := by
    change B.starProjection (A.starProjection (B.starProjection u)) = _
    rw [hQu]
  have hc : c = u - A.starProjection u := by
    simp [c]
  have hcB : B.starProjection c = B.starProjection x := by
    calc
      B.starProjection c = B.starProjection (u - A.starProjection u) := by rw [hc]
      _ = B.starProjection u - B.starProjection (A.starProjection u) := map_sub _ _ _
      _ = u - T u := by rw [hQu, hTu_eq]
      _ = B.starProjection x := hres'
  have hzmem : z ∈ Aᗮ ⊓ Bᗮ := by
    constructor
    · exact Aᗮ.sub_mem hx (Aᗮ.starProjection_apply_mem u)
    · exact B.starProjection_apply_eq_zero_iff.mp (by simp [z, hcB])
  refine ⟨z, hzmem, ?_⟩
  have hR : ‖R‖ ≤ (1 - ‖T‖)⁻¹ := by
    dsimp [R, e]
    change ‖∑' n : ℕ, T ^ n‖ ≤ (1 - ‖T‖)⁻¹
    simpa [ContinuousLinearMap.norm_id] using
      tsum_geometric_le_of_norm_lt_one T (by simpa [T] using hT)
  have hcu : ‖c‖ ≤ ‖u‖ := Aᗮ.norm_starProjection_apply_le u
  have hu : ‖u‖ ≤ ‖R‖ * ‖B.starProjection x‖ := by
    simpa [u] using R.le_opNorm (B.starProjection x)
  have hxz : x - z = c := by simp [z]
  rw [hxz]
  exact hcu.trans <| hu.trans <|
    mul_le_mul_of_nonneg_right hR (norm_nonneg _)

/-- Nearest-point form of `exists_soninIntersection_correction`: the actual orthogonal projection
onto the common kernel obeys the same bound. -/
theorem norm_sub_soninIntersectionProjection_le
    (A B : Submodule 𝕜 H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(Aᗮ ⊓ Bᗮ).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1) {x : H} (hx : x ∈ Aᗮ) :
    ‖x - soninIntersectionProjection A B x‖ ≤
      (1 - ‖soninAlternatingBlock A B‖)⁻¹ * ‖B.starProjection x‖ := by
  obtain ⟨z, hz, hbound⟩ := exists_soninIntersection_correction A B hT hx
  rw [soninIntersectionProjection, Submodule.starProjection_minimal]
  refine (ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
    (⟨z, hz⟩ : ↥(Aᗮ ⊓ Bᗮ))).trans ?_
  simpa using hbound

/-- If the second forbidden projection is norm-null on a sequence lying in the first kernel, then
the common-kernel projection asymptotically fixes that sequence. -/
theorem soninIntersectionProjection_tendsto_shell
    (A B : Submodule 𝕜 H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(Aᗮ ⊓ Bᗮ).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1) (g : ℕ → H)
    (hgA : ∀ n, g n ∈ Aᗮ)
    (hBnull : Filter.Tendsto (fun n => ‖B.starProjection (g n)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ‖soninIntersectionProjection A B (g n) - g n‖)
      Filter.atTop (𝓝 0) := by
  let C : ℝ := (1 - ‖soninAlternatingBlock A B‖)⁻¹
  have hupper : Filter.Tendsto (fun n => C * ‖B.starProjection (g n)‖)
      Filter.atTop (𝓝 0) := by
    simpa using hBnull.const_mul C
  apply squeeze_zero (fun n => norm_nonneg _) _ hupper
  intro n
  rw [norm_sub_rev]
  exact norm_sub_soninIntersectionProjection_le A B hT (hgA n)

end RHTower
