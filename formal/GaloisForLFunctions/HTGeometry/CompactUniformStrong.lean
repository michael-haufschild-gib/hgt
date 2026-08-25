import Mathlib

/-!
# Uniform convergence on compact operator images

A uniformly contractive family indexed by finite coordinate sets and converging strongly to zero
converges in operator norm after composition with any compact operator. The source and target
spaces may differ.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X Y ι : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Uniform smallness on a compact image for a finite-set-indexed strong-null family. -/
theorem tendsto_norm_comp_of_isCompactOperator_finset
    (Q : Finset ι → Y →L[ℂ] Y) (hbdd : ∀ P, ‖Q P‖ ≤ 1)
    (hptw : ∀ y : Y, Tendsto (fun P => Q P y) atTop (nhds 0))
    (B : X →L[ℂ] Y) (hB : IsCompactOperator B) :
    Tendsto (fun P => ‖Q P ∘L B‖) atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set S : Set Y := closure (B '' Metric.closedBall 0 1) with hS
  have hScompact : IsCompact S := hB.isCompact_closure_image_closedBall 1
  have hStb : TotallyBounded S := hScompact.totallyBounded
  obtain ⟨t, htfin, htcover⟩ :=
    (Metric.totallyBounded_iff.mp hStb) (ε / 3) (by linarith)
  have hfin : ∀ᶠ P : Finset ι in atTop, ∀ y ∈ htfin.toFinset, ‖Q P y‖ < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro y hy
    have h := (hptw y).norm
    rw [norm_zero] at h
    exact h.eventually_lt_const (by linarith)
  obtain ⟨F, hF⟩ := Filter.eventually_atTop.mp hfin
  refine ⟨F, fun P hFP => ?_⟩
  have hbound : ‖Q P ∘L B‖ ≤ 2 * ε / 3 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hxc : ((‖x‖ : ℂ)) ≠ 0 := by simpa using hxpos.ne'
      set u : X := ((‖x‖ : ℂ))⁻¹ • x with hu
      have hunorm : ‖u‖ = 1 := by
        rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hxpos.ne']
      have hxu : ((‖x‖ : ℂ)) • u = x := by
        rw [hu, smul_smul, mul_inv_cancel₀ hxc, one_smul]
      have hmem : B u ∈ S := by
        refine subset_closure ⟨u, ?_, rfl⟩
        simp [Metric.mem_closedBall, hunorm]
      obtain ⟨y, hy, hdist⟩ := Set.mem_iUnion₂.mp (htcover hmem)
      have hyfin : y ∈ htfin.toFinset := htfin.mem_toFinset.mpr hy
      have h1 : ‖Q P (B u)‖ ≤ ‖Q P (B u - y)‖ + ‖Q P y‖ := by
        have : Q P (B u) = Q P (B u - y) + Q P y := by
          rw [← map_add]
          congr 1
          abel
        rw [this]
        exact norm_add_le _ _
      have h2 : ‖Q P (B u - y)‖ ≤ ε / 3 := by
        refine le_trans ((Q P).le_opNorm _) ?_
        have h3 : ‖B u - y‖ < ε / 3 := by
          simpa [Metric.mem_ball, dist_eq_norm] using hdist
        calc
          ‖Q P‖ * ‖B u - y‖ ≤ 1 * ‖B u - y‖ :=
            mul_le_mul_of_nonneg_right (hbdd P) (norm_nonneg _)
          _ = ‖B u - y‖ := one_mul _
          _ ≤ ε / 3 := h3.le
      have h4 : ‖Q P y‖ < ε / 3 := hF P hFP y hyfin
      have hu' : ‖Q P (B u)‖ ≤ 2 * ε / 3 := by linarith
      have h5 : Q P (B (((‖x‖ : ℂ)) • u)) = ((‖x‖ : ℂ)) • Q P (B u) := by
        rw [map_smul, map_smul]
      have hscale : (Q P ∘L B) x = ((‖x‖ : ℂ)) • Q P (B u) := by
        rw [← h5, hxu]
        rfl
      rw [hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      calc
        ‖x‖ * ‖Q P (B u)‖ ≤ ‖x‖ * (2 * ε / 3) :=
          mul_le_mul_of_nonneg_left hu' (norm_nonneg _)
        _ = 2 * ε / 3 * ‖x‖ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

end

end GaloisForLFunctions.HTGeometry
