import GaloisForLFunctions.HTGeometry.ContinuousMapLocallyConvex

/-!
# Continuous functionals on a compact-open space of continuous maps are carried by a compact set

A continuous linear functional on a subspace of `C(X, ℂ)` with the compact-open topology is
dominated by the supremum seminorm of a single compact set: continuity at the origin produces a
basic neighbourhood `{h | ∀ x ∈ K, ‖h x‖ < ε}` on which the functional is bounded by one, and
homogeneity turns that into the bound `|f g| ≤ (2/ε)·sup_K ‖g‖`.

* `HTGeometry.exists_compact_dual_bound`.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace HTGeometry

variable {X : Type*} [TopologicalSpace X]

/-- **A continuous functional on a subspace of `C(X, ℂ)` is carried by a compact set.** -/
theorem exists_compact_dual_bound (V : Submodule ℝ C(X, ℂ)) (f : V →L[ℝ] ℝ) :
    ∃ (K : Set X) (C : ℝ), IsCompact K ∧ 0 ≤ C ∧
      ∀ (g : V) (M : ℝ), 0 ≤ M → (∀ x ∈ K, ‖(g : C(X, ℂ)) x‖ ≤ M) → |f g| ≤ C * M := by
  classical
  have hpre : f ⁻¹' (Metric.ball (0 : ℝ) 1) ∈ 𝓝 (0 : V) := by
    have hcont : ContinuousAt (fun v : V => f v) 0 := f.continuous.continuousAt
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (f (0 : V)) := by
      simpa using Metric.ball_mem_nhds (0 : ℝ) one_pos
    exact hcont hball
  rw [nhds_induced (Subtype.val : V → C(X, ℂ))] at hpre
  obtain ⟨U, hU, hUsub⟩ := hpre
  obtain ⟨⟨K, ε⟩, ⟨hK, hε⟩, hsub⟩ :=
    (hasBasis_nhds_zero_continuousMap (X := X)).mem_iff.mp (by simpa using hU)
  refine ⟨K, 2 / ε, hK, by positivity, ?_⟩
  intro g M hM hgM
  have hsmall : ∀ h : V, (∀ x ∈ K, ‖(h : C(X, ℂ)) x‖ < ε) → |f h| < 1 := by
    intro h hh
    have hmemU : (h : C(X, ℂ)) ∈ U := hsub hh
    have : h ∈ (Subtype.val : V → C(X, ℂ)) ⁻¹' U := hmemU
    have hfh := hUsub this
    simpa [Real.dist_eq] using hfh
  have key : ∀ r : ℝ, M < r → |f g| ≤ 2 * r / ε := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt hM hr
    set t : ℝ := ε / (2 * r) with ht
    have ht0 : 0 < t := by rw [ht]; positivity
    have hscale : ∀ x ∈ K, ‖((t • g : V) : C(X, ℂ)) x‖ < ε := by
      intro x hx
      have hval : ((t • g : V) : C(X, ℂ)) x = t • ((g : C(X, ℂ)) x) := by
        simp
      rw [hval, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have h1 : t * ‖(g : C(X, ℂ)) x‖ ≤ t * M := by
        exact mul_le_mul_of_nonneg_left (hgM x hx) ht0.le
      have h2 : t * M < ε := by
        rw [ht]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    have hlt := hsmall (t • g) hscale
    have hval : f (t • g) = t * f g := by
      rw [map_smul, smul_eq_mul]
    rw [hval, abs_mul, abs_of_pos ht0] at hlt
    have : |f g| < 1 / t := by
      rw [lt_div_iff₀ ht0]
      linarith
    have htinv : (1 : ℝ) / t = 2 * r / ε := by
      rw [ht]
      field_simp
    rw [htinv] at this
    exact this.le
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  have hlt : M < M + δ * ε / 2 := by nlinarith
  have := key (M + δ * ε / 2) hlt
  have heq : 2 * (M + δ * ε / 2) / ε = 2 / ε * M + δ := by
    field_simp
  linarith [heq ▸ this]

end HTGeometry
