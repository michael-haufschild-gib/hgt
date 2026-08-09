import GaloisForLFunctions.HTGeometry.ContinuousMapLocallyConvex

/-!
# Every continuous functional on the compact-open space has a compact carrier

A continuous linear functional on `C(X, ℂ)` with the topology of uniform convergence on compact
sets is bounded by a multiple of the supremum over a single compact set.  Continuity at the origin
supplies a basic neighbourhood `{f : ∀ x ∈ K, ‖f x‖ < ε}` mapped into the unit ball, and scaling
turns that qualitative statement into the estimate.

This is the carrier existence behind the Fourier–Borel picture: the dual of a compact-open space of
functions consists of functionals living on compact subsets, so any statement proved for compactly
carried functionals applies to the whole dual.

* `HTGeometry.exists_compact_bound_of_continuousLinearMap`.
-/

open Filter Metric
open scoped Topology

namespace HTGeometry

variable {X : Type*} [TopologicalSpace X]

/-- **A continuous functional on the compact-open space is carried by a compact set.** -/
theorem exists_compact_bound_of_continuousLinearMap (L : C(X, ℂ) →L[ℂ] ℂ) :
    ∃ (K : Set X) (C : ℝ), IsCompact K ∧ 0 < C ∧
      ∀ (f : C(X, ℂ)) (M : ℝ), 0 ≤ M → (∀ x ∈ K, ‖f x‖ ≤ M) → ‖L f‖ ≤ C * M := by
  -- continuity at the origin gives a basic neighbourhood inside the unit ball
  have hpre : (L : C(X, ℂ) → ℂ) ⁻¹' (ball (0 : ℂ) 1) ∈ 𝓝 (0 : C(X, ℂ)) := by
    have hmem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
    have := L.continuous.tendsto (0 : C(X, ℂ))
    have hball : ball (0 : ℂ) 1 ∈ 𝓝 (L 0) := by
      rw [map_zero]
      exact ball_mem_nhds _ one_pos
    exact this hball
  obtain ⟨p, ⟨hK, hε⟩, hsub⟩ := hasBasis_nhds_zero_continuousMap.mem_iff.1 hpre
  obtain ⟨K, ε⟩ := p
  refine ⟨K, 1 / ε, hK, by positivity, ?_⟩
  intro f M hM hf
  have hkey : ∀ g : C(X, ℂ), (∀ x ∈ K, ‖g x‖ < ε) → ‖L g‖ < 1 := by
    intro g hg
    have hmem : g ∈ {h : C(X, ℂ) | ∀ x ∈ K, ‖h x‖ < ε} := hg
    have := hsub hmem
    simpa [Complex.dist_eq] using this
  -- scale `f` into that neighbourhood and let the scale approach its critical value
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set t : ℝ := δ * ε with ht
  have ht0 : 0 < t := by positivity
  have hden : 0 < M + t := by linarith
  set c : ℂ := ((ε / (M + t) : ℝ) : ℂ) with hc
  have hcnorm : ‖c‖ = ε / (M + t) := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hscaled : ∀ x ∈ K, ‖(c • f) x‖ < ε := by
    intro x hx
    have hfx : ‖f x‖ ≤ M := hf x hx
    have happ : (c • f) x = c * f x := by simp
    rw [happ, norm_mul, hcnorm]
    have hlt : ε / (M + t) * ‖f x‖ ≤ ε / (M + t) * M :=
      mul_le_mul_of_nonneg_left hfx (by positivity)
    have hMt : ε / (M + t) * M < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    exact lt_of_le_of_lt hlt hMt
  have hLs : ‖L (c • f)‖ < 1 := hkey _ hscaled
  rw [map_smul, norm_smul, hcnorm] at hLs
  have hfinal : ‖L f‖ < (M + t) / ε := by
    rw [div_mul_eq_mul_div, div_lt_one hden] at hLs
    rw [lt_div_iff₀ hε]
    linarith
  have hsplit : (M + t) / ε = 1 / ε * M + δ := by
    rw [ht]
    field_simp
  rw [hsplit] at hfinal
  exact hfinal.le

end HTGeometry
