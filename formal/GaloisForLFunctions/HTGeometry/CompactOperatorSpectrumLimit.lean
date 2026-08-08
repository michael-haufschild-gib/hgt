/-
# A limit of eigenvalues of nearby operators is an eigenvalue of a compact operator

If operators `Sₐ` converge to a compact `T` in operator norm, each `Sₐ` has a unit eigenvector for
an eigenvalue `λₐ`, and `λₐ → λ ≠ 0`, then `λ` is an eigenvalue of `T`.

The reason is compactness: `T vₐ = λₐ vₐ − (Sₐ − T)vₐ` stays in a fixed compact set, so it clusters
at some `w`; along a filter refining the cluster point, `vₐ → λ⁻¹w`, which has norm one, and
continuity of `T` gives `T(λ⁻¹w) = w = λ·(λ⁻¹w)`.  Mathlib has no spectral semicontinuity for
compact operators, so this is built here.

Main results:
* `mapClusterPt_of_tendsto_dist_zero` — cluster points are unchanged by an asymptotically
  vanishing perturbation.
* `exists_eigenvector_of_tendsto_of_isCompactOperator`.
-/
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ClusterPt

namespace GaloisForLFunctions.HTGeometry

open Filter Metric Topology

/-- A cluster point of a family is a cluster point of any family at asymptotically zero
distance. -/
theorem mapClusterPt_of_tendsto_dist_zero {α X : Type*} [PseudoMetricSpace X] {p : Filter α}
    {x y : α → X} {c : X} (hx : MapClusterPt c p x)
    (hd : Tendsto (fun a => dist (x a) (y a)) p (𝓝 0)) : MapClusterPt c p y := by
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently] at hx ⊢
  intro ε hε
  have h1 : ∃ᶠ a in p, x a ∈ ball c (ε / 2) := hx (ε / 2) (by positivity)
  have h2 : ∀ᶠ a in p, dist (x a) (y a) < ε / 2 :=
    hd.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  refine (h1.and_eventually h2).mono ?_
  rintro a ⟨hxa, hda⟩
  rw [mem_ball] at hxa ⊢
  calc dist (y a) c ≤ dist (y a) (x a) + dist (x a) c := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm (y a) (x a)]; linarith
    _ = ε := by ring

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **A limit of eigenvalues of nearby operators is an eigenvalue of the compact limit.** -/
theorem exists_eigenvector_of_tendsto_of_isCompactOperator {α : Type*} {p : Filter α} [p.NeBot]
    {T : H →L[ℂ] H} (hT : IsCompactOperator (T : H →ₗ[ℂ] H))
    {S : α → H →L[ℂ] H} {v : α → H} {lam : α → ℂ} {l : ℂ}
    (hS : Tendsto (fun a => ‖S a - T‖) p (𝓝 0))
    (hv1 : ∀ a, ‖v a‖ = 1) (heig : ∀ a, S a (v a) = lam a • v a)
    (hlam : Tendsto lam p (𝓝 l)) (hl : l ≠ 0) :
    ∃ w : H, w ≠ 0 ∧ T w = l • w := by
  classical
  set u : α → H := fun a => T (v a) with hu
  -- the family `u` lives in a fixed compact set
  have hcompact : IsCompact (closure ((T : H →ₗ[ℂ] H) '' closedBall (0 : H) 1)) :=
    hT.isCompact_closure_image_closedBall 1
  have hmem : ∀ a, u a ∈ closure ((T : H →ₗ[ℂ] H) '' closedBall (0 : H) 1) := by
    intro a
    refine subset_closure ⟨v a, ?_, rfl⟩
    simp [mem_closedBall, dist_eq_norm, hv1 a]
  obtain ⟨w, _, hw⟩ := hcompact.exists_mapClusterPt (f := p) (u := u)
    (le_principal_iff.mpr (Filter.Eventually.of_forall (f := p) hmem))
  -- the finer filter along which `u` converges to `w`
  set q : Filter α := p ⊓ comap u (𝓝 w) with hq
  have hqne : q.NeBot := by
    rw [hq, ← Filter.map_neBot_iff u, Filter.push_pull, inf_comm]
    exact hw
  have hqle : q ≤ p := inf_le_left
  have hqu : Tendsto u q (𝓝 w) :=
    le_trans (Filter.map_mono inf_le_right) Filter.map_comap_le
  -- the eigenvector family converges to `l⁻¹ • w`
  have herr : Tendsto (fun a => ‖lam a • v a - u a‖) p (𝓝 0) := by
    refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_) hS
    have hrw : lam a • v a - u a = (S a - T) (v a) := by
      rw [sub_apply, heig a, hu]
    rw [hrw]
    calc ‖(S a - T) (v a)‖ ≤ ‖S a - T‖ * ‖v a‖ := (S a - T).le_opNorm _
      _ = ‖S a - T‖ := by rw [hv1 a, mul_one]
  have hlv : Tendsto (fun a => lam a • v a) q (𝓝 w) := by
    have hz : Tendsto (fun a => lam a • v a - u a) q (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      exact (herr.mono_left hqle)
    have := hz.add hqu
    simpa using this
  have hv : Tendsto v q (𝓝 (l⁻¹ • w)) := by
    have hinv : Tendsto (fun a => (lam a)⁻¹) q (𝓝 l⁻¹) :=
      (hlam.mono_left hqle).inv₀ hl
    have := hinv.smul hlv
    refine this.congr' ?_
    have hne : ∀ᶠ a in q, lam a ≠ 0 := by
      have : ∀ᶠ a in p, lam a ≠ 0 := hlam.eventually_ne hl
      exact this.filter_mono hqle
    filter_upwards [hne] with a ha
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  -- the limit has norm one, hence is nonzero
  have hnorm : ‖l⁻¹ • w‖ = 1 := by
    have h1 : Tendsto (fun a => ‖v a‖) q (𝓝 ‖l⁻¹ • w‖) := hv.norm
    have h2 : Tendsto (fun a => ‖v a‖) q (𝓝 1) := by
      simp only [hv1]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hne : (l⁻¹ • w) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  -- continuity of `T` identifies the limit
  have hTv : Tendsto u q (𝓝 (T (l⁻¹ • w))) := T.continuous.continuousAt.tendsto.comp hv
  have hTw : T (l⁻¹ • w) = w := tendsto_nhds_unique hTv hqu
  refine ⟨l⁻¹ • w, hne, ?_⟩
  rw [hTw, smul_smul, mul_inv_cancel₀ hl, one_smul]

end GaloisForLFunctions.HTGeometry
