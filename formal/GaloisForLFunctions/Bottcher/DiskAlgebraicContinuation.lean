import GaloisForLFunctions.Bottcher.BoundaryArcCovering
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Separation.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Disk-side algebraic continuation (the Fatou-free connected-transcendence route)

The connected-case transcendence of `φ_c` over `ℂ(z)` does **not** need Carathéodory/Fatou boundary
theory. Via the (now global, from Gap 2) inverse Böttcher `ψ = β⁻¹`, a relation
`∑ b_j(z) φ_c(z)^j = 0` change-of-variables `z = ψ(w) = w·h(1/w)` into an **algebraic relation for the
disk model `h` over `ℂ(s)`**. An algebraic `h` continues across a circle arc — at any boundary point
off the finite bad set the distinct fibre roots split into holomorphic branches and `h` coincides with
one on the connected lens, so the boundary limit is *produced*, not assumed. That contradicts the
proven natural boundary `natural_boundary_of_even_fe`.

This file assembles the disk-side bricks. The branch machinery it feeds is the tree's
`continuesAcross_of_relation` / `cmem_of_arc_relation` (stated for an arbitrary point, hence usable at
a circle point).
-/

open Metric Set

namespace Bottcher

/-- **The unit circle in `ℂ` is infinite.** It is preconnected (a positive-radius sphere in the
2-dimensional real space `ℂ`) and nontrivial, hence infinite. Used to select a boundary arc avoiding a
finite bad set. -/
theorem infinite_sphere_one : (Metric.sphere (0 : ℂ) 1).Infinite := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact_mod_cast Nat.one_lt_two
  exact (isPreconnected_sphere hrank (0 : ℂ) 1).infinite_of_nontrivial
    ⟨1, by simp [mem_sphere_iff_norm], -1, by simp [mem_sphere_iff_norm], by norm_num⟩

/-- **A boundary arc avoiding a finite bad set.** For any finite `F ⊆ ℂ` there is a boundary point
`ζ₀` (`‖ζ₀‖ = 1`) and a radius `r > 0` whose arc `{ζ : ‖ζ‖ = 1} ∩ ball ζ₀ r` is disjoint from `F`.
This turns "the fibre polynomial degenerates only on a finite set" into the arc hypothesis consumed by
`cmem_of_arc_relation`. -/
theorem exists_arc_avoiding_finite {F : Set ℂ} (hF : F.Finite) :
    ∃ (ζ₀ : ℂ) (r : ℝ), ‖ζ₀‖ = 1 ∧ 0 < r ∧
      ∀ ζ, ‖ζ‖ = 1 → ζ ∈ Metric.ball ζ₀ r → ζ ∉ F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, by simp, one_pos, fun ζ _ _ => Set.notMem_empty ζ⟩
  · obtain ⟨ζ₀, hζ₀s, hζ₀F⟩ := (infinite_sphere_one.diff hF).nonempty
    have hζ₀norm : ‖ζ₀‖ = 1 := by simpa [mem_sphere_iff_norm, sub_zero] using hζ₀s
    refine ⟨ζ₀, Metric.infDist ζ₀ F, hζ₀norm,
      (hF.isClosed.notMem_iff_infDist_pos hne).mp hζ₀F, ?_⟩
    intro ζ _ hζ hζF
    have hle : Metric.infDist ζ₀ F ≤ dist ζ₀ ζ := Metric.infDist_le_dist_of_mem hζF
    rw [mem_ball, dist_comm] at hζ
    linarith

/-- **The intersection of a downward-directed family of nonempty compact connected sets is
connected** (mathlib has the union-of-directed-connected fact but not this nested-intersection form).
Used for the cluster-set argument in the disk-side branch limit: the cluster set of `h` at a boundary
point is `⋂_δ closure (h '' lensₐ)`, a nested family of connected compacts, hence connected; being
contained in the finite root set it is a singleton, which yields the boundary limit with no Fatou
theory. The proof: if `⋂ᵢ Kᵢ` splits across disjoint closed `t, u`, separate the two disjoint compact
pieces by disjoint opens `U, V`; some `Kᵢ ⊆ U ∪ V` (nested-compact finite-intersection), contradicting
its connectedness. -/
theorem isPreconnected_iInter_antitone {X ι : Type*} [TopologicalSpace X] [T2Space X]
    [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    {K : ι → Set X} (hanti : Antitone K) (hcomp : ∀ i, IsCompact (K i))
    (hconn : ∀ i, IsPreconnected (K i)) :
    IsPreconnected (⋂ i, K i) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hCcompact : IsCompact (⋂ i, K i) :=
    (hcomp i₀).of_isClosed_subset (isClosed_iInter fun i => (hcomp i).isClosed) (iInter_subset _ i₀)
  rw [isPreconnected_closed_iff]
  intro t u ht hu hcover htne hune
  by_contra hne'
  rw [not_nonempty_iff_eq_empty] at hne'
  have hCt : IsCompact ((⋂ i, K i) ∩ t) := hCcompact.inter_right ht
  have hCu : IsCompact ((⋂ i, K i) ∩ u) := hCcompact.inter_right hu
  have hdisj : Disjoint ((⋂ i, K i) ∩ t) ((⋂ i, K i) ∩ u) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← hne']; ext x; simp only [mem_inter_iff]; tauto
  obtain ⟨U, V, hU, hV, hCtU, hCuV, hUVdisj⟩ := SeparatedNhds.of_isCompact_isCompact hCt hCu hdisj
  have hCUV : (⋂ i, K i) ⊆ U ∪ V := by
    intro x hx
    rcases hcover hx with hxt | hxu
    · exact Or.inl (hCtU ⟨hx, hxt⟩)
    · exact Or.inr (hCuV ⟨hx, hxu⟩)
  by_cases hall : ∀ i, (K i ∩ (U ∪ V)ᶜ).Nonempty
  · have hdir : Directed (· ⊇ ·) (fun i => K i ∩ (U ∪ V)ᶜ) := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      exact ⟨k, inter_subset_inter_left _ (hanti hik), inter_subset_inter_left _ (hanti hjk)⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun i => K i ∩ (U ∪ V)ᶜ) hdir hall
      (fun i => (hcomp i).inter_right (hU.union hV).isClosed_compl)
      (fun i => (hcomp i).isClosed.inter (hU.union hV).isClosed_compl)
    rw [mem_iInter] at hx
    have hxC : x ∈ ⋂ i, K i := by rw [mem_iInter]; exact fun i => (hx i).1
    exact (hx i₀).2 (hCUV hxC)
  · simp only [not_forall, not_nonempty_iff_eq_empty] at hall
    obtain ⟨i₁, hi₁⟩ := hall
    have hKUV : K i₁ ⊆ U ∪ V := by
      intro x hx
      by_contra hxUV
      have hmem : x ∈ K i₁ ∩ (U ∪ V)ᶜ := ⟨hx, hxUV⟩
      rw [hi₁] at hmem; exact hmem
    have hKU : (K i₁ ∩ U).Nonempty := by
      obtain ⟨x, hx⟩ := htne
      exact ⟨x, iInter_subset _ i₁ hx.1, hCtU hx⟩
    have hKV : (K i₁ ∩ V).Nonempty := by
      obtain ⟨x, hx⟩ := hune
      exact ⟨x, iInter_subset _ i₁ hx.1, hCuV hx⟩
    obtain ⟨x, hx⟩ := hconn i₁ U V hU hV hKUV hKU hKV
    have hxU : x ∈ U := Set.mem_of_mem_inter_left (Set.mem_of_mem_inter_right hx)
    have hxV : x ∈ V := Set.mem_of_mem_inter_right (Set.mem_of_mem_inter_right hx)
    exact Set.disjoint_left.mp hUVdisj hxU hxV

/-- **A preconnected subset of a finite set is a subsingleton** (in a `T1` space). The cluster set of
the disk model `h` at a boundary point is preconnected (previous lemma) and contained in the finite
root set of the fibre polynomial; this lemma collapses it to a single point, which is exactly the
uniqueness feeding `IsCompact.tendsto_nhds_of_unique_mapClusterPt` — the boundary limit with no Fatou
theory. Proof: if `a ≠ b` both lie in `s`, then `{a}` and the (closed, since finite) `s \ {a}` form a
proper closed separation, contradicting `isPreconnected_closed_iff`. -/
theorem isPreconnected_subsingleton_of_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hconn : IsPreconnected s) (hfin : s.Finite) : s.Subsingleton := by
  intro a ha b hb
  by_contra hab
  have hu_closed : IsClosed (s \ {a}) := (hfin.subset Set.diff_subset).isClosed
  have hcover : s ⊆ {a} ∪ (s \ {a}) := by
    intro x hx; by_cases h : x = a
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have h1 : (s ∩ {a}).Nonempty := ⟨a, ha, rfl⟩
  have h2 : (s ∩ (s \ {a})).Nonempty :=
    ⟨b, hb, hb, fun h => hab (Set.mem_singleton_iff.mp h).symm⟩
  obtain ⟨x, hx⟩ := isPreconnected_closed_iff.mp hconn {a} (s \ {a}) isClosed_singleton hu_closed
    hcover h1 h2
  simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff] at hx
  tauto

/-- **The cluster-set engine: a boundary limit with no Fatou theory.** If a map `f` (think: the disk
model `h`) has, along a filter `l` (think: `𝓝[ball 0 1] ζ` at a boundary point) with an antitone
connected-image basis `lens` landing in a compact `B`, all its *cluster values* confined to a finite
set `R` (the roots of the fibre polynomial), then `f` **converges** along `l`. The mechanism: the
map-cluster set equals `⋂ᵢ closure (f '' lens i)` (`HasBasis.clusterPt_iff_forall_mem_closure` on
`map f l`); that is a downward-directed intersection of nonempty compact connected sets, so it is
connected (`isPreconnected_iInter_antitone`); being `⊆ R` finite it is a subsingleton
(`isPreconnected_subsingleton_of_finite`); a compact-supported filter has a cluster point, so the
cluster set is a single point `w₀`, and `IsCompact.tendsto_nhds_of_unique_mapClusterPt` upgrades
"unique cluster point" to `Tendsto f l (𝓝 w₀)`. This is precisely the E-limit crux of the disk-side
route — the boundary value of `h` is *produced*, not assumed, replacing Carathéodory/Fatou. -/
theorem tendsto_of_mapClusterPt_finite {X Y ι : Type*} [TopologicalSpace X] [T2Space X]
    [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    {f : Y → X} {l : Filter Y} [l.NeBot]
    {lens : ι → Set Y} (hbasis : l.HasBasis (fun _ => True) lens)
    {B : Set X} (hB : IsCompact B)
    (hsub : ∀ i, closure (f '' lens i) ⊆ B)
    (hanti : Antitone (fun i => closure (f '' lens i)))
    (hconn : ∀ i, IsPreconnected (f '' lens i))
    {R : Set X} (hR : R.Finite) (hcl : ∀ x, MapClusterPt x l f → x ∈ R) :
    ∃ w₀, Filter.Tendsto f l (nhds w₀) := by
  set K : ι → Set X := fun i => closure (f '' lens i) with hK
  have hKcomp : ∀ i, IsCompact (K i) := fun i => hB.of_isClosed_subset isClosed_closure (hsub i)
  have hKconn : ∀ i, IsPreconnected (K i) := fun i => (hconn i).closure
  have hCconn : IsPreconnected (⋂ i, K i) := isPreconnected_iInter_antitone hanti hKcomp hKconn
  have hbmap : (Filter.map f l).HasBasis (fun _ : ι => True) (fun i => f '' lens i) := hbasis.map f
  have hchar : ∀ x, MapClusterPt x l f ↔ x ∈ ⋂ i, K i := by
    intro x
    rw [mem_iInter]
    show ClusterPt x (Filter.map f l) ↔ ∀ i, x ∈ closure (f '' lens i)
    rw [hbmap.clusterPt_iff_forall_mem_closure]
    simp only [true_implies]
  have hCR : (⋂ i, K i) ⊆ R := fun x hx => hcl x ((hchar x).mpr hx)
  have hCsub : (⋂ i, K i).Subsingleton :=
    isPreconnected_subsingleton_of_finite hCconn (hR.subset hCR)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hev : ∀ᶠ y in l, f y ∈ B :=
    Filter.eventually_of_mem (hbasis.mem_of_mem (i := i₀) trivial)
      (fun y hy => hsub i₀ (subset_closure (mem_image_of_mem f hy)))
  obtain ⟨w₀, _hw₀B, hw₀mc⟩ := hB.exists_mapClusterPt (Filter.le_principal_iff.mpr hev)
  refine ⟨w₀, hB.tendsto_nhds_of_unique_mapClusterPt hev (fun x _hxB hxmc => ?_)⟩
  exact hCsub ((hchar x).mp hxmc) ((hchar w₀).mp hw₀mc)

/-- **A countable (ℕ-indexed) antitone ball basis for the within-neighbourhood filter** `𝓝[s] ζ`.
This is exactly the `hbasis` input of `tendsto_of_mapClusterPt_finite` with index `ι = ℕ`: the lenses
`lensₙ = ball ζ (1/(n+1)) ∩ s` are antitone, so the cluster-set family
`closure (h '' lensₙ)` is antitone as required, and for `s` convex (the unit disk) each `lensₙ` is
convex, hence its `h`-image is connected. Built from `nhdsWithin_basis_ball` by the cofinal sequence
`1/(n+1) → 0`. -/
theorem nhdsWithin_hasBasis_nat_ball {X : Type*} [PseudoMetricSpace X] {ζ : X} {s : Set X} :
    (nhdsWithin ζ s).HasBasis (fun _ : ℕ => True) (fun n => Metric.ball ζ (1/(n+1)) ∩ s) := by
  refine (nhdsWithin_basis_ball).to_hasBasis (fun ε hε => ?_) (fun n _ => ?_)
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, trivial, inter_subset_inter_left s (Metric.ball_subset_ball (le_of_lt hn))⟩
  · exact ⟨1/(n+1), by positivity, subset_rfl⟩

/-- **Every cluster value of `h` at a boundary point is a root of the fibre relation.** If the
continuous relation `g` (think `g (z, w) = ∑ᵢ Aᵢ(z) wⁱ`, the fibre polynomial as a function of the
base point too) vanishes along `h` near `ζ` (`g (z, h z) = 0` eventually in `𝓝[s] ζ`), then any
cluster value `w` of `h` there satisfies `g (ζ, w) = 0`. This is precisely the `hcl` hypothesis of
`tendsto_of_mapClusterPt_finite` (with `R = {w | g (ζ, w) = 0}`, finite when the fibre polynomial is
nonzero): it pins the finite target set the cluster engine needs. Proof by the sequence
characterisation of a map-cluster point (`MapClusterPt.exists_seq_tendsto`, valid since `𝓝[s] ζ` is
countably generated): pick `φ k → ζ` in `s` with `h (φ k) → w`; then `g (φ k, h (φ k)) → g (ζ, w)` by
continuity, while `g (φ k, h (φ k)) = 0` eventually, so `g (ζ, w) = 0`. -/
theorem eq_zero_of_mapClusterPt_relation {s : Set ℂ} {ζ w : ℂ} {h : ℂ → ℂ} {g : ℂ × ℂ → ℂ}
    (hg : Continuous g)
    (hrel : ∀ᶠ z in nhdsWithin ζ s, g (z, h z) = 0)
    (hcl : MapClusterPt w (nhdsWithin ζ s) h) : g (ζ, w) = 0 := by
  obtain ⟨φ, hφw, hφl⟩ := hcl.exists_seq_tendsto
  have hφζ : Filter.Tendsto φ Filter.atTop (nhds ζ) := hφl.mono_right nhdsWithin_le_nhds
  have hpair : Filter.Tendsto (fun k => (φ k, h (φ k))) Filter.atTop (nhds (ζ, w)) := by
    rw [nhds_prod_eq]; exact hφζ.prodMk hφw
  have hg0 : Filter.Tendsto (fun k => g (φ k, h (φ k))) Filter.atTop (nhds (g (ζ, w))) :=
    (hg.tendsto _).comp hpair
  have hev0 : Filter.Tendsto (fun k => g (φ k, h (φ k))) Filter.atTop (nhds 0) :=
    tendsto_nhds_of_eventually_eq (hφl.eventually hrel)
  exact tendsto_nhds_unique hg0 hev0

/-- **The fibre polynomial has a finite root set.** With a nonzero leading coefficient `a N ≠ 0`, the
zero set of `w ↦ ∑_{i≤N} aᵢ wⁱ` is finite. This is the finite `R` the cluster engine
(`tendsto_of_mapClusterPt_finite`) needs together with `eq_zero_of_mapClusterPt_relation`
(cluster values `⊆ R`): the two combine to give the engine its `hcl` and finiteness inputs, so the
boundary limit of `h` at a non-degenerate arc point exists. -/
theorem finite_roots_of_fibre {a : ℕ → ℂ} {N : ℕ} (hlead : a N ≠ 0) :
    {w : ℂ | ∑ i ∈ Finset.range (N + 1), a i * w ^ i = 0}.Finite := by
  set P : Polynomial ℂ := ∑ i ∈ Finset.range (N + 1), Polynomial.C (a i) * Polynomial.X ^ i with hP
  have heval : ∀ w : ℂ, P.eval w = ∑ i ∈ Finset.range (N + 1), a i * w ^ i := by
    intro w
    rw [hP, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hPne : P ≠ 0 := by
    intro h0
    have hc : P.coeff N = a N := by
      rw [hP, Polynomial.finset_sum_coeff,
        Finset.sum_eq_single_of_mem N (Finset.self_mem_range_succ N)]
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro b _ hbN
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hbN h.symm), mul_zero]
    rw [h0, Polynomial.coeff_zero] at hc
    exact hlead hc.symm
  apply Set.Finite.subset P.roots.toFinset.finite_toSet
  intro w hw
  simp only [Set.mem_setOf_eq, ← heval] at hw
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hPne]
  exact hw

/-- **Cauchy root bound for the fibre polynomial.** Any root `w` of `∑_{i≤N} aᵢ wⁱ` with `a N ≠ 0`
satisfies `‖w‖ ≤ 1 + (∑_{i<N} ‖aᵢ‖) / ‖a N‖`. Combined with continuity of the coefficient functions
`Aᵢ(z)` (bounded above) and `A N(z)` (bounded below near a point where `A N(ζ) ≠ 0`), this makes `h`
**uniformly bounded near ζ** — i.e. `closure (h '' lensₙ) ⊆ closedBall 0 M`, the compact-support input
`hsub` of `tendsto_of_mapClusterPt_finite`. This is the last analytic ingredient of the disk-side
boundary-limit production; mathlib has no Cauchy bound, so it is proved here: for `‖w‖ > 1`, isolate
the top term `a N wⁿ = -∑_{i<N} aᵢ wⁱ`, bound `‖w‖ⁱ ≤ ‖w‖^{N-1}`, and cancel `‖w‖^{N-1} > 0`. -/
theorem norm_le_of_fibre_root {a : ℕ → ℂ} {N : ℕ} (hlead : a N ≠ 0) {w : ℂ}
    (hw : ∑ i ∈ Finset.range (N + 1), a i * w ^ i = 0) :
    ‖w‖ ≤ 1 + (∑ i ∈ Finset.range N, ‖a i‖) / ‖a N‖ := by
  have haN : 0 < ‖a N‖ := norm_pos_iff.mpr hlead
  have hSnn : 0 ≤ (∑ i ∈ Finset.range N, ‖a i‖) / ‖a N‖ :=
    div_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _) haN.le
  by_cases hle : ‖w‖ ≤ 1
  · linarith
  push_neg at hle
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, mul_one, zero_add] at hw
    exact absurd hw hlead
  rw [Finset.sum_range_succ] at hw
  have hkey : a N * w ^ N = - ∑ i ∈ Finset.range N, a i * w ^ i := by linear_combination hw
  have hnorm : ‖a N‖ * ‖w‖ ^ N ≤ (∑ i ∈ Finset.range N, ‖a i‖) * ‖w‖ ^ (N - 1) := by
    calc ‖a N‖ * ‖w‖ ^ N = ‖a N * w ^ N‖ := by rw [norm_mul, norm_pow]
      _ = ‖∑ i ∈ Finset.range N, a i * w ^ i‖ := by rw [hkey, norm_neg]
      _ ≤ ∑ i ∈ Finset.range N, ‖a i * w ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range N, ‖a i‖ * ‖w‖ ^ i := by simp only [norm_mul, norm_pow]
      _ ≤ ∑ i ∈ Finset.range N, ‖a i‖ * ‖w‖ ^ (N - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hle.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)))
              (norm_nonneg _)
      _ = (∑ i ∈ Finset.range N, ‖a i‖) * ‖w‖ ^ (N - 1) := by rw [Finset.sum_mul]
  have hpow : ‖w‖ ^ N = ‖w‖ ^ (N - 1) * ‖w‖ := by
    rw [← pow_succ, Nat.sub_add_cancel hNpos]
  rw [hpow] at hnorm
  have hpospow : 0 < ‖w‖ ^ (N - 1) := pow_pos (by linarith) _
  have hcancel : ‖a N‖ * ‖w‖ ≤ ∑ i ∈ Finset.range N, ‖a i‖ := by
    have h2 : (‖a N‖ * ‖w‖) * ‖w‖ ^ (N - 1) ≤ (∑ i ∈ Finset.range N, ‖a i‖) * ‖w‖ ^ (N - 1) := by
      calc (‖a N‖ * ‖w‖) * ‖w‖ ^ (N - 1) = ‖a N‖ * (‖w‖ ^ (N - 1) * ‖w‖) := by ring
        _ ≤ _ := hnorm
    exact le_of_mul_le_mul_right h2 hpospow
  have hfin : ‖w‖ ≤ (∑ i ∈ Finset.range N, ‖a i‖) / ‖a N‖ := by
    rw [le_div_iff₀ haN, mul_comm]; exact hcancel
  linarith

/-- **`h` is uniformly bounded near a non-degenerate boundary point.** If the coefficient functions
`Aᵢ` are continuous at `ζ` with `A N ζ ≠ 0` and `h` satisfies the fibre relation
`∑ᵢ Aᵢ(z)·h(z)ⁱ = 0` eventually along `𝓝[s] ζ`, then `‖h‖` is eventually bounded there. Continuity
gives a neighbourhood where `‖A N z‖ > ‖A N ζ‖/2` and `‖Aᵢ z‖ < ‖Aᵢ ζ‖ + 1`; the Cauchy root bound
(`norm_le_of_fibre_root`) then bounds `‖h z‖` uniformly. This converts the algebraic relation into
the compact-support input `hsub` of the cluster engine `tendsto_of_mapClusterPt_finite`. -/
theorem eventually_norm_h_le {A : ℕ → ℂ → ℂ} {N : ℕ} {ζ : ℂ} {h : ℂ → ℂ} {s : Set ℂ}
    (hAcont : ∀ i, ContinuousAt (A i) ζ) (hlead : A N ζ ≠ 0)
    (hrel : ∀ᶠ z in nhdsWithin ζ s, ∑ i ∈ Finset.range (N + 1), A i z * h z ^ i = 0) :
    ∃ M : ℝ, ∀ᶠ z in nhdsWithin ζ s, ‖h z‖ ≤ M := by
  have hcpos : 0 < ‖A N ζ‖ := norm_pos_iff.mpr hlead
  have hlow : ∀ᶠ z in nhds ζ, ‖A N ζ‖ / 2 < ‖A N z‖ :=
    ((hAcont N).norm).eventually_const_lt (by linarith)
  have hallupp : ∀ᶠ z in nhds ζ, ∀ i ∈ Finset.range N, ‖A i z‖ < ‖A i ζ‖ + 1 :=
    (Filter.eventually_all_finset _).mpr
      (fun i _ => ((hAcont i).norm).eventually_lt_const (by linarith))
  refine ⟨1 + (∑ i ∈ Finset.range N, (‖A i ζ‖ + 1)) / (‖A N ζ‖ / 2), ?_⟩
  filter_upwards [hrel, hlow.filter_mono nhdsWithin_le_nhds,
      hallupp.filter_mono nhdsWithin_le_nhds] with z hzrel hzlow hzupp
  have hlead_z : A N z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hzlow; linarith
  have hcauchy := norm_le_of_fibre_root (a := fun i => A i z) hlead_z hzrel
  have hSbound : (∑ i ∈ Finset.range N, ‖A i z‖) ≤ ∑ i ∈ Finset.range N, (‖A i ζ‖ + 1) :=
    Finset.sum_le_sum (fun i hi => le_of_lt (hzupp i hi))
  have hSnn : 0 ≤ ∑ i ∈ Finset.range N, ‖A i z‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hstep : (∑ i ∈ Finset.range N, ‖A i z‖) / ‖A N z‖
      ≤ (∑ i ∈ Finset.range N, (‖A i ζ‖ + 1)) / (‖A N ζ‖ / 2) := by
    apply div_le_div₀ (by positivity) hSbound (by linarith) (le_of_lt hzlow)
  calc ‖h z‖ ≤ 1 + (∑ i ∈ Finset.range N, ‖A i z‖) / ‖A N z‖ := hcauchy
    _ ≤ 1 + (∑ i ∈ Finset.range N, (‖A i ζ‖ + 1)) / (‖A N ζ‖ / 2) := by linarith

/-- **THE E-LIMIT SUPPLIER: a boundary limit for `h` at every non-degenerate boundary point — with
no Fatou/Carathéodory theory.** If `h` (continuous on the unit disk) satisfies the fibre relation
`∑_{i≤N} Aᵢ(z)·h(z)ⁱ = 0` near a circle point `ζ` where the leading coefficient does not vanish
(`A N ζ ≠ 0`), then `h` has a limit `w₀` along `𝓝[ball 0 1] ζ`, and `w₀` is a root of the limit
fibre polynomial `∑ᵢ Aᵢ(ζ)·wⁱ`. Assembly of the whole brick suite: `eventually_norm_h_le` (Cauchy
bound ⟹ `h` bounded on `s' = ball 0 1 ∩ ball ζ r₀`), `nhdsWithin_hasBasis_nat_ball` (antitone convex
lens basis, transported through `𝓝[s'] ζ = 𝓝[ball 0 1] ζ`), convexity ⟹ connected lens images,
`finite_roots_of_fibre` + `eq_zero_of_mapClusterPt_relation` (cluster values in the finite root set),
and the cluster engine `tendsto_of_mapClusterPt_finite`. This is the input `Tendsto h (𝓝[ball 0 1] ζ)
(𝓝 w₀)` that `continuesAcross_of_relation`/`cmem_of_arc_relation` consume: the "Fatou-type input"
those lemmas isolate is hereby produced from the algebraic relation itself. -/
theorem exists_boundary_limit_of_fibre_relation {A : ℕ → ℂ → ℂ} {N : ℕ} {ζ : ℂ} {h : ℂ → ℂ}
    (hAcont : ∀ i, Continuous (A i)) (hlead : A N ζ ≠ 0) (hζ : ‖ζ‖ = 1)
    (hhc : ContinuousOn h (ball 0 1))
    (hrel : ∀ᶠ z in nhdsWithin ζ (ball 0 1),
      ∑ i ∈ Finset.range (N + 1), A i z * h z ^ i = 0) :
    ∃ w₀ : ℂ, Filter.Tendsto h (nhdsWithin ζ (ball 0 1)) (nhds w₀) ∧
      ∑ i ∈ Finset.range (N + 1), A i ζ * w₀ ^ i = 0 := by
  haveI hne : (nhdsWithin ζ (ball (0:ℂ) 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_ball 0 one_ne_zero, mem_closedBall,
      dist_zero_right, hζ]
  obtain ⟨M, hM⟩ := eventually_norm_h_le (fun i => (hAcont i).continuousAt) hlead hrel
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hM
  obtain ⟨r₀, hr₀, hMball⟩ := hM
  set s' : Set ℂ := ball (0:ℂ) 1 ∩ ball ζ r₀ with hs'
  have hfeq : nhdsWithin ζ s' = nhdsWithin ζ (ball (0:ℂ) 1) :=
    nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds ζ hr₀))
  have hbasis : (nhdsWithin ζ (ball (0:ℂ) 1)).HasBasis (fun _ : ℕ => True)
      (fun n => Metric.ball ζ (1/(n+1)) ∩ s') := by
    rw [← hfeq]; exact nhdsWithin_hasBasis_nat_ball
  have hbnd : ∀ z ∈ s', ‖h z‖ ≤ M := fun z hz => hMball (mem_ball.mp hz.2) hz.1
  have hsub : ∀ n : ℕ, closure (h '' (Metric.ball ζ (1/(n+1)) ∩ s')) ⊆ closedBall 0 M := by
    intro n
    apply closure_minimal _ isClosed_closedBall
    rintro w ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact hbnd z hz.2
  have hlensanti : Antitone (fun n : ℕ => Metric.ball ζ (1/(n+1)) ∩ s') := by
    intro n m hnm
    apply inter_subset_inter_left
    apply ball_subset_ball
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hnm
  have hanti : Antitone (fun n : ℕ => closure (h '' (Metric.ball ζ (1/(n+1)) ∩ s'))) :=
    fun n m hnm => closure_mono (image_mono (hlensanti hnm))
  have hconn : ∀ n : ℕ, IsPreconnected (h '' (Metric.ball ζ (1/(n+1)) ∩ s')) := by
    intro n
    have hcvx : Convex ℝ (Metric.ball ζ (1/(n+1)) ∩ s') :=
      (convex_ball ζ _).inter ((convex_ball 0 1).inter (convex_ball ζ r₀))
    exact hcvx.isPreconnected.image h (hhc.mono (fun z hz => hz.2.1))
  have hRfin : {w : ℂ | ∑ i ∈ Finset.range (N + 1), A i ζ * w ^ i = 0}.Finite :=
    finite_roots_of_fibre (a := fun i => A i ζ) hlead
  have hgcont : Continuous (fun p : ℂ × ℂ => ∑ i ∈ Finset.range (N + 1), A i p.1 * p.2 ^ i) :=
    continuous_finsetSum _
      (fun i _ => ((hAcont i).comp continuous_fst).mul (continuous_snd.pow i))
  have hcl : ∀ x, MapClusterPt x (nhdsWithin ζ (ball (0:ℂ) 1)) h →
      x ∈ {w : ℂ | ∑ i ∈ Finset.range (N + 1), A i ζ * w ^ i = 0} := by
    intro x hx
    exact eq_zero_of_mapClusterPt_relation hgcont hrel hx
  obtain ⟨w₀, hw₀⟩ := tendsto_of_mapClusterPt_finite hbasis (isCompact_closedBall (0:ℂ) M)
    hsub hanti hconn hRfin hcl
  exact ⟨w₀, hw₀, eq_zero_of_mapClusterPt_relation hgcont hrel hw₀.mapClusterPt⟩

end Bottcher
