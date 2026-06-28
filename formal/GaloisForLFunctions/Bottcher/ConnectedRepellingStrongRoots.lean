import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect
import GaloisForLFunctions.Bottcher.JuliaFrontierPerfect
import GaloisForLFunctions.Bottcher.RepellingPeriodicFrontier

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-- Eventual bounded root defect plus eventual bounded non-strong count implies the strong-root pool
is frequently larger than every finite threshold.  This is the direct counting bridge into the
unbounded-strong-root hRigid input. -/
theorem frequently_strongFixedPointRoots_card_gt_of_eventually_rootDefect_nonStrong_card_le
    (c : ℂ) (D N : ℕ)
    (hrootDefect : ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D)
    (hN : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N) :
    ∀ A : ℕ, ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card := by
  intro A
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  have hbig : ∀ᶠ p : ℕ in atTop, A + N + D < 2 ^ p :=
    htwo.eventually_gt_atTop (A + N + D)
  have hev : ∀ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card := by
    filter_upwards [hrootDefect, hN, hbig] with p hdef hNcard hbigp
    have hsplit :=
      strongFixedPointRoots_card_add_nonStrongFixedPointRoots_card_eq_roots_card c p
    rw [← hsplit] at hdef
    omega
  exact hev.frequently

/-- Eventual duplicate-excess bounds plus eventual bounded non-strong count imply the unbounded
strong-root input. -/
theorem frequently_strongFixedPointRoots_card_gt_of_eventually_roots_count_excess_nonStrong_card_le
    (c : ℂ) (D N : ℕ)
    (hD : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      (∑ z ∈ (fixedPointPoly c p).roots.toFinset,
        ((fixedPointPoly c p).roots.count z - 1)) ≤ D)
    (hN : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N) :
    ∀ A : ℕ, ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card :=
  frequently_strongFixedPointRoots_card_gt_of_eventually_rootDefect_nonStrong_card_le
    c D N
    (eventually_fixedPointPoly_rootDefect_bound_of_eventually_roots_count_excess_le c D hD)
    hN

/-- Eventual finite multiplier-one support with local duplicate-excess bounds, together with eventual
bounded non-strong count, implies the unbounded strong-root input. -/
theorem frequently_strongFixedPointRoots_card_gt_of_eventually_multiplierOne_subset_nonStrong_card_le
    (c : ℂ) (F : Finset ℂ) (L N : ℕ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L))
    (hN : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N) :
    ∀ A : ℕ, ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card :=
  frequently_strongFixedPointRoots_card_gt_of_eventually_rootDefect_nonStrong_card_le
    c (F.card * L) N
    (eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiplierOne_subset
      c F L hmultiplierOne)
    hN

/-- Frequently unbounded strong-root counts give an actual infinite set of strong periodic targets. -/
theorem infinite_strongFixedPointRoots_union_of_frequently_card_gt
    {c : ℂ}
    (hstrong : ∀ A : ℕ,
      ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card) :
    {z : ℂ | ∃ p : ℕ, z ∈ strongFixedPointRoots c p}.Infinite := by
  classical
  intro hfin
  let Tfin := hfin.toFinset
  have hbound : ∀ p : ℕ, (strongFixedPointRoots c p).card ≤ Tfin.card := by
    intro p
    have hsub : strongFixedPointRoots c p ⊆ Tfin := by
      intro z hz
      exact hfin.mem_toFinset.mpr ⟨p, hz⟩
    exact Finset.card_le_card hsub
  obtain ⟨p, hpgt⟩ := (hstrong Tfin.card).exists
  exact not_lt_of_ge (hbound p) hpgt

/-- Frequently unbounded strong-root counts produce a Julia-frontier accumulation point for the
union of all strong fixed roots. -/
theorem exists_frontier_accumulation_of_frequently_strongFixedPointRoots_card_gt
    {c : ℂ}
    (hstrong : ∀ A : ℕ,
      ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card) :
    ∃ z₁ ∈ frontier (filledJulia c),
      AccPt z₁ (𝓟 {z : ℂ | ∃ p : ℕ, z ∈ strongFixedPointRoots c p}) := by
  let S : Set ℂ := {z : ℂ | ∃ p : ℕ, z ∈ strongFixedPointRoots c p}
  have hSinf : S.Infinite := by
    simpa [S] using infinite_strongFixedPointRoots_union_of_frequently_card_gt hstrong
  have hgeom : ∀ z ∈ S, ∃ p : ℕ,
      (quadratic c)^[p] z = z ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
    intro z hz
    obtain ⟨p, hzp⟩ := hz
    have hzstrong := mem_strongFixedPointRoots.mp hzp
    have hnorm := hzstrong.2
    have hp : 1 ≤ p := by
      cases p with
      | zero =>
          simp at hnorm
      | succ p => omega
    have hFz : (quadratic c)^[p] z = z := by
      rw [← fixedPointPoly_isRoot_iff]
      exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hzstrong.1)
    exact ⟨p, hFz, hnorm⟩
  simpa [S] using
    exists_frontier_accumulation_of_infinite_strongly_repelling_periodic_set hSinf hgeom

/-- Strongly repelling periodic density in orbit-product form gives the exact
`strongFixedPointRoots` density input used by the closed-ball hRigid route. -/
theorem dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic
    {c : ℂ}
    (hdense : frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖}) :
    frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q} := by
  intro z hz
  refine closure_mono ?_ (hdense hz)
  intro y hy
  obtain ⟨q, hfix, hnorm⟩ := hy
  refine ⟨q, ?_⟩
  have hq : 1 ≤ q := by
    cases q with
    | zero =>
        simp at hnorm
    | succ q => omega
  have hroot : y ∈ (fixedPointPoly c q).roots.toFinset := by
    exact Multiset.mem_toFinset.mpr
        ((mem_roots (fixedPointPoly_ne_zero c hq)).mpr
          ((fixedPointPoly_isRoot_iff c q y).mpr hfix))
  exact mem_strongFixedPointRoots.mpr ⟨hroot, hnorm⟩

/-- Local strongly-repelling periodic witnesses in every frontier ball are exactly the
frontier-density statement in orbit-product form. -/
theorem dense_strongly_repelling_periodic_of_forall_frontier_ball
    {c : ℂ}
    (hlocal : ∀ z ∈ frontier (filledJulia c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r,
        ∃ q : ℕ,
          (quadratic c)^[q] y = y ∧
          (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] y‖) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖} := by
  intro z hzfront
  rw [_root_.mem_closure_iff]
  intro U hUo hzU
  obtain ⟨r, hr, hballU⟩ := Metric.isOpen_iff.mp hUo z hzU
  obtain ⟨y, hyball, hygeom⟩ := hlocal z hzfront r hr
  exact ⟨y, hballU hyball, hygeom⟩

/-- Local strongly-repelling periodic witnesses in every frontier ball give the exact
`strongFixedPointRoots` density input used by the closed-ball hRigid route. -/
theorem dense_strongFixedPointRoots_of_forall_frontier_ball_strongly_repelling_periodic
    {c : ℂ}
    (hlocal : ∀ z ∈ frontier (filledJulia c), ∀ r : ℝ, 0 < r →
      ∃ y ∈ Metric.ball z r,
        ∃ q : ℕ,
          (quadratic c)^[q] y = y ∧
          (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] y‖) :
    frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q} :=
  dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic
    (dense_strongly_repelling_periodic_of_forall_frontier_ball hlocal)

/-- If the frontier is locally uncountable near `p`, density of strong fixed roots in the frontier gives
infinitely many strong fixed roots in the closed ball around `p`. -/
theorem infinite_strongFixedPointRoots_closedBall_of_frontier_dense_of_not_countable_ball
    {c p : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hunc : ¬ (Metric.ball p (R / 2) ∩ frontier (filledJulia c)).Countable)
    (hdense : frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}) :
    ({z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q} ∩ Metric.closedBall p R).Infinite := by
  classical
  intro hfin
  let Strong : Set ℂ := {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}
  have hclosed : IsClosed (Strong ∩ Metric.closedBall p R) := by
    simpa [Strong] using hfin.isClosed
  have hclosure_eq : closure (Strong ∩ Metric.closedBall p R) =
      Strong ∩ Metric.closedBall p R := hclosed.closure_eq
  have hhalf : 0 < R / 2 := by linarith
  have hTsub : Metric.ball p (R / 2) ∩ frontier (filledJulia c) ⊆
      Strong ∩ Metric.closedBall p R := by
    intro z hz
    have hzclStrong : z ∈ closure Strong := by
      simpa [Strong] using hdense hz.2
    have hzballR : z ∈ Metric.ball p R := Metric.ball_subset_ball (by linarith) hz.1
    have hclosedN : Metric.closedBall p R ∈ 𝓝 z := Metric.closedBall_mem_nhds_of_mem hzballR
    have hzclLocal : z ∈ closure (Strong ∩ Metric.closedBall p R) := by
      rw [_root_.mem_closure_iff]
      intro W hWo hzW
      have hWclosedN : W ∩ Metric.closedBall p R ∈ 𝓝 z :=
        inter_mem (hWo.mem_nhds hzW) hclosedN
      obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hWclosedN
      have hmeet := (_root_.mem_closure_iff.mp hzclStrong) V hVo hzV
      rcases hmeet with ⟨y, hyV, hyStrong⟩
      exact ⟨y, (hVsub hyV).1, hyStrong, (hVsub hyV).2⟩
    rwa [hclosure_eq] at hzclLocal
  have hfinStrong : (Strong ∩ Metric.closedBall p R).Countable := by
    simpa [Strong] using hfin.countable
  exact hunc (hfinStrong.mono hTsub)

/-- Perfectness of the Julia frontier plus density of strong fixed roots gives infinitely many strong
fixed roots in every closed ball centered at a frontier point. -/
theorem infinite_strongFixedPointRoots_closedBall_of_perfect_frontier_dense
    {c p : ℂ} {R : ℝ}
    (hfront : Perfect (frontier (filledJulia c)))
    (hpfront : p ∈ frontier (filledJulia c))
    (hR : 0 < R)
    (hdense : frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}) :
    ({z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q} ∩ Metric.closedBall p R).Infinite :=
  infinite_strongFixedPointRoots_closedBall_of_frontier_dense_of_not_countable_ball hR
    (not_countable_ball_inter_perfect hfront hpfront (by linarith)) hdense

/-- Density of strong fixed roots in the Julia frontier gives infinitely many such roots in every
closed ball around a local frontier-uncountability seed. -/
theorem infinite_strongFixedPointRoots_closedBall_of_frontier_dense
    {c p : ℂ} {R : ℝ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hpK : p ∈ filledJulia c)
    (hR : 0 < R)
    (hdense : frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}) :
    ({z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q} ∩ Metric.closedBall p R).Infinite :=
  infinite_strongFixedPointRoots_closedBall_of_frontier_dense_of_not_countable_ball hR
    (not_countable_ball_inter_frontier_filledJulia_of_preconnected_emptyInterior
      hconn hempty hpK (by linarith))
    hdense

/-- Frontier-dense strong fixed roots supply the local closed-ball strong-periodic target package used
by the global β/γ hRigid crossing endpoint. -/
theorem exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense
    {c p : ℂ} {Ω : Set ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hpK : p ∈ filledJulia c)
    (hpΩ : p ∈ interior Ω)
    (hdense : frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}) :
    ∃ (r : ℝ) (S : Set ℂ), 0 < r ∧ S.Infinite ∧ S ⊆ Metric.closedBall p r ∧
      Metric.closedBall p r ⊆ Ω ∧
      (∀ z ∈ S, ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖) := by
  have hΩmem : Ω ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hpΩ
  obtain ⟨R, hR, hballΩ⟩ := Metric.mem_nhds_iff.mp hΩmem
  let r : ℝ := R / 2
  let S : Set ℂ := {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q} ∩ Metric.closedBall p r
  have hr : 0 < r := by dsimp [r]; linarith
  have hclosedBallΩ : Metric.closedBall p r ⊆ Ω := by
    intro z hz
    exact hballΩ (Metric.closedBall_subset_ball (by dsimp [r]; linarith) hz)
  have hSinf : S.Infinite := by
    dsimp [S, r]
    exact infinite_strongFixedPointRoots_closedBall_of_frontier_dense
      hconn hempty hpK (by linarith) hdense
  have hSball : S ⊆ Metric.closedBall p r := inter_subset_right
  have hgeom : ∀ z ∈ S, ∃ q : ℕ,
      (quadratic c)^[q] z = z ∧
      (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖ := by
    intro z hz
    obtain ⟨q, hzq⟩ := hz.1
    have hzstrong := mem_strongFixedPointRoots.mp hzq
    have hnorm := hzstrong.2
    have hq : 1 ≤ q := by
      cases q with
      | zero =>
          simp at hnorm
      | succ q => omega
    have hFz : (quadratic c)^[q] z = z := by
      rw [← fixedPointPoly_isRoot_iff]
      exact (mem_roots (fixedPointPoly_ne_zero c hq)).mp (Multiset.mem_toFinset.mp hzstrong.1)
    exact ⟨q, hFz, hnorm⟩
  exact ⟨r, S, hr, hSinf, hSball, hclosedBallΩ, hgeom⟩

/-- Perfectness of the Julia frontier and density of strong fixed roots supply the local closed-ball
strong-periodic target package used by the global β/γ hRigid crossing endpoint. -/
theorem exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense
    {c p : ℂ} {Ω : Set ℂ}
    (hfront : Perfect (frontier (filledJulia c)))
    (hpfront : p ∈ frontier (filledJulia c))
    (hpΩ : p ∈ interior Ω)
    (hdense : frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}) :
    ∃ (r : ℝ) (S : Set ℂ), 0 < r ∧ S.Infinite ∧ S ⊆ Metric.closedBall p r ∧
      Metric.closedBall p r ⊆ Ω ∧
      (∀ z ∈ S, ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖) := by
  have hΩmem : Ω ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hpΩ
  obtain ⟨R, hR, hballΩ⟩ := Metric.mem_nhds_iff.mp hΩmem
  let r : ℝ := R / 2
  let S : Set ℂ := {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q} ∩ Metric.closedBall p r
  have hr : 0 < r := by dsimp [r]; linarith
  have hclosedBallΩ : Metric.closedBall p r ⊆ Ω := by
    intro z hz
    exact hballΩ (Metric.closedBall_subset_ball (by dsimp [r]; linarith) hz)
  have hSinf : S.Infinite := by
    dsimp [S, r]
    exact infinite_strongFixedPointRoots_closedBall_of_perfect_frontier_dense
      hfront hpfront (by linarith) hdense
  have hSball : S ⊆ Metric.closedBall p r := inter_subset_right
  have hgeom : ∀ z ∈ S, ∃ q : ℕ,
      (quadratic c)^[q] z = z ∧
      (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖ := by
    intro z hz
    obtain ⟨q, hzq⟩ := hz.1
    have hzstrong := mem_strongFixedPointRoots.mp hzq
    have hnorm := hzstrong.2
    have hq : 1 ≤ q := by
      cases q with
      | zero =>
          simp at hnorm
      | succ q => omega
    have hFz : (quadratic c)^[q] z = z := by
      rw [← fixedPointPoly_isRoot_iff]
      exact (mem_roots (fixedPointPoly_ne_zero c hq)).mp (Multiset.mem_toFinset.mp hzstrong.1)
    exact ⟨q, hFz, hnorm⟩
  exact ⟨r, S, hr, hSinf, hSball, hclosedBallΩ, hgeom⟩

/-- Open-region form of
`exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense`: an open analytic target region
only needs the seed point to lie in the region. -/
theorem exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense_open
    {c p : ℂ} {Ω : Set ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hΩopen : IsOpen Ω)
    (hpK : p ∈ filledJulia c)
    (hpΩ : p ∈ Ω)
    (hdense : frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}) :
    ∃ (r : ℝ) (S : Set ℂ), 0 < r ∧ S.Infinite ∧ S ⊆ Metric.closedBall p r ∧
      Metric.closedBall p r ⊆ Ω ∧
      (∀ z ∈ S, ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖) := by
  exact exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense
    hconn hempty hpK (mem_interior_iff_mem_nhds.mpr (hΩopen.mem_nhds hpΩ)) hdense

/-- Open-region form of
`exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense`: perfect frontier plus
dense strong roots localize inside any open target region containing the frontier seed. -/
theorem exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense_open
    {c p : ℂ} {Ω : Set ℂ}
    (hfront : Perfect (frontier (filledJulia c)))
    (hΩopen : IsOpen Ω)
    (hpfront : p ∈ frontier (filledJulia c))
    (hpΩ : p ∈ Ω)
    (hdense : frontier (filledJulia c) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c q}) :
    ∃ (r : ℝ) (S : Set ℂ), 0 < r ∧ S.Infinite ∧ S ⊆ Metric.closedBall p r ∧
      Metric.closedBall p r ⊆ Ω ∧
      (∀ z ∈ S, ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖) := by
  exact exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense
    hfront hpfront (mem_interior_iff_mem_nhds.mpr (hΩopen.mem_nhds hpΩ)) hdense

/-- Open-region localizer from natural orbit-product density of strongly repelling periodic points. -/
theorem exists_closedBall_strongly_repelling_periodic_supply_of_frontier_dense_open
    {c p : ℂ} {Ω : Set ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hΩopen : IsOpen Ω)
    (hpK : p ∈ filledJulia c)
    (hpΩ : p ∈ Ω)
    (hdense : frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖}) :
    ∃ (r : ℝ) (S : Set ℂ), 0 < r ∧ S.Infinite ∧ S ⊆ Metric.closedBall p r ∧
      Metric.closedBall p r ⊆ Ω ∧
      (∀ z ∈ S, ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖) := by
  exact exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense_open
    hconn hempty hΩopen hpK hpΩ
    (dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic hdense)

/-- Perfect-frontier open-region localizer from natural orbit-product density of strongly repelling
periodic points. -/
theorem exists_closedBall_strongly_repelling_periodic_supply_of_perfect_frontier_dense_open
    {c p : ℂ} {Ω : Set ℂ}
    (hfront : Perfect (frontier (filledJulia c)))
    (hΩopen : IsOpen Ω)
    (hpfront : p ∈ frontier (filledJulia c))
    (hpΩ : p ∈ Ω)
    (hdense : frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖}) :
    ∃ (r : ℝ) (S : Set ℂ), 0 < r ∧ S.Infinite ∧ S ⊆ Metric.closedBall p r ∧
      Metric.closedBall p r ⊆ Ω ∧
      (∀ z ∈ S, ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖) := by
  exact exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense_open
    hfront hΩopen hpfront hpΩ
    (dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic hdense)

/-- If nonresonant periodic frontier targets are dense in the Julia frontier, and the frontier is
locally uncountable near `p`, then every closed ball around `p` contains infinitely many such targets. -/
theorem infinite_nonresonantPeriodic_closedBall_of_frontier_dense_of_not_countable_ball
    {c p : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hunc : ¬ (Metric.ball p (R / 2) ∩ frontier (filledJulia c)).Countable)
    (hdense : frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)}) :
    ({z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} ∩
      Metric.closedBall p R).Infinite := by
  classical
  intro hfin
  let Nonres : Set ℂ := {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
    (quadratic c)^[q] z = z ∧
    ∀ m : ℕ, 1 ≤ m →
      (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)}
  have hclosed : IsClosed (Nonres ∩ Metric.closedBall p R) := by
    simpa [Nonres] using hfin.isClosed
  have hclosure_eq : closure (Nonres ∩ Metric.closedBall p R) =
      Nonres ∩ Metric.closedBall p R := hclosed.closure_eq
  have hTsub : Metric.ball p (R / 2) ∩ frontier (filledJulia c) ⊆
      Nonres ∩ Metric.closedBall p R := by
    intro z hz
    have hzclNonres : z ∈ closure Nonres := by
      simpa [Nonres] using hdense hz.2
    have hzballR : z ∈ Metric.ball p R := Metric.ball_subset_ball (by linarith) hz.1
    have hclosedN : Metric.closedBall p R ∈ 𝓝 z := Metric.closedBall_mem_nhds_of_mem hzballR
    have hzclLocal : z ∈ closure (Nonres ∩ Metric.closedBall p R) := by
      rw [_root_.mem_closure_iff]
      intro W hWo hzW
      have hWclosedN : W ∩ Metric.closedBall p R ∈ 𝓝 z :=
        inter_mem (hWo.mem_nhds hzW) hclosedN
      obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hWclosedN
      have hmeet := (_root_.mem_closure_iff.mp hzclNonres) V hVo hzV
      rcases hmeet with ⟨y, hyV, hyNonres⟩
      exact ⟨y, (hVsub hyV).1, hyNonres, (hVsub hyV).2⟩
    rwa [hclosure_eq] at hzclLocal
  have hfinNonres : (Nonres ∩ Metric.closedBall p R).Countable := by
    simpa [Nonres] using hfin.countable
  exact hunc (hfinNonres.mono hTsub)

/-- Connected empty-interior geometry plus frontier-density of nonresonant periodic targets creates
the accumulating target set required by the native nonresonant hRigid crossing endpoint. -/
theorem exists_accumulation_nonresonantPeriodic_of_frontier_dense_open
    {c p : ℂ} {Ω : Set ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hΩopen : IsOpen Ω)
    (hpK : p ∈ filledJulia c)
    (hpΩ : p ∈ Ω)
    (hdense : frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)}) :
    ∃ (z₁ : ℂ) (S : Set ℂ), z₁ ∈ Ω ∧ AccPt z₁ (𝓟 S) ∧
      (∀ z ∈ S, z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)) := by
  classical
  obtain ⟨R, hR0, hRΩ⟩ := Metric.isOpen_iff.mp hΩopen p hpΩ
  set r : ℝ := R / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hclosedΩ : Metric.closedBall p r ⊆ Ω := by
    exact (Metric.closedBall_subset_ball (by rw [hrdef]; linarith)).trans hRΩ
  let Nonres : Set ℂ := {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
    (quadratic c)^[q] z = z ∧
    ∀ m : ℕ, 1 ≤ m →
      (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)}
  let S : Set ℂ := Nonres ∩ Metric.closedBall p r
  have hSinf : S.Infinite := by
    simpa [S, Nonres] using
      infinite_nonresonantPeriodic_closedBall_of_frontier_dense_of_not_countable_ball
        (c := c) (p := p) (R := r) hr0
        (not_countable_ball_inter_frontier_filledJulia_of_preconnected_emptyInterior
          hconn hempty hpK (by rw [hrdef]; linarith))
        hdense
  have hSsub : S ⊆ frontier (filledJulia c) ∩ Metric.closedBall p r := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have hKfront : IsCompact (frontier (filledJulia c)) := by
    simpa [juliaSet] using isCompact_juliaSet c
  have hK : IsCompact (frontier (filledJulia c) ∩ Metric.closedBall p r) :=
    hKfront.inter_right isClosed_closedBall
  obtain ⟨z₁, hz₁K, hacc⟩ := hSinf.exists_accPt_of_subset_isCompact hK hSsub
  refine ⟨z₁, S, hclosedΩ hz₁K.2, hacc, ?_⟩
  intro z hz
  exact hz.1

end Bottcher
