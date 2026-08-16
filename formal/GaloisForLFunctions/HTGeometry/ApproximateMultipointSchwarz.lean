import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# An approximate multipoint Schwarz bound

An entire function whose first `q` derivatives are merely *small* at each of finitely many nodes
does not vanish there, so the exact factorisation by the node polynomial is unavailable.  Two
maximum-principle steps replace it.

Cauchy's estimate splits the Taylor series at a node into a head governed by the derivative bound
and a geometric tail governed by the boundary maximum; this makes the function small on a whole
small disc about the node.  The quotient of the function by the node polynomial is then holomorphic
on the large disc punctured by those small discs, and the maximum principle on that domain carries
the two boundary bounds to the interior.

With exactly vanishing derivatives the first step returns `0` and the statement collapses to the
classical multipoint Schwarz bound.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Metric Finset

/-! ## Local smallness from small derivatives

At a single node, the Taylor head is controlled by the derivative bound and the tail by Cauchy's
estimate on a circle of radius `r` about that node.
-/

/-- **Small derivatives make an entire function small on a whole disc.**  The head of the Taylor
series contributes `ε exp ρ` and the tail is the geometric series `M (ρ/r)^q / (1 - ρ/r)`. -/
theorem norm_le_of_forall_norm_iteratedDeriv_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {q : ℕ} {ε ρ r M : ℝ}
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hr : ρ < r)
    (hderiv : ∀ k, k < q → ‖iteratedDeriv k f c‖ ≤ ε)
    (hM : ∀ w ∈ sphere c r, ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z - c‖ ≤ ρ) :
    ‖f z‖ ≤ ε * Real.exp ρ + M * (ρ / r) ^ q / (1 - ρ / r) := by
  have hrpos : 0 < r := lt_of_le_of_lt hρ hr
  have hMnn : 0 ≤ M := by
    refine le_trans (norm_nonneg (f (c + (r : ℂ)))) (hM (c + (r : ℂ)) ?_)
    simp [Metric.mem_sphere_iff_norm, abs_of_pos hrpos]
  have hq : (0 : ℝ) ≤ ρ / r := div_nonneg hρ hrpos.le
  have hq1 : ρ / r < 1 := (div_lt_one hrpos).mpr hr
  -- the Taylor series of `f` at `c`
  set g : ℕ → ℂ := fun n => ((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv n f c with hg
  have hsum : HasSum g (f z) := Complex.hasSum_taylorSeries_of_entire hf c z
  have hgnorm : ∀ n, ‖g n‖ = ‖iteratedDeriv n f c‖ * ‖z - c‖ ^ n / (n ! : ℝ) := by
    intro n
    rw [hg]
    simp only [norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
    field_simp
    ring
  -- Cauchy's estimate at the node
  have hcauchy : ∀ n, ‖iteratedDeriv n f c‖ ≤ (n ! : ℝ) * M / r ^ n := fun n =>
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hrpos
      (hf.diffContOnCl) hM
  have hgeo : ∀ n, ‖g n‖ ≤ M * (ρ / r) ^ n := by
    intro n
    rw [hgnorm n]
    have h1 : ‖iteratedDeriv n f c‖ * ‖z - c‖ ^ n ≤ ((n ! : ℝ) * M / r ^ n) * ρ ^ n := by
      refine mul_le_mul (hcauchy n) (pow_le_pow_left₀ (norm_nonneg _) hz n)
        (pow_nonneg (norm_nonneg _) n) ?_
      positivity
    have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
    rw [div_le_iff₀ hfac]
    refine h1.trans (le_of_eq ?_)
    rw [div_pow]
    field_simp
    ring
  have hsummable : Summable g := hsum.summable
  -- split the series at `q`
  have hsplit : ∑ n ∈ range q, g n + ∑' n, g (n + q) = f z := by
    rw [hsummable.sum_add_tsum_nat_add q, hsum.tsum_eq]
  -- head
  have hhead : ‖∑ n ∈ range q, g n‖ ≤ ε * Real.exp ρ := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ range q, ‖g n‖ ≤ ε * (ρ ^ n / (n ! : ℝ)) := by
      intro n hn
      rw [hgnorm n]
      have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
      rw [div_le_iff₀ hfac]
      have h1 : ‖iteratedDeriv n f c‖ * ‖z - c‖ ^ n ≤ ε * ρ ^ n :=
        mul_le_mul (hderiv n (mem_range.mp hn)) (pow_le_pow_left₀ (norm_nonneg _) hz n)
          (pow_nonneg (norm_nonneg _) n) hε
      refine h1.trans (le_of_eq ?_)
      field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hρ q) hε
  -- tail
  have htailsummable : Summable fun n => ‖g (n + q)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hgeo (n + q)) ?_
    exact ((summable_geometric_of_lt_one hq hq1).mul_left M).comp_injective
      (add_left_injective q)
  have htail : ‖∑' n, g (n + q)‖ ≤ M * (ρ / r) ^ q / (1 - ρ / r) := by
    refine le_trans (norm_tsum_le_tsum_norm htailsummable) ?_
    have hle : ∑' n, ‖g (n + q)‖ ≤ ∑' n : ℕ, M * (ρ / r) ^ (n + q) := by
      refine Summable.tsum_le_tsum (fun n => hgeo (n + q)) htailsummable ?_
      exact ((summable_geometric_of_lt_one hq hq1).mul_left M).comp_injective
        (add_left_injective q)
    refine hle.trans (le_of_eq ?_)
    have hexp : ∀ n : ℕ, M * (ρ / r) ^ (n + q) = (M * (ρ / r) ^ q) * (ρ / r) ^ n := by
      intro n
      rw [pow_add]
      ring
    rw [tsum_congr hexp, (summable_geometric_of_lt_one hq hq1).tsum_mul_left,
      tsum_geometric_of_lt_one hq hq1]
    ring
  calc ‖f z‖ = ‖∑ n ∈ range q, g n + ∑' n, g (n + q)‖ := by rw [hsplit]
    _ ≤ ‖∑ n ∈ range q, g n‖ + ‖∑' n, g (n + q)‖ := norm_add_le _ _
    _ ≤ ε * Real.exp ρ + M * (ρ / r) ^ q / (1 - ρ / r) := add_le_add hhead htail

/-! ## The node polynomial and the punctured maximum principle -/

/-- The node polynomial of a finite set of nodes with a common multiplicity. -/
def nodePoly (nodes : Finset ℂ) (q : ℕ) (z : ℂ) : ℂ := ∏ c ∈ nodes, (z - c) ^ q

theorem norm_nodePoly (nodes : Finset ℂ) (q : ℕ) (z : ℂ) :
    ‖nodePoly nodes q z‖ = ∏ c ∈ nodes, ‖z - c‖ ^ q := by
  rw [nodePoly, norm_prod]
  exact Finset.prod_congr rfl fun c _ => norm_pow _ _

/-- Uniform separation from every node gives the sharp lower bound for the node polynomial. -/
theorem pow_le_norm_nodePoly {nodes : Finset ℂ} {q : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ}
    (hz : ∀ c ∈ nodes, ρ ≤ ‖z - c‖) :
    ρ ^ (q * nodes.card) ≤ ‖nodePoly nodes q z‖ := by
  rw [norm_nodePoly]
  calc ρ ^ (q * nodes.card) = ∏ _c ∈ nodes, ρ ^ q := by
        rw [Finset.prod_const, mul_comm, pow_mul]
    _ ≤ ∏ c ∈ nodes, ‖z - c‖ ^ q := by
        refine Finset.prod_le_prod (fun c _ => pow_nonneg hρ q) fun c hc => ?_
        exact pow_le_pow_left₀ hρ (hz c hc) q

/-- The node polynomial is nonzero away from the nodes. -/
theorem nodePoly_ne_zero {nodes : Finset ℂ} {q : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ}
    (hz : ∀ c ∈ nodes, ρ ≤ ‖z - c‖) : nodePoly nodes q z ≠ 0 := by
  rw [nodePoly]
  refine Finset.prod_ne_zero_iff.mpr fun c hc => pow_ne_zero q ?_
  intro hzero
  rw [hzero] at hz
  simpa using lt_of_lt_of_le hρ (hz c hc)

/-- **Approximate multipoint Schwarz bound.**  Smallness on the small circles around the nodes and
a boundary bound on the large circle transfer to the interior through the node polynomial.  No
vanishing hypothesis is used: the classical statement is the case `εloc = 0`. -/
theorem approximate_multipoint_schwarz
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : Finset ℂ) (q : ℕ)
    {ρ R εloc M D : ℝ} (hρ : 0 < ρ) (hD : 0 < D)
    (hloc : ∀ c ∈ nodes, ∀ w, ‖w - c‖ = ρ → ‖f w‖ ≤ εloc)
    (hbd : ∀ w ∈ sphere (0 : ℂ) R, ‖f w‖ ≤ M)
    (hDlow : ∀ w ∈ sphere (0 : ℂ) R, D ≤ ‖nodePoly nodes q w‖)
    {z : ℂ} (hzR : ‖z‖ < R) (hzout : ∀ c ∈ nodes, ρ < ‖z - c‖) :
    ‖f z‖ * ρ ^ (q * nodes.card) ≤
      max εloc (M * ρ ^ (q * nodes.card) / D) * ‖nodePoly nodes q z‖ := by
  classical
  set N := q * nodes.card with hN
  set U : Set ℂ := ball (0 : ℂ) R \ ⋃ c ∈ nodes, closedBall c ρ with hU
  -- every limit point of `U` stays `ρ`-away from each node
  have hfar : ∀ w ∈ closure U, ∀ c ∈ nodes, ρ ≤ ‖w - c‖ := by
    have hclosed : IsClosed {w : ℂ | ∀ c ∈ nodes, ρ ≤ ‖w - c‖} := by
      have : {w : ℂ | ∀ c ∈ nodes, ρ ≤ ‖w - c‖} = ⋂ c ∈ nodes, {w : ℂ | ρ ≤ ‖w - c‖} := by
        ext w; simp
      rw [this]
      refine isClosed_biInter fun c _ => ?_
      exact isClosed_le continuous_const (by fun_prop)
    intro w hw
    refine (closure_minimal ?_ hclosed) hw
    intro v hv c hc
    have : v ∉ closedBall c ρ := fun hmem =>
      hv.2 (Set.mem_biUnion hc hmem)
    simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using this.le
  have hball : closure U ⊆ closedBall (0 : ℂ) R := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    exact fun w hw => ball_subset_closedBall hw.1
  -- the quotient by the node polynomial
  set G : ℂ → ℂ := fun w => f w * ((ρ : ℂ) ^ N / nodePoly nodes q w) with hG
  have hGdiff : ∀ w ∈ closure U, DifferentiableAt ℂ G w := by
    intro w hw
    have hne : nodePoly nodes q w ≠ 0 := nodePoly_ne_zero hρ (hfar w hw)
    have hpoly : DifferentiableAt ℂ (fun v => nodePoly nodes q v) w := by
      rw [nodePoly]
      exact DifferentiableAt.finset_prod fun c _ => by fun_prop
    exact (hf w).mul ((differentiableAt_const _).div hpoly hne)
  have hGcl : DiffContOnCl ℂ G U :=
    ⟨fun w hw => (hGdiff w (subset_closure hw)).differentiableWithinAt,
      fun w hw => (hGdiff w hw).continuousAt.continuousWithinAt⟩
  -- boundary control
  have hfrontier : ∀ w ∈ frontier U, ‖G w‖ ≤ max εloc (M * ρ ^ N / D) := by
    intro w hw
    have hwcl : w ∈ closure U := frontier_subset_closure hw
    have hfarw := hfar w hwcl
    have hne : nodePoly nodes q w ≠ 0 := nodePoly_ne_zero hρ hfarw
    have hlow : ρ ^ N ≤ ‖nodePoly nodes q w‖ := pow_le_norm_nodePoly hρ.le hfarw
    have hGw : ‖G w‖ = ‖f w‖ * ρ ^ N / ‖nodePoly nodes q w‖ := by
      rw [hG]
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ]
      ring
    have hwnotU : w ∉ U := by
      have hopen : IsOpen U := by
        rw [hU]
        refine Metric.isOpen_ball.sdiff ?_
        exact isClosed_biUnion_finset fun c _ => Metric.isClosed_closedBall
      have := hopen.frontier_eq ▸ hw
      exact this.2
    by_cases hsphere : ‖w‖ = R
    · -- outer boundary
      have hb : ‖f w‖ ≤ M := hbd w (by simpa [Metric.mem_sphere_iff_norm] using hsphere)
      have hd : D ≤ ‖nodePoly nodes q w‖ :=
        hDlow w (by simpa [Metric.mem_sphere_iff_norm] using hsphere)
      refine le_trans (le_of_eq hGw) (le_trans ?_ (le_max_right _ _))
      rw [div_le_div_iff₀ (lt_of_lt_of_le hD hd) hD]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hb (pow_nonneg hρ.le N)) hd hD.le
        (mul_nonneg (le_trans (norm_nonneg _) hb) (pow_nonneg hρ.le N))
    · -- inner boundary: `w` lies on one of the small circles
      have hwR : ‖w‖ < R := lt_of_le_of_ne (by simpa [Metric.mem_closedBall, dist_eq_norm]
        using hball hwcl) hsphere
      have hnode : ∃ c ∈ nodes, ‖w - c‖ = ρ := by
        by_contra hcon
        push_neg at hcon
        refine hwnotU ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hwR, ?_⟩
        intro hmem
        obtain ⟨c, hc, hmemc⟩ := Set.mem_iUnion₂.mp hmem
        have h1 : ‖w - c‖ ≤ ρ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hmemc
        exact hcon c hc (le_antisymm h1 (hfarw c hc))
      obtain ⟨c, hc, hcρ⟩ := hnode
      refine le_trans (le_of_eq hGw) (le_trans ?_ (le_max_left _ _))
      rw [div_le_iff₀ (lt_of_lt_of_le (pow_pos hρ N) hlow)]
      have hfw : ‖f w‖ ≤ εloc := hloc c hc w hcρ
      calc ‖f w‖ * ρ ^ N ≤ εloc * ρ ^ N :=
            mul_le_mul_of_nonneg_right hfw (pow_nonneg hρ.le N)
        _ ≤ εloc * ‖nodePoly nodes q w‖ := by
            refine mul_le_mul_of_nonneg_left hlow ?_
            exact le_trans (norm_nonneg _) hfw
  -- the maximum principle on the punctured disc
  have hzU : z ∈ U := by
    refine ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hzR, ?_⟩
    intro hmem
    obtain ⟨c, hc, hmemc⟩ := Set.mem_iUnion₂.mp hmem
    have : ‖z - c‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hmemc
    exact absurd this (not_le.mpr (hzout c hc))
  have hbounded : Bornology.IsBounded U := Metric.isBounded_ball.subset (fun w hw => hw.1)
  have hGz : ‖G z‖ ≤ max εloc (M * ρ ^ N / D) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hbounded hGcl hfrontier (subset_closure hzU)
  have hne : nodePoly nodes q z ≠ 0 :=
    nodePoly_ne_zero hρ fun c hc => (hzout c hc).le
  have hGzval : ‖G z‖ = ‖f z‖ * ρ ^ N / ‖nodePoly nodes q z‖ := by
    rw [hG]
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    ring
  rw [hGzval, div_le_iff₀ (norm_pos_iff.mpr hne)] at hGz
  exact hGz

/-! ## The assembled bound

The two steps combine into the form used by extrapolation arguments: small derivatives at the nodes
and a boundary bound produce an interior estimate whose only trace of the nodes is the node
polynomial.
-/

/-- **Extrapolation from approximate zeros.**  Derivative smallness of order `q` at every node,
together with boundary control on the small circles' radius `r` and on the large circle, bounds the
function at any interior point away from the nodes. -/
theorem norm_le_of_forall_norm_iteratedDeriv_le_multipoint
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : Finset ℂ) (q : ℕ)
    {ε ρ r R M D : ℝ} (hε : 0 ≤ ε) (hρ : 0 < ρ) (hr : ρ < r) (hD : 0 < D)
    (hderiv : ∀ c ∈ nodes, ∀ k, k < q → ‖iteratedDeriv k f c‖ ≤ ε)
    (hMr : ∀ c ∈ nodes, ∀ w ∈ sphere c r, ‖f w‖ ≤ M)
    (hbd : ∀ w ∈ sphere (0 : ℂ) R, ‖f w‖ ≤ M)
    (hDlow : ∀ w ∈ sphere (0 : ℂ) R, D ≤ ‖nodePoly nodes q w‖)
    {z : ℂ} (hzR : ‖z‖ < R) (hzout : ∀ c ∈ nodes, ρ < ‖z - c‖) :
    ‖f z‖ * ρ ^ (q * nodes.card) ≤
      max (ε * Real.exp ρ + M * (ρ / r) ^ q / (1 - ρ / r))
        (M * ρ ^ (q * nodes.card) / D) * ‖nodePoly nodes q z‖ := by
  refine approximate_multipoint_schwarz hf nodes q hρ hD ?_ hbd hDlow hzR hzout
  intro c hc w hw
  exact norm_le_of_forall_norm_iteratedDeriv_le hf hε hρ.le hr (hderiv c hc)
    (hMr c hc) (le_of_eq hw)

end GaloisForLFunctions.HTGeometry
