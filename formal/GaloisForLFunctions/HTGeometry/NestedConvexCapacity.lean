import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries

/-!
# The affine capacity horizon

A decreasing family of nonempty closed convex subsets of a Hilbert space has a common point
exactly when the distances from the origin stay bounded.  Finite consistency alone is not enough:
the missing global object escapes every bounded-capacity region.

The proof is elementary.  Each set carries a unique nearest point to the origin; the parallelogram
law applied to the midpoint of two such nearest points shows they form a Cauchy sequence as soon
as the distances are bounded, and the limit lies in every member of the family.

The harmonic profile `k ↦ 1/√(k+1)` in `ℓ²` realizes the failure: every finite constraint problem
is exactly solvable while the distances diverge, so the full intersection is empty.
-/

open Filter Metric
open scoped Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

section Capacity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The nested convex capacity criterion.**  A decreasing family of nonempty closed convex sets
in a Hilbert space has a common point exactly when the distances from the origin are bounded. -/
theorem nonempty_iInter_iff_bddAbove_infDist (C : ℕ → Set H)
    (hne : ∀ n, (C n).Nonempty) (hcl : ∀ n, IsClosed (C n)) (hconv : ∀ n, Convex ℝ (C n))
    (hmono : ∀ n, C (n + 1) ⊆ C n) :
    (⋂ n, C n).Nonempty ↔ ∃ R : ℝ, ∀ n, Metric.infDist 0 (C n) ≤ R := by
  have hanti : Antitone C := antitone_nat_of_succ_le hmono
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨‖x‖, fun n => ?_⟩
    have hxn : x ∈ C n := Set.mem_iInter.mp hx n
    have := Metric.infDist_le_dist_of_mem (x := (0 : H)) hxn
    simpa [dist_eq_norm] using this
  · rintro ⟨R, hR⟩
    set d : ℕ → ℝ := fun n => Metric.infDist 0 (C n) with hd
    have hnear : ∀ n, ∃ v ∈ C n, ‖v‖ = d n := by
      intro n
      obtain ⟨v, hv, hnorm⟩ :=
        exists_norm_eq_iInf_of_complete_convex (hne n) ((hcl n).isComplete) (hconv n) 0
      refine ⟨v, hv, ?_⟩
      have hiInf : Metric.infDist (0 : H) (C n) = ⨅ w : C n, ‖(0 : H) - (w : H)‖ := by
        rw [Metric.infDist_eq_iInf]
        exact iInf_congr fun w => dist_eq_norm 0 (w : H)
      show ‖v‖ = Metric.infDist 0 (C n)
      rw [hiInf, ← hnorm, zero_sub, norm_neg]
    choose x hxmem hxnorm using hnear
    have hdnn : ∀ n, 0 ≤ d n := fun n => Metric.infDist_nonneg
    have hdmono : Monotone d := by
      intro n m hnm
      exact Metric.infDist_le_infDist_of_subset (hanti hnm) (hne m)
    have hbdd : BddAbove (Set.range d) := ⟨R, by rintro _ ⟨n, rfl⟩; exact hR n⟩
    set L : ℝ := ⨆ n, d n with hL
    have hdL : ∀ n, d n ≤ L := fun n => le_ciSup hbdd n
    have htendL : Tendsto d atTop (𝓝 L) := tendsto_atTop_ciSup hdmono hbdd
    have hkey : ∀ n m : ℕ, n ≤ m → ‖x n - x m‖ ^ 2 ≤ 2 * ((d m) ^ 2 - (d n) ^ 2) := by
      intro n m hnm
      have hxm : x m ∈ C n := hanti hnm (hxmem m)
      have hmid : (1 / 2 : ℝ) • x n + (1 / 2 : ℝ) • x m ∈ C n :=
        hconv n (hxmem n) hxm (by norm_num) (by norm_num) (by norm_num)
      have hmidnorm : d n ≤ ‖(1 / 2 : ℝ) • x n + (1 / 2 : ℝ) • x m‖ := by
        have hle := Metric.infDist_le_dist_of_mem (x := (0 : H)) hmid
        rw [dist_eq_norm, zero_sub, norm_neg] at hle
        exact hle
      have hsum : (1 / 2 : ℝ) • x n + (1 / 2 : ℝ) • x m = (1 / 2 : ℝ) • (x n + x m) :=
        (smul_add _ _ _).symm
      rw [hsum, norm_smul] at hmidnorm
      have hhalf : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
        rw [Real.norm_eq_abs]; norm_num
      rw [hhalf] at hmidnorm
      have h2 : 2 * d n ≤ ‖x n + x m‖ := by linarith
      have hpar := parallelogram_law_with_norm ℝ (x n) (x m)
      rw [hxnorm n, hxnorm m] at hpar
      nlinarith [norm_nonneg (x n + x m), hdnn n]
    set b : ℕ → ℝ := fun N => Real.sqrt (2 * (L ^ 2 - (d N) ^ 2)) with hb
    have hbtend : Tendsto b atTop (𝓝 0) := by
      have hinner : Tendsto (fun N => 2 * (L ^ 2 - (d N) ^ 2)) atTop (𝓝 (2 * (L ^ 2 - L ^ 2))) :=
        ((tendsto_const_nhds.sub (htendL.pow 2)).const_mul 2)
      have hzero : (2 : ℝ) * (L ^ 2 - L ^ 2) = 0 := by ring
      rw [hzero] at hinner
      have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hinner
      simpa [hb, Function.comp_def] using this
    have hcauchy : CauchySeq x := by
      refine cauchySeq_of_le_tendsto_0 b ?_ hbtend
      intro n m N hNn hNm
      have hstep : ∀ p q : ℕ, N ≤ p → p ≤ q → dist (x p) (x q) ≤ b N := by
        intro p q hNp hpq
        have h1 : ‖x p - x q‖ ^ 2 ≤ 2 * ((d q) ^ 2 - (d p) ^ 2) := hkey p q hpq
        have h2 : 2 * ((d q) ^ 2 - (d p) ^ 2) ≤ 2 * (L ^ 2 - (d N) ^ 2) := by
          have hq : d q ≤ L := hdL q
          have hNp' : d N ≤ d p := hdmono hNp
          nlinarith [hdnn q, hdnn p, hdnn N]
        have h3 : ‖x p - x q‖ ^ 2 ≤ 2 * (L ^ 2 - (d N) ^ 2) := le_trans h1 h2
        rw [dist_eq_norm]
        calc ‖x p - x q‖ = Real.sqrt (‖x p - x q‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (2 * (L ^ 2 - (d N) ^ 2)) := Real.sqrt_le_sqrt h3
      rcases le_total n m with h | h
      · exact hstep n m hNn h
      · rw [dist_comm]
        exact hstep m n hNm h
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨z, Set.mem_iInter.mpr fun n => ?_⟩
    refine (hcl n).mem_of_tendsto hz ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hanti hm (hxmem m)

end Capacity

/-! ## Perfect finite consistency with no global point -/

section HarmonicExample

/-- The harmonic profile `k ↦ 1/√(k+1)`. -/
noncomputable def harmonicProfile (k : ℕ) : ℝ := (Real.sqrt ((k : ℝ) + 1))⁻¹

theorem harmonicProfile_nonneg (k : ℕ) : 0 ≤ harmonicProfile k := by
  rw [harmonicProfile]
  positivity

theorem harmonicProfile_sq (k : ℕ) : harmonicProfile k ^ 2 = ((k : ℝ) + 1)⁻¹ := by
  rw [harmonicProfile, inv_pow, Real.sq_sqrt (by positivity)]

/-- The nested affine constraints prescribing the harmonic profile on an initial segment. -/
def harmonicConstraint (n : ℕ) : Set (lp (fun _ : ℕ => ℝ) 2) :=
  {x | ∀ k ≤ n, x k = harmonicProfile k}

theorem harmonicConstraint_antitone (n : ℕ) :
    harmonicConstraint (n + 1) ⊆ harmonicConstraint n := by
  intro x hx k hk
  exact hx k (by omega)

/-- Every finite harmonic constraint problem is exactly solvable. -/
theorem harmonicConstraint_nonempty (n : ℕ) : (harmonicConstraint n).Nonempty := by
  classical
  have hmem : Memℓp (fun k : ℕ => if k ≤ n then harmonicProfile k else 0) 2 := by
    refine memℓp_gen ?_
    refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) ?_
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have hkn : ¬ k ≤ n := by omega
    simp [hkn]
  refine ⟨⟨_, hmem⟩, ?_⟩
  intro k hk
  show (if k ≤ n then harmonicProfile k else 0) = harmonicProfile k
  simp [hk]

theorem harmonicConstraint_isClosed (n : ℕ) : IsClosed (harmonicConstraint n) := by
  have hrepr : harmonicConstraint n =
      ⋂ k ∈ Finset.range (n + 1),
        (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k) ⁻¹' {harmonicProfile k} := by
    ext x
    simp only [harmonicConstraint, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx k hk
      exact hx k (by omega)
    · intro hx k hk
      exact hx k (by omega)
  rw [hrepr]
  refine isClosed_biInter fun k _ => ?_
  exact IsClosed.preimage (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k).continuous isClosed_singleton

theorem harmonicConstraint_convex (n : ℕ) : Convex ℝ (harmonicConstraint n) := by
  intro x hx y hy a b ha hb hab k hk
  have hxk : x k = harmonicProfile k := hx k hk
  have hyk : y k = harmonicProfile k := hy k hk
  have hval : (a • x + b • y) k = a * x k + b * y k := by
    have h1 : ((a • x + b • y : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) = a • (x : ℕ → ℝ) + b • y := by
      rw [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul]
    rw [show (a • x + b • y : lp (fun _ : ℕ => ℝ) 2) k
      = ((a • x + b • y : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) k from rfl, h1]
    simp
  rw [hval, hxk, hyk, ← add_mul, hab, one_mul]

theorem sqrt_harmonicSum_le_infDist (n : ℕ) :
    Real.sqrt (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)
      ≤ Metric.infDist 0 (harmonicConstraint n) := by
  rw [Metric.le_infDist (harmonicConstraint_nonempty n)]
  intro y hy
  have hsum : ∑ k ∈ Finset.range (n + 1), ‖y k‖ ^ ((2 : ℝ≥0∞).toReal)
      ≤ ‖y‖ ^ ((2 : ℝ≥0∞).toReal) :=
    lp.sum_rpow_le_norm_rpow (by norm_num) y _
  have htoReal : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [htoReal] at hsum
  simp only [Real.rpow_natCast] at hsum
  have hentry : ∀ k ∈ Finset.range (n + 1), ‖y k‖ ^ (2 : ℕ) = ((k : ℝ) + 1)⁻¹ := by
    intro k hk
    have hkn : k ≤ n := by
      simp only [Finset.mem_range] at hk; omega
    rw [hy k hkn, Real.norm_eq_abs, abs_of_nonneg (harmonicProfile_nonneg k),
      harmonicProfile_sq]
  rw [Finset.sum_congr rfl hentry] at hsum
  rw [dist_eq_norm, zero_sub, norm_neg]
  calc Real.sqrt (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)
      ≤ Real.sqrt (‖y‖ ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsum
    _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)

theorem tendsto_infDist_harmonicConstraint_atTop :
    Tendsto (fun n => Metric.infDist 0 (harmonicConstraint n)) atTop atTop := by
  have hharm : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹) atTop atTop := by
    have hbase : Tendsto (fun n => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) atTop atTop :=
      Real.tendsto_sum_range_one_div_nat_succ_atTop
    have heq : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))
        = ∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹ := by
      intro n
      exact Finset.sum_congr rfl fun i _ => one_div _
    simp only [heq] at hbase
    exact hbase.comp (tendsto_add_atTop_nat 1)
  have hsqrt : Tendsto
      (fun n => Real.sqrt (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hharm
  exact tendsto_atTop_mono sqrt_harmonicSum_le_infDist hsqrt

/-- **Perfect finite consistency with no global point.**  Every finite harmonic constraint problem
is exactly solvable, the sets are nested nonempty closed convex, yet the intersection is empty:
the missing global object escapes every bounded-capacity region. -/
theorem harmonicConstraint_iInter_eq_empty : (⋂ n, harmonicConstraint n) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  intro hne
  obtain ⟨R, hR⟩ := (nonempty_iInter_iff_bddAbove_infDist harmonicConstraint
    harmonicConstraint_nonempty harmonicConstraint_isClosed harmonicConstraint_convex
    harmonicConstraint_antitone).mp hne
  have hlt := (tendsto_infDist_harmonicConstraint_atTop.eventually_gt_atTop R).exists
  obtain ⟨n, hn⟩ := hlt
  exact absurd (hR n) (not_le.mpr hn)

end HarmonicExample

end GaloisForLFunctions.HTGeometry
