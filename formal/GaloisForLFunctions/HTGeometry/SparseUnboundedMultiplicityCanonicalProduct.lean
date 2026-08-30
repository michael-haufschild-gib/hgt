import GaloisForLFunctions.HTGeometry.CanonicalProductE1Divisor
import GaloisForLFunctions.RHTower.XiZeroSumDivergence
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.HTGeometry.OrderOneEnvelope

/-!
# Sparse unbounded-multiplicity order-one canonical product

The cubic nodes `((k+1)^3 + 3/2)` with multiplicity `k+1` have summable first reciprocal mass.
Their genus-one canonical product is therefore entire and lies in the order-one envelope, while
its analytic order at the `k`-th node is exactly `k+1`.  This is the positive survivor exposed by
the sparse-unbounded-jet FZZ no-go: unbounded local multiplicity is compatible with order-one
growth when cumulative weighted density is sparse enough.

**[PROVED HERE]** This file closes first- and second-reciprocal summability with multiplicity,
local finiteness, exact fiber cardinality, exact analytic order, and the global growth envelope.
-/

open Complex Set Filter

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.CountableDivisor

/-- Multiplicity copies above the `k`-th sparse physical response node. -/
abbrev SparseJetMultiplicityIndex := Σ k : ℕ, Fin (k + 1)

/-- Cubic sparse physical response order. -/
def sparseJetPhysicalNode (k : ℕ) : ℕ := (k + 1) ^ 3

/-- Positive centered canonical-product node corresponding to `sparseJetPhysicalNode k`. -/
def sparseJetCenteredNode (k : ℕ) : ℝ :=
  (sparseJetPhysicalNode k : ℝ) + 3 / 2

/-- Repeated genus-one divisor: the `k`-th node occurs `k+1` times. -/
def sparseJetDivisorPoint (q : SparseJetMultiplicityIndex) : ℂ :=
  (sparseJetCenteredNode q.1 : ℂ)

/-- Genus-one product carrying sparse unbounded multiplicities. -/
def sparseJetCanonicalProduct : ℂ → ℂ :=
  canonicalProductE1Indexed sparseJetDivisorPoint

private theorem summable_one_div_nat_succ_sq :
    Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff
    (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hbase
  exact hshift.congr fun k => by
    push_cast
    ring

theorem sparseJetDivisorPoint_norm (q : SparseJetMultiplicityIndex) :
    ‖sparseJetDivisorPoint q‖ =
      (((q.1 + 1 : ℕ) : ℝ) ^ 3 + 3 / 2) := by
  rw [sparseJetDivisorPoint, sparseJetCenteredNode, sparseJetPhysicalNode,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  · push_cast
    ring
  · positivity

theorem sparseJetDivisorPoint_ne_zero (q : SparseJetMultiplicityIndex) :
    sparseJetDivisorPoint q ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [sparseJetDivisorPoint_norm]
  positivity

theorem sparseJetDivisorPoint_inv_summable :
    Summable (fun q : SparseJetMultiplicityIndex => 1 / ‖sparseJetDivisorPoint q‖) := by
  rw [summable_sigma_of_nonneg (fun q => by positivity)]
  constructor
  · intro k
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => by positivity)
      (fun k => ?_) summable_one_div_nat_succ_sq
    have hx : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    have hden : 0 < (((k + 1 : ℕ) : ℝ) ^ 3 + 3 / 2) := by positivity
    rw [tsum_fintype]
    simp only [sparseJetDivisorPoint_norm, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div]
    rw [div_le_div_iff₀ hden (pow_pos hx 2)]
    nlinarith [sq_nonneg (((k + 1 : ℕ) : ℝ))]

theorem sparseJetDivisorPoint_inv_sq_summable :
    Summable (fun q : SparseJetMultiplicityIndex => 1 / ‖sparseJetDivisorPoint q‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    sparseJetDivisorPoint_inv_summable
  have hp : 0 < ‖sparseJetDivisorPoint q‖ :=
    norm_pos_iff.mpr (sparseJetDivisorPoint_ne_zero q)
  have h1 : 1 ≤ ‖sparseJetDivisorPoint q‖ := by
    rw [sparseJetDivisorPoint_norm]
    have hx : (1 : ℝ) ≤ (((q.1 + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le q.1)
    nlinarith [sq_nonneg (((q.1 + 1 : ℕ) : ℝ))]
  rw [div_le_div_iff₀ (pow_pos hp 2) hp]
  nlinarith [sq_nonneg ‖sparseJetDivisorPoint q‖]

theorem sparseJetDivisorPoint_locallyFinite :
    LocallyFiniteDivisor sparseJetDivisorPoint := by
  intro r
  let S : ℝ := max r 0 + 1
  have hS : 0 < S := by
    dsimp [S]
    linarith [le_max_right r 0]
  have hev : {q : SparseJetMultiplicityIndex | S ≤ ‖sparseJetDivisorPoint q‖} ∈
      (cofinite : Filter SparseJetMultiplicityIndex) :=
    eventually_norm_ge_of_summable_inv_sq sparseJetDivisorPoint_ne_zero
      sparseJetDivisorPoint_inv_sq_summable hS
  have hfin : {q : SparseJetMultiplicityIndex | S ≤ ‖sparseJetDivisorPoint q‖}ᶜ.Finite :=
    Filter.mem_cofinite.mp hev
  refine hfin.subset ?_
  intro q hq
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  exact lt_of_le_of_lt (hq.trans (le_max_left r 0)) (lt_add_one _)

theorem sparseJetCenteredNode_injective : Function.Injective sparseJetCenteredNode := by
  intro k l h
  have hpowR : (((k + 1) ^ 3 : ℕ) : ℝ) = (((l + 1) ^ 3 : ℕ) : ℝ) := by
    dsimp [sparseJetCenteredNode, sparseJetPhysicalNode] at h
    linarith
  have hpowN : (k + 1) ^ 3 = (l + 1) ^ 3 := by
    exact_mod_cast hpowR
  have hadd : k + 1 = l + 1 := Nat.pow_left_injective (by norm_num : 3 ≠ 0) hpowN
  omega

theorem sparseJetDivisorPoint_fiber_ncard (k : ℕ) :
    {q : SparseJetMultiplicityIndex |
      sparseJetDivisorPoint q = (sparseJetCenteredNode k : ℂ)}.ncard = k + 1 := by
  let e : Fin (k + 1) → SparseJetMultiplicityIndex := fun j => ⟨k, j⟩
  have heinj : Function.Injective e := by
    intro a b h
    have hv : a.val = b.val := congrArg (fun q : SparseJetMultiplicityIndex => q.2.val) h
    exact Fin.ext hv
  have hfiber : {q : SparseJetMultiplicityIndex |
      sparseJetDivisorPoint q = (sparseJetCenteredNode k : ℂ)} = Set.range e := by
    ext q
    rcases q with ⟨l, j⟩
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro h
      have hlk : l = k := by
        apply sparseJetCenteredNode_injective
        dsimp [sparseJetDivisorPoint] at h
        exact_mod_cast h
      subst l
      exact ⟨j, rfl⟩
    · rintro ⟨j', hq⟩
      rw [← hq]
      rfl
  rw [hfiber, Set.ncard_range_of_injective heinj, Nat.card_fin]

theorem differentiable_sparseJetCanonicalProduct :
    Differentiable ℂ sparseJetCanonicalProduct := by
  intro z
  exact (canonicalProductE1Indexed_analytic sparseJetDivisorPoint
    sparseJetDivisorPoint_ne_zero sparseJetDivisorPoint_inv_sq_summable
      z (Set.mem_univ z)).differentiableAt

theorem sparseJetCanonicalProduct_ne_zero {z : ℂ}
    (hz : ∀ k : ℕ, z ≠ (sparseJetCenteredNode k : ℂ)) :
    sparseJetCanonicalProduct z ≠ 0 := by
  apply canonicalProductE1Indexed_ne_zero sparseJetDivisorPoint
    sparseJetDivisorPoint_ne_zero sparseJetDivisorPoint_inv_sq_summable
  intro q h
  exact hz q.1 (by simpa [sparseJetDivisorPoint] using h)

theorem analyticOrderAt_sparseJetCanonicalProduct (k : ℕ) :
    analyticOrderAt sparseJetCanonicalProduct (sparseJetCenteredNode k : ℂ) =
      ((k + 1 : ℕ) : ℕ∞) := by
  have hkne : (sparseJetCenteredNode k : ℂ) ≠ 0 := by
    intro h
    have hreal : sparseJetCenteredNode k = 0 := by exact_mod_cast h
    have hpos : 0 < sparseJetCenteredNode k := by
      dsimp [sparseJetCenteredNode, sparseJetPhysicalNode]
      positivity
    linarith
  rw [sparseJetCanonicalProduct,
    analyticOrderAt_canonicalProductE1Indexed sparseJetDivisorPoint_ne_zero
      sparseJetDivisorPoint_locallyFinite sparseJetDivisorPoint_inv_sq_summable hkne,
    sparseJetDivisorPoint_fiber_ncard]

/-- Sparse unbounded-multiplicity canonical products remain in the order-one envelope. -/
theorem orderOneEnvelope_sparseJetCanonicalProduct :
    OrderOneEnvelope sparseJetCanonicalProduct := by
  let S : ℝ := ∑' q : SparseJetMultiplicityIndex, 1 / ‖sparseJetDivisorPoint q‖
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + 2 * S / Real.log 2, by positivity, fun z => ?_⟩
  refine (norm_canonicalProductE1Indexed_le_exp_of_summable_inv
    sparseJetDivisorPoint sparseJetDivisorPoint_ne_zero
    sparseJetDivisorPoint_inv_sq_summable sparseJetDivisorPoint_inv_summable z).trans ?_
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have hlognn : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hshape : ‖z‖ * Real.log 2 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
    calc
      ‖z‖ * Real.log 2 ≤ ‖z‖ * Real.log (2 + ‖z‖) :=
        mul_le_mul_of_nonneg_left hlog (norm_nonneg z)
      _ ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
        exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg z]) hlognn
  have hscale : 0 ≤ 2 * S / Real.log 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hshape hscale
  have hcancel : (2 * S / Real.log 2) * (‖z‖ * Real.log 2) = 2 * ‖z‖ * S := by
    field_simp
  rw [hcancel] at hmul
  rw [orderOneWeight]
  nlinarith [shape_nonneg z]

/-- Exact reusable survivor package: an order-one entire function with multiplicities `k+1`
at cubic-spaced centered nodes and no accidental zeros. -/
theorem sparseJetCanonicalProduct_package :
    Differentiable ℂ sparseJetCanonicalProduct ∧
      OrderOneEnvelope sparseJetCanonicalProduct ∧
      (∀ k : ℕ,
        analyticOrderAt sparseJetCanonicalProduct (sparseJetCenteredNode k : ℂ) =
          ((k + 1 : ℕ) : ℕ∞)) := by
  exact ⟨differentiable_sparseJetCanonicalProduct,
    orderOneEnvelope_sparseJetCanonicalProduct,
    analyticOrderAt_sparseJetCanonicalProduct⟩

end RHTower
