/-
Finite interval dissection for Bourgain's critical-line zeta argument.

An antitone chain of cut points tiles `(d K,d 0]`.  Triangle inequality
reduces its Dirichlet sum to block sums.  Combining that partition with
`norm_sum_Ioc_critical_cpow_le` gives the exact partial-summation and block
dissection step used after the approximate functional equation.
-/
import GaloisForLFunctions.RHTower.BourgainPartialSummation
import GaloisForLFunctions.HTGeometry.IocPartitionSum

open Complex

namespace RHTower

/-- Norm of a sum over an interval is at most the sum of norms over any
antitone finite partition of that interval. -/
theorem norm_sum_Ioc_partition_le
    (F : ℕ → ℂ) (d : ℕ → ℕ) (K : ℕ)
    (hanti : ∀ k, k < K → d (k + 1) ≤ d k) :
    ‖∑ n ∈ Finset.Ioc (d K) (d 0), F n‖
      ≤ ∑ k ∈ Finset.range K,
          ‖∑ n ∈ Finset.Ioc (d (k + 1)) (d k), F n‖ := by
  rw [← HTGeometry.sum_Ioc_partition F d K hanti]
  exact norm_sum_le _ _

/-- Uniform block control loses only the number of blocks. -/
theorem norm_sum_Ioc_partition_le_mul
    (F : ℕ → ℂ) (d : ℕ → ℕ) (K : ℕ)
    (hanti : ∀ k, k < K → d (k + 1) ≤ d k)
    {B : ℝ}
    (hblock : ∀ k < K, ‖∑ n ∈ Finset.Ioc (d (k + 1)) (d k), F n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc (d K) (d 0), F n‖ ≤ K * B := by
  calc
    ‖∑ n ∈ Finset.Ioc (d K) (d 0), F n‖
        ≤ ∑ k ∈ Finset.range K,
            ‖∑ n ∈ Finset.Ioc (d (k + 1)) (d k), F n‖ :=
      norm_sum_Ioc_partition_le F d K hanti
    _ ≤ ∑ _k ∈ Finset.range K, B := by
      gcongr with k hk
      exact hblock k (Finset.mem_range.mp hk)
    _ = K * B := by simp

/-- **Bourgain block-dissection bridge.** On every block, a bound for all
unweighted logarithmic phase partial sums transfers to the critical-line
Dirichlet block. Summing over an antitone partition gives the displayed
global estimate. -/
theorem norm_sum_Ioc_critical_cpow_partition_le
    (d : ℕ → ℕ) (K : ℕ)
    (hstrict : ∀ k, k < K → d (k + 1) < d k)
    (t : ℝ) (B : ℕ → ℝ)
    (hpartial : ∀ k, k < K → ∀ n ∈ Finset.Ioc (d (k + 1)) (d k),
      ‖∑ m ∈ Finset.Ioc (d (k + 1)) n,
          (m : ℂ) ^ (-Complex.I * (t : ℂ))‖ ≤ B k) :
    ‖∑ n ∈ Finset.Ioc (d K) (d 0),
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖
      ≤ ∑ k ∈ Finset.range K,
          B k * ((d (k + 1) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  calc
    ‖∑ n ∈ Finset.Ioc (d K) (d 0),
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖
        ≤ ∑ k ∈ Finset.range K,
            ‖∑ n ∈ Finset.Ioc (d (k + 1)) (d k),
                (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖ :=
      norm_sum_Ioc_partition_le _ d K (fun k hk => (hstrict k hk).le)
    _ ≤ ∑ k ∈ Finset.range K,
          B k * ((d (k + 1) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      gcongr with k hk
      exact norm_sum_Ioc_critical_cpow_le
        (hstrict k (Finset.mem_range.mp hk)) t
        (hpartial k (Finset.mem_range.mp hk))

/-- Descending dyadic cut `⌊N/2ᵏ⌋`. -/
def bourgainDyadicCut (N k : ℕ) : ℕ := N / 2 ^ k

/-- Number of descending dyadic blocks required to reach zero. -/
def bourgainDyadicDepth (N : ℕ) : ℕ := N.log2 + 1

@[simp] theorem bourgainDyadicCut_zero (N : ℕ) :
    bourgainDyadicCut N 0 = N := by
  simp [bourgainDyadicCut]

@[simp] theorem bourgainDyadicCut_depth (N : ℕ) :
    bourgainDyadicCut N (bourgainDyadicDepth N) = 0 := by
  rw [bourgainDyadicCut, bourgainDyadicDepth, Nat.div_eq_zero_iff]
  exact Or.inr Nat.lt_log2_self

/-- Every nonterminal descending dyadic cut is strictly smaller than its
predecessor. -/
theorem bourgainDyadicCut_strict {N : ℕ} (hN : 0 < N)
    {k : ℕ} (hk : k < bourgainDyadicDepth N) :
    bourgainDyadicCut N (k + 1) < bourgainDyadicCut N k := by
  have hklog : k ≤ N.log2 := by
    simpa [bourgainDyadicDepth] using hk
  have hpow : 2 ^ k ≤ N := (Nat.le_log2 hN.ne').mp hklog
  have hpos : 0 < N / 2 ^ k := Nat.div_pos hpow (by positivity)
  rw [bourgainDyadicCut, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.div_lt_self hpos (by omega)

/-- The explicit descending dyadic blocks partition `(0,N]` exactly. -/
theorem sum_bourgainDyadicBlocks
    (F : ℕ → ℂ) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range (bourgainDyadicDepth N),
        ∑ n ∈ Finset.Ioc (bourgainDyadicCut N (k + 1)) (bourgainDyadicCut N k), F n
      = ∑ n ∈ Finset.Ioc 0 N, F n := by
  simpa using HTGeometry.sum_Ioc_partition F (bourgainDyadicCut N)
    (bourgainDyadicDepth N)
    (fun k hk => (bourgainDyadicCut_strict hN hk).le)

/-- Critical-line specialization on the explicit dyadic partition of `(0,N]`.
This is the finite dyadic-dissection conclusion invoked after Bourgain's
short exponential-sum estimates. -/
theorem norm_sum_Ioc_critical_cpow_dyadic_le
    {N : ℕ} (hN : 0 < N) (t : ℝ) (B : ℕ → ℝ)
    (hpartial : ∀ k, k < bourgainDyadicDepth N →
      ∀ n ∈ Finset.Ioc (bourgainDyadicCut N (k + 1)) (bourgainDyadicCut N k),
        ‖∑ m ∈ Finset.Ioc (bourgainDyadicCut N (k + 1)) n,
            (m : ℂ) ^ (-Complex.I * (t : ℂ))‖ ≤ B k) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖
      ≤ ∑ k ∈ Finset.range (bourgainDyadicDepth N),
          B k * ((bourgainDyadicCut N (k + 1) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  simpa using norm_sum_Ioc_critical_cpow_partition_le
    (bourgainDyadicCut N) (bourgainDyadicDepth N)
    (fun k hk => bourgainDyadicCut_strict hN hk) t B hpartial

end RHTower
