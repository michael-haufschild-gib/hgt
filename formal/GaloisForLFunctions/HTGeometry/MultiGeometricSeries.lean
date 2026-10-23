import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# The geometric series in several variables

The product of the geometric series of finitely many contractions is the sum, over all multi-indices,
of the corresponding monomials.  Grouping the multi-indices by total degree turns this into a series
indexed by the degree, whose terms are the finite sums over the tuples of a given sum.  This is the
expansion of the Cauchy kernel of a polydisc.

* `summable_multiGeometric_nonneg` : summability of the monomials of nonnegative contractions.
* `hasSum_multiGeometric` : the multi-variable geometric series.
* `hasSum_degree_regroup` : regrouping a multi-index family by total degree.
-/

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

section Regroup

variable {α : Type*} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α]

omit [T2Space α] in
/-- **Regrouping a family indexed by multi-indices according to the total degree.** -/
theorem hasSum_degree_regroup {n : ℕ} {g : (Fin n → ℕ) → α} {S : α} (h : HasSum g S) :
    HasSum (fun k : ℕ => ∑ m ∈ Finset.Nat.antidiagonalTuple n k, g m) S := by
  classical
  have hfib : ∀ k : ℕ, HasSum (fun x : {m : Fin n → ℕ // ∑ i, m i = k} => g x.1)
      (∑ m ∈ Finset.Nat.antidiagonalTuple n k, g m) := by
    intro k
    haveI : Fintype {m : Fin n → ℕ // ∑ i, m i = k} :=
      Fintype.subtype (Finset.Nat.antidiagonalTuple n k) fun _ => Finset.Nat.mem_antidiagonalTuple
    have hsum := hasSum_fintype fun x : {m : Fin n → ℕ // ∑ i, m i = k} => g x.1
    rwa [← Finset.sum_subtype (Finset.Nat.antidiagonalTuple n k)
      (fun _ => Finset.Nat.mem_antidiagonalTuple) g] at hsum
  have hbase : HasSum (fun x : Σ k : ℕ, {m : Fin n → ℕ // ∑ i, m i = k} => g x.2.1) S := by
    exact (Equiv.hasSum_iff (f := g)
      (Equiv.sigmaFiberEquiv fun m : Fin n → ℕ => ∑ i, m i)).2 h
  exact hbase.sigma hfib

end Regroup

section MultiGeometric

/-- **Summability of the monomials of nonnegative contractions.** -/
theorem summable_multiGeometric_nonneg : ∀ (n : ℕ) (t : Fin n → ℝ), (∀ i, 0 ≤ t i) →
    (∀ i, t i < 1) → Summable fun m : Fin n → ℕ => ∏ i, (t i) ^ (m i) := by
  intro n
  induction n with
  | zero =>
      intro t _ _
      exact Summable.of_finite
  | succ n ih =>
      intro t h0 h1
      have hhead : Summable fun j : ℕ => (t 0) ^ j :=
        summable_geometric_of_lt_one (h0 0) (h1 0)
      have htail : Summable fun m : Fin n → ℕ => ∏ i, (t (Fin.succ i)) ^ (m i) :=
        ih (fun i : Fin n => t (Fin.succ i)) (fun i : Fin n => h0 (Fin.succ i))
          (fun i : Fin n => h1 (Fin.succ i))
      have hnn1 : (0 : ℕ → ℝ) ≤ fun j : ℕ => (t 0) ^ j := fun j => pow_nonneg (h0 0) j
      have hnn2 : (0 : (Fin n → ℕ) → ℝ) ≤ fun m : Fin n → ℕ => ∏ i, (t (Fin.succ i)) ^ (m i) :=
        fun m => Finset.prod_nonneg fun i _ => pow_nonneg (h0 (Fin.succ i)) _
      have hprod : Summable fun p : ℕ × (Fin n → ℕ) =>
          (t 0) ^ p.1 * ∏ i, (t (Fin.succ i)) ^ (p.2 i) :=
        Summable.mul_of_nonneg
          (f := fun j : ℕ => (t 0) ^ j)
          (g := fun m : Fin n → ℕ => ∏ i, (t (Fin.succ i)) ^ (m i))
          hhead htail hnn1 hnn2
      have hcomp : Summable ((fun m : Fin (n + 1) → ℕ => ∏ i, (t i) ^ (m i)) ∘
          (Fin.consEquiv fun _ : Fin (n + 1) => ℕ)) := by
        refine hprod.congr fun p => ?_
        show (t 0) ^ p.1 * (∏ i, (t (Fin.succ i)) ^ (p.2 i)) =
          ∏ i, (t i) ^ ((Fin.consEquiv fun _ : Fin (n + 1) => ℕ) p i)
        simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      exact (Equiv.summable_iff
        (f := fun m : Fin (n + 1) → ℕ => ∏ i, (t i) ^ (m i))
        (Fin.consEquiv fun _ : Fin (n + 1) => ℕ)).1 hcomp

/-- **The geometric series in several variables.**  The product of the geometric series of the
coordinates is the sum of all monomials in the coordinates. -/
theorem hasSum_multiGeometric : ∀ (n : ℕ) (u : Fin n → ℂ), (∀ i, ‖u i‖ < 1) →
    HasSum (fun m : Fin n → ℕ => ∏ i, (u i) ^ (m i)) (∏ i, (1 - u i)⁻¹) := by
  intro n
  induction n with
  | zero =>
      intro u _
      simp
  | succ n ih =>
      intro u h
      have hhead : HasSum (fun j : ℕ => (u 0) ^ j) (1 - u 0)⁻¹ :=
        hasSum_geometric_of_norm_lt_one (h 0)
      have htail : HasSum (fun m : Fin n → ℕ => ∏ i, (u (Fin.succ i)) ^ (m i))
          (∏ i, (1 - u (Fin.succ i))⁻¹) :=
        ih (fun i : Fin n => u (Fin.succ i)) fun i : Fin n => h (Fin.succ i)
      have hheadnorm : Summable fun j : ℕ => ‖(u 0) ^ j‖ := by
        have hfun : (fun j : ℕ => ‖(u 0) ^ j‖) = fun j : ℕ => ‖u 0‖ ^ j := by
          funext j
          rw [norm_pow]
        rw [hfun]
        exact summable_geometric_of_lt_one (norm_nonneg _) (h 0)
      have htailnorm : Summable fun m : Fin n → ℕ => ‖∏ i, (u (Fin.succ i)) ^ (m i)‖ := by
        have hfun : (fun m : Fin n → ℕ => ‖∏ i, (u (Fin.succ i)) ^ (m i)‖) =
            fun m : Fin n → ℕ => ∏ i, ‖u (Fin.succ i)‖ ^ (m i) := by
          funext m
          rw [norm_prod]
          exact Finset.prod_congr rfl fun i _ => norm_pow _ _
        rw [hfun]
        exact summable_multiGeometric_nonneg n (fun i : Fin n => ‖u (Fin.succ i)‖)
          (fun i : Fin n => norm_nonneg _) (fun i : Fin n => h (Fin.succ i))
      have hprodsummable : Summable fun p : ℕ × (Fin n → ℕ) =>
          (u 0) ^ p.1 * ∏ i, (u (Fin.succ i)) ^ (p.2 i) :=
        summable_mul_of_summable_norm (f := fun j : ℕ => (u 0) ^ j)
          (g := fun m : Fin n → ℕ => ∏ i, (u (Fin.succ i)) ^ (m i)) hheadnorm htailnorm
      have hvalue : (∑' p : ℕ × (Fin n → ℕ), (u 0) ^ p.1 * ∏ i, (u (Fin.succ i)) ^ (p.2 i)) =
          (1 - u 0)⁻¹ * ∏ i, (1 - u (Fin.succ i))⁻¹ := by
        rw [← tsum_mul_tsum_of_summable_norm (f := fun j : ℕ => (u 0) ^ j)
          (g := fun m : Fin n → ℕ => ∏ i, (u (Fin.succ i)) ^ (m i)) hheadnorm htailnorm,
          hhead.tsum_eq, htail.tsum_eq]
      have hprod : HasSum
          (fun p : ℕ × (Fin n → ℕ) => (u 0) ^ p.1 * ∏ i, (u (Fin.succ i)) ^ (p.2 i))
          ((1 - u 0)⁻¹ * ∏ i, (1 - u (Fin.succ i))⁻¹) := by
        rw [← hvalue]
        exact hprodsummable.hasSum
      rw [Fin.prod_univ_succ]
      have hfun : ((fun m : Fin (n + 1) → ℕ => ∏ i, (u i) ^ (m i)) ∘
          (Fin.consEquiv fun _ : Fin (n + 1) => ℕ)) =
          fun p : ℕ × (Fin n → ℕ) => (u 0) ^ p.1 * ∏ i, (u (Fin.succ i)) ^ (p.2 i) := by
        funext p
        show (∏ i, (u i) ^ ((Fin.consEquiv fun _ : Fin (n + 1) => ℕ) p i)) =
          (u 0) ^ p.1 * ∏ i, (u (Fin.succ i)) ^ (p.2 i)
        simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      have hcomp : HasSum ((fun m : Fin (n + 1) → ℕ => ∏ i, (u i) ^ (m i)) ∘
          (Fin.consEquiv fun _ : Fin (n + 1) => ℕ))
          ((1 - u 0)⁻¹ * ∏ i, (1 - u (Fin.succ i))⁻¹) := by
        rw [hfun]
        exact hprod
      exact (Equiv.hasSum_iff
        (f := fun m : Fin (n + 1) → ℕ => ∏ i, (u i) ^ (m i))
        (Fin.consEquiv fun _ : Fin (n + 1) => ℕ)).1 hcomp

end MultiGeometric

end GaloisForLFunctions.HTGeometry
