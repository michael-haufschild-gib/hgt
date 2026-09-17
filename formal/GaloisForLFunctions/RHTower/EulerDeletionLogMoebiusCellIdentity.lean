import GaloisForLFunctions.RHTower.EulerDeletionCoefficientPrefixEnergy
import GaloisForLFunctions.RHTower.TruncatedMoebiusResidual
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMoebius

/-!
# Initial physical cells of the logarithmic Möbius source

The literal logarithmically weighted Euler-deletion source has an exact
initial-cell formula.  At every cell within the coefficient cutoff, the
truncated divisor term is the cumulative Chebyshev mass.  This retains the
complete physical tail: the formula supplies no estimate beyond the initial
cells and no source-energy bound.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

private theorem sum_moebius_log_divisors (k : ℕ) :
    ∑ d ∈ k.divisors, ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) = -vonMangoldt k :=
  ArithmeticFunction.sum_moebius_mul_log_eq

private theorem sum_moebius_log_floor_eq_neg_psi {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) =
      -Chebyshev.psi (n : ℝ) := by
  have hsub : Icc 1 n ⊆ Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hd).1, le_trans (Finset.mem_Icc.mp hd).2 hnN⟩
  have hdrop : ∀ d ∈ Icc 1 N, d ∉ Icc 1 n →
      ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) = 0 := by
    intro d hd hdn
    have hnd : n < d := by
      by_contra hnot
      exact hdn (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hd).1, Nat.le_of_not_gt hnot⟩)
    simp [Nat.div_eq_of_lt hnd]
  rw [← Finset.sum_subset hsub hdrop]
  have hIcc : Icc 1 n = Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hcount : ∀ d ∈ Icc 1 n,
      ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) =
        ∑ k ∈ Finset.filter (fun k => d ∣ k) (Icc 1 n),
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) := by
    intro d hd
    rw [Finset.sum_const, hIcc, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
    ring
  have hdiv : ∀ k ∈ Icc 1 n,
      Finset.filter (fun d => d ∣ k) (Icc 1 n) = k.divisors := by
    intro k hk
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · intro h
      rcases h with ⟨⟨_, _⟩, hdvd⟩
      exact ⟨hdvd, ne_of_gt (Finset.mem_Icc.mp hk).1⟩
    · intro h
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hkpos,
        le_trans (Nat.le_of_dvd hkpos h.1) (Finset.mem_Icc.mp hk).2⟩, h.1⟩
  calc
    (∑ d ∈ Icc 1 n,
      ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ)) =
        ∑ d ∈ Icc 1 n,
          ∑ k ∈ Finset.filter (fun k => d ∣ k) (Icc 1 n),
            ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) := by
          apply Finset.sum_congr rfl hcount
    _ = ∑ x ∈ Icc 1 n,
      ∑ y ∈ Finset.filter (fun y => y ∣ x) (Icc 1 n),
        ((moebius y : ℤ) : ℝ) * Real.log (y : ℝ) := by
          refine Finset.sum_comm' ?_
          intro d k
          simp only [Finset.mem_filter, Finset.mem_Icc]
          tauto
    _ = ∑ x ∈ Icc 1 n, -vonMangoldt x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hdiv x hx, sum_moebius_log_divisors]
    _ = -Chebyshev.psi (n : ℝ) := by
      rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Finset.sum_neg_distrib]
      have hset : Icc 0 n = insert 0 (Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      simp

private theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ d ∈ Icc 1 N, f d := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- On every physical cell within the cutoff, the literal logarithmic Möbius
source is reciprocal logarithmic Möbius mass plus the cumulative Chebyshev
mass.  The formula does not alter or discard any cell beyond the cutoff. -/
theorem physical_log_moebius_cell_eq_chebyshev {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    DeletionCoefficientTransfer.cell
      (fun d => ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) N n =
      (n : ℝ) * ∑ d ∈ Icc 1 N,
        (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) / (d : ℝ) + Chebyshev.psi (n : ℝ) := by
  rw [DeletionCoefficientTransfer.cell]
  calc
    (∑ i ∈ range N,
      (((moebius (i + 1) : ℤ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ)) *
        ((n % (i + 1) : ℕ) : ℝ) / ((i : ℝ) + 1)) =
      ∑ d ∈ Icc 1 N,
        (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) *
          (((n % d : ℕ) : ℝ) / (d : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using
          (sum_range_succ_eq_sum_Icc
            (fun d => (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) *
              (((n % d : ℕ) : ℝ) / (d : ℝ))) N)
    _ = (n : ℝ) * ∑ d ∈ Icc 1 N,
        (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) / (d : ℝ) -
        ∑ d ∈ Icc 1 N,
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        rw [RHTower.modSeq_eq_sub_floor hd1]
        have hd0 : (d : ℝ) ≠ 0 := by
          exact ne_of_gt (by exact_mod_cast (show 0 < d by omega))
        field_simp
    _ = _ := by
      rw [sum_moebius_log_floor_eq_neg_psi hn hnN]
      ring

/-- Every physical cell of the literal logarithmic Möbius source is its
Chebyshev initial-cell term plus the complete, signed divisor tail past the
coefficient cutoff.  This is an identity, not an estimate of that tail. -/
theorem physical_log_moebius_cell_eq_chebyshev_add_divisor_tail {n N : ℕ}
    (hn : 1 ≤ n) :
    DeletionCoefficientTransfer.cell
      (fun d => ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) N n =
      (n : ℝ) * ∑ d ∈ Icc 1 N,
        (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) / (d : ℝ) + Chebyshev.psi (n : ℝ) +
        ∑ d ∈ Ioc N n,
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) := by
  have hraw :
      DeletionCoefficientTransfer.cell
        (fun d => ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) N n =
        (n : ℝ) * ∑ d ∈ Icc 1 N,
          (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) / (d : ℝ) -
          ∑ d ∈ Icc 1 N,
            ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) := by
    rw [DeletionCoefficientTransfer.cell]
    calc
      (∑ i ∈ range N,
        (((moebius (i + 1) : ℤ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ)) *
          ((n % (i + 1) : ℕ) : ℝ) / ((i : ℝ) + 1)) =
        ∑ d ∈ Icc 1 N,
          (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) *
            (((n % d : ℕ) : ℝ) / (d : ℝ)) := by
          simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using
            (sum_range_succ_eq_sum_Icc
              (fun d => (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) *
                (((n % d : ℕ) : ℝ) / (d : ℝ))) N)
      _ = (n : ℝ) * ∑ d ∈ Icc 1 N,
          (((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) / (d : ℝ) -
          ∑ d ∈ Icc 1 N,
            ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          rw [RHTower.modSeq_eq_sub_floor hd1]
          have hd0 : (d : ℝ) ≠ 0 := by
            exact ne_of_gt (by exact_mod_cast (show 0 < d by omega))
          field_simp
  by_cases hNn : N ≤ n
  · have htail :
        (∑ d ∈ Ioc N n,
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ)) =
          (∑ d ∈ Icc 1 n,
            ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ)) -
            ∑ d ∈ Icc 1 N,
              ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      have hsub : Icc 1 N ⊆ Icc 1 n := by
        intro d hd
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hNn⟩
      have hdiff : Icc 1 n \ Icc 1 N = Ioc N n := by
        ext d
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [← hdiff, eq_sub_iff_add_eq]
      exact Finset.sum_sdiff hsub
    rw [hraw, htail, sum_moebius_log_floor_eq_neg_psi hn le_rfl]
    ring
  · have hnN : n ≤ N := by omega
    have hsub : Icc 1 n ⊆ Icc 1 N := by
      intro d hd
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hnN⟩
    have hdrop : ∀ d ∈ Icc 1 N, d ∉ Icc 1 n →
        ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) = 0 := by
      intro d hd hdn
      have hnd : n < d := by
        by_contra hnot
        exact hdn (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hd).1, Nat.le_of_not_gt hnot⟩)
      simp [Nat.div_eq_of_lt hnd]
    have hprefix :
        (∑ d ∈ Icc 1 N,
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ)) =
          ∑ d ∈ Icc 1 n,
            ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ) :=
      (Finset.sum_subset hsub hdrop).symm
    have htail :
        (∑ d ∈ Ioc N n,
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * ((n / d : ℕ) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hd' := Finset.mem_Ioc.mp hd
      exfalso
      omega
    rw [hraw, hprefix, sum_moebius_log_floor_eq_neg_psi hn le_rfl, htail]
    ring

end RHTower

end
