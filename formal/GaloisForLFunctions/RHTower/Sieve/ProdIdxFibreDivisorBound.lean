import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# The fibres of the product index are divisor-bounded

`DirichletBilinear.sum_norm_sq_dirConv_le` bounds the `ℓ²` norm of a convolution by the product of
the factors' `ℓ²` norms, with a constant `D` bounding the fibres of `(n,m) ↦ nm`.  A pair with a
given product is determined by its first entry, which divides the product, so `D ≤ d(nm)`, and the
divisor bound makes that an arbitrarily small power.

This discharges the last hypothesis of the bilinear coefficient estimate.
-/

namespace RHTower.Sieve

open Finset

/-- **A product fibre injects into the divisors.** -/
theorem prodIdx_fibre_card_le_divisors (N M : ℕ) (r : Fin (N * M)) :
    ((Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r)).card
      ≤ (Nat.divisors ((r : ℕ) + 1)).card := by
  classical
  set S : Finset (Fin N × Fin M) :=
    (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r) with hS
  have hprod : ∀ q ∈ S, ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1 := by
    intro q hq
    rw [hS, Finset.mem_filter] at hq
    rw [← prodIdx_val q, hq.2]
  have hmaps : ∀ q ∈ S, ((q.1 : ℕ) + 1) ∈ Nat.divisors ((r : ℕ) + 1) := by
    intro q hq
    refine Nat.mem_divisors.2 ⟨⟨((q.2 : ℕ) + 1), ?_⟩, by omega⟩
    rw [← hprod q hq]
  have hinj : Set.InjOn (fun q : Fin N × Fin M => (q.1 : ℕ) + 1) S := by
    intro q hq q' hq' hpq
    have hq1 : (q.1 : ℕ) + 1 = (q'.1 : ℕ) + 1 := hpq
    have h1 : q.1 = q'.1 := Fin.ext (by omega)
    have hep := hprod q hq
    have heq := hprod q' hq'
    have hpos : 0 < (q.1 : ℕ) + 1 := Nat.succ_pos _
    have heq' : ((q.1 : ℕ) + 1) * ((q'.2 : ℕ) + 1) = (r : ℕ) + 1 := by
      rw [h1]; exact heq
    have h2n : ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = ((q.1 : ℕ) + 1) * ((q'.2 : ℕ) + 1) := by
      rw [hep, heq']
    have h2 : q.2 = q'.2 := Fin.ext (by
      have := Nat.eq_of_mul_eq_mul_left hpos h2n
      omega)
    exact Prod.ext h1 h2
  exact Finset.card_le_card_of_injOn _ hmaps hinj

/-- **The product fibres, bounded by an arbitrarily small power.** -/
theorem exists_prodIdx_fibre_card_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N M : ℕ) (r : Fin (N * M)),
      ((((Finset.univ : Finset (Fin N × Fin M)).filter
          (fun q => prodIdx q = r)).card : ℕ) : ℝ)
        ≤ C * ((N * M : ℕ) : ℝ) ^ ε := by
  obtain ⟨C₀, hC₀, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow hε
  refine ⟨C₀, hC₀, ?_⟩
  intro N M r
  have hd := hdiv ((r : ℕ) + 1) (by omega)
  have hjle : ((r : ℕ) + 1) ≤ N * M := r.isLt
  have hjcast : (((r : ℕ) + 1 : ℕ) : ℝ) ≤ ((N * M : ℕ) : ℝ) := by exact_mod_cast hjle
  have hbase : (((r : ℕ) + 1 : ℕ) : ℝ) ^ ε ≤ ((N * M : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) hjcast hε.le
  have hcard : ((((Finset.univ : Finset (Fin N × Fin M)).filter
      (fun q => prodIdx q = r)).card : ℕ) : ℝ)
      ≤ ((Nat.divisors ((r : ℕ) + 1)).card : ℝ) := by
    exact_mod_cast prodIdx_fibre_card_le_divisors N M r
  have hstep : ((Nat.divisors ((r : ℕ) + 1)).card : ℝ) ≤ C₀ * ((N * M : ℕ) : ℝ) ^ ε :=
    le_trans hd (mul_le_mul_of_nonneg_left hbase hC₀.le)
  linarith

/-- **The bilinear `ℓ²` bound, with no hypothesis on the fibres.** -/
theorem exists_sum_norm_sq_dirConv_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ),
      ∑ r : Fin (N * M), ‖dirConv N M a b r‖ ^ 2
        ≤ C * ((N * M : ℕ) : ℝ) ^ ε
            * ((∑ j : Fin N, ‖a j‖ ^ 2) * (∑ k : Fin M, ‖b k‖ ^ 2)) := by
  obtain ⟨C, hC, hfib⟩ := exists_prodIdx_fibre_card_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro N M a b
  exact sum_norm_sq_dirConv_le N M a b (fun r => hfib N M r)

end RHTower.Sieve
