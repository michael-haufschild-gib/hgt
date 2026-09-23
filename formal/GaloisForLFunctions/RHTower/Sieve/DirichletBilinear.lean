import GaloisForLFunctions.RHTower.Sieve.DirichletPoly
import Mathlib.Algebra.Order.Chebyshev

/-!
# The bilinear sum is a product of Dirichlet polynomials

The frequencies of a Dirichlet polynomial are logarithms, so multiplying two of them adds the
logarithms, that is multiplies the underlying integers:

`dirPoly N a t · dirPoly M b t = ∑_{j,k} a_j b_k exp(i t log((j+1)(k+1)))`.

This is the junction between the two halves of the bilinear method.  The Ramaré decomposition
produces exactly a sum over pairs (designated prime, cofactor) weighted by `f(p)·g(m)`; this lemma
says such a sum *is* the product of the prime polynomial and the cofactor polynomial, which is what
the mean-value and large-value theorems act on.
-/

namespace RHTower.Sieve

open Finset

/-- **A product of Dirichlet polynomials is the pair sum with multiplied frequencies.** -/
theorem dirPoly_mul (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) (t : ℝ) :
    dirPoly N a t * dirPoly M b t
      = ∑ j : Fin N, ∑ k : Fin M,
          a j * b k
            * Complex.exp
                (((t * Real.log ((((j : ℕ) : ℝ) + 1) * (((k : ℕ) : ℝ) + 1)) : ℝ) : ℂ)
                  * Complex.I) := by
  rw [dirPoly, dirPoly, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hj : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) < ((k : ℕ) : ℝ) + 1 := by positivity
  have hlog : Real.log ((((j : ℕ) : ℝ) + 1) * (((k : ℕ) : ℝ) + 1))
      = Real.log (((j : ℕ) : ℝ) + 1) + Real.log (((k : ℕ) : ℝ) + 1) :=
    Real.log_mul (ne_of_gt hj) (ne_of_gt hk)
  rw [hlog]
  have hsplit : (((t * (Real.log (((j : ℕ) : ℝ) + 1) + Real.log (((k : ℕ) : ℝ) + 1)) : ℝ) : ℂ)
        * Complex.I)
      = ((t * Real.log (((j : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I
        + ((t * Real.log (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  ring

/-- The Dirichlet convolution of two coefficient vectors, indexed by the product range. -/
noncomputable def dirConv (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) (r : Fin (N * M)) : ℂ :=
  ∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter
      (fun q => ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1),
    a q.1 * b q.2

/-- The product index of a pair, as an element of the product range. -/
def prodIdx {N M : ℕ} (q : Fin N × Fin M) : Fin (N * M) :=
  ⟨((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) - 1, by
    have h1 : (q.1 : ℕ) + 1 ≤ N := q.1.isLt
    have h2 : (q.2 : ℕ) + 1 ≤ M := q.2.isLt
    have hle : ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) ≤ N * M := Nat.mul_le_mul h1 h2
    have hpos : 0 < ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) := Nat.mul_pos (by omega) (by omega)
    omega⟩

/-- **The product of two Dirichlet polynomials is a Dirichlet polynomial.**  Its coefficients are
the Dirichlet convolution, so the whole mean-value and localisation machinery applies to it. -/
theorem dirPoly_mul_eq_dirPoly (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) (t : ℝ) :
    dirPoly N a t * dirPoly M b t = dirPoly (N * M) (dirConv N M a b) t := by
  classical
  have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin N × Fin M)),
      prodIdx q ∈ (Finset.univ : Finset (Fin (N * M))) := fun q _ => Finset.mem_univ _
  have hfib : ∀ q : Fin N × Fin M,
      ((prodIdx q : Fin (N * M)) : ℕ) + 1 = ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) := by
    intro q
    have hpos : 0 < ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) := Nat.mul_pos (by omega) (by omega)
    simp only [prodIdx]
    omega
  have hRHS : dirPoly (N * M) (dirConv N M a b) t
      = ∑ q : Fin N × Fin M,
          a q.1 * b q.2
            * Complex.exp
                (((t * Real.log ((((q.1 : ℕ) : ℝ) + 1) * (((q.2 : ℕ) : ℝ) + 1)) : ℝ) : ℂ)
                  * Complex.I) := by
    rw [dirPoly]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun q => a q.1 * b q.2
        * Complex.exp
            (((t * Real.log ((((q.1 : ℕ) : ℝ) + 1) * (((q.2 : ℕ) : ℝ) + 1)) : ℝ) : ℂ)
              * Complex.I))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [dirConv, Finset.sum_mul]
    refine Finset.sum_congr ?_ ?_
    · ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have := hfib q
        apply Fin.ext
        omega
      · intro h
        rw [← h, hfib q]
    · intro q hq
      rw [Finset.mem_filter] at hq
      have hq2 : ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1 := by
        have h := hfib q
        rw [hq.2] at h
        omega
      have hcast : ((((q.1 : ℕ) : ℝ) + 1) * (((q.2 : ℕ) : ℝ) + 1)) = ((r : ℕ) : ℝ) + 1 := by
        have hc := congrArg (fun n : ℕ => (n : ℝ)) hq2
        push_cast at hc
        linarith [hc]
      rw [hcast]
  rw [hRHS, dirPoly_mul N M a b t, ← Finset.sum_product', Finset.univ_product_univ]

/-- The product index recovers the product. -/
theorem prodIdx_val {N M : ℕ} (q : Fin N × Fin M) :
    ((prodIdx q : Fin (N * M)) : ℕ) + 1 = ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) := by
  have hpos : 0 < ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) := Nat.mul_pos (by omega) (by omega)
  simp only [prodIdx]
  omega

/-- The convolution fibre is the fibre of the product index. -/
theorem filter_prodIdx_eq {N M : ℕ} (r : Fin (N * M)) :
    (Finset.univ : Finset (Fin N × Fin M)).filter
        (fun q => ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1)
      = (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r) := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have := prodIdx_val q
    apply Fin.ext
    omega
  · intro h
    rw [← h, prodIdx_val q]

/-- **The convolution coefficients, bounded fibrewise.** -/
theorem norm_dirConv_le (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) (r : Fin (N * M)) :
    ‖dirConv N M a b r‖
      ≤ ∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r),
          ‖a q.1‖ * ‖b q.2‖ := by
  classical
  rw [dirConv, filter_prodIdx_eq r]
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum fun q _ => le_of_eq (norm_mul _ _)

/-- **The convolution has the product `ℓ¹` norm.**  This is the coefficient-size input the
localisation and mean-value theorems consume. -/
theorem sum_norm_dirConv_le (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) :
    ∑ r : Fin (N * M), ‖dirConv N M a b r‖
      ≤ (∑ j : Fin N, ‖a j‖) * (∑ k : Fin M, ‖b k‖) := by
  classical
  have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin N × Fin M)),
      prodIdx q ∈ (Finset.univ : Finset (Fin (N * M))) := fun q _ => Finset.mem_univ _
  have hfibre := Finset.sum_fiberwise_of_maps_to hmaps (fun q : Fin N × Fin M => ‖a q.1‖ * ‖b q.2‖)
  refine le_trans (Finset.sum_le_sum fun r _ => norm_dirConv_le N M a b r) ?_
  rw [hfibre, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]

/-- **The convolution `ℓ²` bound.**  With the fibres of the product index bounded by `D` — a divisor
bound — the mean-value theorems' coefficient input is the product of the factor `ℓ²` norms. -/
theorem sum_norm_sq_dirConv_le (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) {D : ℝ}
    (hD : ∀ r : Fin (N * M),
      ((((Finset.univ : Finset (Fin N × Fin M)).filter
        (fun q => prodIdx q = r)).card : ℕ) : ℝ) ≤ D) :
    ∑ r : Fin (N * M), ‖dirConv N M a b r‖ ^ (2 : ℕ)
      ≤ D * ((∑ j : Fin N, ‖a j‖ ^ (2 : ℕ)) * (∑ k : Fin M, ‖b k‖ ^ (2 : ℕ))) := by
  classical
  have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin N × Fin M)),
      prodIdx q ∈ (Finset.univ : Finset (Fin (N * M))) := fun q _ => Finset.mem_univ _
  have hterm : ∀ r : Fin (N * M),
      ‖dirConv N M a b r‖ ^ (2 : ℕ)
        ≤ D * ∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r),
            ‖a q.1‖ ^ (2 : ℕ) * ‖b q.2‖ ^ (2 : ℕ) := by
    intro r
    have hnn : (0 : ℝ) ≤ ∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter
        (fun q => prodIdx q = r), ‖a q.1‖ * ‖b q.2‖ := by positivity
    have h1 : ‖dirConv N M a b r‖ ^ (2 : ℕ)
        ≤ (∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r),
            ‖a q.1‖ * ‖b q.2‖) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_dirConv_le N M a b r) 2
    have h2 := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r))
      (f := fun q : Fin N × Fin M => ‖a q.1‖ * ‖b q.2‖)
    have h3 : ∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r),
        (‖a q.1‖ * ‖b q.2‖) ^ (2 : ℕ)
        = ∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter (fun q => prodIdx q = r),
            ‖a q.1‖ ^ (2 : ℕ) * ‖b q.2‖ ^ (2 : ℕ) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have hsq : (0 : ℝ) ≤ ∑ q ∈ (Finset.univ : Finset (Fin N × Fin M)).filter
        (fun q => prodIdx q = r), ‖a q.1‖ ^ (2 : ℕ) * ‖b q.2‖ ^ (2 : ℕ) := by positivity
    rw [h3] at h2
    have h4 := mul_le_mul_of_nonneg_right (hD r) hsq
    linarith [h1, h2, h4]
  refine le_trans (Finset.sum_le_sum fun r _ => hterm r) ?_
  rw [← Finset.mul_sum]
  have hfibre := Finset.sum_fiberwise_of_maps_to hmaps
    (fun q : Fin N × Fin M => ‖a q.1‖ ^ (2 : ℕ) * ‖b q.2‖ ^ (2 : ℕ))
  rw [hfibre]
  have hprod : ∑ q : Fin N × Fin M, ‖a q.1‖ ^ (2 : ℕ) * ‖b q.2‖ ^ (2 : ℕ)
      = (∑ j : Fin N, ‖a j‖ ^ (2 : ℕ)) * (∑ k : Fin M, ‖b k‖ ^ (2 : ℕ)) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hprod]

end RHTower.Sieve
