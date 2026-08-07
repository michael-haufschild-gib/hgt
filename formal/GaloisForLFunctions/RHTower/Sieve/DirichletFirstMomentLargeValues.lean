import GaloisForLFunctions.HTGeometry.CellMaxDiscretisation
import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesL1
/-!
# The first moment of a Dirichlet polynomial on an interval, by large values

Discretising the interval into `2n` cells, taking the maximum on each, splitting the cells by parity into two
families whose consecutive members are separated by a cell, and applying the corpus's first-moment large-values
bound to each family gives

`∫_{Δ/2}^{Δ/2+2nΔ} ‖D(t)‖ dt ≤ 2Δ·√(n·((2n+1)Δ + 4N(1+log N))(1/Δ + 2 log N)·∑‖a_i‖²)`.

No window and no measure appears: the bound is governed by the number of cells and the `ℓ²` mass of the
coefficients.  This is the Montgomery–Halász shape, and it is what the measure-based treatments of the exceptional
set could not produce — there the trivial size of the integrand multiplied a length, here nothing does.

The parameters are chosen so that the corpus's estimate applies verbatim: `2n` cells starting at `Δ/2` give each
parity family exactly `n` points, matching its initial-segment sum, and the height `(2n+1)Δ` is exactly
`Δ/2 + 2nΔ + Δ/2`, which is what its low and high conditions require.
-/

noncomputable section
namespace RHTower.Sieve
open Finset GaloisForLFunctions.HTGeometry

/-- **The first moment of a Dirichlet polynomial on an interval, by large values.**  Discretise by cell maxima,
split the cells by parity into two families with a gap of `Δ` at every index, and apply the corpus's first-moment
large-values bound to each.  No window and no measure enters: the bound is governed by the `ℓ²` mass of the
coefficients and the number of cells. -/
theorem integral_norm_dirPoly_le_largeValues (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {Δ : ℝ}
    (hΔ : 0 < Δ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in (Δ / 2)..(Δ / 2 + ((2 * n : ℕ) : ℝ) * Δ), ‖dirPoly N a t‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * (N : ℝ) * (1 + Real.log N))
              * (1 / Δ + 2 * Real.log N) * ∑ i : Fin N, ‖a i‖ ^ 2)) := by
  classical
  set F : ℝ → ℝ := fun t => ‖dirPoly N a t‖ with hF
  have hcont : Continuous F := (continuous_dirPoly N a).norm
  set T : ℝ := ((2 * n + 1 : ℕ) : ℝ) * Δ with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  set B : ℝ := (T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / Δ + 2 * Real.log N)
      * ∑ i : Fin N, ‖a i‖ ^ 2 with hB
  obtain ⟨c, hc, hint⟩ := exists_cell_max_integral_le hcont (Δ / 2) Δ hΔ (2 * n)
  -- one family per parity
  have hfam : ∀ r : ℕ, r ≤ 1 → (∑ j ∈ Finset.range n, F (c (2 * j + r)))
      ≤ Real.sqrt ((n : ℝ) * B) := by
    intro r hr
    obtain ⟨lam, hgap, hval⟩ := exists_gap_sequence_of_cells (c := c) (a := Δ / 2) hΔ hc r
    have hvals : ∀ j ∈ Finset.range n, F (c (2 * j + r)) = F (lam j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hval j (by omega)]
    rw [Finset.sum_congr rfl hvals]
    have hlow : Δ / 2 ≤ lam 0 := by
      rw [hval 0 (by omega)]
      have h := (hc (2 * 0 + r) (by omega)).1
      have hcast : (0 : ℝ) ≤ ((2 * 0 + r : ℕ) : ℝ) * Δ := by positivity
      linarith [h]
    have hhigh : lam (n - 1) + Δ / 2 ≤ T := by
      rw [hval (n - 1) (by omega)]
      have h := (hc (2 * (n - 1) + r) (by omega)).2
      have hcast : ((2 * (n - 1) + r : ℕ) : ℝ) + 1 ≤ ((2 * n : ℕ) : ℝ) := by
        have : 2 * (n - 1) + r + 1 ≤ 2 * n := by omega
        exact_mod_cast this
      have hTexp : T = Δ / 2 + ((2 * n : ℕ) : ℝ) * Δ + Δ / 2 := by
        rw [hT]
        push_cast
        ring
      rw [hTexp]
      nlinarith [h, hcast, hΔ.le]
    have hmv := sum_norm_dirPoly_le_sqrt N hN a hΔ hT0 hgap hlow (n - 1) hhigh
    have hrange : n - 1 + 1 = n := by omega
    rw [hrange] at hmv
    refine hmv.trans (le_of_eq ?_)
    congr 1
    rw [hB, hT]
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have : (n - 1 : ℕ) + 1 = n := by omega
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
    rw [hcast]
  -- assemble
  refine hint.trans ?_
  have hsplit : (∑ k ∈ Finset.range (2 * n), Δ * F (c k))
      = Δ * ((∑ j ∈ Finset.range n, F (c (2 * j + 0)))
          + ∑ j ∈ Finset.range n, F (c (2 * j + 1))) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * n)) (fun k => k % 2 = 0)
      (fun k => Δ * F (c k))]
    rw [sum_filter_even_eq_sum_range (2 * n) (fun k => Δ * F (c k)),
      sum_filter_odd_eq_sum_range (2 * n) (fun k => Δ * F (c k))]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
    congr 2
    · have h : (2 * n + 1) / 2 = n := by omega
      rw [h]
      exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_zero]
    · have h : (2 * n) / 2 = n := by omega
      rw [h]
  rw [hsplit]
  have h0 := hfam 0 (by omega)
  have h1 := hfam 1 (by omega)
  have hsum : (∑ j ∈ Finset.range n, F (c (2 * j + 0)))
      + ∑ j ∈ Finset.range n, F (c (2 * j + 1)) ≤ 2 * Real.sqrt ((n : ℝ) * B) := by
    linarith [h0, h1]
  calc Δ * ((∑ j ∈ Finset.range n, F (c (2 * j + 0)))
        + ∑ j ∈ Finset.range n, F (c (2 * j + 1)))
      ≤ Δ * (2 * Real.sqrt ((n : ℝ) * B)) := mul_le_mul_of_nonneg_left hsum hΔ.le
    _ = 2 * Δ * Real.sqrt ((n : ℝ) * B) := by ring

end RHTower.Sieve
end
