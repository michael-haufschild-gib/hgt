/-
# Exceptional-term estimates for the fixed-point index formula

The Zdunik-free obstruction `IndexFormula.false_of_exceptional_mass_small` needs the exceptional index mass
`∑_{z∈B} ‖(λ_z - 1)⁻¹‖` to be small. The exceptional set `B` (for the parameters this route handles) is the
set of fixed points of `f_c` — period-`1` points — which appear as fixed points of every `f_c^[p]` with
multiplier `λ_z = (2z)^p`. When such a fixed point is **repelling** (`‖2z‖ > 1`) its multiplier modulus
`‖2z‖^p` grows geometrically, so its index `‖(λ_z - 1)⁻¹‖ ≤ (‖2z‖^p - 1)⁻¹` decays geometrically — fast
enough that `(2^p - 1)·` (its index) `→ 0` (the index decays like `2^{-p}·(2/‖2z‖)^p` relative to the bulk
`2^p`). This file proves the per-term bound; it is the analytic input that makes the bulk dominate.

New file (hRigid / connected lane, Zdunik-free route). General estimate + the fixed-point specialisation.
-/
import GaloisForLFunctions.Bottcher.IndexFormula

open Polynomial Finset Filter Topology

namespace Bottcher

/-- **The fixed-point index is bounded by the reverse-triangle estimate.** For `‖λ‖ > 1`,
`‖(λ - 1)⁻¹‖ ≤ (‖λ‖ - 1)⁻¹` (since `‖λ - 1‖ ≥ ‖λ‖ - 1 > 0`). -/
theorem norm_index_le {lam : ℂ} (h : 1 < ‖lam‖) : ‖(lam - 1)⁻¹‖ ≤ (‖lam‖ - 1)⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ (by linarith)
  calc ‖lam‖ - 1 = ‖lam‖ - ‖(1 : ℂ)‖ := by rw [norm_one]
    _ ≤ ‖lam - 1‖ := norm_sub_norm_le lam 1

/-- The period-`p` multiplier at a **fixed** point `z` of `f_c` is `(2z)^p`: the orbit is constant `z`, so
`∏_{k<p} 2·f_c^[k] z = ∏_{k<p} 2z = (2z)^p`. -/
theorem prod_multiplier_at_fixed {c z : ℂ} (h : quadratic c z = z) (p : ℕ) :
    (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 * z) ^ p := by
  rw [Finset.prod_congr rfl (fun k _ => by rw [Function.iterate_fixed h k]), Finset.prod_const,
    Finset.card_range]

/-- **Geometric decay of a repelling fixed point's index.** If `z` is a fixed point of `f_c` with
`‖2z‖^p > 1` (repelling), its index as a fixed point of `f_c^[p]` is bounded by `(‖2z‖^p - 1)⁻¹`. Since
`‖2z‖ > 1` makes `‖2z‖^p → ∞`, this `→ 0`; multiplied by the bulk weight `2^p - 1` it still vanishes
relative to the bulk count `2^p` (the ratio is `≍ ‖2z‖^{-p}`), so a repelling fixed point cannot prop up the
exceptional mass. -/
theorem norm_index_at_fixed_le {c z : ℂ} (h : quadratic c z = z) {p : ℕ} (hrep : 1 < ‖2 * z‖ ^ p) :
    ‖((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹‖ ≤ (‖2 * z‖ ^ p - 1)⁻¹ := by
  rw [prod_multiplier_at_fixed h]
  have hn : ‖(2 * z) ^ p‖ = ‖2 * z‖ ^ p := norm_pow _ _
  have hb := norm_index_le (lam := (2 * z) ^ p) (by rw [hn]; exact hrep)
  rwa [hn] at hb

/-- **The index-formula obstruction in the no-attracting-fixed-point case.** Suppose `f_c^[p] - X` is
separable (`p ≥ 1`), the cycle splits into the pinned bulk (multiplier `2^p` off the exceptional set `B`)
and a `B` consisting entirely of **repelling fixed points** of `f_c` (`f_c z = z`, `‖2z‖^p > 1`), and the
explicit exceptional bound `(2^p-1)·∑_{z∈B} (‖2z‖^p - 1)⁻¹ < card(roots∖B)` holds. Then `False`.

This packages the whole Zdunik-free engine into the dynamical inputs it needs: a finite exceptional set of
*repelling* fixed points (no attracting fixed point), a pinned bulk (supplied by `resonance_order` through
the relation's continuation), and the geometric exceptional bound (`norm_index_at_fixed_le`). The last
inequality holds for all large `p` because the LHS grows like `(2/‖2z‖)^p` while the RHS `≍ 2^p` — so the
bulk strictly dominates. Discharging `hG`/`hrep` for an actual relation is the remaining dynamical wiring;
the algebra and the estimate are complete here. -/
theorem false_of_pinned_bulk_repelling (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable)
    (B : Finset ℂ) (hB : B ⊆ (fixedPointPoly c p).roots.toFinset)
    (hG : ∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p)
    (hrep : ∀ z ∈ B, quadratic c z = z ∧ 1 < ‖2 * z‖ ^ p)
    (hsmall : ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
      < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)) :
    False := by
  apply false_of_exceptional_mass_small c hp hsep B hB hG
  have h2nn : (0 : ℝ) ≤ (2 : ℝ) ^ p - 1 := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num)
    linarith
  calc ((2 : ℝ) ^ p - 1) *
        ∑ z ∈ B, ‖((∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) - 1)⁻¹‖
      ≤ ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ h2nn
        apply Finset.sum_le_sum
        intro z hz
        exact norm_index_at_fixed_le (hrep z hz).1 (hrep z hz).2
    _ < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ) := hsmall

/-! ### Discharging the smallness hypothesis asymptotically -/

/-- For `r > 1`, the index weight `(r^p - 1)⁻¹ → 0` as `p → ∞` (`r^p → ∞`). -/
theorem inv_pow_sub_one_tendsto {r : ℝ} (h : 1 < r) :
    Tendsto (fun p : ℕ => (r ^ p - 1)⁻¹) atTop (𝓝 0) := by
  apply Filter.Tendsto.inv_tendsto_atTop
  have := tendsto_atTop_add_const_right atTop (-1 : ℝ) (tendsto_pow_atTop_atTop_of_one_lt h)
  simpa using this

/-- **The exceptional mass is eventually small.** For a finite set `B` of *repelling* points
(`∀ z ∈ B, ‖2z‖ > 1`), the weighted exceptional mass `(2^p-1)·∑_{z∈B}(‖2z‖^p-1)⁻¹` is eventually below
`2^p - card B`: the exceptional sum `→ 0` while the ratio `(2^p-card B)/(2^p-1) → 1`, so for large `p` the
pinned bulk strictly dominates. This discharges the `hsmall` hypothesis of `false_of_pinned_bulk_repelling`
/ `false_of_branches_and_repelling` for all sufficiently large `p` (the final assembly intersects this with
the prime/separable/`B`-is-repelling conditions). -/
theorem eventually_exceptional_mass_small (B : Finset ℂ) (hB : ∀ z ∈ B, 1 < ‖2 * z‖) :
    ∀ᶠ p : ℕ in atTop,
      ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹ < (2 : ℝ) ^ p - (B.card : ℝ) := by
  have hsum0 : Tendsto (fun p : ℕ => ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ z ∈ B, (0 : ℝ) by simp]
    exact tendsto_finsetSum _ (fun z hz => inv_pow_sub_one_tendsto (hB z hz))
  have hsumlt : ∀ᶠ p : ℕ in atTop, ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹ < 1 / 2 :=
    hsum0.eventually (eventually_lt_nhds (by norm_num))
  have hbig : Tendsto (fun p : ℕ => (2 : ℝ) ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hratio : ∀ᶠ p : ℕ in atTop,
      (1 : ℝ) / 2 < ((2 : ℝ) ^ p - (B.card : ℝ)) / ((2 : ℝ) ^ p - 1) := by
    filter_upwards [hbig.eventually_gt_atTop (2 * (B.card : ℝ)), hbig.eventually_gt_atTop 2]
      with p hp2 hp1
    rw [lt_div_iff₀ (by linarith)]; linarith
  filter_upwards [hsumlt, hratio, hbig.eventually_gt_atTop 2] with p hsmall hr hp1
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by linarith
  have hchain : ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
      < ((2 : ℝ) ^ p - (B.card : ℝ)) / ((2 : ℝ) ^ p - 1) := lt_trans hsmall hr
  rw [lt_div_iff₀ hpos] at hchain
  rw [mul_comm]; exact hchain

/-- The bulk count as a real number: `card(roots∖B) = 2^p - card B` (separable ⟹ `2^p` distinct roots). -/
theorem card_sdiff_roots (c : ℂ) {p : ℕ} (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable)
    (B : Finset ℂ) (hB : B ⊆ (fixedPointPoly c p).roots.toFinset) :
    (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ) = (2 : ℝ) ^ p - (B.card : ℝ) := by
  have hadd : (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ) + (B.card : ℝ)
      = ((fixedPointPoly c p).roots.toFinset.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hB]
  rw [fixedPointPoly_roots_card c hp hsep] at hadd
  have hcast : ((2 ^ p : ℕ) : ℝ) = (2 : ℝ) ^ p := by push_cast; ring
  rw [hcast] at hadd
  linarith

/-- **The exceptional mass is eventually small against the actual root bulk.** This is the
root-count form of `eventually_exceptional_mass_small`: once the fixed-point polynomial is separable and
the exceptional fixed set `B` is contained in its roots, the analytic bound
`(2^p - 1) * exceptionalMass < 2^p - |B|` is exactly the hRigid/index-route smallness hypothesis with
right side `card(roots ∖ B)`. -/
theorem eventually_exceptional_mass_small_roots (c : ℂ) (B : Finset ℂ)
    (hBrep : ∀ z ∈ B, 1 < ‖2 * z‖) :
    ∀ᶠ p : ℕ in atTop,
      ∀ (_hp : 1 ≤ p), (fixedPointPoly c p).Separable →
        B ⊆ (fixedPointPoly c p).roots.toFinset →
          ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
            < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ) := by
  filter_upwards [eventually_exceptional_mass_small B hBrep] with p hsmall hp hsep hBsub
  simpa [card_sdiff_roots c hp hsep B hBsub] using hsmall

/-- **Pinned bulk contradiction with smallness discharged asymptotically.** For a fixed finite exceptional
set `B` of repelling fixed points of `f_c`, every sufficiently large period satisfying separability,
`B ⊆ roots(f_c^[p] - X)`, and the pinned-bulk multiplier identity already contradicts the index formula.

This removes the explicit `hsmall` terminal hypothesis from
`false_of_pinned_bulk_repelling`; it is created from `eventually_exceptional_mass_small_roots`. -/
theorem eventually_false_of_pinned_bulk_repelling (c : ℂ) (B : Finset ℂ)
    (hBfix : ∀ z ∈ B, quadratic c z = z)
    (hBrep : ∀ z ∈ B, 1 < ‖2 * z‖) :
    ∀ᶠ p : ℕ in atTop,
      ∀ (_hp : 1 ≤ p), (fixedPointPoly c p).Separable →
        B ⊆ (fixedPointPoly c p).roots.toFinset →
        (∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
          (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p) →
        False := by
  filter_upwards [eventually_exceptional_mass_small_roots c B hBrep] with p hsmall hp hsep hBsub hG
  have hrep : ∀ z ∈ B, quadratic c z = z ∧ 1 < ‖2 * z‖ ^ p := by
    intro z hz
    refine ⟨hBfix z hz, ?_⟩
    exact one_lt_pow₀ (hBrep z hz) (by omega : p ≠ 0)
  exact false_of_pinned_bulk_repelling c hp hsep B hBsub hG hrep (hsmall hp hsep hBsub)

end Bottcher
