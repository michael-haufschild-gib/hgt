/-
Strip rigidity for a reflection-symmetric entire function, and half-plane boundedness of a
convergent Dirichlet series.

Let `F` be entire with the exact reflection symmetry `F(s) = F(1−s)`, bounded on some right
half-plane `Re s ≥ σₐ` with `σₐ > 1/2`.  Reflection carries the bound to the left half-plane
`Re s ≤ 1−σₐ`, so both edges of the vertical strip `1−σₐ < Re s < σₐ` are bounded by the same
constant.  A Phragmén–Lindelöf principle on this strip, fed an admissible growth bound, extends
the constant to the closed strip; the three regions cover `ℂ`, so `F` is globally bounded, hence
constant by Liouville.  The single residual input is the strip-growth hypothesis.

* `gammaless_strip_rigidity` — the reduction: entire + reflection symmetry + a right half-plane
  norm bound + the Phragmén–Lindelöf growth bound on the strip `⟹ F` is constant.
* `lseries_bounded_on_halfplane` — the free half-plane bound: an ordinary Dirichlet series
  absolutely convergent at the real abscissa `σ₀` is bounded on the whole half-plane `Re s ≥ σ₀`
  by `∑ₙ ‖term a σ₀ n‖`, since `‖term a s n‖ ≤ ‖term a σ₀ n‖` for `Re s ≥ σ₀` (the modulus
  `n^{−Re s}` is decreasing in the exponent).  This discharges the right half-plane bound for any
  convergent carrier, making the strip-rigidity edges automatic.
-/
import Mathlib

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- **Strip rigidity for a reflection-symmetric entire function.**  An entire `F` with the exact
reflection symmetry `F(s) = F(1−s)`, bounded by `C` on a right half-plane `Re s ≥ σₐ` (with
`σₐ > 1/2`), and obeying the Phragmén–Lindelöf admissible-growth bound on the open strip
`1−σₐ < Re s < σₐ`, is constant.  Reflection sends the right half-plane bound onto the left
half-plane `Re s ≤ 1−σₐ`, so both edges `Re s = 1−σₐ` and `Re s = σₐ` are bounded by `C`;
Phragmén–Lindelöf extends the bound across the closed strip, and the three regions cover `ℂ`, so
`F` is bounded on all of `ℂ` and Liouville forces it constant.  The growth bound is the sole
analytic input and appears verbatim as a hypothesis. -/
theorem gammaless_strip_rigidity {F : ℂ → ℂ} {σa : ℝ} (_hσ : (1 : ℝ) / 2 < σa)
    (hF : Differentiable ℂ F) (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hbdd : ∃ C, ∀ s : ℂ, σa ≤ s.re → ‖F s‖ ≤ C)
    (hgrowth : ∃ c < Real.pi / (σa - (1 - σa)), ∃ B : ℝ,
        F =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
              Filter.principal (Complex.re ⁻¹' Set.Ioo (1 - σa) σa)]
          fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|))) :
    ∃ c : ℂ, ∀ s : ℂ, F s = c := by
  obtain ⟨C, hC⟩ := hbdd
  -- The bound transports to the left half-plane by reflection.
  have hleft : ∀ s : ℂ, s.re ≤ 1 - σa → ‖F s‖ ≤ C := by
    intro s hs
    rw [hsym s]
    refine hC _ ?_
    rw [Complex.sub_re, Complex.one_re]
    linarith
  -- Both vertical edges of the strip carry the same bound.
  have hedgeL : ∀ z : ℂ, z.re = 1 - σa → ‖F z‖ ≤ C := fun z hz => hleft z hz.le
  have hedgeR : ∀ z : ℂ, z.re = σa → ‖F z‖ ≤ C := fun z hz => hC z hz.ge
  -- Phragmén–Lindelöf extends the bound to the closed strip.
  have hstrip : ∀ s : ℂ, 1 - σa ≤ s.re → s.re ≤ σa → ‖F s‖ ≤ C := fun s h1 h2 =>
    PhragmenLindelof.vertical_strip hF.diffContOnCl hgrowth hedgeL hedgeR h1 h2
  -- The three regions cover the plane, giving a global bound.
  have hall : ∀ s : ℂ, ‖F s‖ ≤ C := by
    intro s
    rcases le_or_gt s.re (1 - σa) with h | h
    · exact hleft s h
    · rcases le_or_gt s.re σa with h2 | h2
      · exact hstrip s h.le h2
      · exact hC s h2.le
  -- Bounded range + entire ⟹ constant (Liouville).
  have hrange : Bornology.IsBounded (Set.range F) := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := C)) ?_
    rintro _ ⟨z, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hall z
  exact hF.exists_const_forall_eq_of_bounded hrange

/-- **Half-plane boundedness of a convergent Dirichlet series.**  If `∑ aₙ n^{−s}` converges
absolutely at the real abscissa `σ₀`, then it is bounded on the whole closed half-plane
`Re s ≥ σ₀` by `C = ∑ₙ ‖term a σ₀ n‖`.  Termwise, `‖term a s n‖ = ‖aₙ‖·n^{−Re s}` is decreasing
in `Re s` (for `n ≥ 1`, since `n ≥ 1`), so `‖term a s n‖ ≤ ‖term a σ₀ n‖` whenever `Re s ≥ σ₀`;
summing through `‖∑'‖ ≤ ∑' ‖·‖` gives the uniform bound.  This supplies the right half-plane
bound consumed by `gammaless_strip_rigidity` for any absolutely convergent carrier. -/
theorem lseries_bounded_on_halfplane {a : ℕ → ℂ} {σ₀ : ℝ} (hsum : LSeriesSummable a σ₀) :
    ∃ C, ∀ s : ℂ, (σ₀ : ℝ) ≤ s.re → ‖LSeries a s‖ ≤ C := by
  -- Termwise domination of the modulus by its value at the abscissa.
  have hterm_le : ∀ s : ℂ, (σ₀ : ℝ) ≤ s.re → ∀ n : ℕ,
      ‖LSeries.term a s n‖ ≤ ‖LSeries.term a (σ₀ : ℂ) n‖ := by
    intro s hs n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [if_neg hn, if_neg hn]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnp : (0 : ℝ) < (n : ℝ) ^ σ₀ :=
        Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
      have hle : (n : ℝ) ^ σ₀ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn1 hs
      gcongr
  refine ⟨∑' n, ‖LSeries.term a (σ₀ : ℂ) n‖, fun s hs => ?_⟩
  have hsum0 : Summable fun n => ‖LSeries.term a (σ₀ : ℂ) n‖ := summable_norm_iff.mpr hsum
  have hsums : Summable fun n => ‖LSeries.term a s n‖ :=
    summable_norm_iff.mpr (hsum.of_re_le_re (by rw [Complex.ofReal_re]; exact hs))
  calc ‖LSeries a s‖ = ‖∑' n, LSeries.term a s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term a s n‖ := norm_tsum_le_tsum_norm hsums
    _ ≤ ∑' n, ‖LSeries.term a (σ₀ : ℂ) n‖ :=
        Summable.tsum_le_tsum (fun n => hterm_le s hs n) hsums hsum0

end RHTower
