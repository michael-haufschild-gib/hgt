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

/-- **Order-one growth automatically satisfies the strip Phragmén--Lindelöf hypothesis.**
On the fixed strip `1 - σa < Re z < σa`, the real part is bounded, hence
`‖z‖ ≤ K + |Im z|`.  The order-one exponent is therefore at most a quadratic polynomial in
`|Im z|`, and every such polynomial is dominated by `B exp(c |Im z|)` for any `c > 0`.
Choosing `c` strictly below the strip's Phragmén--Lindelöf threshold supplies exactly the
double-exponential `IsBigO` premise used by `gammaless_strip_rigidity`. -/
theorem orderOneGrowth_phragmenLindelof_strip
    {F : ℂ → ℂ} {σa : ℝ} (hσ : (1 : ℝ) / 2 < σa)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ c < Real.pi / (σa - (1 - σa)), ∃ B : ℝ,
      F =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo (1 - σa) σa)]
        fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨C, hC, hF⟩ := hgrowth
  set w : ℝ := σa - (1 - σa) with hw_def
  have hw : 0 < w := by rw [hw_def]; linarith
  set c : ℝ := Real.pi / (2 * w) with hc_def
  have hc : 0 < c := by rw [hc_def]; positivity
  have hc_lt : c < Real.pi / w := by
    rw [hc_def]
    exact div_lt_div_of_pos_left Real.pi_pos hw (by linarith)
  set K : ℝ := 2 + |1 - σa| + |σa| with hK_def
  have hK : 0 < K := by rw [hK_def]; positivity
  set B : ℝ := C * (2 * K ^ 2 + 8 / c ^ 2) with hB_def
  refine ⟨c, by simpa [w] using hc_lt, B, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  have hstrip : ∀ᶠ z : ℂ in
      Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Set.Ioo (1 - σa) σa),
      z.re ∈ Set.Ioo (1 - σa) σa := by
    apply Filter.Eventually.filter_mono inf_le_right
    simp
  filter_upwards [hstrip] with z hz
  set t : ℝ := |z.im| with ht_def
  have ht : 0 ≤ t := by rw [ht_def]; positivity
  have hre : |z.re| ≤ |1 - σa| + |σa| := by
    rw [abs_le]
    constructor
    · have hl := neg_abs_le (1 - σa)
      have hnon : 0 ≤ |σa| := abs_nonneg _
      linarith [hz.1]
    · have hu := le_abs_self σa
      have hnon : 0 ≤ |1 - σa| := abs_nonneg _
      linarith [hz.2]
  have hnorm : ‖z‖ ≤ (K - 2) + t := by
    have hn := Complex.norm_le_abs_re_add_abs_im z
    calc
      ‖z‖ ≤ |z.re| + |z.im| := hn
      _ ≤ (K - 2) + t := by rw [hK_def, ht_def]; linarith
  have hbase : 0 ≤ K + t := by positivity
  have hfac1 : 1 + ‖z‖ ≤ K + t := by linarith
  have hfac2 : Real.log (2 + ‖z‖) ≤ K + t := by
    calc
      Real.log (2 + ‖z‖) ≤ 2 + ‖z‖ := Real.log_le_self (by positivity)
      _ ≤ K + t := by linarith
  have hexp_half : c * t / 2 ≤ Real.exp (c * t / 2) := by
    have h := Real.add_one_le_exp (c * t / 2)
    linarith
  have ht_exp : t ≤ (2 / c) * Real.exp (c * t / 2) := by
    calc
      t = (2 / c) * (c * t / 2) := by field_simp
      _ ≤ (2 / c) * Real.exp (c * t / 2) :=
        mul_le_mul_of_nonneg_left hexp_half (by positivity)
  have ht_sq : t ^ 2 ≤ (4 / c ^ 2) * Real.exp (c * t) := by
    calc
      t ^ 2 ≤ ((2 / c) * Real.exp (c * t / 2)) ^ 2 :=
        pow_le_pow_left₀ ht ht_exp 2
      _ = (4 / c ^ 2) * Real.exp (c * t) := by
        have hexpsq : Real.exp (c * t / 2) ^ 2 = Real.exp (c * t) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [mul_pow, hexpsq]
        field_simp
        norm_num
  have hone : 1 ≤ Real.exp (c * t) :=
    Real.one_le_exp (mul_nonneg hc.le ht)
  have hquad : (K + t) ^ 2 ≤ (2 * K ^ 2 + 8 / c ^ 2) * Real.exp (c * t) := by
    have hsplit : (K + t) ^ 2 ≤ 2 * K ^ 2 + 2 * t ^ 2 := by
      nlinarith [sq_nonneg (K - t)]
    have hconst : 2 * K ^ 2 ≤ 2 * K ^ 2 * Real.exp (c * t) := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hone (show 0 ≤ 2 * K ^ 2 by positivity))
    have htail : 2 * t ^ 2 ≤ (8 / c ^ 2) * Real.exp (c * t) := by
      calc
        2 * t ^ 2 ≤ 2 * ((4 / c ^ 2) * Real.exp (c * t)) :=
          mul_le_mul_of_nonneg_left ht_sq (by norm_num)
        _ = (8 / c ^ 2) * Real.exp (c * t) := by ring
    calc
      (K + t) ^ 2 ≤ 2 * K ^ 2 + 2 * t ^ 2 := hsplit
      _ ≤ 2 * K ^ 2 * Real.exp (c * t) +
          (8 / c ^ 2) * Real.exp (c * t) := add_le_add hconst htail
      _ = (2 * K ^ 2 + 8 / c ^ 2) * Real.exp (c * t) := by ring
  have hinner : C * (1 + ‖z‖) * Real.log (2 + ‖z‖)
      ≤ B * Real.exp (c * t) := by
    have hprod : (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤ (K + t) ^ 2 := by
      calc
        (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤ (K + t) * (K + t) :=
          mul_le_mul hfac1 hfac2
            (Real.log_nonneg (by linarith [norm_nonneg z])) hbase
        _ = (K + t) ^ 2 := by ring
    calc
      C * (1 + ‖z‖) * Real.log (2 + ‖z‖)
          = C * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by ring
      _ ≤ C * (K + t) ^ 2 := mul_le_mul_of_nonneg_left hprod hC.le
      _ ≤ C * ((2 * K ^ 2 + 8 / c ^ 2) * Real.exp (c * t)) :=
        mul_le_mul_of_nonneg_left hquad hC.le
      _ = B * Real.exp (c * t) := by rw [hB_def]; ring
  have hnormF : ‖F z‖ ≤ Real.exp (B * Real.exp (c * t)) :=
    (hF z).trans (Real.exp_le_exp.mpr hinner)
  simpa [t, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hnormF

/-- **The strip-growth hypothesis is eliminated by order-one growth.**  A reflection-symmetric
entire function that is bounded on a right half-plane and has the standard order-one envelope is
constant; the Phragmén--Lindelöf premise of `gammaless_strip_rigidity` is now constructed rather
than supplied. -/
theorem gammaless_strip_rigidity_of_orderOne {F : ℂ → ℂ} {σa : ℝ}
    (hσ : (1 : ℝ) / 2 < σa) (hF : Differentiable ℂ F)
    (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hbdd : ∃ C, ∀ s : ℂ, σa ≤ s.re → ‖F s‖ ≤ C)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ c : ℂ, ∀ s : ℂ, F s = c :=
  gammaless_strip_rigidity hσ hF hsym hbdd
    (orderOneGrowth_phragmenLindelof_strip hσ hgrowth)

/-- **Order-one gammaless Dirichlet carriers are constant.**  If an entire, reflection-symmetric
function agrees on `Re s ≥ σa > 1/2` with an absolutely convergent ordinary Dirichlet series and
has order at most one, then it is constant.  Absolute convergence supplies the half-plane bound
and order one supplies the strip-growth law, so neither analytic interface remains. -/
theorem gammaless_lseries_orderOne_constant {F : ℂ → ℂ} {a : ℕ → ℂ} {σa : ℝ}
    (hσ : (1 : ℝ) / 2 < σa) (hF : Differentiable ℂ F)
    (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hsum : LSeriesSummable a σa)
    (hFeq : ∀ s : ℂ, σa ≤ s.re → F s = LSeries a s)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ c : ℂ, ∀ s : ℂ, F s = c := by
  obtain ⟨C, hC⟩ := lseries_bounded_on_halfplane hsum
  exact gammaless_strip_rigidity_of_orderOne hσ hF hsym
    ⟨C, fun s hs => by rw [hFeq s hs]; exact hC s hs⟩ hgrowth

end RHTower
