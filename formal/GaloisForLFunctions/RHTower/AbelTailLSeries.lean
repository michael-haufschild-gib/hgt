import GaloisForLFunctions.RHTower.DirichletAbelTail
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.RHTower.HarmonicTriangularProjection

/-!
# The Abel tail of a summatory profile is its `L`-series

For a source `a` with partial sums `R(N) = ∑_{m ≤ N} a_m`, summation by parts turns the Dirichlet
series of `a` into the series of `R` against the increments of `n^{-s}`:

`∑_{n ≥ 1} a_n n^{-s} = ∑_{n ≥ 1} R(n) (n^{-s} − (n+1)^{-s})`.

The boundary term vanishes and the increment series converges absolutely as soon as `R` is
polynomially bounded with an exponent below `Re s`, since the unit increment of `x^{-s}` is
`O(x^{-Re s − 1})`.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-- The Abel tail `∑_{n ≥ 1} R(n)(n^{-s} − (n+1)^{-s})` of a profile. -/
def abelTailSeries (R : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, (R (k + 1) : ℂ)
    * ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s))

/-- Reindexing a range sum as an `Icc` sum. -/
theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f (i + 1) = ∑ m ∈ Finset.Icc 1 n, f m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem coeffPartial_ofReal (b : ℕ → ℝ) (n : ℕ) :
    coeffPartial (fun i => (b (i + 1) : ℂ)) n = (sourcePartialSum b n : ℂ) := by
  rw [coeffPartial, sourcePartialSum, Complex.ofReal_sum,
    ← sum_range_succ_eq_sum_Icc (fun m => ((b m : ℝ) : ℂ)) n]

/-! ## The two convergence inputs -/

theorem norm_abelTail_term_le {b : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ‖coeffPartial (fun i => (b (i + 1) : ℂ)) (k + 1)
        * ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s))‖
      ≤ C * ‖s‖ * ((k : ℝ) + 1) ^ (θ - s.re - 1) := by
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hincr := GaloisForLFunctions.RHTower.norm_cpow_unit_diff_le hs hx
  have hrw : (((k : ℝ) + 1 + 1 : ℝ) : ℂ) = (((k : ℝ) + 2 : ℝ) : ℂ) := by
    congr 1
    ring
  rw [hrw] at hincr
  have hpart : ‖coeffPartial (fun i => (b (i + 1) : ℂ)) (k + 1)‖ ≤ C * ((k : ℝ) + 1) ^ θ := by
    rw [coeffPartial_ofReal, Complex.norm_real, Real.norm_eq_abs]
    have h := hb (k + 1)
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    exact h
  rw [norm_mul]
  have hsplit : ((k : ℝ) + 1) ^ (θ - s.re - 1)
      = ((k : ℝ) + 1) ^ θ * ((k : ℝ) + 1) ^ (-s.re - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc ‖coeffPartial (fun i => (b (i + 1) : ℂ)) (k + 1)‖
        * ‖(((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)‖
      ≤ (C * ((k : ℝ) + 1) ^ θ) * (‖s‖ * ((k : ℝ) + 1) ^ (-s.re - 1)) := by
        refine mul_le_mul hpart hincr (norm_nonneg _) (by positivity)
    _ = C * ‖s‖ * ((k : ℝ) + 1) ^ (θ - s.re - 1) := by
        rw [hsplit]
        ring

theorem summable_abelTail_majorant {θ σ : ℝ} (hθσ : θ < σ) :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ (θ - σ - 1) := by
  have h : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (σ + 1 - θ) := by
    have := (Real.summable_one_div_nat_add_rpow 1 (σ + 1 - θ)).2 (by linarith)
    refine this.congr fun k => ?_
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [abs_of_pos hpos]
  refine h.congr fun k => ?_
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [one_div, ← Real.rpow_neg hpos.le]
  congr 1
  ring

theorem summable_abelTail {b : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re)
    (hθs : θ < s.re) :
    Summable fun k : ℕ => coeffPartial (fun i => (b (i + 1) : ℂ)) (k + 1)
      * ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => norm_abelTail_term_le hC hb hs k) ?_
  exact ((summable_abelTail_majorant hθs).mul_left (C * ‖s‖))

theorem tendsto_abelTail_boundary {b : ℕ → ℝ} {C θ : ℝ}
    (hb : ∀ N : ℕ, |sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hθs : θ < s.re) :
    Tendsto (fun n : ℕ => ((n : ℝ) : ℂ) ^ (-s) * coeffPartial (fun i => (b (i + 1) : ℂ)) n)
      atTop (𝓝 0) := by
  have hmaj : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (θ - s.re)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => x ^ (θ - s.re)) atTop (𝓝 0) := by
      have heq : θ - s.re = -(s.re - θ) := by ring
      rw [heq]
      exact tendsto_rpow_neg_atTop (by linarith)
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) ^ (θ - s.re)) atTop (𝓝 0) :=
      hbase.comp tendsto_natCast_atTop_atTop
    simpa using hnat.const_mul C
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [norm_mul, coeffPartial_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hcpow : ‖((n : ℝ) : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
  rw [hcpow]
  have hexp : (n : ℝ) ^ (θ - s.re) = (n : ℝ) ^ θ * (n : ℝ) ^ (-s.re) := by
    rw [← Real.rpow_add hn0]
    congr 1
  have hsplit : C * (n : ℝ) ^ (θ - s.re) = (n : ℝ) ^ (-s.re) * (C * (n : ℝ) ^ θ) := by
    rw [hexp]
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (hb n) (Real.rpow_nonneg hn0.le _)

/-! ## The identification -/

theorem tsum_shift_eq_LSeries {b : ℕ → ℝ} {s : ℂ}
    (hsum : LSeriesSummable (fun n => (b n : ℂ)) s) :
    (∑' i : ℕ, (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * (b (i + 1) : ℂ))
      = LSeries (fun n => (b n : ℂ)) s := by
  have hshift := hsum.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, LSeries.term_zero, zero_add] at hshift
  rw [LSeries, ← hshift]
  refine tsum_congr fun i => ?_
  rw [LSeries.term_of_ne_zero (by omega : i + 1 ≠ 0)]
  have hcast : ((i + 1 : ℕ) : ℂ) = (((i : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.cpow_neg]
  ring

theorem summable_shift_of_LSeriesSummable {b : ℕ → ℝ} {s : ℂ}
    (hsum : LSeriesSummable (fun n => (b n : ℂ)) s) :
    Summable fun i : ℕ => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * (b (i + 1) : ℂ) := by
  have hcomp : Summable fun i : ℕ => LSeries.term (fun n => (b n : ℂ)) s (i + 1) :=
    hsum.comp_injective (add_left_injective 1)
  refine hcomp.congr fun i => ?_
  rw [LSeries.term_of_ne_zero (by omega : i + 1 ≠ 0)]
  have hcast : ((i + 1 : ℕ) : ℂ) = (((i : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.cpow_neg]
  ring

/-- **The Abel tail of the summatory profile is the `L`-series of its source.** -/
theorem abelTailSeries_sourcePartialSum {b : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re)
    (hθs : θ < s.re) (hsum : LSeriesSummable (fun n => (b n : ℂ)) s) :
    abelTailSeries (sourcePartialSum b) s = LSeries (fun n => (b n : ℂ)) s := by
  have habel := tsum_eq_abelTail (c := fun i => (b (i + 1) : ℂ)) (s := s)
    (summable_shift_of_LSeriesSummable hsum) (summable_abelTail hC hb hs hθs)
    (tendsto_abelTail_boundary hb hθs)
  rw [abelTailSeries, ← tsum_shift_eq_LSeries hsum, habel]
  refine tsum_congr fun k => ?_
  rw [coeffPartial_ofReal]

end

end RHTower
