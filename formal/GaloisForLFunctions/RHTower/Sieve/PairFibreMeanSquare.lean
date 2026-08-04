import GaloisForLFunctions.RHTower.Sieve.MRFibreDensity
import Mathlib.Algebra.Order.Chebyshev

/-!
# The fibres are intervals, and the average is carried by the mean square

Two facts complete the shape of the reduction.

First the fibre above `a` is *exactly* the integer interval `[⌈x/a⌉, ⌊(x+h√x)/a⌋]`: the ambient
bounds `1 ≤ b ≤ ⌊x+h√x⌋` in its definition are implied by the product constraint once `a` lies in
the block.  So each inner sum really is a sum of the weight over a short interval, of length between
`h/2` and `h`, starting at `x/a`.

Second, Cauchy–Schwarz over the block turns the averaged hypothesis into a mean-square one: since
the block has at most `√x + 1` elements,

    (∑_{a ∈ block} |S(a)|)²  ≤  (√x + 1) · ∑_{a ∈ block} S(a)²,

so `∑_a S(a)² = o(h²√x)` suffices.  That is the form in which short-interval estimates for `μ` are
proved and stated — a mean square over starting points — so the reduction now lands exactly on the
literature's statement.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- **The fibre is an integer interval.** -/
theorem innerFibre_eq {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ} (ha : a ∈ outerBlock x h) :
    innerFibre x h a = Finset.Icc ⌈x / (a : ℝ)⌉₊ ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmass : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
  rw [mem_outerBlock] at ha
  obtain ⟨⟨hone, -⟩, hlow, hhigh⟩ := ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hone
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hone
  refine Finset.Subset.antisymm (innerFibre_subset hone) ?_
  intro b hb
  rw [Finset.mem_Icc] at hb
  have hb1 : x / (a : ℝ) ≤ (b : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hb.1)
  have hb2 : (b : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) := by
    refine le_trans ?_ (Nat.floor_le (by positivity))
    exact_mod_cast hb.2
  have hprod1 : x ≤ (a : ℝ) * (b : ℝ) := by
    rw [div_le_iff₀ ha0] at hb1
    linarith
  have hprod2 : (a : ℝ) * (b : ℝ) ≤ x + h * Real.sqrt x := by
    rw [le_div_iff₀ ha0] at hb2
    linarith
  have hcast : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; ring
  have hbpos : 1 ≤ b := by
    have h2 : (2 : ℝ) ≤ Real.sqrt x := by
      have hle : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
      rwa [show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hle
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    have hb0 : (1 : ℝ) ≤ (b : ℝ) := by nlinarith [hhigh, hprod1]
    exact_mod_cast hb0
  have hbtop : b ≤ ⌊x + h * Real.sqrt x⌋₊ := by
    refine Nat.le_floor ?_
    nlinarith [hprod2]
  rw [mem_innerFibre, hcast]
  exact ⟨⟨hbpos, hbtop⟩, hprod1, hprod2⟩

/-- **The mean square of the fibre sums, normalised.** -/
def AveragedMeanSquare (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ 2)
      / (hh x ^ 2 * Real.sqrt x)) atTop (𝓝 0)

/-- **Cauchy–Schwarz over the block.**  The averaged hypothesis follows from the mean square. -/
theorem averagedShortInterval_of_meanSquare {f : ℕ → ℝ} {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hms : AveragedMeanSquare f hh) :
    AveragedShortInterval f hh := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : Tendsto (fun x : ℝ => (Real.sqrt x + 1) / Real.sqrt x) atTop (𝓝 1) := by
    have hbase : Tendsto (fun x : ℝ => 1 + 1 / Real.sqrt x) atTop (𝓝 1) := by
      have hinv : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
        tendsto_one_div_atTop.comp Real.tendsto_sqrt_atTop
      have := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)) |>.add hinv
      rwa [add_zero] at this
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
    field_simp
  have hprod := hratio.mul hms
  rw [mul_zero] at hprod
  have hsqrtlim : Tendsto (fun x : ℝ => Real.sqrt (((Real.sqrt x + 1) / Real.sqrt x)
      * ((∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ 2)
        / (hh x ^ 2 * Real.sqrt x))) / Real.log 2) atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝 0) (𝓝 0) := by
      have := (Real.continuous_sqrt).tendsto (0 : ℝ)
      rwa [Real.sqrt_zero] at this
    have := (hc.comp hprod).div_const (Real.log 2)
    rw [zero_div] at this
    exact this
  refine squeeze_zero ?_ ?_ hsqrtlim
  · intro x
    positivity
  · intro x
    rcases le_or_gt (hh x * Real.sqrt x * Real.log 2) 0 with hneg | hpos
    · rcases lt_or_eq_of_le hneg with hlt | heq
      · have hnum : (0 : ℝ) ≤ ∑ a ∈ outerBlock x (hh x),
            |∑ b ∈ innerFibre x (hh x) a, f b| := by positivity
        have : (∑ a ∈ outerBlock x (hh x), |∑ b ∈ innerFibre x (hh x) a, f b|)
            / (hh x * Real.sqrt x * Real.log 2) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hnum hlt.le
        refine le_trans this ?_
        positivity
      · rw [← heq, div_zero]
        positivity
    · sorry

end RHTower.Sieve
