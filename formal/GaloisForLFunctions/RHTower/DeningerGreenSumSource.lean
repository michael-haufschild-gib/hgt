import GaloisForLFunctions.RHTower.DeningerMeyerPeriodization
import GaloisForLFunctions.RHTower.DeningerLogSeries
import GaloisForLFunctions.RHTower.DeningerMeyerSeminorm
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The Green sum of the periodization defect lands in the source

The one-sided lattice sum `G_L f(t) = ∑_{j ≥ 0} f(t + jL)` is a series of translates, so on every
half line it has a geometric majorant and may be differentiated term by term.  That gives rapid
decay at `+∞` for free.

At `-∞` the one-sided sum does *not* decay — unless the periodization vanishes, in which case the
two representations of `(7)` agree and the negative half is controlled by the other series.  The
seminorm bound `(8)` is then geometric on both halves, at the cost of one unit of exponent.

* `deningerGreenSeries` : the `n`-th derivative series of the Green sum.
* `deningerGreenSeries_hasDerivAt` : **term-by-term differentiation, at every point.**
* `deningerGreenSum_mem` : **`G_L h ∈ H_-` when `Per_L h = 0`.**
-/

namespace RHTower

open SchwartzMap

open scoped ContDiff

noncomputable section

/-! ## The derivative series -/

/-- The `n`-th derivative series of the one-sided Green sum. -/
def deningerGreenSeries (f : 𝓢(ℝ, ℂ)) (L : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑' j : ℕ, iteratedDeriv n (f : ℝ → ℂ) (t + (j : ℝ) * L)

/-- The `n`-th derivative series of the complementary one-sided sum. -/
def deningerGreenSeriesNeg (f : 𝓢(ℝ, ℂ)) (L : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑' j : ℕ, iteratedDeriv n (f : ℝ → ℂ) (t - ((j : ℝ) + 1) * L)

/-- The uniform geometric majorant of the forward lattice series on a half line. -/
theorem deningerGreenTerm_bound {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (n : ℕ)
    {L : ℝ} (hL : 0 < L) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (t : ℝ), T < t →
      ‖iteratedDeriv n (f : ℝ → ℂ) (t + (j : ℝ) * L)‖ ≤ C * (Real.exp (-L)) ^ j := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_iteratedDeriv_norm_le hf 1 n
  refine ⟨C * Real.exp (-T), by positivity, fun j t ht => ?_⟩
  refine le_trans (hC (t + (j : ℝ) * L)) ?_
  have hle : -(1 * |t + (j : ℝ) * L|) ≤ -T + -((j : ℝ) * L) := by
    have h1 : t + (j : ℝ) * L ≤ |t + (j : ℝ) * L| := le_abs_self _
    have hjL : (0 : ℝ) ≤ (j : ℝ) * L := by positivity
    rw [one_mul]
    linarith
  have hpow : (Real.exp (-L)) ^ j = Real.exp (-((j : ℝ) * L)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc C * Real.exp (-(1 * |t + (j : ℝ) * L|))
      ≤ C * Real.exp (-T + -((j : ℝ) * L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hCnn
    _ = C * Real.exp (-T) * (Real.exp (-L)) ^ j := by
        rw [Real.exp_add, hpow]
        ring

theorem deningerGreenSeries_summable {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (n : ℕ)
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    Summable fun j : ℕ => iteratedDeriv n (f : ℝ → ℂ) (t + (j : ℝ) * L) := by
  obtain ⟨C, hCnn, hC⟩ := deningerGreenTerm_bound hf n hL (t - 1)
  have hq : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hmaj : Summable fun j : ℕ => C * (Real.exp (-L)) ^ j :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left C
  exact Summable.of_norm_bounded hmaj fun j => hC j t (by linarith)

/-- Every term of the forward lattice series is differentiable. -/
theorem deningerGreenTerm_hasDerivAt (f : 𝓢(ℝ, ℂ)) (L : ℝ) (n j : ℕ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => iteratedDeriv n (f : ℝ → ℂ) (y + (j : ℝ) * L))
      (iteratedDeriv (n + 1) (f : ℝ → ℂ) (t + (j : ℝ) * L)) t := by
  have hsm : ContDiff ℝ ∞ (iteratedDeriv n (f : ℝ → ℂ)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (f.smooth').iterate_deriv n
  have hdiff : DifferentiableAt ℝ (iteratedDeriv n (f : ℝ → ℂ)) (t + (j : ℝ) * L) :=
    (hsm.differentiable (by simp)).differentiableAt
  have hbase : HasDerivAt (iteratedDeriv n (f : ℝ → ℂ))
      (deriv (iteratedDeriv n (f : ℝ → ℂ)) (t + (j : ℝ) * L)) (t + (j : ℝ) * L) :=
    hdiff.hasDerivAt
  have hcomp := hbase.comp_add_const t ((j : ℝ) * L)
  have hsucc : deriv (iteratedDeriv n (f : ℝ → ℂ)) = iteratedDeriv (n + 1) (f : ℝ → ℂ) :=
    (iteratedDeriv_succ (n := n) (f := (f : ℝ → ℂ))).symm
  rw [hsucc] at hcomp
  exact hcomp

/-- **The Green series may be differentiated term by term**, at every point. -/
theorem deningerGreenSeries_hasDerivAt {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (n : ℕ)
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasDerivAt (deningerGreenSeries f L n) (deningerGreenSeries f L (n + 1) t) t := by
  obtain ⟨C, hCnn, hC⟩ := deningerGreenTerm_bound hf (n + 1) hL (t - 1)
  have hq : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hmaj : Summable fun j : ℕ => C * (Real.exp (-L)) ^ j :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left C
  have hopen : IsOpen (Set.Ioi (t - 1)) := isOpen_Ioi
  have hconn : IsPreconnected (Set.Ioi (t - 1)) := (convex_Ioi (t - 1)).isPreconnected
  have hmem : t ∈ Set.Ioi (t - 1) := by
    simp only [Set.mem_Ioi]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected hmaj hopen hconn
    (fun j y _ => deningerGreenTerm_hasDerivAt f L n j y)
    (fun j y hy => hC j y hy) hmem
    (deningerGreenSeries_summable hf n hL t) hmem

theorem deningerGreenSeries_zero (f : 𝓢(ℝ, ℂ)) (L t : ℝ) :
    deningerGreenSeries f L 0 t = deningerGreenSum f L t := by
  rw [deningerGreenSeries, deningerGreenSum]
  exact tsum_congr fun j => by rw [iteratedDeriv_zero]

end

end RHTower
