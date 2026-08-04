import GaloisForLFunctions.RHTower.Sieve.MRFibreDensityAt
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

/-- **Cauchy–Schwarz over the block.**  A mean-square bound for any family of deviations gives the
corresponding averaged bound, because the block has at most `√X + 1` elements. -/
theorem tendsto_sum_abs_div_of_meanSquare {g : ℝ → ℕ → ℝ} {X hh : ℝ → ℝ}
    (hXtop : Tendsto X atTop atTop) (hhtop : Tendsto hh atTop atTop)
    (hms : Tendsto (fun x => (∑ a ∈ outerBlock (X x) (hh x), (g x a) ^ 2)
        / (hh x ^ 2 * Real.sqrt (X x))) atTop (𝓝 0)) :
    Tendsto (fun x => (∑ a ∈ outerBlock (X x) (hh x), |g x a|)
        / (hh x * Real.sqrt (X x) * Real.log 2)) atTop (𝓝 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hXsqrt : Tendsto (fun x => Real.sqrt (X x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hXtop
  have hratio : Tendsto (fun x : ℝ => (Real.sqrt (X x) + 1) / Real.sqrt (X x)) atTop (𝓝 1) := by
    have hbase : Tendsto (fun x : ℝ => 1 + 1 / Real.sqrt (X x)) atTop (𝓝 1) := by
      have hinv : Tendsto (fun x : ℝ => 1 / Real.sqrt (X x)) atTop (𝓝 0) :=
        tendsto_one_div_atTop.comp hXsqrt
      have := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)) |>.add hinv
      rwa [add_zero] at this
    refine Tendsto.congr' ?_ hbase
    filter_upwards [hXsqrt.eventually_gt_atTop 0] with x hs
    field_simp
  have hprod := hratio.mul hms
  rw [mul_zero] at hprod
  have hsqrtlim : Tendsto (fun x : ℝ => Real.sqrt (((Real.sqrt (X x) + 1) / Real.sqrt (X x))
      * ((∑ a ∈ outerBlock (X x) (hh x), (g x a) ^ 2)
        / (hh x ^ 2 * Real.sqrt (X x)))) / Real.log 2) atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝 0) (𝓝 0) := by
      have := (Real.continuous_sqrt).tendsto (0 : ℝ)
      rwa [Real.sqrt_zero] at this
    have := (hc.comp hprod).div_const (Real.log 2)
    rw [zero_div] at this
    exact this
  refine squeeze_zero_norm' ?_ hsqrtlim
  filter_upwards [hXtop.eventually_gt_atTop 4, hhtop.eventually_gt_atTop 0,
    hXsqrt.eventually_gt_atTop 0] with x hx hhx hs
  have hd : (0 : ℝ) < hh x * Real.sqrt (X x) := by positivity
  set A : ℝ := ∑ a ∈ outerBlock (X x) (hh x), |g x a| with hAdef
  set Q : ℝ := ∑ a ∈ outerBlock (X x) (hh x), (g x a) ^ 2 with hQdef
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hAdef]
    positivity
  have hQ0 : (0 : ℝ) ≤ Q := by
    rw [hQdef]
    positivity
  have hcs : A ^ 2 ≤ ((outerBlock (X x) (hh x)).card : ℝ) * Q := by
    have hbase := sq_sum_le_card_mul_sum_sq (s := outerBlock (X x) (hh x))
      (f := fun a => |g x a|)
    have hval : ∑ a ∈ outerBlock (X x) (hh x), |g x a| ^ 2 = Q := by
      rw [hQdef]
      exact Finset.sum_congr rfl (fun a _ => sq_abs _)
    rw [hval] at hbase
    exact hbase
  have hcard : ((outerBlock (X x) (hh x)).card : ℝ) ≤ Real.sqrt (X x) + 1 :=
    card_outerBlock_le (le_of_lt hx) hhx.le
  have hbound : A ^ 2 ≤ (Real.sqrt (X x) + 1) * Q :=
    le_trans hcs (mul_le_mul_of_nonneg_right hcard hQ0)
  set K : ℝ := ((Real.sqrt (X x) + 1) / Real.sqrt (X x))
    * (Q / (hh x ^ 2 * Real.sqrt (X x))) with hKdef
  have hK : (A / (hh x * Real.sqrt (X x))) ^ 2 ≤ K := by
    rw [hKdef, div_pow, div_le_iff₀ (by positivity)]
    have hexp : ((Real.sqrt (X x) + 1) / Real.sqrt (X x)) * (Q / (hh x ^ 2 * Real.sqrt (X x)))
        * (hh x * Real.sqrt (X x)) ^ 2 = (Real.sqrt (X x) + 1) * Q := by
      field_simp
    rw [hexp]
    exact hbound
  have hstep : A / (hh x * Real.sqrt (X x)) ≤ Real.sqrt K := by
    calc A / (hh x * Real.sqrt (X x))
        = Real.sqrt ((A / (hh x * Real.sqrt (X x))) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hK
  have hfinal : A / (hh x * Real.sqrt (X x) * Real.log 2) ≤ Real.sqrt K / Real.log 2 := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hstep hlog2.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hfinal

/-- **The mean square of the fibre sums, normalised.** -/
def AveragedMeanSquare (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ 2)
      / (hh x ^ 2 * Real.sqrt x)) atTop (𝓝 0)

/-- **The centred mean square of the fibre sums, at a moving pair of parameters.** -/
def AveragedMeanSquareDensityAt (f : ℕ → ℝ) (c : ℝ) (X hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ a ∈ outerBlock (X x) (hh x),
      ((∑ b ∈ innerFibre (X x) (hh x) a, f b)
        - c * (hh x * Real.sqrt (X x) / (a : ℝ))) ^ 2)
      / (hh x ^ 2 * Real.sqrt (X x))) atTop (𝓝 0)

/-- The cancellation hypothesis follows from the mean square. -/
theorem averagedShortInterval_of_meanSquare {f : ℕ → ℝ} {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hms : AveragedMeanSquare f hh) :
    AveragedShortInterval f hh :=
  tendsto_sum_abs_div_of_meanSquare (X := id)
    (g := fun x a => ∑ b ∈ innerFibre x (hh x) a, f b) tendsto_id hgrow hms

/-- The equidistribution hypothesis follows from the centred mean square. -/
theorem averagedShortIntervalDensity_of_meanSquare {f : ℕ → ℝ} {c : ℝ} {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hms : AveragedMeanSquareDensityAt f c id hh) :
    AveragedShortIntervalDensity f c hh :=
  tendsto_sum_abs_div_of_meanSquare (X := id)
    (g := fun x a => (∑ b ∈ innerFibre x (hh x) a, f b) - c * (hh x * Real.sqrt x / (a : ℝ)))
    tendsto_id hgrow hms

/-- The equidistribution hypothesis at a moving pair of parameters, from the centred mean square. -/
theorem averagedShortIntervalDensityAt_of_meanSquare {f : ℕ → ℝ} {c : ℝ} {X hh : ℝ → ℝ}
    (hXtop : Tendsto X atTop atTop) (hgrow : Tendsto hh atTop atTop)
    (hms : AveragedMeanSquareDensityAt f c X hh) :
    AveragedShortIntervalDensityAt f c X hh :=
  tendsto_sum_abs_div_of_meanSquare
    (g := fun x a => (∑ b ∈ innerFibre (X x) (hh x) a, f b)
      - c * (hh x * Real.sqrt (X x) / (a : ℝ)))
    hXtop hgrow hms

end RHTower.Sieve
