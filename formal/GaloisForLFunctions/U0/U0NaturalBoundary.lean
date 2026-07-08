/-
# Natural boundary of u₀ at the unit circle

The function `u₀(z) = ∑_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}` has the unit circle `{|z|=1}` as
a natural boundary — it cannot be analytically continued across any arc of the unit circle.

## Proof strategy

Substituting `w = 1/z`, the companion series is `U₀(w) = u₀(1/w) = ∑_{n≥0} 2^{-(n+1)} w^{2^{n+1}-1}`.
- The exponents `2^{n+1}-1` satisfy `lim_{n→∞} λ_{n+1}/λ_n = 2 > 1`, so the series has
  **Hadamard gaps** (Ostrowski–Hadamard gap theorem).
- Every point on the unit circle `|w|=1` is a singular point of U₀.
- Equivalently, every point on the unit circle `|z|=1` is a singular point of u₀.

In Lean: stated with the genuine *analytic-continuation* predicate `ContinuesAcross` (NOT `¬AnalyticAt`
of the junk-extended tsum, which is trivially true for the wrong reason — see the ⚠ note below).
`u0_natural_boundary` is **fully proven** (`#print axioms`: only `propext`/`Classical.choice`/`Quot.sound`,
no `sorryAx`), with **no appeal to the Ostrowski–Hadamard gap theorem**. The ingredients, all proven
here: convergence/divergence (companion series radius = 1), the Mahler-equation propagation
`continues_sq`, dyadic-root density `dense_dyadic_roots`, closedness `isClosed_singular`, and the
`seed_singularity` (one boundary singularity) via a sheaf-gluing of analytic continuations — uniform
Lebesgue cover + `overlap_consistency` (chord-midpoints + identity theorem) + a radial-projection
construction + the radius-1 endpoint `glue_contradiction`.
-/
import GaloisForLFunctions.U0.U0Series
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.RingTheory.Algebraic.Basic

open Complex Filter Topology U0

namespace U0NaturalBoundary

/-! ## Radius of convergence of U₀ = 1 -/

/-- The companion series U₀(w) = u₀(1/w) converges absolutely for |w| < 1. -/
@[aesop safe]
theorem U0_summable_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (2 : ℝ) ^ (-(n + 1 : ℤ)))
  · exact summable_two_zpow_neg
  · intro n
    rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_two]
    have hw1 : ‖w‖ ≤ 1 := le_of_lt hw
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    have hexp : (0 : ℤ) ≤ 2 ^ (n + 1) - 1 := by
      have h : (1 : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast Nat.one_le_two_pow
      linarith
    have hwpow : ‖w‖ ^ (2 ^ (n + 1) - 1 : ℤ) ≤ 1 := by
      lift (2 ^ (n + 1) - 1 : ℤ) to ℕ using hexp with m hm
      rw [zpow_natCast]
      exact pow_le_one₀ hw0 hw1
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(↑n + 1 : ℤ)) := zpow_nonneg (by norm_num) _
    linarith [mul_le_mul_of_nonneg_left hwpow h2]

/-! ## The single irreducible analytic core

⚠ **Correctness note (junk-extension trap).** `∑'` is `0` wherever the series diverges, so the
*literal* tsum function jumps to `0` across `‖·‖=1` and is trivially non-`AnalyticAt` there — for the
WRONG reason (a discontinuous junk extension, which an *algebraic* function would share). That trivial
statement does **not** encode a natural boundary and does **not** imply transcendence. The genuine
content is *analytic continuation from the domain of convergence*, captured by `ContinuesAcross`:
an analytic `g` near `z₀` agreeing with the function on the convergence-side neighborhood. Junk values
off the domain cannot satisfy this, so it carries real content. -/

/-- `f` continues analytically across `z₀` from the domain `D`: some `g` analytic at `z₀` agrees with
`f` on a `D`-side neighborhood of `z₀`. Its negation, for every boundary point, is a *genuine* natural
boundary (unlike `¬ AnalyticAt` of a junk-extended tsum). -/
def ContinuesAcross (f : ℂ → ℂ) (D : Set ℂ) (z₀ : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ ∀ᶠ w in nhdsWithin z₀ D, g w = f w

/-- The exterior `{z | 1 < ‖z‖}`, the genuine domain of convergence of `u₀`. -/
def Ext : Set ℂ := {z : ℂ | 1 < ‖z‖}

@[aesop safe]
theorem isOpen_Ext : IsOpen Ext := isOpen_lt continuous_const continuous_norm

@[aesop safe]
theorem ne_zero_of_Ext {z : ℂ} (hz : z ∈ Ext) : z ≠ 0 := by
  intro h; rw [h] at hz; simp only [Ext, Set.mem_setOf_eq, norm_zero] at hz; linarith

/-- Each term `2^{-(n+1)}·z^{-(2^{n+1}-1)}` is holomorphic on the exterior (`z ≠ 0` there). -/
@[aesop safe]
theorem term_differentiableOn_Ext (n : ℕ) : DifferentiableOn ℂ
    (fun z : ℂ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))) Ext :=
  DifferentiableOn.const_mul
    (DifferentiableOn.zpow differentiableOn_id (Or.inl (fun _ hx => ne_zero_of_Ext hx))) _

/-- **u₀ is holomorphic on the exterior `Ext` (PROVEN).** Weierstrass M-test: each term is
holomorphic on `Ext` and bounded there by the summable `2^{-(n+1)}` (`norm_u0_term_le`). -/
@[aesop safe]
theorem u0_differentiableOn_Ext : DifferentiableOn ℂ u0 Ext :=
  differentiableOn_tsum_of_summable_norm summable_two_zpow_neg
    term_differentiableOn_Ext isOpen_Ext
    (fun n _ hw => norm_u0_term_le (le_of_lt hw) n)

/-- **u₀ is analytic on the exterior `Ext` (PROVEN).** The analytic realization underlying the
natural-boundary statement: on `Ext`, `u₀` is the genuine convergent sum, not a junk extension. -/
@[aesop safe]
theorem u0_analyticOnNhd_Ext : AnalyticOnNhd ℂ u0 Ext :=
  u0_differentiableOn_Ext.analyticOnNhd isOpen_Ext

/-- **Propagation by the Mahler functional equation (step 3, PROVEN).**
If `u₀` continues analytically across `z₀ ≠ 0`, it continues across `z₀²`.

The continuation `g` of `u₀` near `z₀` is pushed to a continuation of `u₀` near `z₀²` via the local
analytic inverse `s` of `z ↦ z²` (`analyticAt_localInverse`, valid since `z₀ ≠ 0`): set
`h(v) = 2·s(v)·g(s(v)) − 1`. On the exterior side, `s(v) ∈ Ext`, `g(s v) = u₀(s v)`, `(s v)² = v`, and
the functional equation `2·(s v)·u₀(s v) = 1 + u₀((s v)²)` give `h(v) = u₀(v)`. This is the step the
generic Ostrowski–Hadamard proof lacks — it is special to series with a Mahler equation. -/
@[aesop safe]
theorem continues_sq {z₀ : ℂ} (hz0 : z₀ ≠ 0) (h : ContinuesAcross u0 Ext z₀) :
    ContinuesAcross u0 Ext (z₀ ^ 2) := by
  obtain ⟨g, hg_an, hg_eq⟩ := h
  have hf : AnalyticAt ℂ (fun z : ℂ => z ^ 2) z₀ := by fun_prop
  have hfderiv : deriv (fun z : ℂ => z ^ 2) z₀ ≠ 0 := by
    rw [show deriv (fun z : ℂ => z ^ 2) z₀ = 2 * z₀ from by simp]; simp [hz0]
  set s := hf.hasStrictDerivAt.localInverse _ _ _ hfderiv with hs_def
  have hs_an : AnalyticAt ℂ s (z₀ ^ 2) := hf.analyticAt_localInverse hfderiv
  have hs_pt : s (z₀ ^ 2) = z₀ := by
    have := (hf.hasStrictDerivAt.eventually_left_inverse hfderiv).self_of_nhds
    rw [hs_def]
    exact this
  have hs_rinv : ∀ᶠ v in nhds (z₀ ^ 2), (s v) ^ 2 = v :=
    hf.hasStrictDerivAt.eventually_right_inverse hfderiv
  refine ⟨fun v => 2 * s v * g (s v) - 1, ?_, ?_⟩
  · have hgs : AnalyticAt ℂ (fun v => g (s v)) (z₀ ^ 2) := by
      have hg' : AnalyticAt ℂ g (s (z₀ ^ 2)) := by rw [hs_pt]; exact hg_an
      exact hg'.comp hs_an
    exact (((analyticAt_const.mul hs_an).mul hgs).sub analyticAt_const)
  · have ha : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), (s v) ^ 2 = v := hs_rinv.filter_mono nhdsWithin_le_nhds
    have hv_ext : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), v ∈ Ext := self_mem_nhdsWithin
    have hb : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), s v ∈ Ext := by
      filter_upwards [ha, hv_ext] with v hva hvb
      have hvn : 1 < ‖v‖ := hvb
      rw [← hva, norm_pow] at hvn
      have hsn : 0 ≤ ‖s v‖ := norm_nonneg _
      show 1 < ‖s v‖
      nlinarith [hvn, hsn]
    have hc : ∀ᶠ v in 𝓝[Ext] (z₀ ^ 2), g (s v) = u0 (s v) := by
      have htends : Tendsto s (𝓝[Ext] (z₀ ^ 2)) (𝓝[Ext] z₀) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, hb⟩
        have hcont : Tendsto s (𝓝 (z₀ ^ 2)) (𝓝 z₀) := by
          have := hs_an.continuousAt; rw [ContinuousAt, hs_pt] at this; exact this
        exact hcont.mono_left nhdsWithin_le_nhds
      exact htends.eventually hg_eq
    filter_upwards [ha, hb, hc] with v hva hvb hvc
    have hsv1 : 1 ≤ ‖s v‖ := le_of_lt hvb
    have hfe := functional_equation hsv1
    show 2 * s v * g (s v) - 1 = u0 v
    rw [hva] at hfe
    rw [hvc, hfe]; ring

/-- **Singularity spreads to square roots (contrapositive of `continues_sq`).**
If `u₀` does not continue across `z₀² (z₀ ≠ 0)`, it does not continue across `z₀`. -/
@[aesop safe]
theorem not_continues_of_sq {z₀ : ℂ} (hz0 : z₀ ≠ 0)
    (h : ¬ ContinuesAcross u0 Ext (z₀ ^ 2)) : ¬ ContinuesAcross u0 Ext z₀ :=
  fun hc => h (continues_sq hz0 hc)

/-- **The set of continuation points is open (step 5, PROVEN).**
If `u₀` continues across `z₀` via `g`, the *same* `g` witnesses continuation across every nearby `z`
(`g` is analytic on a neighborhood, and the agreement set `W ∩ Ext` is an `Ext`-neighborhood of each
`z ∈ W`). Hence the singular set is closed. -/
@[aesop safe]
theorem isOpen_continues : IsOpen {z : ℂ | ContinuesAcross u0 Ext z} := by
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨g, hg_an, hg_eq⟩
  obtain ⟨W, hWopen, hz₀W, hWsub⟩ := mem_nhdsWithin.mp hg_eq
  have hWnhds : W ∈ 𝓝 z₀ := hWopen.mem_nhds hz₀W
  have hAnhds : {z | AnalyticAt ℂ g z} ∈ 𝓝 z₀ := (isOpen_analyticAt ℂ g).mem_nhds hg_an
  filter_upwards [hWnhds, hAnhds] with z hzW hzAn
  exact ⟨g, hzAn, mem_nhdsWithin.mpr ⟨W, hWopen, hzW, hWsub⟩⟩

/-- The singular set `{z | ¬ ContinuesAcross u0 Ext z}` is closed. -/
@[aesop safe]
theorem isClosed_singular : IsClosed {z : ℂ | ¬ ContinuesAcross u0 Ext z} :=
  isOpen_continues.isClosed_compl

/-! ### Companion power series on the unit disk (foundation for the seed)

`U0sum(w) = ∑ 2^{-(n+1)} w^{2^{n+1}-1} = u₀(1/w)` is the genuine convergent companion on `‖w‖<1`. It is
holomorphic on the open disk (Weierstrass M-test) and so carries a Cauchy power series on every
`closedBall 0 r`, `r<1` — giving radius `≥ 1`. With the proven divergence `U0term_norm_tendsto_atTop`
(radius `≤ 1`), the companion has radius exactly `1`. This is the disk-side machinery the seed argument
(Pringsheim, via the nonnegative coefficients `2^{-(n+1)} > 0`) runs on. -/

/-- The companion sum `U₀(w) = ∑ 2^{-(n+1)} w^{2^{n+1}-1}` on the disk. -/
noncomputable def U0sum (w : ℂ) : ℂ :=
  ∑' n : ℕ, (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ)

/-- Each companion term `2^{-(n+1)} w^{2^{n+1}-1}` is entire (nonnegative integer exponent). -/
@[aesop safe]
theorem companion_term_diff (n : ℕ) : Differentiable ℂ
    (fun w : ℂ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ)) := by
  have hexp : (0:ℤ) ≤ 2 ^ (n + 1) - 1 := by
    have : (1:ℤ) ≤ 2 ^ (n+1) := by exact_mod_cast Nat.one_le_two_pow
    linarith
  apply Differentiable.const_mul
  lift (2 ^ (n + 1) - 1 : ℤ) to ℕ using hexp with m
  simp only [zpow_natCast]
  exact differentiable_pow m

/-- On the open unit disk each companion term is bounded by the summable `2^{-(n+1)}`. -/
@[aesop safe]
theorem companion_bound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball (0:ℂ) 1) :
    ‖(2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ)‖ ≤ (2 : ℝ) ^ (-(n + 1 : ℤ)) := by
  rw [Metric.mem_ball, dist_zero_right] at hw
  rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_two]
  have hexp : (0:ℤ) ≤ 2 ^ (n + 1) - 1 := by
    have : (1:ℤ) ≤ 2 ^ (n+1) := by exact_mod_cast Nat.one_le_two_pow
    linarith
  have hwle : ‖w‖ ^ (2 ^ (n + 1) - 1 : ℤ) ≤ 1 := by
    lift (2 ^ (n + 1) - 1 : ℤ) to ℕ using hexp with m
    rw [zpow_natCast]
    exact pow_le_one₀ (norm_nonneg _) (le_of_lt hw)
  have h2 : (0:ℝ) ≤ (2:ℝ)^(-(↑n+1:ℤ)) := zpow_nonneg (by norm_num) _
  nlinarith [mul_le_mul_of_nonneg_left hwle h2]

/-- **U₀sum is holomorphic on the open unit disk (PROVEN).** -/
@[aesop safe]
theorem U0sum_diff_open : DifferentiableOn ℂ U0sum (Metric.ball 0 1) :=
  differentiableOn_tsum_of_summable_norm summable_two_zpow_neg
    (fun n => (companion_term_diff n).differentiableOn) Metric.isOpen_ball
    companion_bound

/-- **The companion has a Cauchy power series on every disk `r < 1` (PROVEN).**
Hence its radius of convergence is `≥ 1`; with divergence (`U0term_norm_tendsto_atTop`) it is `= 1`. -/
@[aesop safe]
theorem U0sum_hasFPS {r : NNReal} (hr0 : 0 < r) (hr1 : (r:ℝ) < 1) :
    HasFPowerSeriesOnBall U0sum (cauchyPowerSeries U0sum 0 r) 0 r := by
  apply DifferentiableOn.hasFPowerSeriesOnBall _ hr0
  refine U0sum_diff_open.mono (fun w hw => ?_)
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt hw hr1

/-! ### Explicit power-series form of the companion (foundation for Pringsheim)

`U0sum(w) = ∑_k lacCoeff(k)·w^k`, where `lacCoeff` is supported on `k = 2^{n+1}-1` with value
`2^{-(n+1)} > 0` — **nonnegative** coefficients, the hypothesis of Pringsheim's theorem. The reindexing
`lac_reindex` identifies the lacunary tsum with a genuine power series in `w^k`. -/

/-- The lacunary power-series coefficient: `2^{-(n+1)}` at `k = 2^{n+1}-1`, else `0`. -/
noncomputable def lacCoeff (k : ℕ) : ℂ :=
  ∑' n : ℕ, if k = 2 ^ (n + 1) - 1 then (2 : ℂ) ^ (-(n + 1 : ℤ)) else 0

/-- The lacunary exponent map `n ↦ 2^{n+1}-1` is injective. -/
@[aesop safe]
theorem emb_inj : Function.Injective (fun n : ℕ => 2 ^ (n + 1) - 1) := by
  intro a b hab
  simp only at hab
  have ha : (1:ℕ) ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
  have hb : (1:ℕ) ≤ 2 ^ (b + 1) := Nat.one_le_two_pow
  have h2 : (2:ℕ) ^ (a + 1) = 2 ^ (b + 1) := by omega
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

@[aesop safe]
theorem lacCoeff_emb (n : ℕ) : lacCoeff (2 ^ (n + 1) - 1) = (2 : ℂ) ^ (-(n + 1 : ℤ)) := by
  unfold lacCoeff
  rw [tsum_eq_single n]
  · simp
  · intro m hm; rw [if_neg]; intro h; exact hm (emb_inj h.symm)

@[aesop safe]
theorem lacCoeff_zero {k : ℕ} (hk : ∀ n, k ≠ 2 ^ (n + 1) - 1) : lacCoeff k = 0 := by
  unfold lacCoeff
  convert tsum_zero with n
  rw [if_neg (hk n)]

/-- **Reindexing (PROVEN):** the companion equals a genuine power series `∑_k lacCoeff(k)·w^k`. -/
@[aesop safe]
theorem lac_reindex (w : ℂ) :
    ∑' k : ℕ, lacCoeff k * w ^ k = U0sum w := by
  rw [U0sum]
  have hg : Function.support (fun k => lacCoeff k * w ^ k) ⊆
      Set.range (fun n : ℕ => 2 ^ (n + 1) - 1) := by
    intro k hk
    simp only [Function.mem_support] at hk
    by_contra hkr
    exact hk (by rw [lacCoeff_zero (fun n h => hkr ⟨n, h.symm⟩), zero_mul])
  rw [← emb_inj.tsum_eq hg]
  apply tsum_congr
  intro n
  rw [lacCoeff_emb n]
  congr 1
  rw [← zpow_natCast w (2 ^ (n + 1) - 1)]
  congr 1
  have h1 : (1:ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  push_cast [Nat.cast_sub h1]
  ring

/-- The `e_n`-th term of the lacunary power series is exactly `U0term`. -/
@[aesop safe]
theorem lac_term_eq (x : ℂ) (n : ℕ) :
    lacCoeff (2 ^ (n + 1) - 1) * x ^ (2 ^ (n + 1) - 1) = U0term x n := by
  rw [lacCoeff_emb n, U0term]
  congr 1
  rw [← zpow_natCast x (2 ^ (n + 1) - 1)]
  congr 1
  have h1 : (1:ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  push_cast [Nat.cast_sub h1]; ring

/-- **The lacunary power series diverges for `‖x‖ > 1` (PROVEN).** Its `e_n`-subsequence is `U0term x n`,
whose norm `→ ∞` (`U0term_norm_tendsto_atTop`), so the terms do not tend to `0`. This is the endpoint
the Pringsheim contradiction lands on: continuation past `‖·‖=1` would force convergence here. -/
@[aesop safe]
theorem lac_not_summable {x : ℂ} (hx : 1 < ‖x‖) :
    ¬ Summable (fun k => lacCoeff k * x ^ k) := by
  intro hsum
  have hterm0 := hsum.tendsto_atTop_zero
  have hcomp : Tendsto (fun n : ℕ => lacCoeff (2 ^ (n + 1) - 1) * x ^ (2 ^ (n + 1) - 1))
      atTop (nhds 0) := by
    apply hterm0.comp
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    exact ⟨b, fun a ha => le_trans ha (by
      have hlt : a + 1 < 2 ^ (a + 1) := Nat.lt_two_pow_self
      omega)⟩
  simp only [lac_term_eq] at hcomp
  have hnorm := hcomp.norm
  simp only [norm_zero] at hnorm
  exact absurd (U0term_norm_tendsto_atTop hx) (not_tendsto_atTop_of_tendsto_nhds hnorm)

/-- The companion lacunary terms are summable on the open disk (bounded by `2^{-(n+1)}`). -/
@[aesop safe]
theorem companion_summable_disk {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => lacCoeff (2 ^ (n + 1) - 1) * w ^ (2 ^ (n + 1) - 1)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (2:ℝ)^(-(n+1:ℤ))) summable_two_zpow_neg
  intro n
  rw [lac_term_eq, U0term_norm_eq]
  have hwle : ‖w‖ ^ (2 ^ (n + 1) - 1 : ℤ) ≤ 1 := by
    have hexp : (0:ℤ) ≤ 2 ^ (n + 1) - 1 := by
      have : (1:ℤ) ≤ 2 ^ (n+1) := by exact_mod_cast Nat.one_le_two_pow
      linarith
    lift (2 ^ (n + 1) - 1 : ℤ) to ℕ using hexp with m
    rw [zpow_natCast]; exact pow_le_one₀ (norm_nonneg _) (le_of_lt hw)
  have h2 : (0:ℝ) ≤ (2:ℝ)^(-(↑n+1:ℤ)) := zpow_nonneg (by norm_num) _
  nlinarith [mul_le_mul_of_nonneg_left hwle h2]

/-- **The lacunary power series is summable on the open disk (PROVEN).** -/
@[aesop safe]
theorem lac_summable {w : ℂ} (hw : ‖w‖ < 1) : Summable (fun k => lacCoeff k * w ^ k) := by
  have hzero : ∀ k ∉ Set.range (fun n : ℕ => 2 ^ (n + 1) - 1), lacCoeff k * w ^ k = 0 := by
    intro k hk; rw [lacCoeff_zero (fun n h => hk ⟨n, h.symm⟩), zero_mul]
  rw [← Function.Injective.summable_iff emb_inj hzero]
  exact companion_summable_disk hw

/-- **The lacunary power series sums to `U0sum` on the open disk (PROVEN).** -/
@[aesop safe]
theorem lac_hasSum {w : ℂ} (hw : ‖w‖ < 1) : HasSum (fun k => lacCoeff k * w ^ k) (U0sum w) := by
  rw [← lac_reindex w]
  exact (lac_summable hw).hasSum

open FormalMultilinearSeries in
/-- Each coefficient has norm `≤ 1` (`0` or `2^{-j} ≤ 1/2`). -/
@[aesop safe]
theorem lacCoeff_norm_le (n : ℕ) : ‖lacCoeff n‖ ≤ 1 := by
  by_cases h : ∃ m, n = 2 ^ (m + 1) - 1
  · obtain ⟨m, rfl⟩ := h
    rw [lacCoeff_emb m, norm_zpow, Complex.norm_two]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  · rw [lacCoeff_zero (fun m hm => h ⟨m, hm⟩), norm_zero]; norm_num

open FormalMultilinearSeries in
/-- The explicit lacunary series has radius of convergence `≥ 1`. -/
@[aesop safe]
theorem lac_radius_ge_one : (1 : ENNReal) ≤ (ofScalars ℂ lacCoeff).radius := by
  apply le_radius_of_bound _ 1 (r := 1)
  intro n
  rw [ofScalars_norm]
  simp only [NNReal.coe_one, one_pow, mul_one]
  exact lacCoeff_norm_le n

open FormalMultilinearSeries in
/-- **Keystone (PROVEN): `U0sum` IS its explicit lacunary power series on the unit disk.**
Combined with `lac_not_summable` (divergence off the disk), the radius of convergence is exactly `1`.
This is the disk-side power-series object the Pringsheim seed argument runs on. -/
@[aesop safe]
theorem U0sum_hasFPS_explicit :
    HasFPowerSeriesOnBall U0sum (ofScalars ℂ lacCoeff) 0 1 where
  r_le := lac_radius_ge_one
  r_pos := by norm_num
  hasSum := by
    intro y hy
    rw [Metric.mem_eball, edist_zero_right] at hy
    have hy1 : ‖y‖ < 1 := by
      have h := hy
      rw [enorm_eq_nnnorm] at h
      rw [← ENNReal.coe_one, ENNReal.coe_lt_coe] at h
      exact_mod_cast h
    simp only [zero_add]
    have heq : (fun k => (ofScalars ℂ lacCoeff k) (fun _ => y)) = (fun k => lacCoeff k * y ^ k) := by
      funext k; rw [ofScalars_apply_eq]; ring
    rw [heq]; exact lac_hasSum hy1

open FormalMultilinearSeries in
/-- The radius is `≤ 1`: at any real `r > 1` inside a hypothetical larger radius the series would be
summable, contradicting `lac_not_summable`. -/
@[aesop safe]
theorem lac_radius_le_one : (ofScalars ℂ lacCoeff).radius ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨c, h1c, hcr⟩ := exists_between h
  have hcfin : c ≠ ⊤ := ne_top_of_lt hcr
  set r : ℝ := c.toReal with hrdef
  have hr1 : 1 < r := by
    rw [hrdef, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) hcfin).mpr h1c
  have hxnorm : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hx_mem : (r : ℂ) ∈ Metric.eball 0 (ofScalars ℂ lacCoeff).radius := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, hxnorm, hrdef,
      ENNReal.ofReal_toReal hcfin]
    exact hcr
  have hsumn := (ofScalars ℂ lacCoeff).summable_norm_apply hx_mem
  have hsum : Summable (fun n => lacCoeff n * (r:ℂ)^n) := by
    apply Summable.of_norm
    refine hsumn.congr (fun n => ?_)
    rw [ofScalars_apply_eq, smul_eq_mul]
  exact lac_not_summable (by rw [hxnorm]; exact hr1) hsum

open FormalMultilinearSeries in
/-- **The companion power series has radius of convergence exactly `1` (PROVEN).** -/
@[aesop safe]
theorem lac_radius_eq_one : (ofScalars ℂ lacCoeff).radius = 1 :=
  le_antisymm lac_radius_le_one lac_radius_ge_one

open FormalMultilinearSeries in
/-- **Contradiction endpoint of the seed argument (PROVEN).**
If the companion `U0sum` admitted an analytic extension `G` on a disk of radius `R > 1` (agreeing with
`U0sum` near `0`), then `G`'s Cauchy series at `0` equals the companion series (uniqueness of power
series), forcing its radius `≥ R > 1` — contradicting `lac_radius_eq_one`. Thus `U0sum` cannot be
extended to any disk past radius `1`; the only missing step to `seed_singularity` is assembling such a
`G` from the per-boundary-point continuations (the sheaf-gluing). -/
@[aesop safe]
theorem glue_contradiction {G : ℂ → ℂ} {R : NNReal} (hR : 1 < (R:ℝ))
    (hGdiff : DifferentiableOn ℂ G (Metric.closedBall 0 R))
    (hGeq : G =ᶠ[𝓝 0] U0sum) : False := by
  have hRpos : 0 < R := by exact_mod_cast (by linarith : (0:ℝ) < R)
  have hG_fps : HasFPowerSeriesOnBall G (cauchyPowerSeries G 0 R) 0 R :=
    hGdiff.hasFPowerSeriesOnBall hRpos
  have hU_fps : HasFPowerSeriesAt U0sum (ofScalars ℂ lacCoeff) 0 := ⟨1, U0sum_hasFPS_explicit⟩
  have hG_at : HasFPowerSeriesAt G (cauchyPowerSeries G 0 R) 0 := ⟨R, hG_fps⟩
  have hG_at2 : HasFPowerSeriesAt G (ofScalars ℂ lacCoeff) 0 := hU_fps.congr hGeq.symm
  have huniq : cauchyPowerSeries G 0 R = ofScalars ℂ lacCoeff :=
    hG_at.eq_formalMultilinearSeries hG_at2
  have hrad_ge : (R:ENNReal) ≤ (cauchyPowerSeries G 0 R).radius := hG_fps.r_le
  rw [huniq, lac_radius_eq_one] at hrad_ge
  rw [show (1:ENNReal) = ((1:NNReal):ENNReal) from by simp, ENNReal.coe_le_coe] at hrad_ge
  have : (R:ℝ) ≤ 1 := by exact_mod_cast hrad_ge
  linarith

/-- The companion series equals `u₀ ∘ (·⁻¹)` as tsums: `(w⁻¹)^{-(2^{n+1}-1)} = w^{2^{n+1}-1}`.
Pure algebra; underlies the `w ↦ 1/w` bridge between the u₀-side and U₀-side boundary statements. -/
@[aesop safe]
theorem u0_inv_eq_companion (w : ℂ) :
    u0 w⁻¹ = ∑' n : ℕ, (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ) := by
  simp only [u0]; congr 1; ext n; congr 1
  rw [inv_zpow, zpow_neg, inv_inv]

/-- `U0sum` continues analytically across `w₀` from the open unit disk. -/
def ContinuesAcrossDisk (w₀ : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g w₀ ∧ ∀ᶠ w in nhdsWithin w₀ (Metric.ball 0 1), g w = U0sum w

/-- **Local identity theorem (PROVEN):** two germs analytic at `w₀` that agree frequently near `w₀`
agree on a neighborhood. (Restriction to a common ball + `eqOn_of_preconnected_of_frequently_eq`.) -/
@[aesop safe]
theorem continuation_unique {w₀ : ℂ} {g h : ℂ → ℂ} (hg : AnalyticAt ℂ g w₀) (hh : AnalyticAt ℂ h w₀)
    (hfreq : ∃ᶠ w in 𝓝[≠] w₀, g w = h w) : g =ᶠ[𝓝 w₀] h := by
  obtain ⟨rg, hrg, hgB⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨rh, hrh, hhB⟩ := hh.exists_ball_analyticOnNhd
  have hrpos : 0 < min rg rh := lt_min hrg hrh
  have hgB' : AnalyticOnNhd ℂ g (Metric.ball w₀ (min rg rh)) :=
    hgB.mono (Metric.ball_subset_ball (min_le_left _ _))
  have hhB' : AnalyticOnNhd ℂ h (Metric.ball w₀ (min rg rh)) :=
    hhB.mono (Metric.ball_subset_ball (min_le_right _ _))
  have hw₀B : w₀ ∈ Metric.ball w₀ (min rg rh) := Metric.mem_ball_self hrpos
  exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hw₀B)
    (hgB'.eqOn_of_preconnected_of_frequently_eq hhB'
      (convex_ball w₀ (min rg rh)).isPreconnected hw₀B hfreq)

/-- Two disk-side continuations across a boundary point `w₀` (`‖w₀‖=1`) agree on a neighborhood:
both equal `U0sum` on the disk-side, which is a `NeBot` filter `≤ 𝓝[≠] w₀`. -/
@[aesop safe]
theorem continuation_unique_disk {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1) {g h : ℂ → ℂ}
    (hg : AnalyticAt ℂ g w₀) (hh : AnalyticAt ℂ h w₀)
    (hge : ∀ᶠ w in 𝓝[Metric.ball 0 1] w₀, g w = U0sum w)
    (hhe : ∀ᶠ w in 𝓝[Metric.ball 0 1] w₀, h w = U0sum w) : g =ᶠ[𝓝 w₀] h := by
  apply continuation_unique hg hh
  have hsub : 𝓝[Metric.ball 0 1] w₀ ≤ 𝓝[{w₀}ᶜ] w₀ := by
    apply nhdsWithin_mono
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    rw [Metric.mem_ball, dist_zero_right, hw₀] at hw
    exact lt_irrefl 1 hw
  have hne : (𝓝[Metric.ball 0 1] w₀).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_ball 0 (one_ne_zero), Metric.mem_closedBall, dist_zero_right, hw₀]
  have heq : ∀ᶠ w in 𝓝[Metric.ball 0 1] w₀, g w = h w := by
    filter_upwards [hge, hhe] with w h1 h2; rw [h1, h2]
  exact (heq.frequently).filter_mono hsub

/-- **Inversion transfer (PROVEN):** if `u₀` continues across `z₀` from the exterior, then the
companion `U0sum` continues across `z₀⁻¹` from the disk (via the biholomorphism `w ↦ 1/w` and
`u0_inv_eq_companion`). This carries the `¬seed` hypothesis to the disk side where the radius
machinery lives. -/
@[aesop safe]
theorem continuesDisk_of_continuesExt {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1)
    (h : ContinuesAcross u0 Ext z₀) : ContinuesAcrossDisk z₀⁻¹ := by
  obtain ⟨g, hg_an, hg_eq⟩ := h
  have hz₀_ne : z₀ ≠ 0 := by intro hh; rw [hh] at hz₀; simp at hz₀
  set w₀ := z₀⁻¹ with hw₀
  have hw₀_ne : w₀ ≠ 0 := inv_ne_zero hz₀_ne
  have hw₀_inv : w₀⁻¹ = z₀ := inv_inv z₀
  refine ⟨fun w => g w⁻¹, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ g (w₀⁻¹) := by rw [hw₀_inv]; exact hg_an
    exact h1.comp (analyticAt_inv hw₀_ne)
  · have htends : Tendsto (fun w : ℂ => w⁻¹) (𝓝[Metric.ball 0 1] w₀) (𝓝[Ext] z₀) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Tendsto (fun w : ℂ => w⁻¹) (𝓝 w₀) (𝓝 z₀) := by
          have := continuousAt_inv₀ hw₀_ne; rw [ContinuousAt, hw₀_inv] at this; exact this
        exact hc.mono_left nhdsWithin_le_nhds
      · have hball : ∀ᶠ w in 𝓝[Metric.ball 0 1] w₀, w ∈ Metric.ball 0 1 := self_mem_nhdsWithin
        have hne : ∀ᶠ w in 𝓝[Metric.ball 0 1] w₀, w ≠ 0 :=
          (eventually_ne_nhds hw₀_ne).filter_mono nhdsWithin_le_nhds
        filter_upwards [hball, hne] with w hw hwne
        rw [Metric.mem_ball, dist_zero_right] at hw
        show 1 < ‖w⁻¹‖
        rw [norm_inv, lt_inv_comm₀ (by positivity) (by rwa [norm_pos_iff])]
        simpa using hw
    filter_upwards [htends.eventually hg_eq] with w hw
    rw [hw, U0sum]
    exact u0_inv_eq_companion w

/-- Extract a metric ball on which the continuation is analytic and matches `U0sum` on the disk-side. -/
@[aesop safe]
theorem continuesDisk_ball {w₀ : ℂ} (h : ContinuesAcrossDisk w₀) :
    ∃ ρ > 0, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball w₀ ρ) ∧
      ∀ w ∈ Metric.ball w₀ ρ ∩ Metric.ball 0 1, g w = U0sum w := by
  obtain ⟨g, hg_an, hg_eq⟩ := h
  obtain ⟨ρ₁, hρ₁, hgB⟩ := hg_an.exists_ball_analyticOnNhd
  rw [eventually_nhdsWithin_iff] at hg_eq
  obtain ⟨W, hWsub, hWopen, hw₀W⟩ := _root_.mem_nhds_iff.mp hg_eq
  obtain ⟨ρ₂, hρ₂, hball2⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds hw₀W)
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, g, hgB.mono (Metric.ball_subset_ball (min_le_left _ _)), ?_⟩
  rintro w ⟨hw1, hw2⟩
  exact hWsub (hball2 (Metric.ball_subset_ball (min_le_right _ _) hw1)) hw2

/-- **Uniform-radius continuation cover (PROVEN).** If `U0sum` continues across *every* unit-circle
point, the Lebesgue number lemma gives a single `δ > 0` such that across every boundary point `x`
there is a continuation analytic on `ball x δ` agreeing with `U0sum` on the disk-side. The uniform
radius is what makes the overlaps' chord-midpoints land inside the disk, so the per-ball continuations
are forced to agree (`continuation_unique`) — the key to gluing them into one function. -/
@[aesop safe]
theorem uniform_continuation_cover (hcont : ∀ w₀ : ℂ, ‖w₀‖ = 1 → ContinuesAcrossDisk w₀) :
    ∃ δ > 0, ∀ x : ℂ, ‖x‖ = 1 → ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball x δ) ∧
      ∀ w ∈ Metric.ball x δ ∩ Metric.ball 0 1, g w = U0sum w := by
  classical
  set ρf : {w₀ : ℂ // ‖w₀‖ = 1} → ℝ := fun s => (continuesDisk_ball (hcont s.1 s.2)).choose
  have hρpos : ∀ s, 0 < ρf s := fun s => (continuesDisk_ball (hcont s.1 s.2)).choose_spec.1
  have hcover : Metric.sphere (0:ℂ) 1 ⊆ ⋃ s, Metric.ball s.1 (ρf s) := by
    intro x hx
    rw [mem_sphere_zero_iff_norm] at hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hρpos ⟨x, hx⟩)⟩
  obtain ⟨δ, hδ, hδspec⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_sphere 0 1) (fun _ => Metric.isOpen_ball) hcover
  refine ⟨δ, hδ, fun x hx => ?_⟩
  obtain ⟨s, hs⟩ := hδspec x (mem_sphere_zero_iff_norm.mpr hx)
  obtain ⟨g, hgan, hgeq⟩ := (continuesDisk_ball (hcont s.1 s.2)).choose_spec.2
  exact ⟨g, hgan.mono hs, fun w hw => hgeq w ⟨hs hw.1, hw.2⟩⟩

/-- Uniform-radius disk continuations obtained directly from exterior continuations of `u₀`. -/
@[aesop safe]
theorem uniform_continuation_cover_of_continuesExt
    (hcont : ∀ z₀ : ℂ, ‖z₀‖ = 1 → ContinuesAcross u0 Ext z₀) :
    ∃ δ > 0, ∀ x : ℂ, ‖x‖ = 1 → ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball x δ) ∧
      ∀ w ∈ Metric.ball x δ ∩ Metric.ball 0 1, g w = U0sum w := by
  refine uniform_continuation_cover ?_
  intro w₀ hw₀
  have hinv : ‖w₀⁻¹‖ = 1 := by rw [norm_inv, hw₀, inv_one]
  have := continuesDisk_of_continuesExt hinv (hcont w₀⁻¹ hinv)
  rwa [inv_inv] at this

/-- **Overlap consistency (PROVEN).** Two equal-radius continuations centered at unit-circle points
`x, y` agree at any common point `w`: their chord-midpoint `(x+y)/2` lies strictly inside the disk
(strict convexity) and inside both balls, where both equal `U0sum`; the identity theorem on the convex
overlap then forces agreement. This makes the per-ball continuations glue into a single function. -/
@[aesop safe]
theorem overlap_consistency {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {δ : ℝ} {gx gy : ℂ → ℂ}
    (hgxan : AnalyticOnNhd ℂ gx (Metric.ball x δ)) (hgyan : AnalyticOnNhd ℂ gy (Metric.ball y δ))
    (hgxeq : ∀ w ∈ Metric.ball x δ ∩ Metric.ball 0 1, gx w = U0sum w)
    (hgyeq : ∀ w ∈ Metric.ball y δ ∩ Metric.ball 0 1, gy w = U0sum w)
    {w : ℂ} (hwx : w ∈ Metric.ball x δ) (hwy : w ∈ Metric.ball y δ) : gx w = gy w := by
  have hδ : 0 < δ := Metric.pos_of_mem_ball hwx
  obtain ⟨m, hmx, hmy, hm_disk⟩ :
      ∃ m, m ∈ Metric.ball x δ ∧ m ∈ Metric.ball y δ ∧ m ∈ Metric.ball 0 1 := by
    by_cases hxy : x = y
    · subst hxy
      set t := min δ 1 / 2 with ht
      have ht0 : 0 < t := by positivity
      have htδ : t < δ := by rw [ht]; have := min_le_left δ (1:ℝ); linarith
      have ht1 : t < 1 := by rw [ht]; have := min_le_right δ (1:ℝ); linarith
      refine ⟨((1 - t : ℝ) : ℂ) * x, ?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, show ((1-t:ℝ):ℂ)*x - x = ((-t:ℝ):ℂ)*x by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, hx, mul_one, abs_neg, abs_of_pos ht0]
        exact htδ
      · rw [Metric.mem_ball, dist_eq_norm, show ((1-t:ℝ):ℂ)*x - x = ((-t:ℝ):ℂ)*x by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, hx, mul_one, abs_neg, abs_of_pos ht0]
        exact htδ
      · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, hx,
          mul_one, abs_of_pos (by linarith)]
        linarith
    · set m := (x + y) / 2 with hm
      have hxy_dist : ‖x - y‖ < 2 * δ := by
        calc ‖x - y‖ ≤ ‖x - w‖ + ‖w - y‖ := norm_sub_le_norm_sub_add_norm_sub x w y
          _ < δ + δ := by
              have h1 : ‖w - x‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hwx
              have h2 : ‖w - y‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hwy
              rw [norm_sub_rev x w]; linarith
          _ = 2 * δ := by ring
      refine ⟨m, ?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, show m - x = (y - x)/2 from by rw [hm]; ring, norm_div]
        simp only [Complex.norm_ofNat]; rw [norm_sub_rev y x]; linarith
      · rw [Metric.mem_ball, dist_eq_norm, show m - y = (x - y)/2 from by rw [hm]; ring, norm_div]
        simp only [Complex.norm_ofNat]; linarith
      · rw [Metric.mem_ball, dist_zero_right, hm]
        have hns : ¬ SameRay ℝ x y := fun h => hxy (h.eq_of_norm_eq (by rw [hx, hy]))
        have hlt := norm_add_lt_of_not_sameRay hns
        rw [hx, hy] at hlt
        rw [norm_div]; simp only [Complex.norm_ofNat]; linarith
  have hgx_m : gx =ᶠ[𝓝 m] U0sum :=
    eventually_of_mem ((Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds ⟨hmx, hm_disk⟩) hgxeq
  have hgy_m : gy =ᶠ[𝓝 m] U0sum :=
    eventually_of_mem ((Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds ⟨hmy, hm_disk⟩) hgyeq
  have heqOn : Set.EqOn gx gy (Metric.ball x δ ∩ Metric.ball y δ) :=
    (hgxan.mono Set.inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      (hgyan.mono Set.inter_subset_right)
      ((convex_ball x δ).inter (convex_ball y δ)).isPreconnected ⟨hmx, hmy⟩ (hgx_m.trans hgy_m.symm)
  exact heqOn ⟨hwx, hwy⟩

/-- The radial projection `w ↦ w/‖w‖` lands on the unit sphere (for `‖w‖ ≥ 1`). -/
@[aesop safe]
theorem radial_norm {w : ℂ} (hw : 1 ≤ ‖w‖) : ‖w / (‖w‖ : ℂ)‖ = 1 := by
  have hne : ‖w‖ ≠ 0 := by intro h; rw [h] at hw; linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w), div_self hne]

/-- Distance from `w` to its radial projection is `‖w‖ − 1`. -/
@[aesop safe]
theorem radial_dist {w : ℂ} (hw : 1 ≤ ‖w‖) : ‖w - w / (‖w‖ : ℂ)‖ = ‖w‖ - 1 := by
  have hwne : (‖w‖ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; intro h; rw [h] at hw; linarith
  have hcast : (((‖w‖ - 1:ℝ)):ℂ) = (‖w‖:ℂ) - 1 := by push_cast; ring
  have key : w - w / (‖w‖:ℂ) = w / (‖w‖:ℂ) * (((‖w‖ - 1 : ℝ)) : ℂ) := by rw [hcast]; field_simp
  rw [key, norm_mul, radial_norm hw, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

/-- **Seed singularity (step 2 — PROVEN).**
`u₀` fails to continue across **some** unit-circle point.

Proof (by contradiction): if `u₀` continued across *every* boundary point, the inversion transfer
(`continuesDisk_of_continuesExt`) gives a disk-side continuation of `U0sum` at every boundary point;
the uniform-radius cover (`uniform_continuation_cover`, Lebesgue number) and overlap consistency
(`overlap_consistency`, via chord-midpoints + identity theorem) glue them — together with `U0sum` on the
disk — into a single function `G` analytic on a disk of radius `1+δ/2 > 1` (built here via the radial
projection `w ↦ w/‖w‖` and `differentiableOn_of_locally_differentiableOn`). That contradicts
`glue_contradiction` (no such `G` exists, since `U0sum`'s series has radius exactly `1`). ∎

This realises the natural boundary with *no* appeal to the Ostrowski–Hadamard gap theorem — only the
Mahler-equation propagation, the doubly-exponential divergence, and this gluing. -/
@[aesop safe]
theorem seed_singularity : ∃ z₁ : ℂ, ‖z₁‖ = 1 ∧ ¬ ContinuesAcross u0 Ext z₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδ, hcov⟩ := uniform_continuation_cover_of_continuesExt hcon
  classical
  set gext : ℂ → (ℂ → ℂ) := fun x => if h : ‖x‖ = 1 then (hcov x h).choose else 0 with hgext
  have hgext_an : ∀ x, ‖x‖ = 1 → AnalyticOnNhd ℂ (gext x) (Metric.ball x δ) := by
    intro x hx; rw [hgext]; simp only [hx, dif_pos]; exact (hcov x hx).choose_spec.1
  have hgext_eq : ∀ x, ‖x‖ = 1 → ∀ w ∈ Metric.ball x δ ∩ Metric.ball 0 1, gext x w = U0sum w := by
    intro x hx; rw [hgext]; simp only [hx, dif_pos]; exact (hcov x hx).choose_spec.2
  set G : ℂ → ℂ := fun w => if ‖w‖ < 1 then U0sum w else gext (w / (‖w‖:ℂ)) w with hG
  set R : NNReal := ⟨1 + δ/2, by positivity⟩ with hR
  have hRcoe : (R:ℝ) = 1 + δ/2 := rfl
  have hR1 : 1 < (R:ℝ) := by rw [hRcoe]; linarith
  have hGeq0 : G =ᶠ[𝓝 0] U0sum := by
    apply eventually_of_mem (Metric.isOpen_ball.mem_nhds (by simp : (0:ℂ) ∈ Metric.ball 0 1))
    intro w hw; simp only [hG, Metric.mem_ball, dist_zero_right] at hw ⊢; rw [if_pos hw]
  have hGdiff : DifferentiableOn ℂ G (Metric.closedBall 0 R) := by
    apply differentiableOn_of_locally_differentiableOn
    intro w hw
    by_cases hw1 : ‖w‖ < 1
    · refine ⟨Metric.ball 0 1, Metric.isOpen_ball, by simpa using hw1, ?_⟩
      apply (U0sum_diff_open.mono Set.inter_subset_right).congr
      intro w' hw'
      have hlt : ‖w'‖ < 1 := by simpa using hw'.2
      simp only [hG]; rw [if_pos hlt]
    · push Not at hw1
      set x₀ := w / (‖w‖:ℂ) with hx₀
      have hx₀norm : ‖x₀‖ = 1 := radial_norm hw1
      refine ⟨Metric.ball x₀ δ, Metric.isOpen_ball, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, hx₀, radial_dist hw1]
        have hle : ‖w‖ ≤ (R:ℝ) := by simpa using hw
        rw [hRcoe] at hle; linarith
      · apply ((hgext_an x₀ hx₀norm).mono Set.inter_subset_right).differentiableOn.congr
        intro w' hw'
        have hw'x : w' ∈ Metric.ball x₀ δ := hw'.2
        simp only [hG]
        by_cases hw'1 : ‖w'‖ < 1
        · rw [if_pos hw'1]
          exact (hgext_eq x₀ hx₀norm w' ⟨hw'x, by simpa using hw'1⟩).symm
        · rw [if_neg hw'1]
          push Not at hw'1
          set x' := w' / (‖w'‖:ℂ) with hx'
          have hx'norm : ‖x'‖ = 1 := radial_norm hw'1
          have hw'R : ‖w'‖ ≤ (R:ℝ) := by
            have := hw'.1; simp only [Metric.mem_closedBall, dist_zero_right] at this; exact this
          have hw'inx' : w' ∈ Metric.ball x' δ := by
            rw [Metric.mem_ball, dist_eq_norm, hx', radial_dist hw'1]
            rw [hRcoe] at hw'R; linarith
          exact overlap_consistency hx'norm hx₀norm (hgext_an x' hx'norm) (hgext_an x₀ hx₀norm)
            (hgext_eq x' hx'norm) (hgext_eq x₀ hx₀norm) hw'inx' hw'x
  exact glue_contradiction hR1 hGdiff hGeq0

/-- Lipschitz-type bound on the imaginary axis: `‖exp(aI) − exp(bI)‖ ≤ 2·|a−b|` for `|a−b| ≤ 1`.
(`exp(aI) − exp(bI) = exp(bI)·(exp((a−b)I) − 1)` and `‖exp(x) − 1‖ ≤ 2‖x‖` for `‖x‖ ≤ 1`.) -/
@[aesop safe]
private theorem norm_exp_imI_sub (a b : ℝ) (h : |a - b| ≤ 1) :
    ‖Complex.exp (a * I) - Complex.exp (b * I)‖ ≤ 2 * |a - b| := by
  have factor : Complex.exp (a * I) - Complex.exp (b * I)
      = Complex.exp (b * I) * (Complex.exp (((a - b : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [factor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnorm : ‖((a - b : ℝ) : ℂ) * I‖ = |a - b| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hkey := norm_exp_sub_one_le (x := ((a - b : ℝ) : ℂ) * I) (by rw [hnorm]; exact h)
  rwa [hnorm] at hkey

/-- **Density of dyadic roots (step 4, PROVEN).** The `2ⁿ`-th roots of a unit-circle point `z₁` are
dense in the unit circle. For target `w = exp(α I)` and tolerance `ε`, pick `n` with `2π/2ⁿ < ε` and
`k = round((2ⁿα − arg z₁)/2π)`; then `exp(((arg z₁)+2πk)/2ⁿ · I)` is a `2ⁿ`-th root of `z₁` within
`2π/2ⁿ` of `w` (argument error `≤ π/2ⁿ`, exp Lipschitz). -/
@[aesop safe]
theorem dense_dyadic_roots (z₁ : ℂ) (hz₁ : ‖z₁‖ = 1) :
    Metric.sphere (0 : ℂ) 1 ⊆ closure {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = z₁} := by
  intro w hw
  rw [mem_sphere_zero_iff_norm] at hw
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (max (2 * Real.pi / ε) (2 * Real.pi)) (by norm_num : (1:ℝ) < 2)
  have h2n_pos : (0:ℝ) < 2 ^ n := by positivity
  set θ₁ := z₁.arg
  set α := w.arg
  set t : ℝ := (2 ^ n * α - θ₁) / (2 * Real.pi) with ht
  set k : ℤ := round t with hk
  set β : ℝ := (θ₁ + 2 * Real.pi * k) / 2 ^ n with hβ
  have hz₁eq : Complex.exp ((θ₁:ℂ) * I) = z₁ := by
    simpa [hz₁] using norm_mul_exp_arg_mul_I z₁
  have hweq : w = Complex.exp ((α:ℂ) * I) := by
    have := norm_mul_exp_arg_mul_I w; rw [hw] at this; simpa using this.symm
  refine ⟨Complex.exp ((β:ℂ) * I), ?_, ?_⟩
  · refine ⟨n, ?_⟩
    rw [← Complex.exp_nat_mul]
    have hβ2 : (2 ^ n : ℕ) * ((β:ℂ) * I) = ((θ₁ : ℂ) + 2 * Real.pi * (k:ℂ)) * I := by
      push_cast [hβ]; field_simp
    rw [hβ2, show ((θ₁ : ℂ) + 2 * Real.pi * (k:ℂ)) * I = (θ₁:ℂ) * I + (k : ℂ) * (2 * Real.pi * I)
        by ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hz₁eq]
  · rw [dist_eq_norm, hweq]
    have habs : |α - β| ≤ Real.pi / 2 ^ n := by
      have hαβ : α - β = (2 * Real.pi / 2 ^ n) * (t - k) := by rw [hβ, ht]; field_simp; ring
      rw [hαβ, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi / 2 ^ n)]
      calc 2 * Real.pi / 2 ^ n * |t - (k:ℝ)|
          ≤ 2 * Real.pi / 2 ^ n * (1/2) :=
            mul_le_mul_of_nonneg_left (by rw [hk]; exact abs_sub_round t) (by positivity)
        _ = Real.pi / 2 ^ n := by ring
    have hpi_le : Real.pi / 2 ^ n ≤ 1 := by
      rw [div_le_one h2n_pos]
      have h2 : 2 * Real.pi ≤ 2 ^ n := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
      linarith [Real.pi_pos]
    have hle1 : |α - β| ≤ 1 := le_trans habs hpi_le
    have hbound := norm_exp_imI_sub α β hle1
    have hπ : 2 * (Real.pi / 2 ^ n) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ h2n_pos]
      have h2πε : 2 * Real.pi / ε < 2 ^ n := lt_of_le_of_lt (le_max_left _ _) hn
      rw [div_lt_iff₀ hε, mul_comm] at h2πε
      linarith [h2πε]
    have hfin : 2 * |α - β| < ε := by
      calc 2 * |α - β| ≤ 2 * (Real.pi / 2 ^ n) := by linarith [habs]
        _ < ε := hπ
    linarith [hbound]

/-- **Natural boundary of u₀ — ASSEMBLED from the two leaf inputs (genuine form).**

`u₀` (analytic on the exterior `Ext`) continues across **no** point of the unit circle. This — not the
junk `¬AnalyticAt` form — is the real content equivalent to "u₀ transcendental over ℂ(z)".

**This theorem is fully proven modulo the two named leaf sorries** `seed_singularity` (step 2, the
genuine analytic core) and `dense_dyadic_roots` (step 4, elementary). The connective tissue —
propagation (`continues_sq`, step 3), the root induction, closedness (`isClosed_singular`, step 5),
and the closed-⊇-dense closure — is all proven here.

**Proof blueprint — softer than the generic Ostrowski–Hadamard gap theorem because it uses the Mahler
functional equation `(2/w)·U₀(w) = 1 + U₀(w²)` that this specific series satisfies:**

1. *Radius of convergence exactly 1.* `U0_summable_lt_one` + `U0term_norm_tendsto_atTop`. [PROVEN]
2. *Seed singularity.* `seed_singularity`. [leaf sorry — the genuine analytic core]
3. *Propagation.* `continues_sq` / `not_continues_of_sq`. [PROVEN]
4. *Density.* `dense_dyadic_roots`. [PROVEN]
5. *Close up.* `isClosed_singular` + `closure_minimal`. [PROVEN]

So on the analytic side the three-card independence result reduces to step 2 alone (step 4 being
routine). -/
@[aesop safe]
theorem u0_natural_boundary :
    ∀ z₀ : ℂ, ‖z₀‖ = 1 → ¬ ContinuesAcross u0 Ext z₀ := by
  obtain ⟨z₁, hz₁norm, hz₁sing⟩ := seed_singularity
  -- every 2ⁿ-th root of the seed is singular (induction via `not_continues_of_sq`)
  have hroots : ∀ (n : ℕ) (z : ℂ), z ^ (2 ^ n) = z₁ → ¬ ContinuesAcross u0 Ext z := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simp only [pow_zero, pow_one] at hz
      rw [hz]; exact hz₁sing
    | succ m ih =>
      intro z hz
      have hexp : 2 ^ (m + 1) ≠ 0 := by positivity
      have hznorm : ‖z‖ = 1 := by
        have h1 : ‖z‖ ^ (2 ^ (m + 1)) = 1 := by rw [← norm_pow, hz, hz₁norm]
        rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
        · exact absurd h1 (by have := pow_lt_one₀ (norm_nonneg z) hlt hexp; linarith)
        · exact heq
        · exact absurd h1 (by have := one_lt_pow₀ hgt hexp; linarith)
      have hz0 : z ≠ 0 := by intro h; rw [h] at hznorm; simp at hznorm
      apply not_continues_of_sq hz0
      apply ih (z ^ 2)
      rw [← pow_mul, show 2 * 2 ^ m = 2 ^ (m + 1) from by rw [pow_succ]; ring]
      exact hz
  have hRootsSub : {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = z₁} ⊆
      {z : ℂ | ¬ ContinuesAcross u0 Ext z} := by
    rintro z ⟨n, hn⟩; exact hroots n z hn
  -- the seed's roots are dense in the circle; the singular set is closed ⊇ them ⟹ ⊇ circle
  intro z₀ hz₀
  have hz₀sphere : z₀ ∈ Metric.sphere (0 : ℂ) 1 := by rwa [mem_sphere_zero_iff_norm]
  exact (closure_minimal hRootsSub isClosed_singular)
    (dense_dyadic_roots z₁ hz₁norm hz₀sphere)

end U0NaturalBoundary
