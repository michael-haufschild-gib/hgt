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

/-! ## The complementary series and the two representations -/

namespace RHTower

open SchwartzMap

open scoped ContDiff

noncomputable section

/-- The uniform geometric majorant of the backward lattice series on a half line. -/
theorem deningerGreenTermNeg_bound {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (n : ℕ)
    {L : ℝ} (_hL : 0 < L) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (t : ℝ), t < T →
      ‖iteratedDeriv n (f : ℝ → ℂ) (t - ((j : ℝ) + 1) * L)‖ ≤ C * (Real.exp (-L)) ^ j := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_iteratedDeriv_norm_le hf 1 n
  refine ⟨C * Real.exp (T - L), by positivity, fun j t ht => ?_⟩
  refine le_trans (hC (t - ((j : ℝ) + 1) * L)) ?_
  have habs : -(t - ((j : ℝ) + 1) * L) ≤ |t - ((j : ℝ) + 1) * L| := neg_le_abs _
  have hle : -(1 * |t - ((j : ℝ) + 1) * L|) ≤ T - L + -((j : ℝ) * L) := by
    rw [one_mul]
    nlinarith [habs, ht]
  have hpow : (Real.exp (-L)) ^ j = Real.exp (-((j : ℝ) * L)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc C * Real.exp (-(1 * |t - ((j : ℝ) + 1) * L|))
      ≤ C * Real.exp (T - L + -((j : ℝ) * L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hCnn
    _ = C * Real.exp (T - L) * (Real.exp (-L)) ^ j := by
        rw [Real.exp_add, hpow]
        ring

theorem deningerGreenSeriesNeg_summable {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (n : ℕ)
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    Summable fun j : ℕ => iteratedDeriv n (f : ℝ → ℂ) (t - ((j : ℝ) + 1) * L) := by
  obtain ⟨C, hCnn, hC⟩ := deningerGreenTermNeg_bound hf n hL (t + 1)
  have hq : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hmaj : Summable fun j : ℕ => C * (Real.exp (-L)) ^ j :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left C
  exact Summable.of_norm_bounded hmaj fun j => hC j t (by linarith)

theorem deningerGreenTermNeg_hasDerivAt (f : 𝓢(ℝ, ℂ)) (L : ℝ) (n j : ℕ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => iteratedDeriv n (f : ℝ → ℂ) (y - ((j : ℝ) + 1) * L))
      (iteratedDeriv (n + 1) (f : ℝ → ℂ) (t - ((j : ℝ) + 1) * L)) t := by
  have hsm : ContDiff ℝ ∞ (iteratedDeriv n (f : ℝ → ℂ)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (f.smooth').iterate_deriv n
  have hdiff : DifferentiableAt ℝ (iteratedDeriv n (f : ℝ → ℂ)) (t - ((j : ℝ) + 1) * L) :=
    (hsm.differentiable (by simp)).differentiableAt
  have hbase : HasDerivAt (iteratedDeriv n (f : ℝ → ℂ))
      (deriv (iteratedDeriv n (f : ℝ → ℂ)) (t - ((j : ℝ) + 1) * L))
      (t - ((j : ℝ) + 1) * L) := hdiff.hasDerivAt
  have hcomp := hbase.comp_add_const t (-(((j : ℝ) + 1) * L))
  have hsucc : deriv (iteratedDeriv n (f : ℝ → ℂ)) = iteratedDeriv (n + 1) (f : ℝ → ℂ) :=
    (iteratedDeriv_succ (n := n) (f := (f : ℝ → ℂ))).symm
  rw [hsucc] at hcomp
  exact hcomp

theorem deningerGreenSeriesNeg_hasDerivAt {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (n : ℕ)
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasDerivAt (deningerGreenSeriesNeg f L n) (deningerGreenSeriesNeg f L (n + 1) t) t := by
  obtain ⟨C, hCnn, hC⟩ := deningerGreenTermNeg_bound hf (n + 1) hL (t + 1)
  have hq : Real.exp (-L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hmaj : Summable fun j : ℕ => C * (Real.exp (-L)) ^ j :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left C
  have hopen : IsOpen (Set.Iio (t + 1)) := isOpen_Iio
  have hconn : IsPreconnected (Set.Iio (t + 1)) := (convex_Iio (t + 1)).isPreconnected
  have hmem : t ∈ Set.Iio (t + 1) := by
    simp only [Set.mem_Iio]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected hmaj hopen hconn
    (fun j y _ => deningerGreenTermNeg_hasDerivAt f L n j y)
    (fun j y hy => hC j y hy) hmem
    (deningerGreenSeriesNeg_summable hf n hL t) hmem

/-- **The two representations `(7)` agree exactly when the periodization vanishes**, at every
derivative order. -/
theorem deningerGreenSeries_eq_neg {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (hper : ∀ t : ℝ, deningerPeriodizationSum f L t = 0) (n : ℕ) (t : ℝ) :
    deningerGreenSeries f L n t = -deningerGreenSeriesNeg f L n t := by
  induction n generalizing t with
  | zero =>
    have h1 : Summable fun j : ℕ =>
        (f : ℝ → ℂ) (t + ((j : ℤ) : ℝ) * L) := by
      refine (deningerShiftNat_summable hf hL t).congr fun j => ?_
      have harg : t + (j : ℝ) * L = t + ((j : ℤ) : ℝ) * L := by
        push_cast
        ring
      exact congrArg (fun y : ℝ => (f : ℝ → ℂ) y) harg
    have h2 : Summable fun j : ℕ =>
        (f : ℝ → ℂ) (t + ((-((j : ℤ) + 1) : ℤ) : ℝ) * L) := by
      refine (deningerGreenSeriesNeg_summable hf 0 hL t).congr fun j => ?_
      have harg : t - ((j : ℝ) + 1) * L = t + ((-((j : ℤ) + 1) : ℤ) : ℝ) * L := by
        push_cast
        ring
      rw [iteratedDeriv_zero]
      exact congrArg (fun y : ℝ => (f : ℝ → ℂ) y) harg
    have hsplit := tsum_of_nat_of_neg_add_one
      (f := fun j : ℤ => (f : ℝ → ℂ) (t + (j : ℝ) * L)) h1 h2
    have hbase : deningerPeriodizationSum f L t
        = deningerGreenSeries f L 0 t + deningerGreenSeriesNeg f L 0 t := by
      have e1 : (∑' j : ℕ, (f : ℝ → ℂ) (t + ((j : ℤ) : ℝ) * L))
          = ∑' j : ℕ, iteratedDeriv 0 (f : ℝ → ℂ) (t + (j : ℝ) * L) := by
        refine tsum_congr fun j => ?_
        rw [iteratedDeriv_zero]
        exact congrArg (fun y : ℝ => (f : ℝ → ℂ) y) (by push_cast; ring)
      have e2 : (∑' j : ℕ, (f : ℝ → ℂ) (t + ((-((j : ℤ) + 1) : ℤ) : ℝ) * L))
          = ∑' j : ℕ, iteratedDeriv 0 (f : ℝ → ℂ) (t - ((j : ℝ) + 1) * L) := by
        refine tsum_congr fun j => ?_
        rw [iteratedDeriv_zero]
        exact congrArg (fun y : ℝ => (f : ℝ → ℂ) y) (by push_cast; ring)
      rw [deningerPeriodizationSum, hsplit, deningerGreenSeries, deningerGreenSeriesNeg, e1, e2]
    have hz := hper t
    rw [hbase] at hz
    exact eq_neg_of_add_eq_zero_left hz
  | succ n ih =>
    have hfun : deningerGreenSeries f L n = fun y => -deningerGreenSeriesNeg f L n y :=
      funext fun y => ih y
    have h1 : HasDerivAt (deningerGreenSeries f L n) (deningerGreenSeries f L (n + 1) t) t :=
      deningerGreenSeries_hasDerivAt hf n hL t
    have h2 : HasDerivAt (fun y => -deningerGreenSeriesNeg f L n y)
        (-deningerGreenSeriesNeg f L (n + 1) t) t :=
      (deningerGreenSeriesNeg_hasDerivAt hf n hL t).neg
    rw [hfun] at h1
    exact h1.unique h2

end

end RHTower

/-! ## Smoothness and the seminorm bound `(8)` -/

namespace RHTower

open SchwartzMap

open scoped ContDiff

noncomputable section

theorem deningerGreenSeries_deriv {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (n : ℕ) :
    deriv (deningerGreenSeries f L n) = deningerGreenSeries f L (n + 1) :=
  funext fun t => (deningerGreenSeries_hasDerivAt hf n hL t).deriv

theorem deningerGreenSeries_contDiff_nat {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) : ∀ (m n : ℕ), ContDiff ℝ m (deningerGreenSeries f L n) := by
  intro m
  induction m with
  | zero =>
    intro n
    have hd : Differentiable ℝ (deningerGreenSeries f L n) := fun t =>
      (deningerGreenSeries_hasDerivAt hf n hL t).differentiableAt
    have h : ContDiff ℝ 0 (deningerGreenSeries f L n) := contDiff_zero.mpr hd.continuous
    simpa using h
  | succ m ih =>
    intro n
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by
      push_cast
      ring
    rw [hcast]
    refine contDiff_succ_iff_deriv.mpr
      ⟨fun t => (deningerGreenSeries_hasDerivAt hf n hL t).differentiableAt, ?_, ?_⟩
    · intro hω
      exact absurd hω (by simp)
    · rw [deningerGreenSeries_deriv hf hL n]
      exact ih (n + 1)

theorem deningerGreenSeries_contDiff {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (n : ℕ) : ContDiff ℝ ∞ (deningerGreenSeries f L n) :=
  contDiff_infty.mpr fun m => deningerGreenSeries_contDiff_nat hf hL m n

theorem deningerGreenSeries_iteratedDeriv {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (n : ℕ) :
    iteratedDeriv n (deningerGreenSeries f L 0) = deningerGreenSeries f L n := by
  induction n with
  | zero => rw [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deningerGreenSeries_deriv hf hL n]

/-- **The seminorm bound `(8)`.**  When the periodization vanishes, the Green sum obeys the source
condition at every exponent, at the cost of one unit of exponent on the right. -/
theorem deningerGreenSeries_expBound {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (hper : ∀ t : ℝ, deningerPeriodizationSum f L t = 0) {A : ℝ} (hA : 0 ≤ A)
    (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, Real.exp (A * |t|) * ‖deningerGreenSeries f L n t‖ ≤ C := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := deningerExpSchwartz_iteratedDeriv_norm_le hf (A + 1) n
  set q : ℝ := Real.exp (-((A + 1) * L)) with hq
  have hqnn : (0 : ℝ) ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hgeo : ∑' j : ℕ, q ^ j = (1 - q)⁻¹ := tsum_geometric_of_lt_one hqnn hqlt
  have hSnn : (0 : ℝ) ≤ (1 - q)⁻¹ := by
    have : (0 : ℝ) < 1 - q := by linarith
    positivity
  refine ⟨C₀ * (1 - q)⁻¹, fun t => ?_⟩
  rcases le_total 0 t with ht | ht
  · -- forward representation
    have habs : |t| = t := abs_of_nonneg ht
    have hterm : ∀ j : ℕ,
        ‖iteratedDeriv n (f : ℝ → ℂ) (t + (j : ℝ) * L)‖
          ≤ (C₀ * Real.exp (-((A + 1) * t))) * q ^ j := by
      intro j
      refine le_trans (hC₀ (t + (j : ℝ) * L)) ?_
      have hpow : q ^ j = Real.exp (-((A + 1) * ((j : ℝ) * L))) := by
        rw [hq, ← Real.exp_nat_mul]
        congr 1
        ring
      have hle : -((A + 1) * |t + (j : ℝ) * L|)
          ≤ -((A + 1) * t) + -((A + 1) * ((j : ℝ) * L)) := by
        have h1 : t + (j : ℝ) * L ≤ |t + (j : ℝ) * L| := le_abs_self _
        nlinarith [hA]
      calc C₀ * Real.exp (-((A + 1) * |t + (j : ℝ) * L|))
          ≤ C₀ * Real.exp (-((A + 1) * t) + -((A + 1) * ((j : ℝ) * L))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hC₀nn
        _ = (C₀ * Real.exp (-((A + 1) * t))) * q ^ j := by
            rw [Real.exp_add, hpow]
            ring
    have hsum := deningerGreenSeries_summable hf n hL t
    have hmaj : Summable fun j : ℕ => (C₀ * Real.exp (-((A + 1) * t))) * q ^ j :=
      (summable_geometric_of_lt_one hqnn hqlt).mul_left _
    have hbd : ‖deningerGreenSeries f L n t‖
        ≤ (C₀ * Real.exp (-((A + 1) * t))) * (1 - q)⁻¹ := by
      refine le_trans (norm_tsum_le_tsum_norm hsum.norm) ?_
      refine le_trans (Summable.tsum_le_tsum hterm hsum.norm hmaj) (le_of_eq ?_)
      rw [Summable.tsum_mul_left _ (summable_geometric_of_lt_one hqnn hqlt), hgeo]
    have hexp : Real.exp (A * |t|) * ((C₀ * Real.exp (-((A + 1) * t))) * (1 - q)⁻¹)
        = C₀ * (1 - q)⁻¹ * Real.exp (-t) := by
      rw [habs]
      have hmul : Real.exp (A * t) * Real.exp (-((A + 1) * t)) = Real.exp (-t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc Real.exp (A * t) * ((C₀ * Real.exp (-((A + 1) * t))) * (1 - q)⁻¹)
          = C₀ * (1 - q)⁻¹ * (Real.exp (A * t) * Real.exp (-((A + 1) * t))) := by ring
        _ = C₀ * (1 - q)⁻¹ * Real.exp (-t) := by rw [hmul]
    calc Real.exp (A * |t|) * ‖deningerGreenSeries f L n t‖
        ≤ Real.exp (A * |t|) * ((C₀ * Real.exp (-((A + 1) * t))) * (1 - q)⁻¹) :=
          mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le
      _ = C₀ * (1 - q)⁻¹ * Real.exp (-t) := hexp
      _ ≤ C₀ * (1 - q)⁻¹ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = C₀ * (1 - q)⁻¹ := by ring
  · -- backward representation, valid because the periodization vanishes
    have habs : |t| = -t := abs_of_nonpos ht
    have hterm : ∀ j : ℕ,
        ‖iteratedDeriv n (f : ℝ → ℂ) (t - ((j : ℝ) + 1) * L)‖
          ≤ (C₀ * Real.exp (-((A + 1) * (-t)))) * q ^ j := by
      intro j
      refine le_trans (hC₀ (t - ((j : ℝ) + 1) * L)) ?_
      have hpow : q ^ j = Real.exp (-((A + 1) * ((j : ℝ) * L))) := by
        rw [hq, ← Real.exp_nat_mul]
        congr 1
        ring
      have hneg : -(t - ((j : ℝ) + 1) * L) ≤ |t - ((j : ℝ) + 1) * L| := neg_le_abs _
      have hle : -((A + 1) * |t - ((j : ℝ) + 1) * L|)
          ≤ -((A + 1) * (-t)) + -((A + 1) * ((j : ℝ) * L)) := by
        nlinarith [hA, hL.le]
      calc C₀ * Real.exp (-((A + 1) * |t - ((j : ℝ) + 1) * L|))
          ≤ C₀ * Real.exp (-((A + 1) * (-t)) + -((A + 1) * ((j : ℝ) * L))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hC₀nn
        _ = (C₀ * Real.exp (-((A + 1) * (-t)))) * q ^ j := by
            rw [Real.exp_add, hpow]
            ring
    have hsum := deningerGreenSeriesNeg_summable hf n hL t
    have hmaj : Summable fun j : ℕ => (C₀ * Real.exp (-((A + 1) * (-t)))) * q ^ j :=
      (summable_geometric_of_lt_one hqnn hqlt).mul_left _
    have hbd : ‖deningerGreenSeriesNeg f L n t‖
        ≤ (C₀ * Real.exp (-((A + 1) * (-t)))) * (1 - q)⁻¹ := by
      refine le_trans (norm_tsum_le_tsum_norm hsum.norm) ?_
      refine le_trans (Summable.tsum_le_tsum hterm hsum.norm hmaj) (le_of_eq ?_)
      rw [Summable.tsum_mul_left _ (summable_geometric_of_lt_one hqnn hqlt), hgeo]
    have hswap : ‖deningerGreenSeries f L n t‖ = ‖deningerGreenSeriesNeg f L n t‖ := by
      rw [deningerGreenSeries_eq_neg hf hL hper n t, norm_neg]
    have hexp : Real.exp (A * |t|) * ((C₀ * Real.exp (-((A + 1) * (-t)))) * (1 - q)⁻¹)
        = C₀ * (1 - q)⁻¹ * Real.exp t := by
      rw [habs]
      have hmul : Real.exp (A * -t) * Real.exp (-((A + 1) * -t)) = Real.exp t := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc Real.exp (A * -t) * ((C₀ * Real.exp (-((A + 1) * (-t)))) * (1 - q)⁻¹)
          = C₀ * (1 - q)⁻¹ * (Real.exp (A * -t) * Real.exp (-((A + 1) * -t))) := by ring
        _ = C₀ * (1 - q)⁻¹ * Real.exp t := by rw [hmul]
    rw [hswap]
    calc Real.exp (A * |t|) * ‖deningerGreenSeriesNeg f L n t‖
        ≤ Real.exp (A * |t|) * ((C₀ * Real.exp (-((A + 1) * (-t)))) * (1 - q)⁻¹) :=
          mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le
      _ = C₀ * (1 - q)⁻¹ * Real.exp t := hexp
      _ ≤ C₀ * (1 - q)⁻¹ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.exp_le_one_iff.mpr ht
      _ = C₀ * (1 - q)⁻¹ := by ring

end

end RHTower

/-! ## The Green sum as a member of the source, and `(6)` -/

namespace RHTower

open SchwartzMap

open scoped ContDiff

noncomputable section

theorem deningerGreenSeries_expBound_all {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (hper : ∀ t : ℝ, deningerPeriodizationSum f L t = 0) (A : ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, Real.exp (A * |t|) *
      ‖iteratedFDeriv ℝ n (deningerGreenSeries f L 0) t‖ ≤ C := by
  obtain ⟨C, hC⟩ := deningerGreenSeries_expBound hf hL hper (le_max_right A 0) n
  refine ⟨C, fun t => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, deningerGreenSeries_iteratedDeriv hf hL n]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (hC t)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left A 0) (abs_nonneg t))

/-- **The Green sum of a zero-periodization element is again in the source.** -/
def deningerGreenSchwartz {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ} (hL : 0 < L)
    (hper : ∀ t : ℝ, deningerPeriodizationSum f L t = 0) : 𝓢(ℝ, ℂ) :=
  deningerExpSchwartzOfBounds (deningerGreenSeries f L 0)
    (deningerGreenSeries_contDiff hf hL 0)
    (deningerGreenSeries_expBound_all hf hL hper)

theorem deningerGreenSchwartz_apply {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (hper : ∀ t : ℝ, deningerPeriodizationSum f L t = 0) (t : ℝ) :
    deningerGreenSchwartz hf hL hper t = deningerGreenSum f L t :=
  deningerGreenSeries_zero f L t

theorem deningerGreenSchwartz_mem {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (hper : ∀ t : ℝ, deningerPeriodizationSum f L t = 0) :
    deningerGreenSchwartz hf hL hper ∈ DeningerExpSchwartz :=
  deningerExpSchwartzOfBounds_mem _ _ _

/-- **`Δ_L G_L = 1` on the zero-periodization sector.** -/
theorem deningerGreenSchwartz_defect {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) (hper : ∀ t : ℝ, deningerPeriodizationSum f L t = 0) :
    deningerPeriodizationDefect L
        ⟨deningerGreenSchwartz hf hL hper, deningerGreenSchwartz_mem hf hL hper⟩
      = ⟨f, hf⟩ := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerPeriodizationDefect_apply]
  show deningerGreenSchwartz hf hL hper t - deningerGreenSchwartz hf hL hper (t + L) = f t
  rw [deningerGreenSchwartz_apply, deningerGreenSchwartz_apply]
  exact deningerGreenSum_telescope hf hL t

/-- The periodization is additive on the source. -/
theorem deningerPeriodizationSum_sub {f g : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz)
    (hg : g ∈ DeningerExpSchwartz) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    deningerPeriodizationSum (f - g) L t
      = deningerPeriodizationSum f L t - deningerPeriodizationSum g L t := by
  have hsf := deningerShiftInt_summable hf hL t
  have hsg := deningerShiftInt_summable hg hL t
  rw [deningerPeriodizationSum, deningerPeriodizationSum, deningerPeriodizationSum,
    ← hsf.tsum_sub hsg]
  exact tsum_congr fun j => rfl

/-- **`(6)`: the image of the periodization defect is the kernel of the periodization.** -/
theorem deningerPeriodization_range_eq_kernel {L : ℝ} (hL : 0 < L) :
    Set.range (deningerPeriodizationDefect L)
      = {h : DeningerExpSchwartz |
          ∀ t : ℝ, deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t = 0} := by
  ext h
  constructor
  · rintro ⟨g, rfl⟩ t
    have hcoe : ((deningerPeriodizationDefect L g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
        = ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
          - deningerExpShift L ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) := rfl
    rw [hcoe, deningerPeriodizationSum_sub g.2 (deningerExpShift_mem g.2 L) hL]
    have := deningerPeriodization_defect ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t
    linear_combination (norm := ring_nf) this
  · intro hker
    refine ⟨⟨deningerGreenSchwartz h.2 hL hker, deningerGreenSchwartz_mem h.2 hL hker⟩, ?_⟩
    have := deningerGreenSchwartz_defect h.2 hL hker
    rw [this]

end

end RHTower
