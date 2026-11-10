import GaloisForLFunctions.RHTower.FractionalPartZeta
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The constant terms on the two sides of the line agree

Let `G` be a function with a generalized Dirichlet expansion `Σ b_i a_i^s`, `0 < a_i ≤ 1`, right of
the critical line and an expansion `Σ c_j q_j^s`, `q_j ≥ 1`, left of it, whose singularities on the
line are cancelled by zeros of `ζ`: `F = −G ζ/s` is holomorphic on the strip `0 < Re s < 1` and
bounded near the line. Then the two constant terms agree
(`constantTerms_agree`): `Σ_{q_j = 1} c_j = Σ_{a_i = 1} b_i`.

The mechanism is the jump of the fractional part. Since `∫_0^∞ {u} u^{−s−1} du = −ζ(s)/s` in the
strip, `F` is the Mellin transform of `g₊(u) = Σ b_i {a_i u}` right of the line and of
`g₋(u) = Σ c_j {q_j u}` left of it (`mellin_fractSeries`). The transforms of `g₊ − g₋` over
`(1, ∞)` and over `(0, 1)` glue with `F` to a bounded entire function that tends to zero, so
`g₊ = g₋` at every point of continuity. Both functions are regulated; at `u = 1/k` the jump of
`g₊` is `−[k = 1] Σ_{a_i = 1} b_i` and the jump of `g₋` is `−Σ_{k ∣ q_j} c_j`
(`tendsto_fractSeries_left`). Möbius inversion over `k` gives the statement.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*} {κ : Type*}

/-! ### Series of fractional parts -/

/-- The fractional part as a complex function. -/
def fractC (x : ℝ) : ℂ := ((Int.fract x : ℝ) : ℂ)

/-- `Σ b_i {a_i u}`. -/
def fractSeries (b : ι → ℂ) (a : ι → ℝ) (u : ℝ) : ℂ := ∑' i, b i * fractC (a i * u)

theorem fract_le_rpow {y : ℝ} (hy : 0 ≤ y) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    Int.fract y ≤ y ^ σ := by
  rcases le_or_gt 1 y with h | h
  · exact (Int.fract_lt_one y).le.trans (Real.one_le_rpow h h0)
  · rw [Int.fract_eq_self.mpr ⟨hy, h⟩]
    calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ ≤ y ^ σ := Real.rpow_le_rpow_of_exponent_ge' hy h.le h0 h1

theorem norm_fractC (x : ℝ) : ‖fractC x‖ = Int.fract x := by
  rw [fractC, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]

theorem norm_fractTerm_le (b : ι → ℂ) {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1) {u : ℝ} (hu : 0 ≤ u) (i : ι) :
    ‖b i * fractC (a i * u)‖ ≤ ‖b i‖ * a i ^ σ * u ^ σ := by
  rw [norm_mul, norm_fractC, mul_assoc, ← Real.mul_rpow (ha i).le hu]
  exact mul_le_mul_of_nonneg_left (fract_le_rpow (mul_nonneg (ha i).le hu) h0 h1) (norm_nonneg _)

theorem summable_fractTerm {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {u : ℝ} (hu : 0 ≤ u) :
    Summable fun i => b i * fractC (a i * u) :=
  Summable.of_norm_bounded (hsum.mul_right (u ^ σ)) (norm_fractTerm_le b ha h0 h1 hu)

/-- `‖Σ b_i {a_i u}‖ ≤ (Σ ‖b_i‖ a_i^σ) u^σ` for `0 ≤ σ ≤ 1`. -/
theorem norm_fractSeries_le {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {u : ℝ} (hu : 0 ≤ u) :
    ‖fractSeries b a u‖ ≤ (∑' i, ‖b i‖ * a i ^ σ) * u ^ σ := by
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded ((hsum.mul_right (u ^ σ)).hasSum) (norm_fractTerm_le b ha h0 h1 hu)

theorem measurable_fractC : Measurable fractC :=
  Complex.measurable_ofReal.comp measurable_fract

theorem measurable_fractSeries [Countable ι] (b : ι → ℂ) (a : ι → ℝ) :
    Measurable (fractSeries b a) :=
  Measurable.tsum fun i => (measurable_fractC.comp (measurable_const_mul (a i))).const_mul (b i)

/-! ### One-sided limits -/

theorem tendsto_fract_mul_right {a : ℝ} (ha : 0 < a) (u₀ : ℝ) :
    Tendsto (fun u : ℝ => Int.fract (a * u)) (𝓝[>] u₀) (𝓝 (Int.fract (a * u₀))) := by
  have hmul : Tendsto (fun u : ℝ => a * u) (𝓝[>] u₀) (𝓝[≥] (a * u₀)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_const_mul a).continuousAt.continuousWithinAt
      (by filter_upwards [self_mem_nhdsWithin] with u hu
          exact mul_le_mul_of_nonneg_left (le_of_lt hu) ha.le)
  have hfloor : Tendsto (fun u : ℝ => ((⌊a * u⌋ : ℤ) : ℝ)) (𝓝[>] u₀) (𝓝 ((⌊a * u₀⌋ : ℤ) : ℝ)) :=
    (tendsto_pure_nhds (fun n : ℤ => (n : ℝ)) ⌊a * u₀⌋).comp
      ((tendsto_floor_right_pure_floor (α := ℝ) (a * u₀)).comp hmul)
  have hlin : Tendsto (fun u : ℝ => a * u) (𝓝[>] u₀) (𝓝 (a * u₀)) :=
    (continuous_const_mul a).continuousAt.continuousWithinAt
  exact hlin.sub hfloor

/-- From the left the fractional part of `a u` tends to `a u₀ − ⌈a u₀⌉ + 1`. -/
theorem tendsto_fract_mul_left {a : ℝ} (ha : 0 < a) (u₀ : ℝ) :
    Tendsto (fun u : ℝ => Int.fract (a * u)) (𝓝[<] u₀) (𝓝 (a * u₀ - (⌈a * u₀⌉ - 1 : ℤ))) := by
  have hmul : Tendsto (fun u : ℝ => a * u) (𝓝[<] u₀) (𝓝[<] (a * u₀)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_const_mul a).continuousAt.continuousWithinAt
      (by filter_upwards [self_mem_nhdsWithin] with u hu
          exact mul_lt_mul_of_pos_left hu ha)
  have hfloor : Tendsto (fun u : ℝ => ((⌊a * u⌋ : ℤ) : ℝ)) (𝓝[<] u₀)
      (𝓝 ((⌈a * u₀⌉ - 1 : ℤ) : ℝ)) :=
    (tendsto_pure_nhds (fun n : ℤ => (n : ℝ)) (⌈a * u₀⌉ - 1)).comp
      ((tendsto_floor_left_pure_ceil_sub_one (α := ℝ) (a * u₀)).comp hmul)
  have hlin : Tendsto (fun u : ℝ => a * u) (𝓝[<] u₀) (𝓝 (a * u₀)) :=
    (continuous_const_mul a).continuousAt.continuousWithinAt
  exact hlin.sub hfloor

open scoped Classical in
/-- The left limit differs from the value exactly at the integers. -/
theorem fract_sub_leftLimit (x : ℝ) :
    Int.fract x - (x - (⌈x⌉ - 1 : ℤ)) = if ∃ n : ℤ, x = n then -1 else 0 := by
  by_cases h : ∃ n : ℤ, x = n
  · obtain ⟨n, rfl⟩ := h
    rw [if_pos ⟨n, rfl⟩, Int.fract_intCast, Int.ceil_intCast]
    push_cast
    ring
  · rw [if_neg h]
    have hlt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) fun he => h ⟨⌊x⌋, he.symm⟩
    have hceil : ⌈x⌉ = ⌊x⌋ + 1 := by
      rw [Int.ceil_eq_iff]
      push_cast
      exact ⟨by linarith, (Int.lt_floor_add_one x).le⟩
    rw [hceil, Int.fract]
    push_cast
    ring

/-- Near a point `u₀ > 0` the terms are dominated uniformly. -/
theorem eventually_norm_fractTerm_le (b : ι → ℂ) {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∀ᶠ u in 𝓝 u₀, ∀ i, ‖b i * fractC (a i * u)‖ ≤ ‖b i‖ * a i ^ σ * (u₀ + 1) ^ σ := by
  filter_upwards [Ioo_mem_nhds hu₀ (lt_add_one u₀)] with u hu i
  refine (norm_fractTerm_le b ha h0 h1 hu.1.le i).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu.1.le hu.2.le h0)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ha i).le _))

/-- The series is right continuous. -/
theorem tendsto_fractSeries_right {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) :
    Tendsto (fractSeries b a) (𝓝[>] u₀) (𝓝 (fractSeries b a u₀)) := by
  refine tendsto_tsum_of_dominated_convergence (hsum.mul_right ((u₀ + 1) ^ σ)) (fun i => ?_)
    (nhdsWithin_le_nhds (eventually_norm_fractTerm_le b ha h0 h1 hu₀))
  exact ((Complex.continuous_ofReal.tendsto _).comp (tendsto_fract_mul_right (ha i) u₀)).const_mul
    (b i)

/-- The left limit of the series. -/
theorem tendsto_fractSeries_left {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) :
    Tendsto (fractSeries b a) (𝓝[<] u₀)
      (𝓝 (∑' i, b i * ((a i * u₀ - (⌈a i * u₀⌉ - 1 : ℤ) : ℝ) : ℂ))) := by
  refine tendsto_tsum_of_dominated_convergence (hsum.mul_right ((u₀ + 1) ^ σ)) (fun i => ?_)
    (nhdsWithin_le_nhds (eventually_norm_fractTerm_le b ha h0 h1 hu₀))
  exact ((Complex.continuous_ofReal.tendsto _).comp (tendsto_fract_mul_left (ha i) u₀)).const_mul
    (b i)

open scoped Classical in
/-- **The jump of the series**: the value minus the left limit is minus the weight carried by the
indices with `a_i u₀` an integer. -/
theorem fractSeries_sub_leftLimit {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) :
    fractSeries b a u₀ - ∑' i, b i * ((a i * u₀ - (⌈a i * u₀⌉ - 1 : ℤ) : ℝ) : ℂ) =
      -∑' i, if ∃ n : ℤ, a i * u₀ = n then b i else 0 := by
  have hs1 := summable_fractTerm ha h0 h1 hsum hu₀.le
  have hs2 : Summable fun i => b i * ((a i * u₀ - (⌈a i * u₀⌉ - 1 : ℤ) : ℝ) : ℂ) := by
    refine Summable.of_norm_bounded (hsum.mul_right ((u₀ + 1) ^ σ)) fun i => ?_
    refine le_of_tendsto (((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_fract_mul_left (ha i) u₀)).const_mul (b i)).norm ?_
    exact nhdsWithin_le_nhds
      ((eventually_norm_fractTerm_le b ha h0 h1 hu₀).mono fun u hu => hu i)
  rw [fractSeries, ← hs1.tsum_sub hs2, ← tsum_neg]
  refine tsum_congr fun i => ?_
  rw [fractC, ← mul_sub, ← Complex.ofReal_sub, fract_sub_leftLimit]
  split_ifs
  · push_cast
    ring
  · rw [Complex.ofReal_zero, mul_zero, neg_zero]

/-- The series is continuous at a point where no visible term jumps. -/
theorem continuousAt_fractSeries {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) (hni : ∀ i, b i ≠ 0 → ∀ n : ℤ, a i * u₀ ≠ n) :
    ContinuousAt (fractSeries b a) u₀ := by
  refine tendsto_tsum_of_dominated_convergence (hsum.mul_right ((u₀ + 1) ^ σ)) (fun i => ?_)
    (eventually_norm_fractTerm_le b ha h0 h1 hu₀)
  by_cases hb : b i = 0
  · simp only [hb, zero_mul]
    exact tendsto_const_nhds
  · have hfr : ContinuousAt (fun u : ℝ => Int.fract (a i * u)) u₀ := by
      have h1' : ContinuousAt (Int.fract : ℝ → ℝ) (a i * u₀) :=
        continuousAt_fract (fun he => hni i hb ⌊a i * u₀⌋ he)
      exact h1'.comp (continuous_const_mul (a i)).continuousAt
    exact ((Complex.continuous_ofReal.continuousAt.comp hfr).tendsto).const_mul (b i)

end GaloisForLFunctions.InfiniteRankPurityTheory
