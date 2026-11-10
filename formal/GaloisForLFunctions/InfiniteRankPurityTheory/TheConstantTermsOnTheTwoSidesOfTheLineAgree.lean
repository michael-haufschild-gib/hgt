import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

More is true (`tsum_scale_eq_zero`, `tsum_left_eq_const`, `eq_const_mul_riemannZeta_div`): at the
points `1/(kt)`, `t > 1`, the right series has no jump at all, so the left expansion carries no
weight at any scale `t > 1`; it is a constant `β`, and `F = −β ζ(s)/s` on the whole strip. The
critical zeros of `ζ` cancel the poles of no two-sided expansion other than a constant.

Two tools for the hypotheses: `g f'/f` is holomorphic wherever `g` vanishes at the zeros of `f`
(`exists_differentiableOn_deriv_mul_div`), and a holomorphic function on a strip is bounded by its
bounds on the boundary lines and on horizontal segments at heights met in every interval of a
fixed length (`norm_le_of_good_heights`).
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

/-! ### Mellin transforms -/

theorem locallyIntegrableOn_of_bound {f : ℝ → ℂ} (hf : Measurable f) {C σ : ℝ} (h0 : 0 ≤ σ)
    (hb : ∀ u : ℝ, 0 < u → ‖f u‖ ≤ C * u ^ σ) : LocallyIntegrableOn f (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ⟨Ioo (x / 2) (2 * x), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
    ?_⟩
  refine Measure.integrableOn_of_bounded (M := |C| * (2 * x) ^ σ) ?_ hf.aestronglyMeasurable ?_
  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := by linarith [hu.1]
    refine (hb u hu0).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hu0.le _)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu0.le hu.2.le h0) (abs_nonneg C)

/-- A function supported on `u > 1` and `O(u^σ)` there has a Mellin transform on `Re z < −σ`,
holomorphic and bounded by `C/(−σ − Re z)`. -/
theorem mellin_of_support_Ioi {f : ℝ → ℂ} (hf : Measurable f) {C σ : ℝ} (hσ : 0 ≤ σ)
    (hb : ∀ u : ℝ, 0 < u → ‖f u‖ ≤ C * u ^ σ) (hz0 : ∀ u : ℝ, u ≤ 1 → f u = 0) {z : ℂ}
    (hz : z.re < -σ) :
    MellinConvergent f z ∧ DifferentiableAt ℂ (mellin f) z ∧ ‖mellin f z‖ ≤ C / (-σ - z.re) := by
  have hloc := locallyIntegrableOn_of_bound hf hσ hb
  have htop : f =O[atTop] fun u : ℝ => u ^ (-(-σ)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg hu.le _)]
    exact hb u hu
  have hbot : f =O[𝓝[>] (0 : ℝ)] fun u : ℝ => u ^ (-(z.re - 1)) := by
    have heq : f =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with u hu
      exact hz0 u hu.2.le
    exact (Asymptotics.isBigO_zero _ _).congr' heq.symm EventuallyEq.rfl
  refine ⟨mellinConvergent_of_isBigO_rpow hloc htop hz hbot (by linarith),
    mellin_differentiableAt_of_isBigO_rpow hloc htop hz hbot (by linarith), ?_⟩
  have hexp : z.re - 1 + σ < -1 := by linarith
  have hgi : Integrable (fun t : ℝ => (Ioi (1 : ℝ)).indicator (fun t => C * t ^ (z.re - 1 + σ)) t)
      (volume.restrict (Ioi 0)) :=
    (IntegrableOn.integrable_indicator (show IntegrableOn (fun t : ℝ => C * t ^ (z.re - 1 + σ))
      (Ioi 1) volume from (integrableOn_Ioi_rpow_of_lt hexp one_pos).const_mul C)
      measurableSet_Ioi).restrict
  have hle : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ‖(t : ℂ) ^ (z - 1) • f t‖ ≤
      (Ioi (1 : ℝ)).indicator (fun t => C * t ^ (z.re - 1 + σ)) t := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    by_cases h1 : 1 < t
    · rw [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1), Real.rpow_add ht0]
      calc t ^ (z.re - 1) * ‖f t‖ ≤ t ^ (z.re - 1) * (C * t ^ σ) :=
            mul_le_mul_of_nonneg_left (hb t ht0) (Real.rpow_nonneg ht0.le _)
        _ = C * (t ^ (z.re - 1) * t ^ σ) := by ring
    · rw [indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from h1), hz0 t (not_lt.mp h1), norm_zero,
        mul_zero]
  have h := norm_integral_le_of_norm_le hgi hle
  rw [setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one),
    integral_const_mul, integral_Ioi_rpow_of_lt hexp one_pos, Real.one_rpow] at h
  refine h.trans (le_of_eq ?_)
  have hne : z.re - 1 + σ + 1 ≠ 0 := by linarith
  have hne' : -σ - z.re ≠ 0 := by linarith
  field_simp
  ring

/-- A function supported on `u ≤ 1` and `O(u^σ)` there has a Mellin transform on `Re z > −σ`,
holomorphic and bounded by `C/(Re z + σ)`. -/
theorem mellin_of_support_Iic {f : ℝ → ℂ} (hf : Measurable f) {C σ : ℝ} (hσ : 0 ≤ σ)
    (hb : ∀ u : ℝ, 0 < u → ‖f u‖ ≤ C * u ^ σ) (hz1 : ∀ u : ℝ, 1 < u → f u = 0) {z : ℂ}
    (hz : -σ < z.re) :
    MellinConvergent f z ∧ DifferentiableAt ℂ (mellin f) z ∧ ‖mellin f z‖ ≤ C / (z.re + σ) := by
  have hloc := locallyIntegrableOn_of_bound hf hσ hb
  have hbot : f =O[𝓝[>] (0 : ℝ)] fun u : ℝ => u ^ (-(-σ)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _)]
    exact hb u hu0
  have htop : f =O[atTop] fun u : ℝ => u ^ (-(z.re + 1)) := by
    have heq : f =ᶠ[atTop] fun _ => (0 : ℂ) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
      exact hz1 u hu
    exact (Asymptotics.isBigO_zero _ _).congr' heq.symm EventuallyEq.rfl
  refine ⟨mellinConvergent_of_isBigO_rpow hloc htop (by linarith) hbot hz,
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hbot hz, ?_⟩
  have hexp : -1 < z.re - 1 + σ := by linarith
  have hgi : Integrable (fun t : ℝ => (Ioc (0 : ℝ) 1).indicator (fun t => C * t ^ (z.re - 1 + σ)) t)
      (volume.restrict (Ioi 0)) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ (z.re - 1 + σ)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hexp).1
    exact (IntegrableOn.integrable_indicator (show IntegrableOn
      (fun t : ℝ => C * t ^ (z.re - 1 + σ)) (Ioc 0 1) volume from h1.const_mul C)
      measurableSet_Ioc).restrict
  have hle : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ‖(t : ℂ) ^ (z - 1) • f t‖ ≤
      (Ioc (0 : ℝ) 1).indicator (fun t => C * t ^ (z.re - 1 + σ)) t := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    by_cases h1 : t ≤ 1
    · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, h1⟩), Real.rpow_add ht0]
      calc t ^ (z.re - 1) * ‖f t‖ ≤ t ^ (z.re - 1) * (C * t ^ σ) :=
            mul_le_mul_of_nonneg_left (hb t ht0) (Real.rpow_nonneg ht0.le _)
        _ = C * (t ^ (z.re - 1) * t ^ σ) := by ring
    · rw [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => h1 h.2),
        hz1 t (not_le.mp h1), norm_zero, mul_zero]
  have h := norm_integral_le_of_norm_le hgi hle
  rw [setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 from inter_eq_right.mpr Ioc_subset_Ioi_self,
    integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hexp), Real.one_rpow, Real.zero_rpow (by linarith)] at h
  refine h.trans (le_of_eq ?_)
  have hne : z.re - 1 + σ + 1 ≠ 0 := by linarith
  have hne' : z.re + σ ≠ 0 := by linarith
  field_simp
  ring

/-- The fractional part has a Mellin transform on `−1 < Re z < 0`. -/
theorem mellinConvergent_fractC {z : ℂ} (h0 : -1 < z.re) (h1 : z.re < 0) :
    MellinConvergent fractC z := by
  have hb : ∀ u : ℝ, 0 < u → ‖fractC u‖ ≤ 1 * u ^ (0 : ℝ) := fun u _ => by
    rw [norm_fractC, Real.rpow_zero, mul_one]
    exact (Int.fract_lt_one u).le
  have hloc := locallyIntegrableOn_of_bound measurable_fractC le_rfl hb
  have htop : fractC =O[atTop] fun u : ℝ => u ^ (-(0 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun u => ?_)
    rw [norm_fractC, neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact (Int.fract_lt_one u).le
  have hbot : fractC =O[𝓝[>] (0 : ℝ)] fun u : ℝ => u ^ (-(-1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with u hu
    rw [norm_fractC, neg_neg, Real.rpow_one, Real.norm_of_nonneg hu.1.le, one_mul,
      Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩]
  exact mellinConvergent_of_isBigO_rpow hloc htop h1 hbot h0

/-- `∫_0^∞ {u} u^{−s−1} du = −ζ(s)/s` in the strip. -/
theorem mellin_fractC_neg {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin fractC (-s) = -(riemannZeta s / s) := by
  rw [← _root_.RHTower.integral_Ioi_zero_fract_cpow h0 h1, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, mul_comm, fractC, show -s - 1 = -(s + 1) by ring]

/-- The real Mellin integral of the fractional part. -/
def fractMass (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (x - 1) * Int.fract t

theorem integral_rpow_mul_fract_comp (x : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), t ^ (x - 1) * Int.fract (a * t)) = a ^ (-x) * fractMass x := by
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => y ^ (x - 1) * Int.fract y) 0 ha
  rw [mul_zero] at h
  have hfun : ∀ t ∈ Ioi (0 : ℝ), (a * t) ^ (x - 1) * Int.fract (a * t) =
      a ^ (x - 1) * (t ^ (x - 1) * Int.fract (a * t)) := by
    intro t ht
    rw [Real.mul_rpow ha.le (le_of_lt ht)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul, smul_eq_mul] at h
  have hpos : 0 < a ^ (x - 1) := Real.rpow_pos_of_pos ha _
  have hsplit : a ^ (-x) = (a ^ (x - 1))⁻¹ * a⁻¹ := by
    rw [← Real.rpow_neg ha.le, ← Real.rpow_neg_one a, ← Real.rpow_add ha]
    congr 1
    ring
  rw [fractMass, hsplit, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- **The Mellin transform of a series of fractional parts.** -/
theorem hasSum_mellin_fractSeries [Countable ι] {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {z : ℂ} (h0 : -1 < z.re) (h1 : z.re < 0) (hsum : Summable fun i => ‖b i‖ * a i ^ (-z.re)) :
    HasSum (fun i => b i * ((a i : ℂ) ^ (-z) * mellin fractC z)) (mellin (fractSeries b a) z) := by
  have hint : ∀ i, Integrable (fun t : ℝ => (t : ℂ) ^ (z - 1) • (b i * fractC (a i * t)))
      (volume.restrict (Ioi 0)) := fun i => by
    have h := ((MellinConvergent.comp_mul_left (ha i)).mpr
      (mellinConvergent_fractC h0 h1)).const_smul (b i)
    have h' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • (b i * fractC (a i * t))) (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul] using h
    exact h'
  have hnorm : ∀ i, (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (z - 1) • (b i * fractC (a i * t))‖) =
      ‖b i‖ * a i ^ (-z.re) * fractMass z.re := by
    intro i
    rw [mul_assoc, ← integral_rpow_mul_fract_comp z.re (ha i), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re,
      norm_mul, norm_fractC]
    ring
  have hsum' : Summable fun i => ∫ t in Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (z - 1) • (b i * fractC (a i * t))‖ := by
    simp only [hnorm]
    exact hsum.mul_right _
  have h := hasSum_integral_of_summable_integral_norm hint hsum'
  have hL : ∀ i, (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) • (b i * fractC (a i * t))) =
      b i * ((a i : ℂ) ^ (-z) * mellin fractC z) := fun i => by
    rw [← smul_eq_mul (a := (a i : ℂ) ^ (-z)), ← mellin_comp_mul_left fractC z (ha i), mellin,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]
    ring
  have hR : (∫ t in Ioi (0 : ℝ), ∑' i, (t : ℂ) ^ (z - 1) • (b i * fractC (a i * t))) =
      mellin (fractSeries b a) z := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul, fractSeries, tsum_mul_left]
  rw [← hR]
  simpa only [hL] using h

/-- In the strip, `M[Σ b_i {a_i ·}](−s) = −(ζ(s)/s) Σ b_i a_i^s`. -/
theorem mellin_fractSeries [Countable ι] {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hsum : Summable fun i => ‖b i‖ * a i ^ s.re) :
    mellin (fractSeries b a) (-s) = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s := by
  have hsum' : Summable fun i => ‖b i‖ * a i ^ (-(-s).re) := by
    simpa only [Complex.neg_re, neg_neg] using hsum
  have h := hasSum_mellin_fractSeries ha (z := -s) (by rw [Complex.neg_re]; linarith)
    (by rw [Complex.neg_re]; linarith) hsum'
  rw [← h.tsum_eq, mellin_fractC_neg h0 h1, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [neg_neg]
  ring

/-! ### Truncations -/

/-- The part of a function on `u > 1`. -/
def topPart (g : ℝ → ℂ) : ℝ → ℂ := (Ioi (1 : ℝ)).indicator g

/-- The part of a function on `u ≤ 1`. -/
def botPart (g : ℝ → ℂ) : ℝ → ℂ := (Iic (1 : ℝ)).indicator g

theorem topPart_of_lt {g : ℝ → ℂ} {u : ℝ} (h : 1 < u) : topPart g u = g u :=
  indicator_of_mem (show u ∈ Ioi (1 : ℝ) from h) g

theorem topPart_of_le {g : ℝ → ℂ} {u : ℝ} (h : u ≤ 1) : topPart g u = 0 :=
  indicator_of_notMem (show u ∉ Ioi (1 : ℝ) from not_lt.mpr h) g

theorem botPart_of_le {g : ℝ → ℂ} {u : ℝ} (h : u ≤ 1) : botPart g u = g u :=
  indicator_of_mem (show u ∈ Iic (1 : ℝ) from h) g

theorem botPart_of_lt {g : ℝ → ℂ} {u : ℝ} (h : 1 < u) : botPart g u = 0 :=
  indicator_of_notMem (show u ∉ Iic (1 : ℝ) from not_le.mpr h) g

theorem topPart_add_botPart (g : ℝ → ℂ) (u : ℝ) : topPart g u + botPart g u = g u := by
  rcases lt_or_ge 1 u with h | h
  · rw [topPart_of_lt h, botPart_of_lt h, add_zero]
  · rw [topPart_of_le h, botPart_of_le h, zero_add]

theorem norm_topPart_le (g : ℝ → ℂ) (u : ℝ) : ‖topPart g u‖ ≤ ‖g u‖ :=
  norm_indicator_le_norm_self g u

theorem norm_botPart_le (g : ℝ → ℂ) (u : ℝ) : ‖botPart g u‖ ≤ ‖g u‖ :=
  norm_indicator_le_norm_self g u

/-- The upper part of a function `O(u^σ)` has a Mellin transform on `Re z < −σ`. -/
theorem mellin_topPart {g : ℝ → ℂ} (hg : Measurable g) {C σ : ℝ} (hσ : 0 ≤ σ)
    (hb : ∀ u : ℝ, 0 < u → ‖g u‖ ≤ C * u ^ σ) {z : ℂ} (hz : z.re < -σ) :
    MellinConvergent (topPart g) z ∧ DifferentiableAt ℂ (mellin (topPart g)) z ∧
      ‖mellin (topPart g) z‖ ≤ C / (-σ - z.re) :=
  mellin_of_support_Ioi (hg.indicator measurableSet_Ioi) hσ
    (fun u hu => (norm_topPart_le g u).trans (hb u hu)) (fun _ hu => topPart_of_le hu) hz

/-- The lower part of a function `O(u^σ)` has a Mellin transform on `Re z > −σ`. -/
theorem mellin_botPart {g : ℝ → ℂ} (hg : Measurable g) {C σ : ℝ} (hσ : 0 ≤ σ)
    (hb : ∀ u : ℝ, 0 < u → ‖g u‖ ≤ C * u ^ σ) {z : ℂ} (hz : -σ < z.re) :
    MellinConvergent (botPart g) z ∧ DifferentiableAt ℂ (mellin (botPart g)) z ∧
      ‖mellin (botPart g) z‖ ≤ C / (z.re + σ) :=
  mellin_of_support_Iic (hg.indicator measurableSet_Iic) hσ
    (fun u hu => (norm_botPart_le g u).trans (hb u hu)) (fun _ hu => botPart_of_lt hu) hz

/-! ### Countable sets of jumps -/

theorem countable_jumpSet [Countable ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    {u : ℝ | ∃ i, ∃ n : ℤ, a i * u = n}.Countable := by
  have hsub : {u : ℝ | ∃ i, ∃ n : ℤ, a i * u = n} ⊆ ⋃ i, ⋃ n : ℤ, {(n : ℝ) / a i} := by
    rintro u ⟨i, n, h⟩
    simp only [mem_iUnion, mem_singleton_iff]
    exact ⟨i, n, by rw [← h, mul_div_cancel_left₀ _ (ha i).ne']⟩
  exact (countable_iUnion fun i => countable_iUnion fun n => countable_singleton _).mono hsub

theorem frequently_nhdsGT_notMem {S : Set ℝ} (hS : S.Countable) (u : ℝ) :
    ∃ᶠ x in 𝓝[>] u, x ∉ S := by
  intro h
  obtain ⟨w, hw, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  obtain ⟨x, hx, hxu⟩ := (hS.dense_compl ℝ).exists_between hw
  exact hsub hxu hx

/-! ### The two series agree -/

/-- **The two series of fractional parts agree.** If the Mellin transforms of `Σ b_i {a_i u}` and
of `Σ c_j {q_j u}` are the two sides of one function holomorphic on the strip and bounded near the
line, the two series are equal at every `u > 0`. -/
theorem fractSeries_eq [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {u : ℝ} (hu : 0 < u) : fractSeries b a u = fractSeries c q u := by
  have mR := measurable_fractSeries b a
  have mL := measurable_fractSeries c q
  have bR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ∀ u : ℝ, 0 < u →
      ‖fractSeries b a u‖ ≤ (∑' i, ‖b i‖ * a i ^ σ) * u ^ σ :=
    fun σ h0 h1 u hu => norm_fractSeries_le ha (by linarith) h1 (hR σ h0) hu.le
  have bL : ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 → ∀ u : ℝ, 0 < u →
      ‖fractSeries c q u‖ ≤ (∑' j, ‖c j‖ * q j ^ σ) * u ^ σ :=
    fun σ h0 h1 u hu => norm_fractSeries_le hq h0 (by linarith) (hL σ h1) hu.le
  -- the four pieces, as functions of `z = −s`
  have TR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ∀ z : ℂ, z.re < -σ →
      MellinConvergent (topPart (fractSeries b a)) z ∧
      DifferentiableAt ℂ (mellin (topPart (fractSeries b a))) z ∧
      ‖mellin (topPart (fractSeries b a)) z‖ ≤ (∑' i, ‖b i‖ * a i ^ σ) / (-σ - z.re) :=
    fun σ h0 h1 z hz => mellin_topPart mR (by linarith) (bR σ h0 h1) hz
  have TL : ∀ z : ℂ, z.re < 0 →
      MellinConvergent (topPart (fractSeries c q)) z ∧
      DifferentiableAt ℂ (mellin (topPart (fractSeries c q))) z ∧
      ‖mellin (topPart (fractSeries c q)) z‖ ≤ (∑' j, ‖c j‖ * q j ^ (0 : ℝ)) / (-0 - z.re) :=
    fun z hz => mellin_topPart mL le_rfl (bL 0 le_rfl (by norm_num)) (by simpa using hz)
  have BR : ∀ z : ℂ, -1 < z.re →
      MellinConvergent (botPart (fractSeries b a)) z ∧
      DifferentiableAt ℂ (mellin (botPart (fractSeries b a))) z ∧
      ‖mellin (botPart (fractSeries b a)) z‖ ≤ (∑' i, ‖b i‖ * a i ^ (1 : ℝ)) / (z.re + 1) :=
    fun z hz => mellin_botPart mR zero_le_one (bR 1 (by norm_num) le_rfl) hz
  have BL : ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 → ∀ z : ℂ, -σ < z.re →
      MellinConvergent (botPart (fractSeries c q)) z ∧
      DifferentiableAt ℂ (mellin (botPart (fractSeries c q))) z ∧
      ‖mellin (botPart (fractSeries c q)) z‖ ≤ (∑' j, ‖c j‖ * q j ^ σ) / (z.re + σ) :=
    fun σ h0 h1 z hz => mellin_botPart mL h0 (bL σ h0 h1) hz
  set Tr : ℂ → ℂ := fun s => mellin (topPart (fractSeries b a)) (-s) with hTr
  set Tl : ℂ → ℂ := fun s => mellin (topPart (fractSeries c q)) (-s) with hTl
  set Br : ℂ → ℂ := fun s => mellin (botPart (fractSeries b a)) (-s) with hBr
  set Bl : ℂ → ℂ := fun s => mellin (botPart (fractSeries c q)) (-s) with hBl
  set A : ℝ := ∑' i, ‖b i‖ * a i ^ (5 / 8 : ℝ) with hA
  set A₁ : ℝ := ∑' i, ‖b i‖ * a i ^ (1 : ℝ) with hA₁
  set B₀ : ℝ := ∑' j, ‖c j‖ * q j ^ (0 : ℝ) with hB₀
  set B' : ℝ := ∑' j, ‖c j‖ * q j ^ (3 / 8 : ℝ) with hB'
  have hA0 : 0 ≤ A := tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ha i).le _)
  have hA₁0 : 0 ≤ A₁ :=
    tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ha i).le _)
  have hB₀0 : 0 ≤ B₀ :=
    tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hq j).le _)
  have hB'0 : 0 ≤ B' :=
    tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hq j).le _)
  -- the two sides of `F`
  have hRid : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → F s = Tr s + Br s := by
    intro s h0 h1
    have hσ0 : 1 / 2 < (1 / 2 + s.re) / 2 := by linarith
    have hσ1 : (1 / 2 + s.re) / 2 ≤ 1 := by linarith
    have hT := (TR _ hσ0 hσ1 (-s) (by rw [Complex.neg_re]; linarith)).1
    have hB := (BR (-s) (by rw [Complex.neg_re]; linarith)).1
    have hadd := (hasMellin_add hT hB).2
    simp only [topPart_add_botPart] at hadd
    rw [hFR s h0 h1, ← mellin_fractSeries ha (by linarith) h1 (hR s.re h0)]
    exact hadd
  have hLid : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → F s = Tl s + Bl s := by
    intro s h0 h1
    have hσ0 : (0 : ℝ) ≤ (s.re + 1 / 2) / 2 := by linarith
    have hσ1 : (s.re + 1 / 2) / 2 < 1 / 2 := by linarith
    have hT := (TL (-s) (by rw [Complex.neg_re]; linarith)).1
    have hB := (BL _ hσ0 hσ1 (-s) (by rw [Complex.neg_re]; linarith)).1
    have hadd := (hasMellin_add hT hB).2
    simp only [topPart_add_botPart] at hadd
    rw [hFL s h0 h1, ← mellin_fractSeries hq h0 (by linarith) (hL s.re h1)]
    exact hadd
  -- differentiability of the pieces
  have dTr : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ Tr s := by
    intro s hs
    have hσ0 : 1 / 2 < min 1 ((1 / 2 + s.re) / 2) := lt_min (by norm_num) (by linarith)
    have hlt : min 1 ((1 / 2 + s.re) / 2) < s.re :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact ((TR _ hσ0 (min_le_left _ _) (-s) (by rw [Complex.neg_re]; linarith)).2.1).comp s
      differentiableAt_id.neg
  have dTl : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Tl s := fun s hs =>
    ((TL (-s) (by rw [Complex.neg_re]; linarith)).2.1).comp s differentiableAt_id.neg
  have dBr : ∀ s : ℂ, s.re < 1 → DifferentiableAt ℂ Br s := fun s hs =>
    ((BR (-s) (by rw [Complex.neg_re]; linarith)).2.1).comp s differentiableAt_id.neg
  have dBl : ∀ s : ℂ, s.re < 1 / 2 → DifferentiableAt ℂ Bl s := by
    intro s hs
    have hσ0 : (0 : ℝ) ≤ max 0 ((s.re + 1 / 2) / 2) := le_max_left _ _
    have hσ1 : max 0 ((s.re + 1 / 2) / 2) < 1 / 2 := max_lt (by norm_num) (by linarith)
    have hlt : s.re < max 0 ((s.re + 1 / 2) / 2) :=
      lt_of_lt_of_le (by linarith) (le_max_right _ _)
    exact ((BL _ hσ0 hσ1 (-s) (by rw [Complex.neg_re]; linarith)).2.1).comp s
      differentiableAt_id.neg
  -- bounds of the pieces
  have nTr : ∀ s : ℂ, 5 / 8 < s.re → ‖Tr s‖ ≤ A / (s.re - 5 / 8) := by
    intro s hs
    have h := (TR (5 / 8) (by norm_num) (by norm_num) (-s) (by rw [Complex.neg_re]; linarith)).2.2
    rwa [Complex.neg_re, show -(5 / 8 : ℝ) - -s.re = s.re - 5 / 8 by ring] at h
  have nTl : ∀ s : ℂ, 0 < s.re → ‖Tl s‖ ≤ B₀ / s.re := by
    intro s hs
    have h := (TL (-s) (by rw [Complex.neg_re]; linarith)).2.2
    rwa [Complex.neg_re, show -(0 : ℝ) - -s.re = s.re by ring] at h
  have nBr : ∀ s : ℂ, s.re < 1 → ‖Br s‖ ≤ A₁ / (1 - s.re) := by
    intro s hs
    have h := (BR (-s) (by rw [Complex.neg_re]; linarith)).2.2
    rwa [Complex.neg_re, show -s.re + 1 = 1 - s.re by ring] at h
  have nBl : ∀ s : ℂ, s.re < 3 / 8 → ‖Bl s‖ ≤ B' / (3 / 8 - s.re) := by
    intro s hs
    have h := (BL (3 / 8) (by norm_num) (by norm_num) (-s) (by rw [Complex.neg_re]; linarith)).2.2
    rwa [Complex.neg_re, show -s.re + 3 / 8 = 3 / 8 - s.re by ring] at h
  -- the glued function
  set E : ℂ → ℂ := fun s =>
    if 3 / 4 ≤ s.re then Tr s - Tl s else if s.re ≤ 1 / 4 then Bl s - Br s
      else F s - Br s - Tl s with hE
  have hE_right : ∀ s : ℂ, 1 / 2 < s.re → E s = Tr s - Tl s := by
    intro s hs
    simp only [hE]
    by_cases h1 : 3 / 4 ≤ s.re
    · rw [if_pos h1]
    · rw [if_neg h1, if_neg (by linarith), hRid s hs (by linarith)]
      ring
  have hE_left : ∀ s : ℂ, s.re < 1 / 2 → E s = Bl s - Br s := by
    intro s hs
    simp only [hE]
    by_cases h1 : s.re ≤ 1 / 4
    · rw [if_neg (by linarith), if_pos h1]
    · rw [if_neg (by linarith), if_neg h1, hLid s (by linarith) hs]
      ring
  have hE_mid : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → E s = F s - Br s - Tl s := by
    intro s h0 h1
    simp only [hE]
    rw [if_neg (by linarith), if_neg (by linarith)]
  have hEd : Differentiable ℂ E := by
    intro s
    rcases lt_trichotomy s.re (1 / 2) with hs | hs | hs
    · have hopen : {w : ℂ | w.re < 1 / 2} ∈ 𝓝 s :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs
      refine ((dBl s hs).sub (dBr s (by linarith))).congr_of_eventuallyEq ?_
      filter_upwards [hopen] with w hw
      exact hE_left w hw
    · have hopen : {w : ℂ | 1 / 4 < w.re ∧ w.re < 3 / 4} ∈ 𝓝 s :=
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
          ⟨by show (1 : ℝ) / 4 < s.re; rw [hs]; norm_num,
            by show s.re < 3 / 4; rw [hs]; norm_num⟩
      have hstrip : {w : ℂ | 0 < w.re ∧ w.re < 1} ∈ 𝓝 s :=
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
          ⟨by show (0 : ℝ) < s.re; rw [hs]; norm_num,
            by show s.re < 1; rw [hs]; norm_num⟩
      refine (((hFd.differentiableAt hstrip).sub (dBr s (by linarith))).sub
        (dTl s (by linarith))).congr_of_eventuallyEq ?_
      filter_upwards [hopen] with w hw
      exact hE_mid w hw.1 hw.2
    · have hopen : {w : ℂ | 1 / 2 < w.re} ∈ 𝓝 s :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
      refine ((dTr s hs).sub (dTl s (by linarith))).congr_of_eventuallyEq ?_
      filter_upwards [hopen] with w hw
      exact hE_right w hw
  -- the glued function is bounded
  have hEb : ∀ s : ℂ, ‖E s‖ ≤ 8 * A + 4 * B₀ + 4 * A₁ + 8 * B' + |K| := by
    intro s
    have hK := le_abs_self K
    have hK0 := abs_nonneg K
    by_cases h1 : 3 / 4 ≤ s.re
    · rw [hE_right s (by linarith)]
      have t1 : ‖Tr s‖ ≤ 8 * A := (nTr s (by linarith)).trans (by
        rw [div_le_iff₀ (by linarith)]
        nlinarith)
      have t2 : ‖Tl s‖ ≤ 4 * B₀ := (nTl s (by linarith)).trans (by
        rw [div_le_iff₀ (by linarith)]
        nlinarith)
      linarith [norm_sub_le (Tr s) (Tl s)]
    · by_cases h2 : s.re ≤ 1 / 4
      · rw [hE_left s (by linarith)]
        have t1 : ‖Bl s‖ ≤ 8 * B' := (nBl s (by linarith)).trans (by
          rw [div_le_iff₀ (by linarith)]
          nlinarith)
        have t2 : ‖Br s‖ ≤ 4 * A₁ := (nBr s (by linarith)).trans (by
          rw [div_le_iff₀ (by linarith)]
          nlinarith)
        linarith [norm_sub_le (Bl s) (Br s)]
      · have h1' : s.re < 3 / 4 := not_le.mp h1
        have h2' : 1 / 4 < s.re := not_le.mp h2
        rw [hE_mid s h2' h1']
        have t0 := hFb s h2'.le h1'.le
        have t1 : ‖Br s‖ ≤ 4 * A₁ := (nBr s (by linarith)).trans (by
          rw [div_le_iff₀ (by linarith)]
          nlinarith)
        have t2 : ‖Tl s‖ ≤ 4 * B₀ := (nTl s (by linarith)).trans (by
          rw [div_le_iff₀ (by linarith)]
          nlinarith)
        linarith [norm_sub_le (F s - Br s) (Tl s), norm_sub_le (F s) (Br s)]
  -- Liouville: the glued function vanishes
  have hEzero : ∀ s : ℂ, E s = 0 := by
    intro s
    have hbdd : Bornology.IsBounded (range E) :=
      isBounded_iff_forall_norm_le.mpr ⟨_, by rintro _ ⟨w, rfl⟩; exact hEb w⟩
    by_contra hne
    have hpos : 0 < ‖E s‖ := norm_pos_iff.mpr hne
    set x : ℝ := max 2 ((2 * A + B₀) / ‖E s‖ + 1) with hx
    have hx2 : (2 : ℝ) ≤ x := le_max_left _ _
    have hxbig : (2 * A + B₀) / ‖E s‖ < x :=
      lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
    have hconst : E s = E (x : ℂ) := hEd.apply_eq_apply_of_bounded hbdd s x
    have hre : ((x : ℂ)).re = x := Complex.ofReal_re x
    have t1 : ‖Tr (x : ℂ)‖ ≤ 2 * A / x := (nTr _ (by rw [hre]; linarith)).trans (by
      rw [hre, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith)
    have t2 : ‖Tl (x : ℂ)‖ ≤ B₀ / x := by
      have := nTl (x : ℂ) (by rw [hre]; linarith)
      rwa [hre] at this
    have t3 : ‖E s‖ ≤ (2 * A + B₀) / x := by
      rw [hconst, hE_right _ (by rw [hre]; linarith), add_div]
      linarith [norm_sub_le (Tr (x : ℂ)) (Tl (x : ℂ))]
    rw [div_lt_iff₀ hpos] at hxbig
    rw [le_div_iff₀ (by linarith)] at t3
    nlinarith
  have hTop : ∀ s : ℂ, 1 / 2 < s.re → Tr s = Tl s := fun s hs =>
    sub_eq_zero.mp ((hE_right s hs).symm.trans (hEzero s))
  have hBot : ∀ s : ℂ, s.re < 1 / 2 → Bl s = Br s := fun s hs =>
    sub_eq_zero.mp ((hE_left s hs).symm.trans (hEzero s))
  -- Mellin inversion at the points of continuity
  have hinv : ∀ x : ℝ, 0 < x → x ≠ 1 →
      ContinuousAt (fun u => fractSeries b a u - fractSeries c q u) x →
      fractSeries b a x = fractSeries c q x := by
    intro x hx hx1 hcont
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · -- `x < 1`: the lower parts, on the line `Re z = −1/4`
      set f : ℝ → ℂ := fun u => botPart (fractSeries b a) u - botPart (fractSeries c q) u with hf
      have hc1 := fun z (hz : -1 < z.re) => (BR z hz).1
      have hc2 := fun z (hz : -(3 / 8 : ℝ) < z.re) =>
        (BL (3 / 8) (by norm_num) (by norm_num) z hz).1
      have hzero : ∀ y : ℝ, mellin f (((-1 / 4 : ℝ) : ℂ) + y * Complex.I) = 0 := by
        intro y
        have hre : (((-1 / 4 : ℝ) : ℂ) + y * Complex.I).re = -1 / 4 := by simp
        rw [hf, (hasMellin_sub (hc1 _ (by rw [hre]; norm_num)) (hc2 _ (by rw [hre]; norm_num))).2]
        have h := hBot (-(((-1 / 4 : ℝ) : ℂ) + y * Complex.I)) (by
          rw [Complex.neg_re, hre]
          norm_num)
        simp only [hBl, hBr, neg_neg] at h
        rw [h, sub_self]
      have hconv : MellinConvergent f ((-1 / 4 : ℝ) : ℂ) :=
        (hasMellin_sub (hc1 _ (by rw [Complex.ofReal_re]; norm_num))
          (hc2 _ (by rw [Complex.ofReal_re]; norm_num))).1
      have hvert : Complex.VerticalIntegrable (mellin f) (-1 / 4) :=
        (integrable_zero ℝ ℂ volume).congr (Eventually.of_forall fun y => (hzero y).symm)
      have hfc : ContinuousAt f x := by
        refine hcont.congr ?_
        filter_upwards [Iio_mem_nhds hlt] with w hw
        show fractSeries b a w - fractSeries c q w =
          botPart (fractSeries b a) w - botPart (fractSeries c q) w
        rw [botPart_of_le (le_of_lt hw), botPart_of_le (le_of_lt hw)]
      have h := mellinInv_mellin_eq (-1 / 4) f hx hconv hvert hfc
      have h0 : mellinInv (-1 / 4) (mellin f) x = 0 := by
        simp only [mellinInv, hzero, smul_zero, integral_zero]
      rw [h0] at h
      have h' : (0 : ℂ) = botPart (fractSeries b a) x - botPart (fractSeries c q) x := h
      rw [botPart_of_le hlt.le, botPart_of_le hlt.le] at h'
      exact sub_eq_zero.mp h'.symm
    · -- `x > 1`: the upper parts, on the line `Re z = −3/4`
      set f : ℝ → ℂ := fun u => topPart (fractSeries b a) u - topPart (fractSeries c q) u with hf
      have hc1 := fun z (hz : z.re < -(5 / 8 : ℝ)) =>
        (TR (5 / 8) (by norm_num) (by norm_num) z hz).1
      have hc2 := fun z (hz : z.re < 0) => (TL z hz).1
      have hzero : ∀ y : ℝ, mellin f (((-3 / 4 : ℝ) : ℂ) + y * Complex.I) = 0 := by
        intro y
        have hre : (((-3 / 4 : ℝ) : ℂ) + y * Complex.I).re = -3 / 4 := by simp
        rw [hf, (hasMellin_sub (hc1 _ (by rw [hre]; norm_num)) (hc2 _ (by rw [hre]; norm_num))).2]
        have h := hTop (-(((-3 / 4 : ℝ) : ℂ) + y * Complex.I)) (by
          rw [Complex.neg_re, hre]
          norm_num)
        simp only [hTr, hTl, neg_neg] at h
        rw [h, sub_self]
      have hconv : MellinConvergent f ((-3 / 4 : ℝ) : ℂ) :=
        (hasMellin_sub (hc1 _ (by rw [Complex.ofReal_re]; norm_num))
          (hc2 _ (by rw [Complex.ofReal_re]; norm_num))).1
      have hvert : Complex.VerticalIntegrable (mellin f) (-3 / 4) :=
        (integrable_zero ℝ ℂ volume).congr (Eventually.of_forall fun y => (hzero y).symm)
      have hfc : ContinuousAt f x := by
        refine hcont.congr ?_
        filter_upwards [Ioi_mem_nhds hgt] with w hw
        show fractSeries b a w - fractSeries c q w =
          topPart (fractSeries b a) w - topPart (fractSeries c q) w
        rw [topPart_of_lt hw, topPart_of_lt hw]
      have h := mellinInv_mellin_eq (-3 / 4) f hx hconv hvert hfc
      have h0 : mellinInv (-3 / 4) (mellin f) x = 0 := by
        simp only [mellinInv, hzero, smul_zero, integral_zero]
      rw [h0] at h
      have h' : (0 : ℂ) = topPart (fractSeries b a) x - topPart (fractSeries c q) x := h
      rw [topPart_of_lt hgt, topPart_of_lt hgt] at h'
      exact sub_eq_zero.mp h'.symm
  -- points of continuity are dense; both series are right continuous
  have hbad : ({u : ℝ | ∃ i, ∃ n : ℤ, a i * u = n} ∪ {u : ℝ | ∃ j, ∃ n : ℤ, q j * u = n} ∪
      {1}).Countable :=
    ((countable_jumpSet ha).union (countable_jumpSet hq)).union (countable_singleton 1)
  have hfreq : ∃ᶠ x in 𝓝[>] u, fractSeries b a x = fractSeries c q x := by
    refine ((frequently_nhdsGT_notMem hbad u).and_eventually self_mem_nhdsWithin).mono ?_
    rintro x ⟨hx, hxu⟩
    have hx0 : 0 < x := hu.trans hxu
    have hR1 : ∀ i, b i ≠ 0 → ∀ n : ℤ, a i * x ≠ n := fun i _ n hn =>
      hx (Or.inl (Or.inl ⟨i, n, hn⟩))
    have hL1 : ∀ j, c j ≠ 0 → ∀ n : ℤ, q j * x ≠ n := fun j _ n hn =>
      hx (Or.inl (Or.inr ⟨j, n, hn⟩))
    have hx1 : x ≠ 1 := fun h => hx (Or.inr h)
    exact hinv x hx0 hx1
      ((continuousAt_fractSeries ha zero_le_one le_rfl (hR 1 (by norm_num)) hx0 hR1).sub
        (continuousAt_fractSeries hq le_rfl zero_le_one (hL 0 (by norm_num)) hx0 hL1))
  exact tendsto_nhds_unique_of_frequently_eq
    (tendsto_fractSeries_right ha zero_le_one le_rfl (hR 1 (by norm_num)) hu)
    (tendsto_fractSeries_right hq le_rfl zero_le_one (hL 0 (by norm_num)) hu) hfreq

open scoped Classical in
/-- **The jump law.** Under the hypotheses of `fractSeries_eq` the two series have the same jump
at every `u₀ > 0`: the weight of the indices with `a_i u₀` an integer equals the weight of the
indices with `q_j u₀` an integer. -/
theorem tsum_jump_eq [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    (∑' i, if ∃ n : ℤ, a i * u₀ = n then b i else 0) =
      ∑' j, if ∃ n : ℤ, q j * u₀ = n then c j else 0 := by
  have heq : ∀ u : ℝ, 0 < u → fractSeries b a u = fractSeries c q u := fun u hu =>
    fractSeries_eq ha hq hR hL hFd hFb hFR hFL hu
  have hl1 := tendsto_fractSeries_left ha zero_le_one le_rfl (hR 1 (by norm_num)) hu₀
  have hl2 := tendsto_fractSeries_left hq le_rfl zero_le_one (hL 0 (by norm_num)) hu₀
  have hev : ∀ᶠ u in 𝓝[<] u₀, fractSeries b a u = fractSeries c q u := by
    filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
    exact heq u hu.1
  have hlim := tendsto_nhds_unique_of_frequently_eq hl1 hl2 hev.frequently
  have j1 := fractSeries_sub_leftLimit ha zero_le_one le_rfl (hR 1 (by norm_num)) hu₀
  have j2 := fractSeries_sub_leftLimit hq le_rfl zero_le_one (hL 0 (by norm_num)) hu₀
  rw [heq u₀ hu₀, hlim, j2] at j1
  exact neg_injective j1.symm

/-! ### Möbius inversion of the jump law -/

theorem sum_divisors_moebius (n : ℕ) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] at h
  exact h

/-- For `q > 0` and an integer `k ≥ 1`, `q/k` is an integer exactly when `q` is a natural number
divisible by `k`. -/
theorem exists_int_mul_inv_iff {q : ℝ} (hq : 0 < q) {k : ℕ} (hk : 1 ≤ k) :
    (∃ m : ℤ, q * (1 / (k : ℝ)) = m) ↔ ∃ n : ℕ, q = n ∧ k ∣ n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨m, hm⟩
    have hqm : q = m * k := by
      rw [mul_one_div, div_eq_iff hk0.ne'] at hm
      exact hm
    have hmpos : (0 : ℝ) < m := by
      by_contra h
      have h' : (m : ℝ) ≤ 0 := not_lt.mp h
      nlinarith
    have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast hmpos.le
    have hcast : ((m.toNat : ℕ) : ℝ) = m := by
      have h := Int.toNat_of_nonneg hm0
      exact_mod_cast h
    refine ⟨m.toNat * k, ?_, dvd_mul_left _ _⟩
    rw [hqm]
    push_cast
    rw [hcast]
  · rintro ⟨n, rfl, d, rfl⟩
    refine ⟨d, ?_⟩
    push_cast
    field_simp

/-- For `0 < a ≤ 1` and an integer `k ≥ 1`, `a/k` is an integer only for `a = k = 1`. -/
theorem exists_int_mul_inv_iff_of_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {k : ℕ}
    (hk : 1 ≤ k) : (∃ m : ℤ, a * (1 / (k : ℝ)) = m) ↔ k = 1 ∧ a = 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  constructor
  · rintro ⟨m, hm⟩
    have ham : a = m * k := by
      rw [mul_one_div, div_eq_iff hk0.ne'] at hm
      exact hm
    have hmpos : (0 : ℝ) < m := by
      by_contra h
      have h' : (m : ℝ) ≤ 0 := not_lt.mp h
      nlinarith
    have hm1 : (1 : ℝ) ≤ m := by
      have : (0 : ℤ) < m := by exact_mod_cast hmpos
      exact_mod_cast this
    have hk' : (k : ℝ) = 1 := by nlinarith
    refine ⟨by exact_mod_cast hk', ?_⟩
    nlinarith
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, by norm_num⟩

open scoped Classical in
/-- **Möbius inversion of a divisibility law.** For a summable family with positive scales `q_j`,
if the weight of the scales that are natural numbers divisible by `k` is `β` for `k = 1` and `0`
for `k ≥ 2`, then the weight at the scale `1` is `β`. -/
theorem tsum_eq_of_tsum_dvd [Countable κ] {c : κ → ℂ} {q : κ → ℝ} (hq0 : ∀ j, 0 < q j)
    (hcsum : Summable fun j => ‖c j‖) (hc4 : Summable fun j => ‖c j‖ * q j ^ (1 / 4 : ℝ)) {β : ℂ}
    (hS : ∀ k : ℕ, 1 ≤ k →
      (∑' j, if (∃ n : ℕ, q j = n ∧ k ∣ n) then c j else 0) = if k = 1 then β else 0) :
    (∑' j, if q j = 1 then c j else 0) = β := by
  -- truncated Möbius sums
  set e : ℕ → κ → ℂ := fun N j => ∑ k ∈ Finset.Icc 1 N,
    if (∃ n : ℕ, q j = n ∧ k ∣ n) then ((ArithmeticFunction.moebius k : ℤ) : ℂ) else 0 with he
  have hsumk : ∀ k : ℕ, Summable fun j => (if (∃ n : ℕ, q j = n ∧ k ∣ n) then c j else 0 : ℂ) :=
    fun k => Summable.of_norm_bounded hcsum fun j => by
      split_ifs
      · exact le_rfl
      · rw [norm_zero]
        exact norm_nonneg _
  have hAN : ∀ N : ℕ, 1 ≤ N → (∑' j, c j * e N j) = β := by
    intro N hN
    have hterm : ∀ j, c j * e N j = ∑ k ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius k : ℤ) : ℂ) *
          (if (∃ n : ℕ, q j = n ∧ k ∣ n) then c j else 0) := by
      intro j
      simp only [he]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    rw [tsum_congr hterm, Summable.tsum_finsetSum fun k _ => (hsumk k).mul_left _]
    have hk : ∀ k ∈ Finset.Icc 1 N, (∑' j, ((ArithmeticFunction.moebius k : ℤ) : ℂ) *
        (if (∃ n : ℕ, q j = n ∧ k ∣ n) then c j else 0)) =
        ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (if k = 1 then β else 0) := fun k hk => by
      rw [tsum_mul_left, hS k (Finset.mem_Icc.mp hk).1]
    rw [Finset.sum_congr rfl hk, Finset.sum_eq_single 1]
    · simp
    · intro k _ hk1
      rw [if_neg hk1, mul_zero]
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) h
  -- the truncated sums on a natural number
  have hform : ∀ (N : ℕ) (j : κ) (n : ℕ), q j = n → e N j =
      ∑ k ∈ (Finset.Icc 1 N).filter (· ∣ n), ((ArithmeticFunction.moebius k : ℤ) : ℂ) := by
    intro N j n hn
    simp only [he]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hd : k ∣ n
    · rw [if_pos ⟨n, hn, hd⟩, if_pos hd]
    · rw [if_neg hd, if_neg]
      rintro ⟨n', hn', hd'⟩
      have hnn : n' = n := by exact_mod_cast hn'.symm.trans hn
      exact hd (hnn ▸ hd')
  have hzero : ∀ (N : ℕ) (j : κ), (¬∃ n : ℕ, q j = n) → e N j = 0 := by
    intro N j hnat
    simp only [he]
    exact Finset.sum_eq_zero fun k _ => if_neg fun ⟨n, hn, _⟩ => hnat ⟨n, hn⟩
  have hpos_of : ∀ (j : κ) (n : ℕ), q j = n → n ≠ 0 := by
    rintro j n hn rfl
    have := hq0 j
    rw [hn, Nat.cast_zero] at this
    exact lt_irrefl _ this
  set C : ℝ := _root_.RHTower.Sieve.divisorBoundConst (1 / 4) with hC
  have hCpos : 0 < C := _root_.RHTower.Sieve.divisorBoundConst_pos (by norm_num)
  have hebound : ∀ N j, ‖e N j‖ ≤ C * q j ^ (1 / 4 : ℝ) := by
    intro N j
    by_cases hnat : ∃ n : ℕ, q j = n
    · obtain ⟨n, hn⟩ := hnat
      have hn0 := hpos_of j n hn
      rw [hform N j n hn]
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∀ k ∈ (Finset.Icc 1 N).filter (· ∣ n),
          ‖((ArithmeticFunction.moebius k : ℤ) : ℂ)‖ ≤ 1 := fun k _ => by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      refine (Finset.sum_le_card_nsmul _ _ 1 h1).trans ?_
      rw [nsmul_eq_mul, mul_one]
      have hsub : (Finset.Icc 1 N).filter (· ∣ n) ⊆ n.divisors := fun k hk =>
        Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hk).2, hn0⟩
      refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ?_
      rw [hn]
      exact _root_.RHTower.Sieve.card_divisors_le_rpow (by norm_num) hn0
    · rw [hzero N j hnat, norm_zero]
      exact mul_nonneg hCpos.le (Real.rpow_nonneg (hq0 j).le _)
  have hlim : Tendsto (fun N : ℕ => ∑' j, c j * e N j) atTop
      (𝓝 (∑' j, if q j = 1 then c j else 0)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun j => C * (‖c j‖ * q j ^ (1 / 4 : ℝ)))
      (hc4.mul_left C) (fun j => ?_) (Eventually.of_forall fun N j => ?_)
    · by_cases hnat : ∃ n : ℕ, q j = n
      · obtain ⟨n, hn⟩ := hnat
        have hn0 := hpos_of j n hn
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with N hN
        have hfin : (Finset.Icc 1 N).filter (· ∣ n) = n.divisors := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨_, hd⟩
            exact ⟨hd, hn0⟩
          · rintro ⟨hd, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn0),
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd).trans hN⟩, hd⟩
        rw [hform N j n hn, hfin, sum_divisors_moebius]
        by_cases hn1 : n = 1
        · rw [if_pos hn1, mul_one, if_pos (by rw [hn, hn1]; norm_num)]
        · rw [if_neg hn1, mul_zero, if_neg]
          intro h1
          rw [hn] at h1
          exact hn1 (by exact_mod_cast h1)
      · have h1 : q j ≠ 1 := fun h => hnat ⟨1, by rw [h]; norm_num⟩
        rw [if_neg h1]
        refine tendsto_const_nhds.congr fun N => ?_
        rw [hzero N j hnat, mul_zero]
    · rw [norm_mul]
      calc ‖c j‖ * ‖e N j‖ ≤ ‖c j‖ * (C * q j ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hebound N j) (norm_nonneg _)
        _ = C * (‖c j‖ * q j ^ (1 / 4 : ℝ)) := by ring
  refine tendsto_nhds_unique hlim ((tendsto_const_nhds (x := β)).congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (hAN N hN).symm


/-- **The constant terms on the two sides of the line agree.** Let `Σ b_i a_i^s`, `0 < a_i ≤ 1`,
converge absolutely right of the critical line and `Σ c_j q_j^s`, `q_j ≥ 1`, left of it, and let
`F` be holomorphic on the strip, bounded near the line, equal to `−ζ(s)/s` times the first sum
right of the line and times the second left of it. Then the weight at `q = 1` equals the weight
at `a = 1`. -/
theorem constantTerms_agree [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) (hq : ∀ j, 1 ≤ q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s) :
    (∑' j, if q j = 1 then c j else 0) = ∑' i, if a i = 1 then b i else 0 := by
  classical
  have hq0 : ∀ j, 0 < q j := fun j => lt_of_lt_of_le one_pos (hq j)
  set β : ℂ := ∑' i, if a i = 1 then b i else 0 with hβ
  -- the jump law at `1/k`
  have hS : ∀ k : ℕ, 1 ≤ k →
      (∑' j, if (∃ n : ℕ, q j = n ∧ k ∣ n) then c j else 0) = if k = 1 then β else 0 := by
    intro k hk
    have hk0 : (0 : ℝ) < 1 / (k : ℝ) := by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    have h := tsum_jump_eq ha0 hq0 hR hL hFd hFb hFR hFL hk0
    have hl : (∑' i, if ∃ n : ℤ, a i * (1 / (k : ℝ)) = n then b i else 0) =
        if k = 1 then β else 0 := by
      by_cases hk1 : k = 1
      · rw [if_pos hk1, hβ]
        refine tsum_congr fun i => ?_
        by_cases hai : a i = 1
        · rw [if_pos ((exists_int_mul_inv_iff_of_le_one (ha0 i) (ha1 i) hk).mpr ⟨hk1, hai⟩),
            if_pos hai]
        · rw [if_neg fun h' => hai ((exists_int_mul_inv_iff_of_le_one (ha0 i) (ha1 i) hk).mp h').2,
            if_neg hai]
      · rw [if_neg hk1]
        refine (tsum_congr fun i => ?_).trans tsum_zero
        exact if_neg fun h' => hk1 ((exists_int_mul_inv_iff_of_le_one (ha0 i) (ha1 i) hk).mp h').1
    rw [← hl, h]
    refine tsum_congr fun j => ?_
    by_cases hj : ∃ n : ℕ, q j = n ∧ k ∣ n
    · rw [if_pos hj, if_pos ((exists_int_mul_inv_iff (hq0 j) hk).mpr hj)]
    · rw [if_neg hj, if_neg fun h' => hj ((exists_int_mul_inv_iff (hq0 j) hk).mp h')]
  have hcsum : Summable fun j => ‖c j‖ := by
    have h := hL 0 (by norm_num)
    simpa only [Real.rpow_zero, mul_one] using h
  exact tsum_eq_of_tsum_dvd hq0 hcsum (hL (1 / 4) (by norm_num)) hS

/-! ### Rigidity: the two expansions are constant -/

/-- **The left expansion carries no weight off the scale one.** The jump law at the points
`1/(kt)`, `t > 1`, where the right series has no jump, and Möbius inversion over `k`. -/
theorem tsum_scale_eq_zero [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) (hq : ∀ j, 1 ≤ q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {t : ℝ} (ht : 1 < t) : (∑' j, if q j = t then c j else 0) = 0 := by
  classical
  have ht0 : 0 < t := lt_trans one_pos ht
  have hq0 : ∀ j, 0 < q j := fun j => lt_of_lt_of_le one_pos (hq j)
  have hq' : ∀ j, 0 < q j / t := fun j => div_pos (hq0 j) ht0
  have hcsum : Summable fun j => ‖c j‖ := by
    have h := hL 0 (by norm_num)
    simpa only [Real.rpow_zero, mul_one] using h
  have hc4 : Summable fun j => ‖c j‖ * (q j / t) ^ (1 / 4 : ℝ) := by
    refine ((hL (1 / 4) (by norm_num)).div_const (t ^ (1 / 4 : ℝ))).congr fun j => ?_
    rw [Real.div_rpow (hq0 j).le ht0.le, mul_div_assoc]
  have hS : ∀ k : ℕ, 1 ≤ k →
      (∑' j, if (∃ n : ℕ, q j / t = n ∧ k ∣ n) then c j else 0) = if k = 1 then (0 : ℂ) else 0 := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hu : (0 : ℝ) < 1 / t * (1 / (k : ℝ)) := by positivity
    have h := tsum_jump_eq ha0 hq0 hR hL hFd hFb hFR hFL hu
    have hl : (∑' i, if ∃ n : ℤ, a i * (1 / t * (1 / (k : ℝ))) = n then b i else 0) = 0 := by
      refine (tsum_congr fun i => if_neg ?_).trans tsum_zero
      rintro ⟨n, hn⟩
      have hpos : 0 < a i * (1 / t * (1 / (k : ℝ))) := mul_pos (ha0 i) hu
      have hlt : a i * (1 / t * (1 / (k : ℝ))) < 1 := by
        have h1t : 1 / t < 1 := by
          rw [div_lt_one ht0]
          exact ht
        have h1k : 1 / (k : ℝ) ≤ 1 := by
          rw [div_le_one hk0]
          exact_mod_cast hk
        have h1 : 1 / t * (1 / (k : ℝ)) < 1 := by
          nlinarith [one_div_pos.mpr ht0, one_div_pos.mpr hk0]
        calc a i * (1 / t * (1 / (k : ℝ))) ≤ 1 * (1 / t * (1 / (k : ℝ))) :=
              mul_le_mul_of_nonneg_right (ha1 i) hu.le
          _ < 1 := by
              rw [one_mul]
              exact h1
      rw [hn] at hpos hlt
      have hn0 : (0 : ℤ) < n := by exact_mod_cast hpos
      have hn1 : n < (1 : ℤ) := by exact_mod_cast hlt
      omega
    have key : (∑' j, if ∃ n : ℤ, q j * (1 / t * (1 / (k : ℝ))) = n then c j else 0) = 0 :=
      h.symm.trans hl
    rw [ite_self]
    refine (tsum_congr fun j => ?_).trans key
    have hiff : (∃ n : ℤ, q j * (1 / t * (1 / (k : ℝ))) = n) ↔ ∃ n : ℕ, q j / t = n ∧ k ∣ n := by
      rw [← exists_int_mul_inv_iff (hq' j) hk,
        show q j * (1 / t * (1 / (k : ℝ))) = q j / t * (1 / (k : ℝ)) by ring]
    by_cases hj : ∃ n : ℕ, q j / t = n ∧ k ∣ n
    · rw [if_pos hj, if_pos (hiff.mpr hj)]
    · rw [if_neg hj, if_neg fun h' => hj (hiff.mp h')]
  have hmain := tsum_eq_of_tsum_dvd hq' hcsum hc4 hS
  refine (tsum_congr fun j => ?_).trans hmain
  by_cases hj : q j = t
  · rw [if_pos hj, if_pos (by rw [hj, div_self ht0.ne'])]
  · rw [if_neg hj, if_neg fun h' => hj ((div_eq_one_iff_eq ht0.ne').mp h')]

/-- A sum over a family is the sum over the scales of the weight at the scale. -/
theorem hasSum_scale_mul (q : κ → ℝ) (c : κ → ℂ) (g : ℝ → ℂ)
    (h : Summable fun j => c j * g (q j)) :
    HasSum (fun t : ℝ => (∑' j, if q j = t then c j else 0) * g t) (∑' j, c j * g (q j)) := by
  classical
  have hfib := h.hasSum.tsum_fiberwise q
  have hinner : ∀ t : ℝ, (∑' j : q ⁻¹' {t}, c j * g (q j)) =
      (∑' j, if q j = t then c j else 0) * g t := by
    intro t
    have h1 : (∑' j, if q j = t then c j else 0) = ∑' j : q ⁻¹' {t}, c j := by
      rw [tsum_subtype (q ⁻¹' {t}) c]
      refine tsum_congr fun j => ?_
      rw [Set.indicator_apply]
      by_cases hj : q j = t
      · rw [if_pos hj, if_pos (show j ∈ q ⁻¹' {t} from hj)]
      · rw [if_neg hj, if_neg (show j ∉ q ⁻¹' {t} from hj)]
    rw [h1, ← tsum_mul_right]
    exact tsum_congr fun j => by rw [show q j = t from j.2]
  simpa only [hinner] using hfib

/-- **The left expansion is constant**: `Σ c_j q_j^s` is the weight at the scale one. -/
theorem tsum_left_eq_const [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) (hq : ∀ j, 1 ≤ q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {s : ℂ} (h1 : s.re < 1 / 2) :
    (∑' j, c j * (q j : ℂ) ^ s) = ∑' j, if q j = 1 then c j else 0 := by
  have hq0 : ∀ j, 0 < q j := fun j => lt_of_lt_of_le one_pos (hq j)
  have hsum : Summable fun j => c j * (q j : ℂ) ^ s := by
    refine Summable.of_norm ((hL s.re h1).congr fun j => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hq0 j)]
  have h := hasSum_scale_mul q c (fun t : ℝ => (t : ℂ) ^ s) hsum
  rw [← h.tsum_eq, tsum_eq_single (1 : ℝ)]
  · rw [Complex.ofReal_one, Complex.one_cpow, mul_one]
  · intro t ht
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · have hz : (∑' j, if q j = t then c j else 0) = 0 :=
        (tsum_congr fun j => if_neg fun hj => by
          have := hq j
          rw [hj] at this
          linarith).trans tsum_zero
      rw [hz, zero_mul]
    · rw [tsum_scale_eq_zero ha0 ha1 hq hR hL hFd hFb hFR hFL hgt, zero_mul]

/-- **Rigidity.** A function on the strip that is `−ζ(s)/s` times a Dirichlet expansion with
scales `≤ 1` right of the line and times one with scales `≥ 1` left of it, holomorphic and bounded
near the line, is `−β ζ(s)/s` with a constant `β`: the critical zeros of `ζ` cancel the poles of
no two-sided expansion other than a constant. -/
theorem eq_const_mul_riemannZeta_div [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) (hq : ∀ j, 1 ≤ q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    F s = -(riemannZeta s / s) * ∑' j, if q j = 1 then c j else 0 := by
  set β : ℂ := ∑' j, if q j = 1 then c j else 0 with hβ
  have hUo : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : IsPreconnected {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hHd : DifferentiableOn ℂ (fun s => -(riemannZeta s / s) * β)
      {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    intro z hz
    have hz1 : z ≠ 1 := fun h => by
      have := hz.2
      rw [h, Complex.one_re] at this
      exact lt_irrefl 1 this
    have hz0 : z ≠ 0 := fun h => by
      have := hz.1
      rw [h, Complex.zero_re] at this
      exact lt_irrefl 0 this
    exact ((((differentiableAt_riemannZeta hz1).div differentiableAt_id hz0).neg).mul_const
      β).differentiableWithinAt
  have hz₀ : ((1 / 4 : ℝ) : ℂ) ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    show (0 : ℝ) < ((1 / 4 : ℝ) : ℂ).re ∧ ((1 / 4 : ℝ) : ℂ).re < 1
    rw [Complex.ofReal_re]
    norm_num
  have hev : F =ᶠ[𝓝 ((1 / 4 : ℝ) : ℂ)] fun s => -(riemannZeta s / s) * β := by
    have hopen : {z : ℂ | 0 < z.re ∧ z.re < 1 / 2} ∈ 𝓝 ((1 / 4 : ℝ) : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by
          show (0 : ℝ) < ((1 / 4 : ℝ) : ℂ).re ∧ ((1 / 4 : ℝ) : ℂ).re < 1 / 2
          rw [Complex.ofReal_re]
          norm_num)
    filter_upwards [hopen] with z hz
    rw [hFL z hz.1 hz.2, tsum_left_eq_const ha0 ha1 hq hR hL hFd hFb hFR hFL hz.2]
  exact (hFd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hHd.analyticOnNhd hUo) hUc
    hz₀ hev ⟨h0, h1⟩

/-! ### Tools for the hypotheses: analytic quotients and good heights -/

/-- **A logarithmic derivative times a function vanishing at the zero has no pole.** -/
theorem meromorphicOrderAt_deriv_mul_div_nonneg {f g : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hg : AnalyticAt ℂ g ρ) (hfin : analyticOrderAt f ρ ≠ ⊤) (hf0 : f ρ = 0) (hg0 : g ρ = 0) :
    0 ≤ meromorphicOrderAt (deriv f * g * f⁻¹) ρ := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h := (hf.analyticOrderAt_ne_zero).mpr hf0
    exact h (by rw [← hm]; rfl)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hford : analyticOrderAt f ρ = ((k + 1 : ℕ) : ℕ∞) := hm.symm
  have hf'ord : analyticOrderAt (deriv f) ρ = (k : ℕ∞) :=
    analyticOrderAt_deriv_of_pos hf (by rw [hford]; push_cast; rfl)
  have hgne : analyticOrderAt g ρ ≠ 0 := (hg.analyticOrderAt_ne_zero).mpr hg0
  rw [meromorphicOrderAt_mul (hf.deriv.meromorphicAt.mul hg.meromorphicAt) hf.meromorphicAt.inv,
    meromorphicOrderAt_mul hf.deriv.meromorphicAt hg.meromorphicAt, meromorphicOrderAt_inv,
    hf.deriv.meromorphicOrderAt_eq, hg.meromorphicOrderAt_eq, hf.meromorphicOrderAt_eq, hford,
    hf'ord]
  induction h : analyticOrderAt g ρ using ENat.recTopCoe with
  | top => simp
  | coe j =>
    have hj : j ≠ 0 := by
      rintro rfl
      exact hgne (by rw [h]; rfl)
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    simp only [ENat.map_coe]
    rw [← WithTop.coe_add, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
      ← WithTop.coe_zero, WithTop.coe_le_coe]
    push_cast
    linarith

/-- **The analytic quotient.** On an open set, if `g` vanishes at the zeros of `f` and `f` is not
locally zero, `g f'/f` extends to a holomorphic function. -/
theorem exists_differentiableOn_deriv_mul_div {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfin : ∀ z ∈ U, analyticOrderAt f z ≠ ⊤) (hzero : ∀ z ∈ U, f z = 0 → g z = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, f z ≠ 0 → F z = deriv f z * g z / f z := by
  have hfa : ∀ z ∈ U, AnalyticAt ℂ f z := fun z hz => hf.analyticAt (hU.mem_nhds hz)
  have hga : ∀ z ∈ U, AnalyticAt ℂ g z := fun z hz => hg.analyticAt (hU.mem_nhds hz)
  set Q : ℂ → ℂ := deriv f * g * f⁻¹ with hQ
  have hmer : MeromorphicOn Q U := fun z hz =>
    ((hfa z hz).deriv.meromorphicAt.mul (hga z hz).meromorphicAt).mul (hfa z hz).meromorphicAt.inv
  have hord : ∀ z ∈ U, 0 ≤ meromorphicOrderAt Q z := by
    intro z hz
    by_cases h0 : f z = 0
    · exact meromorphicOrderAt_deriv_mul_div_nonneg (hfa z hz) (hga z hz) (hfin z hz) h0
        (hzero z hz h0)
    · exact (((hfa z hz).deriv.mul (hga z hz)).mul ((hfa z hz).inv h0)).meromorphicOrderAt_nonneg
  have hNF := meromorphicNFOn_toMeromorphicNFOn Q U
  refine ⟨toMeromorphicNFOn Q U, fun z hz => ?_, fun z hz h0 => ?_⟩
  · have h1 : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn Q U) z := by
      rw [meromorphicOrderAt_toMeromorphicNFOn hmer hz]
      exact hord z hz
    exact ((hNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp h1).differentiableAt.differentiableWithinAt
  · have han : AnalyticAt ℂ Q z := ((hfa z hz).deriv.mul (hga z hz)).mul ((hfa z hz).inv h0)
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmer hz,
      toMeromorphicNFAt_eq_self.mpr han.meromorphicNFAt]
    simp only [hQ, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]

/-- **The maximum principle between good heights.** A function holomorphic near a vertical strip,
bounded by `K` on its two boundary lines and on horizontal segments at heights met in every
interval of length `L`, is bounded by `K` on the strip. -/
theorem norm_le_of_good_heights {F : ℂ → ℂ} {x₁ x₂ : ℝ} (hx : x₁ < x₂) {U : Set ℂ}
    (hsub : ∀ z : ℂ, x₁ ≤ z.re → z.re ≤ x₂ → z ∈ U) (hF : DifferentiableOn ℂ F U) {K L : ℝ}
    (hline : ∀ z : ℂ, z.re = x₁ ∨ z.re = x₂ → ‖F z‖ ≤ K)
    (hgood : ∀ y : ℝ, ∃ T ∈ Icc y (y + L), ∀ z : ℂ, x₁ ≤ z.re → z.re ≤ x₂ → z.im = T →
      ‖F z‖ ≤ K)
    {w : ℂ} (hw1 : x₁ ≤ w.re) (hw2 : w.re ≤ x₂) : ‖F w‖ ≤ K := by
  obtain ⟨T₁, hT₁mem, hT₁⟩ := hgood (w.im - L - 1)
  obtain ⟨T₂, hT₂mem, hT₂⟩ := hgood (w.im + 1)
  have hT₁w : T₁ < w.im := by linarith [hT₁mem.2]
  have hT₂w : w.im < T₂ := by linarith [hT₂mem.1]
  have hT : T₁ < T₂ := hT₁w.trans hT₂w
  have hcl : closure (Ioo x₁ x₂ ×ℂ Ioo T₁ T₂) = Icc x₁ x₂ ×ℂ Icc T₁ T₂ := by
    rw [Complex.closure_reProdIm, closure_Ioo hx.ne, closure_Ioo hT.ne]
  have hclU : closure (Ioo x₁ x₂ ×ℂ Ioo T₁ T₂) ⊆ U := by
    rw [hcl]
    intro z hz
    exact hsub z hz.1.1 hz.1.2
  have hd : DiffContOnCl ℂ F (Ioo x₁ x₂ ×ℂ Ioo T₁ T₂) :=
    ⟨hF.mono (subset_closure.trans hclU), hF.continuousOn.mono hclU⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Ioo x₁ x₂ ×ℂ Ioo T₁ T₂)
    ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)) hd (fun z hz => ?_) ?_
  · rw [Complex.frontier_reProdIm, closure_Ioo hx.ne, closure_Ioo hT.ne, frontier_Ioo hx,
      frontier_Ioo hT] at hz
    rcases hz with ⟨hre, him⟩ | ⟨hre, him⟩
    · rcases him with h | h
      · exact hT₁ z hre.1 hre.2 h
      · exact hT₂ z hre.1 hre.2 h
    · exact hline z hre
  · rw [hcl]
    exact ⟨⟨hw1, hw2⟩, ⟨hT₁w.le, hT₂w.le⟩⟩

end GaloisForLFunctions.InfiniteRankPurityTheory
