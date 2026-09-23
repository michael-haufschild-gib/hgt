import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def cesaroSignThreshold (B L : ℝ) : ℝ :=
  min 1 (L / (2 * (B + 1)))

theorem cesaroSignThreshold_pos {B L : ℝ} (hB : 0 ≤ B) (hL : 0 < L) :
    0 < cesaroSignThreshold B L := by
  rw [cesaroSignThreshold]
  exact lt_min (by norm_num) (div_pos hL (by positivity))

theorem exists_lt_neg_cesaroSignThreshold_of_mean_zero_of_pos_mean_sq
    {b : ℕ → ℝ} {B L : ℝ}
    (hB : ∀ n, |b n| ≤ B)
    (hmean : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n)
      atTop (nhds 0))
    (hmeanSq : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n ^ (2 : ℕ))
      atTop (nhds L))
    (hL : 0 < L) :
    ∃ n : ℕ, b n < -cesaroSignThreshold B L := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (b 0)) (hB 0)
  let δ : ℝ := cesaroSignThreshold B L
  have hden : 0 < 2 * (B + 1) := by positivity
  have hδ : 0 < δ := by
    exact cesaroSignThreshold_pos hB0 hL
  have hδle : δ ≤ 1 := by
    simpa [δ, cesaroSignThreshold] using
      (min_le_left (1 : ℝ) (L / (2 * (B + 1))))
  have hδsmall : B * δ + δ ^ (2 : ℕ) < L := by
    have hδsq : δ ^ (2 : ℕ) ≤ δ := by nlinarith
    have hδfrac : δ ≤ L / (2 * (B + 1)) := by
      simpa [δ, cesaroSignThreshold] using
        (min_le_right (1 : ℝ) (L / (2 * (B + 1))))
    have hmul : (B + 1) * δ ≤ L / 2 := by
      calc
        (B + 1) * δ ≤ (B + 1) * (L / (2 * (B + 1))) :=
          mul_le_mul_of_nonneg_left hδfrac (by positivity)
        _ = L / 2 := by field_simp
    nlinarith
  by_contra hneg
  push Not at hneg
  have hpoint (n : ℕ) : b n ^ (2 : ℕ) ≤ B * b n + (B * δ + δ ^ (2 : ℕ)) := by
    have habs := hB n
    have hlower : -δ ≤ b n := hneg n
    by_cases hn : 0 ≤ b n
    · have hupper : b n ≤ B := le_trans (le_abs_self (b n)) habs
      have hsq : b n ^ (2 : ℕ) ≤ B * b n := by nlinarith
      nlinarith [mul_nonneg hB0 hδ.le, sq_nonneg δ]
    · have hn' : b n < 0 := lt_of_not_ge hn
      have hsq : b n ^ (2 : ℕ) ≤ δ ^ (2 : ℕ) := by nlinarith
      have hrest : 0 ≤ B * b n + B * δ := by
        have := mul_nonneg hB0 (show 0 ≤ b n + δ by linarith)
        nlinarith
      nlinarith
  have hevent : ∀ᶠ N : ℕ in atTop,
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n ^ (2 : ℕ) ≤
        B * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n) +
          (B * δ + δ ^ (2 : ℕ)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hsum : (∑ n ∈ Finset.range N, b n ^ (2 : ℕ)) ≤
        ∑ n ∈ Finset.range N, (B * b n + (B * δ + δ ^ (2 : ℕ))) := by
      exact Finset.sum_le_sum fun n hn => hpoint n
    calc
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n ^ (2 : ℕ) ≤
          (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            (B * b n + (B * δ + δ ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
      _ = B * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n) +
          (B * δ + δ ^ (2 : ℕ)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum]
        have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
        field_simp [hNne]
  have hrhs : Tendsto
      (fun N : ℕ => B * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, b n) +
        (B * δ + δ ^ (2 : ℕ))) atTop (nhds (B * δ + δ ^ (2 : ℕ))) := by
    simpa using (tendsto_const_nhds.mul hmean).add_const (B * δ + δ ^ (2 : ℕ))
  have hle : L ≤ B * δ + δ ^ (2 : ℕ) :=
    le_of_tendsto_of_tendsto hmeanSq hrhs hevent
  exact (not_lt_of_ge hle) hδsmall

/-- A finite real trigonometric pencil with no constant mode and a nonzero coefficient takes
uniformly negative values arbitrarily late. -/
theorem exists_arbitrarily_late_finiteExponentialPencil_re_lt_neg
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : Set.InjOn z (s : Set ι))
    (hnoOne : ∀ i ∈ s, z i ≠ 1)
    (hc : ∃ i ∈ s, c i ≠ 0)
    (hreal : ∀ n, (finiteExponentialPencil s c z n).im = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ (finiteExponentialPencil s c z n).re < -δ := by
  let B : ℝ := ∑ i ∈ s, ‖c i‖
  let L : ℝ := ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i hi => norm_nonneg _
  have hL : 0 < L := by
    dsimp only [L]
    apply Finset.sum_pos' (fun i hi => sq_nonneg _)
    obtain ⟨i, hi, hci⟩ := hc
    exact ⟨i, hi, sq_pos_of_pos (norm_pos_iff.mpr hci)⟩
  let δ := cesaroSignThreshold B L
  refine ⟨δ, cesaroSignThreshold_pos hB0 hL, fun N => ?_⟩
  let cN : ι → ℂ := fun i => c i * z i ^ N
  let bN : ℕ → ℝ := fun n => (finiteExponentialPencil s c z (N + n)).re
  have hpencil (n : ℕ) :
      finiteExponentialPencil s cN z n = finiteExponentialPencil s c z (N + n) := by
    rw [finiteExponentialPencil, finiteExponentialPencil]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [cN]
    rw [pow_add]
    ring
  have hbound (n : ℕ) : |bN n| ≤ B := by
    calc
      |bN n| ≤ ‖finiteExponentialPencil s c z (N + n)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ∑ i ∈ s, ‖c i * z i ^ (N + n)‖ := norm_sum_le _ _
      _ = B := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, norm_pow, hz i hi, one_pow, mul_one]
  have hmeanComplex : Tendsto
      (fun K : ℕ => ((K : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ Finset.range K, finiteExponentialPencil s cN z n)
      atTop (nhds 0) := by
    have h := tendsto_finset_complex_geometric_cesaro s cN z hz
    have hzero : (∑ i ∈ s, if z i = 1 then cN i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hnoOne i hi]
    simpa only [finiteExponentialPencil, hzero] using h
  have hmeanRe := (Complex.continuous_re.tendsto 0).comp hmeanComplex
  have hmeanRewrite (K : ℕ) :
      ((((K : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ Finset.range K, finiteExponentialPencil s cN z n).re) =
      (K : ℝ)⁻¹ * ∑ n ∈ Finset.range K, bN n := by
    have hreK : ((((K : ℝ) : ℂ)⁻¹).re) = (K : ℝ)⁻¹ := by norm_num
    have himK : ((((K : ℝ) : ℂ)⁻¹).im) = 0 := by norm_num
    rw [Complex.mul_re]
    rw [hreK, himK, zero_mul, sub_zero]
    rw [← Complex.reCLM_apply, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [hpencil]
    rfl
  have hmean : Tendsto
      (fun K : ℕ => (K : ℝ)⁻¹ * ∑ n ∈ Finset.range K, bN n)
      atTop (nhds 0) := by
    convert hmeanRe using 1
    · funext K
      exact (hmeanRewrite K).symm
    · simp
  have hmeanSq0 := tendsto_finiteExponentialPencil_cesaro_norm_sq s cN z hz hinj
  have hmeanSq : Tendsto
      (fun K : ℕ => (K : ℝ)⁻¹ * ∑ n ∈ Finset.range K, bN n ^ (2 : ℕ))
      atTop (nhds L) := by
    convert hmeanSq0 using 1
    · funext K
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [hpencil]
      have him := hreal (N + n)
      rw [Complex.sq_norm, Complex.normSq_apply, him]
      dsimp only [bN]
      ring
    · apply congrArg nhds
      dsimp only [cN, L]
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, norm_pow, hz i hi, one_pow, mul_one]
  obtain ⟨n, hn⟩ :=
    exists_lt_neg_cesaroSignThreshold_of_mean_zero_of_pos_mean_sq
      hbound hmean hmeanSq hL
  refine ⟨N + n, Nat.le_add_right N n, ?_⟩
  simpa only [bN, δ] using hn

/-- Repeated phases are first collapsed by adding coefficients in each mode fiber. -/
theorem exists_arbitrarily_late_finiteExponentialPencil_re_lt_neg_of_fiberCoefficient
    {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hnoOne : ∀ i ∈ s, z i ≠ 1)
    (hc : ∃ u ∈ s.image z,
      finiteExponentialFiberCoefficient s c z u ≠ 0)
    (hreal : ∀ n, (finiteExponentialPencil s c z n).im = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ (finiteExponentialPencil s c z n).re < -δ := by
  classical
  have hzImage : ∀ u ∈ s.image z, ‖id u‖ = 1 := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    simpa using hz i hi
  have hnoOneImage : ∀ u ∈ s.image z, id u ≠ 1 := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    simpa using hnoOne i hi
  have hrealImage : ∀ n,
      (finiteExponentialPencil (s.image z)
        (finiteExponentialFiberCoefficient s c z) id n).im = 0 := by
    intro n
    rw [finiteExponentialPencil_image_eq]
    exact hreal n
  obtain ⟨δ, hδ, hlate⟩ :=
    exists_arbitrarily_late_finiteExponentialPencil_re_lt_neg
      (s.image z) (finiteExponentialFiberCoefficient s c z) id
      hzImage (fun _ _ _ _ h => h) hnoOneImage hc hrealImage
  refine ⟨δ, hδ, fun N => ?_⟩
  obtain ⟨n, hnN, hn⟩ := hlate N
  refine ⟨n, hnN, ?_⟩
  rw [finiteExponentialPencil_image_eq] at hn
  exact hn
/-- A negative value of a real maximal packet survives its norm-summable strictly smaller tail. -/
theorem exists_arbitrarily_late_re_tsum_normalizedExponentialPencil_lt_neg_of_dominantFinset
    {ι : Type*} (c b : ι → ℂ) (hc : Summable c)
    (D : Finset ι) {r : ℝ} (hr : 0 < r)
    (hdom : ∀ i ∈ D, ‖b i‖ = r)
    (hsub : ∀ i ∉ D, ‖b i‖ < r)
    (hnoOne : ∀ i ∈ D, b i / (r : ℂ) ≠ 1)
    (hfiber : ∃ u ∈ D.image (fun i => b i / (r : ℂ)),
      finiteExponentialFiberCoefficient D c (fun i => b i / (r : ℂ)) u ≠ 0)
    (hreal : ∀ n,
      (finiteExponentialPencil D c (fun i => b i / (r : ℂ)) n).im = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (∑' i : ι, c i * (b i / (r : ℂ)) ^ n).re < -δ := by
  classical
  let z : ι → ℂ := fun i => b i / (r : ℂ)
  have hzle (i : ι) : ‖z i‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hble : ‖b i‖ ≤ r := by
      by_cases hi : i ∈ D
      · rw [hdom i hi]
      · exact (hsub i hi).le
    exact (div_le_one hr).2 hble
  have hsum (n : ℕ) : Summable (fun i : ι => c i * z i ^ n) := by
    apply hc.norm.of_norm_bounded
    intro i
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg (c i))
      (pow_le_one₀ (norm_nonneg (z i)) (hzle i))
  have htail : Tendsto
      (fun n : ℕ => ∑' i : {i // i ∉ D}, c i * z i ^ n)
      atTop (nhds 0) := by
    have hbound : Summable (fun i : {i // i ∉ D} => ‖c i‖) :=
      hc.norm.subtype _
    have hpoint (i : {i // i ∉ D}) :
        Tendsto (fun n : ℕ => c i * z i ^ n) atTop (nhds 0) := by
      have hzlt : ‖z i‖ < 1 := by
        dsimp only [z]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        exact (div_lt_one hr).2 (hsub i i.2)
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hzlt)
    have hdominated : ∀ᶠ n : ℕ in atTop, ∀ i : {i // i ∉ D},
        ‖c i * z i ^ n‖ ≤ ‖c i‖ := by
      exact Eventually.of_forall fun n i => by
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg (c i))
          (pow_le_one₀ (norm_nonneg (z i)) (hzle i))
    simpa using tendsto_tsum_of_dominated_convergence hbound hpoint hdominated
  have hsplit (n : ℕ) :
      finiteExponentialPencil D c z n +
          (∑' i : {i // i ∉ D}, c i * z i ^ n) =
        ∑' i : ι, c i * z i ^ n := by
    simpa only [finiteExponentialPencil] using
      (hsum n).sum_add_tsum_subtype_compl D
  have hzD : ∀ i ∈ D, ‖z i‖ = 1 := by
    intro i hi
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hdom i hi]
    exact div_self hr.ne'
  obtain ⟨δ, hδ, hlate⟩ :=
    exists_arbitrarily_late_finiteExponentialPencil_re_lt_neg_of_fiberCoefficient
      D c z hzD (by simpa only [z] using hnoOne)
      (by simpa only [z] using hfiber) (by simpa only [z] using hreal)
  have htailSmall : ∀ᶠ n : ℕ in atTop,
      ‖∑' i : {i // i ∉ D}, c i * z i ^ n‖ < δ / 2 := by
    have hev := htail.eventually (Metric.ball_mem_nhds (0 : ℂ) (by positivity : 0 < δ / 2))
    simpa only [Metric.mem_ball, dist_zero_right] using hev
  obtain ⟨Ntail, hNtail⟩ := eventually_atTop.1 htailSmall
  refine ⟨δ / 2, by positivity, fun N => ?_⟩
  obtain ⟨n, hn, hlead⟩ := hlate (max N Ntail)
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hntail : Ntail ≤ n := le_trans (le_max_right _ _) hn
  have htailRe :
      (∑' i : {i // i ∉ D}, c i * z i ^ n).re < δ / 2 :=
    lt_of_le_of_lt (Complex.re_le_norm _) (hNtail n hntail)
  refine ⟨n, hnN, ?_⟩
  rw [← hsplit]
  simp only [Complex.add_re]
  linarith

end

end RHTower
