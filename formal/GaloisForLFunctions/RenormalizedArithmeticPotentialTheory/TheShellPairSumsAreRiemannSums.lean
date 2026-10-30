import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompletedShellEnergyIsAPositiveFourierIntegral
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCovariantCountertermIsTheAnomaly

/-!
# The shell pair sums are Riemann sums

For the pole weights `n^{−1/2}` and an autocorrelation `G` supported in `[−1, 1]`, the pairs of the
`h`-th successor shell at width `c/N` add up to a Riemann sum:

`Σ_{n+h ≤ N} (n(n+h))^{−1/2} G(N log(1 + h/n)/c) → ∫_{h/c}^1 G(u)/u du`
(`tendsto_shellPairSum`). Only `n ≳ hN/c` contributes, where the two logarithmic and the two
square-root weights agree to `O(1/N²)`, and `Σ_n (1/n) G(hN/(cn))` is a Riemann sum of the
function `y ↦ G(h/(cy))/y`, whose integral is `∫_{h/c}^1 G(u)/u du` by `u = h/(cy)`.

Summing over the finitely many shells `1 ≤ h ≤ ⌈c⌉`, the total off-diagonal pair sum of the pole
profile tends to `2 S(c)`, twice the shell sum of the completed energy
(`tendsto_poleProfile_pairSum`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open CompletedShell

/-! ### Riemann sums of a function continuous on the unit interval -/

/-- Right Riemann sums of a function continuous on `[0, 1]` converge to its integral. -/
theorem tendsto_riemannSum_of_continuousOn {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ range N, F ((k + 1 : ℝ) / N)) atTop
      (𝓝 (∫ y in (0 : ℝ)..1, F y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous hF) (ε / 2)
      (half_pos hε)
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hδ
  refine ⟨n₀ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 n₀) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNδ : 1 / (N : ℝ) < δ := by
    refine lt_of_le_of_lt ?_ hn₀
    apply one_div_le_one_div_of_le (by positivity)
    have : (n₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  set a : ℕ → ℝ := fun k => (k : ℝ) / N with ha
  have hcell : ∀ k < N, Set.uIcc (a k) (a (k + 1)) ⊆ Set.Icc 0 1 := by
    intro k hk y hy
    have h1 : a k ≤ a (k + 1) := by
      simp only [ha]; push_cast; exact div_le_div_of_nonneg_right (by linarith) hN0.le
    rw [uIcc_of_le h1] at hy
    have h0 : 0 ≤ a k := by simp only [ha]; positivity
    have h2 : a (k + 1) ≤ 1 := by
      simp only [ha]; rw [div_le_one hN0]; exact_mod_cast hk
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hint : ∀ k < N, IntervalIntegrable F volume (a k) (a (k + 1)) :=
    fun k hk => (hF.mono (hcell k hk)).intervalIntegrable
  have hsplit : (∫ y in (0 : ℝ)..1, F y) = ∑ k ∈ range N, ∫ y in a k..a (k + 1), F y := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint]
    simp [ha, div_self hN0.ne']
  have hlen : ∀ k, a (k + 1) - a k = 1 / N := fun k => by
    simp only [ha]; push_cast; field_simp; ring
  have hbound : ∀ k ∈ range N, |(N : ℝ)⁻¹ * F ((k + 1 : ℝ) / N) - ∫ y in a k..a (k + 1), F y| ≤
      ε / 2 * (1 / N) := by
    intro k hk
    have hk : k < N := mem_range.mp hk
    have hle : a k ≤ a (k + 1) := by linarith [hlen k, show (0 : ℝ) < 1 / N by positivity]
    have hconst : (N : ℝ)⁻¹ * F ((k + 1 : ℝ) / N) = ∫ _ in a k..a (k + 1), F ((k + 1 : ℝ) / N) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen k, one_div]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint k hk)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k + 1))
      (C := ε / 2) (f := fun y => F ((k + 1 : ℝ) / N) - F y) ?_
    · rwa [abs_of_nonneg (by linarith), hlen k] at h
    intro y hy
    rw [uIoc_of_le hle] at hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := hcell k hk (Set.Ioc_subset_Icc_self.trans
      (by rw [uIcc_of_le hle]) hy)
    have hk1 : ((k + 1 : ℝ) / N) = a (k + 1) := by simp only [ha]; push_cast; ring
    have htop : a (k + 1) ∈ Set.Icc (0 : ℝ) 1 := hcell k hk (by
      rw [uIcc_of_le hle]; exact ⟨hle, le_rfl⟩)
    have hd : dist (a (k + 1)) y < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.2])]
      linarith [hy.1, hlen k]
    rw [Real.norm_eq_abs, hk1]
    exact (hδF _ htop _ hy' hd).le
  rw [Real.dist_eq, hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ range N, ((N : ℝ)⁻¹ * F ((k + 1 : ℝ) / N) - ∫ y in a k..a (k + 1), F y)|
      ≤ ∑ k ∈ range N, |(N : ℝ)⁻¹ * F ((k + 1 : ℝ) / N) - ∫ y in a k..a (k + 1), F y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range N, ε / 2 * (1 / N) := Finset.sum_le_sum hbound
    _ = ε / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := half_lt_self hε

/-! ### The shell profile -/

section Shell

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- The change of variables `u = j/s` with a real ratio `j > 0`. -/
theorem integral_shell_change_real {a b j : ℝ} (ha : 0 < a) (hab : a ≤ b) (hj : 0 < j) :
    ∫ s in a..b, s⁻¹ * shellAutocorr φ (j * s⁻¹) = ∫ u in (j / b)..(j / a), shellAutocorr φ u / u := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => j * y⁻¹) (-(j * (x ^ 2)⁻¹)) x := by
    intro x hx
    exact ((hasDerivAt_inv (ne_of_gt (hpos x hx))).const_mul j).congr_deriv (by ring)
  have hcont : ContinuousOn (fun x => -(j * (x ^ 2)⁻¹)) (Set.uIcc a b) :=
    (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun x hx =>
      pow_ne_zero 2 (ne_of_gt (hpos x hx)))).neg
  have hgcont : ContinuousOn (fun u => shellAutocorr φ u / u) ((fun y => j * y⁻¹) '' Set.uIcc a b) :=
    ((continuous_shellAutocorr hφ hsupp).continuousOn.div continuousOn_id fun u hu => by
      obtain ⟨x, hx, rfl⟩ := hu
      exact (mul_pos hj (inv_pos.mpr (hpos x hx))).ne')
  have key := intervalIntegral.integral_comp_mul_deriv' hderiv hcont hgcont
  have hcongr : ∫ s in a..b, s⁻¹ * shellAutocorr φ (j * s⁻¹) =
      -∫ x in a..b, ((fun u => shellAutocorr φ u / u) ∘ fun y => j * y⁻¹) x *
        -(j * (x ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 := ne_of_gt (hpos x hx)
    have hj0 := hj.ne'
    simp only [Function.comp_apply]
    field_simp
  rw [hcongr, key, intervalIntegral.integral_symm, neg_neg, div_eq_mul_inv, div_eq_mul_inv]

/-- The shell profile `y ↦ G(h/(c y))/y` (zero at `y = 0`). -/
def shellProfile (φ : ℝ → ℝ) (r y : ℝ) : ℝ := shellAutocorr φ (r / y) / y

theorem shellProfile_eq_zero_of_le {r y : ℝ} (hy : 0 < y) (hyr : y ≤ r) :
    shellProfile φ r y = 0 := by
  rw [shellProfile, shellAutocorr_eq_zero_of_one_le hφ hsupp
    (by rw [le_div_iff₀ hy]; linarith), zero_div]

theorem continuousOn_shellProfile {r : ℝ} (hr : 0 < r) :
    ContinuousOn (shellProfile φ r) (Set.Icc 0 1) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with h0 | h0
  · subst h0
    have hzero : ∀ z ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Iio r, shellProfile φ r z = 0 := by
      intro z hz
      rcases eq_or_lt_of_le hz.1.1 with hz0 | hz0
      · rw [← hz0, shellProfile, div_zero]
      · exact shellProfile_eq_zero_of_le hφ hsupp hz0 hz.2.le
    have h0v : shellProfile φ r 0 = 0 := by rw [shellProfile, div_zero]
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ h0v
    have hnhds : Set.Iio r ∈ 𝓝[Set.Icc (0 : ℝ) 1] 0 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)
    filter_upwards [self_mem_nhdsWithin, hnhds] with z hz1 hz2
    exact hzero z ⟨hz1, hz2⟩
  · apply ContinuousAt.continuousWithinAt
    exact ((continuous_shellAutocorr hφ hsupp).continuousAt.comp
      (continuousAt_const.div continuousAt_id h0.ne')).div continuousAt_id h0.ne'

/-- The integral of the shell profile is the shell integral. -/
theorem integral_shellProfile {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    ∫ y in (0 : ℝ)..1, shellProfile φ (h / c) y = ∫ u in (h / c)..1, shellAutocorr φ u / u := by
  have hr : 0 < h / c := div_pos hh hc
  rcases le_or_gt 1 (h / c) with hr1 | hr1
  · rw [integral_shell_eq_zero_of_one_le hφ hsupp hr1]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun y hy => ?_,
      intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le zero_le_one] at hy
    rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · simp only [← hy0, shellProfile, div_zero]
    · exact shellProfile_eq_zero_of_le hφ hsupp hy0 (hy.2.trans hr1)
  · have hcont := continuousOn_shellProfile hφ hsupp hr
    have hi1 : IntervalIntegrable (shellProfile φ (h / c)) volume 0 (h / c) :=
      (hcont.mono (by rw [Set.uIcc_of_le hr.le]; exact Set.Icc_subset_Icc le_rfl hr1.le)).intervalIntegrable
    have hi2 : IntervalIntegrable (shellProfile φ (h / c)) volume (h / c) 1 :=
      (hcont.mono (by rw [Set.uIcc_of_le hr1.le]; exact Set.Icc_subset_Icc hr.le le_rfl)).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hz : ∫ y in (0 : ℝ)..(h / c), shellProfile φ (h / c) y = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun y hy => ?_,
        intervalIntegral.integral_zero]
      rw [Set.uIcc_of_le hr.le] at hy
      rcases eq_or_lt_of_le hy.1 with hy0 | hy0
      · simp only [← hy0, shellProfile, div_zero]
      · exact shellProfile_eq_zero_of_le hφ hsupp hy0 hy.2
    rw [hz, zero_add]
    have hch := integral_shell_change_real hφ hsupp hr hr1.le hr
    rw [div_one, div_self hr.ne'] at hch
    rw [← hch]
    refine intervalIntegral.integral_congr fun y hy => ?_
    simp only [shellProfile, div_eq_mul_inv]
    ring

/-- The `h`-th successor shell of the pole profile at width `c/N`. -/
def shellPairSum (φ : ℝ → ℝ) (c : ℝ) (N h : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, if n + h ≤ N then poleVector n * poleVector (n + h) *
    shellAutocorr φ (N * (Real.log ((n + h : ℕ) : ℝ) - Real.log n) / c) else 0

omit hφ hsupp in
theorem poleVector_mul_poleVector (n h : ℕ) :
    poleVector n * poleVector (n + h) = 1 / Real.sqrt ((n : ℝ) * (n + h : ℕ)) := by
  rw [poleVector, poleVector, Real.sqrt_mul (Nat.cast_nonneg n)]
  field_simp

omit hφ hsupp in
/-- `0 ≤ 1/n − 1/√(n(n+h)) ≤ h/(2n²)`. -/
theorem abs_poleVector_mul_sub_inv_le {n h : ℕ} (hn : 1 ≤ n) :
    |poleVector n * poleVector (n + h) - 1 / (n : ℝ)| ≤ h / (2 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  rw [poleVector_mul_poleVector]
  push_cast
  set r := Real.sqrt ((n : ℝ) * (n + h)) with hr
  have hr2 : r ^ 2 = (n : ℝ) * (n + h) := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrn : (n : ℝ) ≤ r := by nlinarith
  have hrup : r ≤ n + h / 2 := by nlinarith [sq_nonneg (r - (n + h / 2))]
  have hrpos : 0 < r := lt_of_lt_of_le hn0 hrn
  rw [abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hn0 hrn)]
  rw [div_sub_div _ _ hn0.ne' hrpos.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hrup hn0.le]

omit hφ hsupp in
/-- `|log(1 + x) − x| ≤ x²` for `x ≥ 0`. -/
theorem abs_log_one_add_sub_le {x : ℝ} (hx : 0 ≤ x) : |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have h1 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
  have h2 := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + x)
  have h3 : x - x ^ 2 ≤ 1 - (1 + x)⁻¹ := by
    rw [show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring, le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]
  rw [abs_le]
  constructor <;> linarith

/-- Below `hN/(4c)` both shell values vanish. -/
theorem shell_terms_eq_zero_of_small {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) {N n : ℕ}
    (hN : 4 * c ≤ N) (hn1 : 1 ≤ n) (hsmall : (n : ℝ) < h * N / (4 * c)) :
    shellAutocorr φ (N * (Real.log ((n + h : ℕ) : ℝ) - Real.log n) / c) = 0 ∧
      shellAutocorr φ (h * N / (c * n)) = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by linarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hsm := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * c)).mp hsmall
  refine ⟨?_, ?_⟩
  · apply shellAutocorr_eq_zero_of_one_le hφ hsupp
    have hx : 0 ≤ (h : ℝ) / n := by positivity
    have hlog : Real.log (((n + h : ℕ) : ℝ)) - Real.log n = Real.log (1 + h / n) := by
      rw [← Real.log_div (by positivity) hn0.ne']
      congr 1; push_cast; field_simp
    have hlb := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + h / n)
    rw [show 1 - (1 + (h : ℝ) / n)⁻¹ = h / (n + h) by field_simp; ring] at hlb
    rw [hlog, le_div_iff₀ hc, one_mul]
    have hstep : c ≤ N * (h / (n + h)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith
    exact hstep.trans (mul_le_mul_of_nonneg_left hlb hN0.le)
  · apply shellAutocorr_eq_zero_of_one_le hφ hsupp
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith

/-- Interior shell terms differ from their Riemann values by `O(1/N²)`. -/
theorem abs_shell_term_sub_le_interior {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ u v, |shellAutocorr φ u - shellAutocorr φ v| ≤ L * |u - v|) {N n : ℕ}
    (hN0 : (0 : ℝ) < N) (hn1 : 1 ≤ n) (hbig : h * N / (4 * c) ≤ (n : ℝ)) :
    |poleVector n * poleVector (n + h) *
        shellAutocorr φ (N * (Real.log ((n + h : ℕ) : ℝ) - Real.log n) / c) -
      shellAutocorr φ (h * N / (c * n)) / n| ≤
        (8 * (∫ u, φ u ^ 2) + 64 * L) * c ^ 2 / (N : ℝ) ^ 2 := by
  set M := ∫ u, φ u ^ 2 with hMdef
  have hM0 : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hG : ∀ t, |shellAutocorr φ t| ≤ M := fun t =>
    SpacingScaleHarmonicAnalysis.abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) t
  set x := (h : ℝ) / n with hx
  have hx0 : 0 ≤ x := by positivity
  have hinvn : 1 / (n : ℝ) ≤ 4 * c / (h * N) := by
    rw [div_le_div_iff₀ hn0 (by positivity), one_mul]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * c)).mp hbig
    linarith
  set a := N * (Real.log ((n + h : ℕ) : ℝ) - Real.log n) / c with ha
  set b := (h : ℝ) * N / (c * n) with hb
  have harg : |a - b| ≤ N / c * x ^ 2 := by
    have hlog : Real.log (((n + h : ℕ) : ℝ)) - Real.log n = Real.log (1 + x) := by
      rw [← Real.log_div (by positivity) hn0.ne']
      congr 1; rw [hx]; push_cast; field_simp
    rw [ha, hlog, hb, show (h : ℝ) * N / (c * n) = N * x / c by rw [hx]; field_simp,
      show N * Real.log (1 + x) / c - N * x / c = N / c * (Real.log (1 + x) - x) by ring,
      abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_log_one_add_sub_le hx0) (by positivity)
  have hpv := abs_poleVector_mul_sub_inv_le (h := h) hn1
  have hsplit : poleVector n * poleVector (n + h) * shellAutocorr φ a - shellAutocorr φ b / n =
      (poleVector n * poleVector (n + h) - 1 / n) * shellAutocorr φ a +
        (shellAutocorr φ a - shellAutocorr φ b) / n := by ring
  have hA : |(poleVector n * poleVector (n + h) - 1 / n) * shellAutocorr φ a| ≤
      (h * M / 2) * (1 / (n : ℝ)) ^ 2 := by
    rw [abs_mul]
    calc |poleVector n * poleVector (n + h) - 1 / n| * |shellAutocorr φ a|
        ≤ h / (2 * (n : ℝ) ^ 2) * M := mul_le_mul hpv (hG a) (abs_nonneg _) (by positivity)
      _ = (h * M / 2) * (1 / (n : ℝ)) ^ 2 := by field_simp
  have hB : |(shellAutocorr φ a - shellAutocorr φ b) / n| ≤
      (L * N * h ^ 2 / c) * (1 / (n : ℝ)) ^ 3 := by
    rw [abs_div, abs_of_pos hn0]
    calc |shellAutocorr φ a - shellAutocorr φ b| / n ≤ L * (N / c * x ^ 2) / n :=
          div_le_div_of_nonneg_right ((hL a b).trans (mul_le_mul_of_nonneg_left harg hL0)) hn0.le
      _ = (L * N * h ^ 2 / c) * (1 / (n : ℝ)) ^ 3 := by rw [hx]; field_simp
  have hq : (1 / (n : ℝ)) ^ 2 ≤ (4 * c / (h * N)) ^ 2 := pow_le_pow_left₀ (by positivity) hinvn 2
  have hc3 : (1 / (n : ℝ)) ^ 3 ≤ (4 * c / (h * N)) ^ 3 := pow_le_pow_left₀ (by positivity) hinvn 3
  have hA' : (h * M / 2) * (1 / (n : ℝ)) ^ 2 ≤ 8 * M * c ^ 2 / (N : ℝ) ^ 2 := by
    calc (h * M / 2) * (1 / (n : ℝ)) ^ 2 ≤ (h * M / 2) * (4 * c / (h * N)) ^ 2 :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 8 * M * c ^ 2 / ((h : ℝ) * N ^ 2) := by field_simp; ring
      _ ≤ 8 * M * c ^ 2 / (N : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [sq_nonneg (N : ℝ)]
  have hB' : (L * N * h ^ 2 / c) * (1 / (n : ℝ)) ^ 3 ≤ 64 * L * c ^ 2 / (N : ℝ) ^ 2 := by
    calc (L * N * h ^ 2 / c) * (1 / (n : ℝ)) ^ 3 ≤ (L * N * h ^ 2 / c) * (4 * c / (h * N)) ^ 3 :=
          mul_le_mul_of_nonneg_left hc3 (by positivity)
      _ = 64 * L * c ^ 2 / ((h : ℝ) * N ^ 2) := by field_simp; ring
      _ ≤ 64 * L * c ^ 2 / (N : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [sq_nonneg (N : ℝ)]
  rw [hsplit]
  calc _ ≤ |(poleVector n * poleVector (n + h) - 1 / n) * shellAutocorr φ a| +
        |(shellAutocorr φ a - shellAutocorr φ b) / n| := abs_add_le _ _
    _ ≤ 8 * M * c ^ 2 / (N : ℝ) ^ 2 + 64 * L * c ^ 2 / (N : ℝ) ^ 2 := by linarith
    _ = (8 * M + 64 * L) * c ^ 2 / (N : ℝ) ^ 2 := by ring

/-- Boundary Riemann values are `O(1/N)`. -/
theorem abs_shell_riemann_le_boundary {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) {N n : ℕ}
    (hN0 : (0 : ℝ) < N) (hn1 : 1 ≤ n) (hbig : h * N / (4 * c) ≤ (n : ℝ)) :
    |shellAutocorr φ (h * N / (c * n)) / n| ≤ 4 * c * (∫ u, φ u ^ 2) / N := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hinvn : 1 / (n : ℝ) ≤ 4 * c / (h * N) := by
    rw [div_le_div_iff₀ hn0 (by positivity), one_mul]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * c)).mp hbig
    linarith
  rw [abs_div, abs_of_pos hn0, div_eq_mul_one_div]
  calc |shellAutocorr φ (h * N / (c * n))| * (1 / n) ≤ (∫ u, φ u ^ 2) * (4 * c / (h * N)) :=
        mul_le_mul (SpacingScaleHarmonicAnalysis.abs_bumpCorr_le hφ.continuous
          (hasCompactSupport_profile hsupp) _) hinvn (by positivity) hM0
    _ = 4 * c * (∫ u, φ u ^ 2) / (h * N) := by ring
    _ ≤ 4 * c * (∫ u, φ u ^ 2) / N := by
        apply div_le_div_of_nonneg_left (by positivity) hN0
        nlinarith

/-- The `n`-th shell term against its Riemann value: `O(1/N²)`, except the `h` boundary terms,
which are `O(1/N)`. -/
theorem abs_shell_term_sub_le {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u v, |shellAutocorr φ u - shellAutocorr φ v| ≤ L * |u - v|) {N n : ℕ}
    (hN : 4 * c ≤ N) (hn : n ∈ Finset.Icc 1 N) :
    |(if n + h ≤ N then poleVector n * poleVector (n + h) *
        shellAutocorr φ (N * (Real.log ((n + h : ℕ) : ℝ) - Real.log n) / c) else 0) -
      shellAutocorr φ (h * N / (c * n)) / n| ≤
        (8 * (∫ u, φ u ^ 2) + 64 * L) * c ^ 2 / (N : ℝ) ^ 2 +
          (if n + h ≤ N then 0 else 4 * c * (∫ u, φ u ^ 2) / N) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by linarith
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hE0 : 0 ≤ (8 * (∫ u, φ u ^ 2) + 64 * L) * c ^ 2 / (N : ℝ) ^ 2 := by positivity
  rcases lt_or_ge (n : ℝ) (h * N / (4 * c)) with hsmall | hbig
  · obtain ⟨h1, h2⟩ := shell_terms_eq_zero_of_small hφ hsupp hc hh hN hn1 hsmall
    rw [h1, h2, mul_zero, zero_div, sub_zero]
    split_ifs <;> simp only [abs_zero] <;> positivity
  · split_ifs with hnh
    · rw [add_zero]
      exact abs_shell_term_sub_le_interior hφ hsupp hc hh hL0 hL hN0 hn1 hbig
    · rw [zero_sub, abs_neg]
      have := abs_shell_riemann_le_boundary hφ hsupp hc hh hN0 hn1 hbig
      linarith

/-- The shell sum is the Riemann sum of the shell profile up to `O(1/N)`. -/
theorem abs_shellPairSum_sub_le {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) :
    ∃ E : ℝ, ∀ᶠ N : ℕ in atTop, |shellPairSum φ c N h -
      ∑ n ∈ Finset.Icc 1 N, shellAutocorr φ (h * N / (c * n)) / n| ≤ E / N := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (BiScaleUncertainty.ChebyshevGauge.hasCompactSupport_autocorr (hasCompactSupport_profile hsupp))
    (contDiff_shellAutocorr hφ hsupp) (by norm_num)
  have hL : ∀ u v, |shellAutocorr φ u - shellAutocorr φ v| ≤ (K : ℝ) * |u - v| := fun u v => by
    simpa only [Real.dist_eq] using hK.dist_le_mul u v
  set M := ∫ u, φ u ^ 2 with hMdef
  refine ⟨(8 * M + 64 * K) * c ^ 2 + h * (4 * c * M), ?_⟩
  filter_upwards [eventually_ge_atTop ⌈4 * c⌉₊, eventually_ge_atTop 1] with N hN hN1
  have hN4 : 4 * c ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hterm := fun n (hn : n ∈ Finset.Icc 1 N) =>
    abs_shell_term_sub_le hφ hsupp hc hh K.coe_nonneg hL hN4 hn
  rw [shellPairSum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.Icc 1 N).filter (fun n => ¬ n + h ≤ N)).card : ℝ) ≤ h := by
    have hsub : (Finset.Icc 1 N).filter (fun n => ¬ n + h ≤ N) ⊆ Finset.Ioc (N - h) N := by
      intro n hn
      simp only [mem_filter, Finset.mem_Icc, not_le] at hn
      simp only [Finset.mem_Ioc]
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    have h2 : N - (N - h) ≤ h := by omega
    exact_mod_cast this.trans h2
  have hM0 : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hpos : 0 ≤ 4 * c * M / N := by positivity
  calc (N : ℝ) * ((8 * M + 64 * K) * c ^ 2 / (N : ℝ) ^ 2) +
        (((Finset.Icc 1 N).filter (fun n => ¬ n + h ≤ N)).card : ℝ) * (4 * c * M / N)
      ≤ (N : ℝ) * ((8 * M + 64 * K) * c ^ 2 / (N : ℝ) ^ 2) + h * (4 * c * M / N) := by
        gcongr
    _ = ((8 * M + 64 * K) * c ^ 2 + h * (4 * c * M)) / N := by
        field_simp

/-- **The `h`-th shell sum is a Riemann sum.** -/
theorem tendsto_shellPairSum {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N => shellPairSum φ c N h) atTop
      (𝓝 (∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u)) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hr : 0 < (h : ℝ) / c := div_pos hh0 hc
  have hriem := tendsto_riemannSum_of_continuousOn (continuousOn_shellProfile hφ hsupp hr)
  rw [integral_shellProfile hφ hsupp hh0 hc] at hriem
  have heq : ∀ N : ℕ, 1 ≤ N → (N : ℝ)⁻¹ * ∑ k ∈ range N, shellProfile φ (h / c) ((k + 1 : ℝ) / N) =
      ∑ n ∈ Finset.Icc 1 N, shellAutocorr φ (h * N / (c * n)) / n := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hIcc : Finset.Icc 1 N = Finset.Ico (0 + 1) (N + 1) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, ← Finset.sum_Ico_add', ← Finset.range_eq_Ico, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    simp only [shellProfile]
    push_cast
    rw [show (h : ℝ) / c / ((k + 1) / N) = h * N / (c * (k + 1)) by field_simp]
    field_simp
  obtain ⟨E, hE⟩ := abs_shellPairSum_sub_le hφ hsupp hc hh
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, shellAutocorr φ (h * N / (c * n)) / n)
      atTop (𝓝 (∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u)) :=
    hriem.congr' (by filter_upwards [eventually_ge_atTop 1] with N hN using heq N hN)
  have hdiff : Tendsto (fun N : ℕ => shellPairSum φ c N h -
      ∑ n ∈ Finset.Icc 1 N, shellAutocorr φ (h * N / (c * n)) / n) atTop (𝓝 0) := by
    have hEN : Tendsto (fun N : ℕ => E / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hEN
    filter_upwards [hE] with N hN
    rwa [Real.norm_eq_abs]
  simpa using hdiff.add hR

/-- The off-diagonal pair sum of the pole profile against `G(N|log ℓ − log n|/c)`. -/
def poleProfilePairSum (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Icc 1 N, if ℓ = n then 0 else
    poleVector n * poleVector ℓ * shellAutocorr φ (N * |Real.log ℓ - Real.log n| / c)

omit hφ hsupp in
/-- Upper neighbours at distance at most `H` are the shifts `n + h`, `1 ≤ h ≤ H`. -/
theorem sum_upper_eq_sum_shift (N n H : ℕ) (Q : ℕ → ℝ)
    (hQ : ∀ ℓ ∈ Finset.Icc 1 N, n + H < ℓ → Q ℓ = 0) :
    ∑ ℓ ∈ Finset.Icc 1 N, (if n < ℓ then Q ℓ else 0) =
      ∑ h ∈ Finset.Icc 1 H, (if n + h ≤ N then Q (n + h) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hL : ∑ ℓ ∈ (Finset.Icc 1 N).filter (fun ℓ => n < ℓ), Q ℓ =
      ∑ ℓ ∈ (Finset.Icc 1 N).filter (fun ℓ => n < ℓ ∧ ℓ ≤ n + H), Q ℓ := by
    symm
    refine Finset.sum_subset (fun ℓ hℓ => ?_) fun ℓ hℓ hℓ' => ?_
    · simp only [Finset.mem_filter] at hℓ ⊢; exact ⟨hℓ.1, hℓ.2.1⟩
    · simp only [Finset.mem_filter, not_and, not_le] at hℓ hℓ'
      exact hQ ℓ hℓ.1 (hℓ' hℓ.1 hℓ.2)
  rw [hL]
  refine Finset.sum_nbij' (fun ℓ => ℓ - n) (fun h => n + h) ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_Icc] at hℓ ⊢
    omega
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
    omega
  · intro ℓ hℓ
    simp only [Finset.mem_filter] at hℓ
    omega
  · intro h _
    omega
  · intro ℓ hℓ
    simp only [Finset.mem_filter] at hℓ
    congr 1
    omega

/-- The pair sum is twice the sum of its finitely many shells. -/
theorem poleProfilePairSum_eq_sum_shells {c : ℝ} (hc : 0 < c) (N : ℕ) :
    poleProfilePairSum φ c N = 2 * ∑ h ∈ Finset.Icc 1 ⌈c⌉₊, shellPairSum φ c N h := by
  set P : ℕ → ℕ → ℝ := fun n ℓ =>
    poleVector n * poleVector ℓ * shellAutocorr φ (N * |Real.log ℓ - Real.log n| / c) with hP
  have hPsymm : ∀ n ℓ, P n ℓ = P ℓ n := fun n ℓ => by
    simp only [hP, abs_sub_comm (Real.log ℓ), mul_comm (poleVector n)]
  have hpt : ∀ n ℓ : ℕ, (if ℓ = n then 0 else P n ℓ) =
      (if n < ℓ then P n ℓ else 0) + (if ℓ < n then P n ℓ else 0) := by
    intro n ℓ
    rcases lt_trichotomy n ℓ with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), add_zero]
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, zero_add]
  have hhalf : ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Icc 1 N, (if ℓ < n then P n ℓ else 0) =
      ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Icc 1 N, (if n < ℓ then P n ℓ else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun ℓ _ => ?_
    split_ifs <;> simp [hPsymm]
  have hvan : ∀ n ∈ Finset.Icc 1 N, ∀ ℓ, n + ⌈c⌉₊ < ℓ → ℓ ∈ Finset.Icc 1 N → P n ℓ = 0 := by
    intro n hn ℓ hℓ hℓN
    simp only [hP]
    rw [shellAutocorr_eq_zero_of_one_le hφ hsupp, mul_zero]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hℓN' : (ℓ : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hℓN).2
    have hgap : (n : ℝ) + c ≤ ℓ := by
      have : (n : ℝ) + ⌈c⌉₊ < ℓ := by exact_mod_cast hℓ
      linarith [Nat.le_ceil c]
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : (0 : ℝ) < ℓ := by linarith
    have hlog : c / N ≤ Real.log ℓ - Real.log n := by
      rw [← Real.log_div hl0.ne' hn0.ne']
      have hlb := Real.one_sub_inv_le_log_of_pos (div_pos hl0 hn0)
      have h1 : c / N ≤ 1 - ((ℓ : ℝ) / n)⁻¹ := by
        rw [inv_div, show 1 - (n : ℝ) / ℓ = (ℓ - n) / ℓ by field_simp]
        rw [div_le_div_iff₀ (by linarith) hl0]
        nlinarith
      linarith
    rw [abs_of_nonneg (by linarith [div_pos hc (by linarith : (0 : ℝ) < N)]), le_div_iff₀ hc,
      one_mul]
    have hN0 : (0 : ℝ) < N := by linarith
    have := mul_le_mul_of_nonneg_left hlog hN0.le
    rwa [mul_div_cancel₀ c hN0.ne'] at this
  have hfold : poleProfilePairSum φ c N =
      ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Icc 1 N, (if ℓ = n then 0 else P n ℓ) := rfl
  rw [hfold]
  simp_rw [hpt, Finset.sum_add_distrib]
  rw [hhalf, ← two_mul]
  congr 1
  unfold shellPairSum
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [sum_upper_eq_sum_shift N n ⌈c⌉₊ (P n) (fun ℓ hℓN hℓ => hvan n hn ℓ hℓ hℓN)]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs with hnh
  · simp only [hP]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) (by push_cast; linarith
      [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)])))]
  · rfl

end Shell

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
