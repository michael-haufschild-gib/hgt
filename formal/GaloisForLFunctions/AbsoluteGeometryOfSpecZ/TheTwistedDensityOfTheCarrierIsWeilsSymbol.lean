import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDensityOfTheCarrierIsWeilsConstant
import GaloisForLFunctions.RHTower.BlindSymbolSlackPrimePowerPeriodization
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellPairSumsAreRiemannSums

/-!
# The twisted density of the carrier is Weil's symbol

The rational torus acts on the orbit of the adelic carrier, and its characters on the Kronecker
line are `r ↦ r^{iτ}`. Twisting the coupled orbit by such a character multiplies the term at the
reduced displacement `a/n` by `cos(τ log(a/n))`. This file computes the rows of the twisted orbit.

* **The collision row does not see the twist** (`twisted_profile_split`,
  `sum_cos_mul_jetKernel_sq`): `cos(τ log r)/(1 − r⁴) = 1/(4(1 − r)) + P_τ(r)` with
  `P_τ(r) = regularProfile r − (1 − cos(τ log r))/(1 − r⁴)`, and the twisted half-row at height `n`
  is `H_{n−1}/(4n)` plus the twisted smooth row over `n²`.
* **The twisted density** (`tendsto_twistedSmoothRow_div`): the twisted smooth row over `n` tends
  to `c(τ) = c₀ − ∫_0^1 (1 − cos(τ log r))/(1 − r⁴) dr`.
* **It is the archimedean Weil symbol** (`integral_twistDefect`, `four_mul_twistedMean_add`):
  the substitutions `r = e^{−v}`, `x = 2v` turn the integral into
  `½ ∫_0^∞ ω(x)(1 − cos(τx/2)) dx = ½(θ'(τ/2) − θ'(0))`, hence
  `4c(τ) + γ + log 4π = −A(τ/2)` for every `τ`, with `A(r) = Re ψ(¼ + ir/2) − log π`.
* **The packet functional of the carrier** (`weilArchRe_sub_pole_eq_carrier`): for every Weil test
  `f`, the archimedean part of Weil's functional without the pole is
  `−(1/2π) ∫ |f̂(r)|² (4c(2r) + γ + log 4π) dr`.

So the density row of the orbit twisted by the character of frequency `2r`, together with the
harmonic constant of the collision row and the mesh constant of the comb of squares, is the value
at `r` of Weil's archimedean symbol. The archimedean Weil form of a packet is the integral of its
spectral density against the twisted densities of the carrier: the diagonal of Weil's form is a
density of the orbit sum at every frequency.

A tool is proved on the way (`tendsto_riemannSum_of_continuousOn_Ioc`): Riemann sums of a bounded
function that is continuous on `(0, 1]` converge to its integral.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open GaloisForLFunctions.HyperbolicArakelovTheory.CoupledOrbit

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Riemann sums of a bounded function continuous on `(0, 1]` -/

/-- The cut-off of `g` near `0`: `g(r)·min(1, r/δ)`. -/
def cutNearZero (g : ℝ → ℝ) (δ : ℝ) (r : ℝ) : ℝ := g r * min 1 (r / δ)

theorem continuousOn_cutNearZero {g : ℝ → ℝ} {B δ : ℝ} (hδ : 0 < δ)
    (hg : ContinuousOn g (Set.Ioc 0 1)) (hB : ∀ r ∈ Set.Ioc (0 : ℝ) 1, |g r| ≤ B) :
    ContinuousOn (cutNearZero g δ) (Set.Icc 0 1) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1 ⟨one_pos, le_rfl⟩)
  have hcut : Continuous fun r : ℝ => min 1 (r / δ) := continuous_const.min (continuous_id.div_const δ)
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hx0
  · -- at `0` the cut-off wins
    have hval : cutNearZero g δ 0 = 0 := by
      simp [cutNearZero]
    have hbound : ∀ᶠ r in 𝓝[Set.Icc (0 : ℝ) 1] 0, ‖cutNearZero g δ r‖ ≤ B * (r / δ) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rcases hr.1.eq_or_lt with rfl | hr0
      · rw [hval]
        simp
      · have h1 : |g r| ≤ B := hB r ⟨hr0, hr.2⟩
        have h2 : 0 ≤ min 1 (r / δ) := le_min zero_le_one (div_nonneg hr0.le hδ.le)
        have h3 : min 1 (r / δ) ≤ r / δ := min_le_right _ _
        rw [cutNearZero, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
        exact mul_le_mul h1 h3 h2 hB0
    have hlim : Tendsto (fun r : ℝ => B * (r / δ)) (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 0) := by
      have hc : Continuous fun r : ℝ => B * (r / δ) := by fun_prop
      have h0 := hc.tendsto 0
      rw [zero_div, mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := squeeze_zero_norm' hbound hlim
    rw [ContinuousWithinAt, hval]
    exact this
  · have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[Set.Icc (0 : ℝ) 1] x :=
      mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, hx0, fun y hy => ⟨hy.1, hy.2.2⟩⟩
    exact ((hg x ⟨hx0, hx.2⟩).mono_of_mem_nhdsWithin hmem).mul hcut.continuousWithinAt

theorem abs_sub_cutNearZero_le {g : ℝ → ℝ} {B δ : ℝ} (hδ : 0 < δ)
    (hB : ∀ r ∈ Set.Ioc (0 : ℝ) 1, |g r| ≤ B) {r : ℝ} (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    |g r - cutNearZero g δ r| ≤ if r < δ then B else 0 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1 ⟨one_pos, le_rfl⟩)
  have h2 : 0 ≤ min 1 (r / δ) := le_min zero_le_one (div_nonneg hr.1.le hδ.le)
  have h3 : min 1 (r / δ) ≤ 1 := min_le_left _ _
  have he : g r - cutNearZero g δ r = g r * (1 - min 1 (r / δ)) := by
    rw [cutNearZero]
    ring
  by_cases hlt : r < δ
  · rw [if_pos hlt, he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 - min 1 (r / δ) by linarith)]
    calc |g r| * (1 - min 1 (r / δ)) ≤ B * 1 :=
          mul_le_mul (hB r hr) (by linarith) (by linarith) hB0
      _ = B := mul_one B
  · have hge : 1 ≤ r / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    rw [if_neg hlt, he, min_eq_left hge, sub_self, mul_zero, abs_zero]

/-- **Riemann sums of a bounded function continuous on `(0, 1]`** converge to its integral. -/
theorem tendsto_riemannSum_of_continuousOn_Ioc {g : ℝ → ℝ} {B : ℝ}
    (hg : ContinuousOn g (Set.Ioc 0 1)) (hB : ∀ r ∈ Set.Ioc (0 : ℝ) 1, |g r| ≤ B) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ range N, g (((k : ℝ) + 1) / N)) atTop
      (𝓝 (∫ y in (0 : ℝ)..1, g y)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1 ⟨one_pos, le_rfl⟩)
  have hgi : IntervalIntegrable g volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.mono' (integrableOn_const (C := B) (by simp)) (hg.aestronglyMeasurable measurableSet_Ioc) ?_
    exact (ae_restrict_mem measurableSet_Ioc).mono fun r hr => by
      rw [Real.norm_eq_abs]
      exact hB r hr
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the cut-off
  set δ : ℝ := min 1 (ε / (4 * (B + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hBδ : B * δ ≤ ε / 4 := by
    have h1 : δ ≤ ε / (4 * (B + 1)) := min_le_right _ _
    calc B * δ ≤ B * (ε / (4 * (B + 1))) := mul_le_mul_of_nonneg_left h1 hB0
      _ = ε / 4 * (B / (B + 1)) := by field_simp
      _ ≤ ε / 4 * 1 := by
          gcongr
          rw [div_le_one (by linarith)]
          linarith
      _ = ε / 4 := mul_one _
  have hcδ := continuousOn_cutNearZero hδ0 hg hB
  have hcδi : IntervalIntegrable (cutNearZero g δ) volume 0 1 :=
    hcδ.intervalIntegrable_of_Icc zero_le_one
  -- the integrals differ by at most `Bδ`
  have hintdiff : |(∫ y in (0 : ℝ)..1, g y) - ∫ y in (0 : ℝ)..1, cutNearZero g δ y| ≤ B * δ := by
    rw [← intervalIntegral.integral_sub hgi hcδi]
    have hdi := hgi.sub hcδi
    have h0δ : IntervalIntegrable (fun y => g y - cutNearZero g δ y) volume 0 δ :=
      hdi.mono_set (by
        rw [Set.uIcc_of_le hδ0.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc_right hδ1)
    have hδ1i : IntervalIntegrable (fun y => g y - cutNearZero g δ y) volume δ 1 :=
      hdi.mono_set (by
        rw [Set.uIcc_of_le hδ1, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc_left hδ0.le)
    rw [← intervalIntegral.integral_add_adjacent_intervals h0δ hδ1i]
    have hzero : ∫ y in δ..1, (g y - cutNearZero g δ y) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
      · exact intervalIntegral.integral_zero
      · rw [Set.uIcc_of_le hδ1] at hy
        have hy' : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hδ0.trans_le hy.1, hy.2⟩
        have h := abs_sub_cutNearZero_le hδ0 hB hy'
        rw [if_neg (not_lt.mpr hy.1)] at h
        exact abs_nonpos_iff.mp h
    rw [hzero, add_zero]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := B)
      (f := fun y => g y - cutNearZero g δ y) (fun y hy => by
        rw [Set.uIoc_of_le hδ0.le] at hy
        have hy' : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hδ1⟩
        have h := abs_sub_cutNearZero_le hδ0 hB hy'
        rw [Real.norm_eq_abs]
        refine h.trans ?_
        split_ifs
        · exact le_rfl
        · exact hB0)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hδ0] at hb
    exact hb
  -- the Riemann sums differ by at most `B(δ + 1/N)`
  have hsumdiff : ∀ N : ℕ, 0 < N →
      |(N : ℝ)⁻¹ * ∑ k ∈ range N, g (((k : ℝ) + 1) / N) -
        (N : ℝ)⁻¹ * ∑ k ∈ range N, cutNearZero g δ (((k : ℝ) + 1) / N)| ≤ B * (δ + 1 / N) := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.mpr hN')]
    have hterm : ∀ k ∈ range N, |g (((k : ℝ) + 1) / N) - cutNearZero g δ (((k : ℝ) + 1) / N)| ≤
        if k ∈ range ⌈δ * N⌉₊ then B else 0 := by
      intro k hk
      have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hk)
      have hmem : ((k : ℝ) + 1) / N ∈ Set.Ioc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one hN').mpr hkN⟩
      refine (abs_sub_cutNearZero_le hδ0 hB hmem).trans ?_
      by_cases hlt : ((k : ℝ) + 1) / N < δ
      · have hk' : k ∈ range ⌈δ * N⌉₊ := by
          rw [mem_range, ← Nat.cast_lt (α := ℝ)]
          rw [div_lt_iff₀ hN'] at hlt
          exact (by linarith : (k : ℝ) < δ * N).trans_le (Nat.le_ceil _)
        rw [if_pos hlt, if_pos hk']
      · rw [if_neg hlt]
        split_ifs
        · exact hB0
        · exact le_rfl
    have hcard : (∑ k ∈ range N, if k ∈ range ⌈δ * N⌉₊ then B else 0) ≤ (δ * N + 1) * B := by
      have hle : (∑ k ∈ range N, if k ∈ range ⌈δ * N⌉₊ then B else 0) ≤
          ∑ _k ∈ range ⌈δ * N⌉₊, B := by
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.mp hk).2)
          fun _ _ _ => hB0
      refine hle.trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hB0
    calc (N : ℝ)⁻¹ * |∑ k ∈ range N,
          (g (((k : ℝ) + 1) / N) - cutNearZero g δ (((k : ℝ) + 1) / N))|
        ≤ (N : ℝ)⁻¹ * ∑ k ∈ range N,
          |g (((k : ℝ) + 1) / N) - cutNearZero g δ (((k : ℝ) + 1) / N)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.mpr hN').le
      _ ≤ (N : ℝ)⁻¹ * ((δ * N + 1) * B) :=
          mul_le_mul_of_nonneg_left ((Finset.sum_le_sum hterm).trans hcard) (inv_pos.mpr hN').le
      _ = B * (δ + 1 / N) := by
          field_simp
  -- assemble
  have hcorpus := GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tendsto_riemannSum_of_continuousOn hcδ
  rw [Metric.tendsto_atTop] at hcorpus
  obtain ⟨N₁, hN₁⟩ := hcorpus (ε / 4) (by positivity)
  refine ⟨max (max N₁ 1) (⌈4 * B / ε⌉₊ + 1), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNpos : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNB : B / N ≤ ε / 4 := by
    have h1 : 4 * B / ε ≤ N := by
      have h2 : (⌈4 * B / ε⌉₊ : ℝ) ≤ N := by
        exact_mod_cast (Nat.le_succ _).trans ((le_max_right _ _).trans hN)
      exact (Nat.le_ceil _).trans h2
    rw [div_le_iff₀ hN']
    rw [div_le_iff₀ hε] at h1
    linarith
  have h1 := hsumdiff N hNpos
  have h2 := hN₁ N hN1
  rw [Real.dist_eq] at h2 ⊢
  have h3 : B * (δ + 1 / N) ≤ ε / 4 + ε / 4 := by
    have : B * (δ + 1 / N) = B * δ + B / N := by ring
    rw [this]
    linarith
  have habs := abs_sub_le ((N : ℝ)⁻¹ * ∑ k ∈ range N, g (((k : ℝ) + 1) / N))
    ((N : ℝ)⁻¹ * ∑ k ∈ range N, cutNearZero g δ (((k : ℝ) + 1) / N)) (∫ y in (0 : ℝ)..1, g y)
  have habs2 := abs_sub_le ((N : ℝ)⁻¹ * ∑ k ∈ range N, cutNearZero g δ (((k : ℝ) + 1) / N))
    (∫ y in (0 : ℝ)..1, cutNearZero g δ y) (∫ y in (0 : ℝ)..1, g y)
  have hsymm : |(∫ y in (0 : ℝ)..1, cutNearZero g δ y) - ∫ y in (0 : ℝ)..1, g y| ≤ B * δ := by
    rw [abs_sub_comm]
    exact hintdiff
  linarith

/-! ### The twisted profile -/

/-- The defect of the twist: `(1 − cos(τ log r))/(1 − r⁴)`. -/
def twistDefect (τ r : ℝ) : ℝ := (1 - Real.cos (τ * Real.log r)) / (1 - r ^ 4)

/-- The twisted regular profile `P_τ`. -/
def twistedProfile (τ r : ℝ) : ℝ := regularProfile r - twistDefect τ r

/-- **The collision pole does not see the twist.** -/
theorem twisted_profile_split (τ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.cos (τ * Real.log r) / (1 - r ^ 4) = 1 / (4 * (1 - r)) + twistedProfile τ r := by
  have hs := profile_split hr0.le hr1
  rw [twistedProfile, twistDefect, sub_div]
  linarith

theorem twistDefect_one (τ : ℝ) : twistDefect τ 1 = 0 := by simp [twistDefect]

theorem twistDefect_nonneg (τ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : 0 ≤ twistDefect τ r := by
  have h4 : r ^ 4 ≤ 1 := pow_le_one₀ hr0.le hr1
  exact div_nonneg (by linarith [Real.cos_le_one (τ * Real.log r)]) (by linarith)

/-- Near `r = 1` the defect is at most `τ²(1 − r)/(2r²)`. -/
theorem twistDefect_le (τ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    twistDefect τ r ≤ τ ^ 2 * (1 - r) / (2 * r ^ 2) := by
  rcases hr1.eq_or_lt with rfl | hlt
  · rw [twistDefect_one]
    simp
  · have hcos := Real.one_sub_sq_div_two_le_cos (x := τ * Real.log r)
    have hlog1 : 1 - r⁻¹ ≤ Real.log r := Real.one_sub_inv_le_log_of_pos hr0
    have hlog2 : Real.log r ≤ 0 := Real.log_nonpos hr0.le hlt.le
    have hinv : 1 - r⁻¹ = -((1 - r) / r) := by field_simp; ring
    have hsq : Real.log r ^ 2 ≤ ((1 - r) / r) ^ 2 := by
      rw [hinv] at hlog1
      nlinarith
    have hden : 0 < 1 - r ^ 4 := by
      have : r ^ 4 < 1 := pow_lt_one₀ hr0.le hlt (by norm_num)
      linarith
    have hden2 : 1 - r ≤ 1 - r ^ 4 := by nlinarith [pow_pos hr0 2, pow_pos hr0 3]
    have hnum : 1 - Real.cos (τ * Real.log r) ≤ τ ^ 2 * ((1 - r) / r) ^ 2 / 2 := by
      have h1 : (τ * Real.log r) ^ 2 = τ ^ 2 * Real.log r ^ 2 := by ring
      nlinarith [sq_nonneg τ]
    have hr1' : 0 < 1 - r := by linarith
    rw [twistDefect, div_le_iff₀ hden]
    calc 1 - Real.cos (τ * Real.log r) ≤ τ ^ 2 * ((1 - r) / r) ^ 2 / 2 := hnum
      _ = τ ^ 2 * (1 - r) / (2 * r ^ 2) * (1 - r) := by field_simp
      _ ≤ τ ^ 2 * (1 - r) / (2 * r ^ 2) * (1 - r ^ 4) :=
          mul_le_mul_of_nonneg_left hden2 (by positivity)

/-- The defect is bounded on `(0, 1]`. -/
theorem abs_twistDefect_le (τ : ℝ) {r : ℝ} (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    |twistDefect τ r| ≤ 3 + τ ^ 2 := by
  rw [abs_of_nonneg (twistDefect_nonneg τ hr.1 hr.2)]
  by_cases hhalf : r ≤ 1 / 2
  · have h4 : r ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_left₀ hr.1.le hhalf 4
    have hden : (15 : ℝ) / 16 ≤ 1 - r ^ 4 := by norm_num at h4 ⊢; linarith
    rw [twistDefect, div_le_iff₀ (by linarith)]
    nlinarith [Real.neg_one_le_cos (τ * Real.log r), sq_nonneg τ]
  · rw [not_le] at hhalf
    refine (twistDefect_le τ hr.1 hr.2).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : τ ^ 2 * (1 - r) ≤ τ ^ 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg τ)
    have h2 : (1 / 2 : ℝ) ≤ 2 * r ^ 2 := by nlinarith
    have h3 : (3 + τ ^ 2) * (1 / 2) ≤ (3 + τ ^ 2) * (2 * r ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [sq_nonneg τ]

theorem continuousOn_twistDefect (τ : ℝ) : ContinuousOn (twistDefect τ) (Set.Ioc 0 1) := by
  have hopen : ContinuousOn (twistDefect τ) (Set.Ioo 0 1) := by
    have hlog : ContinuousOn Real.log (Set.Ioo (0 : ℝ) 1) :=
      Real.continuousOn_log.mono fun r hr => ne_of_gt hr.1
    refine ContinuousOn.div (continuousOn_const.sub
      (Real.continuous_cos.comp_continuousOn (continuousOn_const.mul hlog)))
      (continuousOn_const.sub (continuousOn_id.pow 4)) fun r hr => ?_
    have : r ^ 4 < 1 := pow_lt_one₀ hr.1.le hr.2 (by norm_num)
    exact (sub_pos.mpr this).ne'
  intro x hx
  rcases hx.2.eq_or_lt with rfl | hlt
  · -- at `1` the defect tends to `0`
    have hbound : ∀ᶠ r in 𝓝[Set.Ioc (0 : ℝ) 1] 1,
        ‖twistDefect τ r‖ ≤ τ ^ 2 * (1 - r) / (2 * r ^ 2) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (twistDefect_nonneg τ hr.1 hr.2)]
      exact twistDefect_le τ hr.1 hr.2
    have hlim : Tendsto (fun r : ℝ => τ ^ 2 * (1 - r) / (2 * r ^ 2)) (𝓝[Set.Ioc (0 : ℝ) 1] 1)
        (𝓝 0) := by
      have hc : ContinuousAt (fun r : ℝ => τ ^ 2 * (1 - r) / (2 * r ^ 2)) 1 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      have h0 := hc.tendsto
      simp only [sub_self, mul_zero, zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := squeeze_zero_norm' hbound hlim
    rw [ContinuousWithinAt, twistDefect_one]
    exact this
  · exact ((hopen x ⟨hx.1, hlt⟩).continuousAt (Ioo_mem_nhds hx.1 hlt)).continuousWithinAt

/-! ### The twisted density is Weil's symbol -/

/-- **The defect integral is the Lévy–Khintchine integral of the archimedean symbol**:
`∫_0^1 (1 − cos(τ log r))/(1 − r⁴) dr = ½(θ'(τ/2) − θ'(0))`. -/
theorem integral_twistDefect (τ : ℝ) :
    ∫ r in (0 : ℝ)..1, twistDefect τ r =
      (_root_.RHTower.gammaHardyPhaseRate (τ / 2) - _root_.RHTower.gammaHardyPhaseRate 0) / 2 := by
  have himg : (fun v : ℝ => Real.exp (-v)) '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith [Set.mem_Ioi.mp hv])⟩
    · rintro ⟨h0, h1⟩
      refine ⟨-Real.log r, ?_, ?_⟩
      · rw [Set.mem_Ioi, neg_pos]
        exact Real.log_neg h0 h1
      · simp only [neg_neg]
        exact Real.exp_log h0
  have hinj : Set.InjOn (fun v : ℝ => Real.exp (-v)) (Set.Ioi 0) :=
    (Real.exp_injective.comp neg_injective).injOn
  have hderiv : ∀ v ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun v : ℝ => Real.exp (-v)) (Real.exp (-v) * -1) (Set.Ioi 0) v :=
    fun v _ => ((hasDerivAt_id' v).neg.exp).hasDerivWithinAt
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  -- the integrand in the variable `v`
  have hint : ∀ v ∈ Set.Ioi (0 : ℝ),
      |Real.exp (-v) * -1| • twistDefect τ (Real.exp (-v)) =
        (fun x : ℝ => _root_.RHTower.archLevyDensity x * (1 - Real.cos (τ / 2 * x))) (2 * v) := by
    intro v _
    have h4 : Real.exp (-v) ^ 4 = Real.exp (-2 * (2 * v)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h1 : Real.exp (-(2 * v) / 2) = Real.exp (-v) := by
      congr 1
      ring
    have hcos : Real.cos (τ * -v) = Real.cos (τ / 2 * (2 * v)) := by
      rw [mul_neg, Real.cos_neg]
      congr 1
      ring
    simp only [_root_.RHTower.archLevyDensity, twistDefect, Real.log_exp, smul_eq_mul]
    rw [mul_neg_one, abs_neg, abs_of_pos (Real.exp_pos _), h4, h1, hcos]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hint,
    integral_comp_mul_left_Ioi
      (fun x : ℝ => _root_.RHTower.archLevyDensity x * (1 - Real.cos (τ / 2 * x))) 0 two_pos,
    mul_zero, ← _root_.RHTower.gammaHardyPhaseRate_sub_zero_eq_integral, smul_eq_mul]
  ring

/-- The mean of the twisted regular profile: the density of the twisted rows. -/
def twistedMean (τ : ℝ) : ℝ := regularMean - ∫ r in (0 : ℝ)..1, twistDefect τ r

/-- **The twisted density of the carrier is Weil's archimedean symbol**:
`4c(τ) + γ + log 4π = −A(τ/2)`. -/
theorem four_mul_twistedMean_add (τ : ℝ) :
    4 * twistedMean τ + Real.eulerMascheroniConstant + Real.log (4 * Real.pi) =
      -EF.gammaBracket (τ / 2) := by
  have h0 := _root_.RHTower.ArchimedeanAnomaly.gammaBracket_zero_eq
  rw [_root_.RHTower.WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate] at h0
  have h8 : Real.log (8 * Real.pi) = Real.log 2 + Real.log (4 * Real.pi) := by
    rw [show (8 : ℝ) * Real.pi = 2 * (4 * Real.pi) by ring,
      Real.log_mul (x := 2) (y := 4 * Real.pi) (by norm_num) (by positivity)]
  rw [twistedMean, integral_twistDefect, regularMean_eq,
    _root_.RHTower.WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
  rw [h8] at h0
  linarith

/-! ### The twisted rows -/

/-- The twisted smooth row at height `n`, with its endpoint. -/
def twistedSmoothRow (τ : ℝ) (n : ℕ) : ℝ := ∑ a ∈ Icc 1 n, twistedProfile τ ((a : ℝ) / n)

theorem twistedSmoothRow_eq (τ : ℝ) (n : ℕ) :
    twistedSmoothRow τ n = smoothRow n - ∑ k ∈ range n, twistDefect τ (((k : ℝ) + 1) / n) := by
  have hI : Icc 1 n = Ico 1 (n + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  have hsum : ∑ a ∈ Icc 1 n, twistDefect τ ((a : ℝ) / n) =
      ∑ k ∈ range n, twistDefect τ (((k : ℝ) + 1) / n) := by
    rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
  rw [twistedSmoothRow, smoothRow, ← hsum, ← Finset.sum_sub_distrib]
  rfl

theorem tendsto_smoothRow_div : Tendsto (fun n : ℕ => smoothRow n / n) atTop (𝓝 regularMean) := by
  have hbound : Tendsto (fun n : ℕ => (3 / 4 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => smoothRow n / n - regularMean) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e : smoothRow n / n - regularMean = rowError n / n := by
      unfold rowError
      field_simp
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos hn']
    exact div_le_div_of_nonneg_right (abs_rowError_le n) hn'.le
  have h := hzero.add_const regularMean
  rw [zero_add] at h
  exact h.congr fun n => by ring

/-- **The twisted density**: the twisted smooth row over `n` tends to `c(τ)`. -/
theorem tendsto_twistedSmoothRow_div (τ : ℝ) :
    Tendsto (fun n : ℕ => twistedSmoothRow τ n / n) atTop (𝓝 (twistedMean τ)) := by
  have hdef := tendsto_riemannSum_of_continuousOn_Ioc (continuousOn_twistDefect τ)
    (fun r hr => abs_twistDefect_le τ hr)
  have h := tendsto_smoothRow_div.sub hdef
  unfold twistedMean
  refine h.congr fun n => ?_
  rw [twistedSmoothRow_eq]
  ring

/-! ### The twisted orbit of the carrier -/

/-- The primitive row at height `n` of the coupled orbit twisted by the character `r ↦ r^{iτ}` of
the rational torus. -/
def twistedGeometricRow (τ : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 n, if Nat.Coprime n a then
    Real.cos (τ * Real.log ((a : ℝ) / n)) * jetKernel (a ^ 2) (n ^ 2) else 0

theorem twistedGeometricRow_zero {n : ℕ} (hn : 2 ≤ n) :
    twistedGeometricRow 0 n = geometricRow n := by
  rw [geometricRow_eq_sum_jetKernel hn, twistedGeometricRow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [zero_mul, Real.cos_zero, one_mul]

/-- **The twisted half-row**: the collision term `H_{n−1}/(4n)`, the same for every `τ`, plus the
twisted smooth row without its endpoint over `n²`. -/
theorem sum_cos_mul_jetKernel_sq (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ a ∈ Ico 1 n, Real.cos (τ * Real.log ((a : ℝ) / n)) * jetKernel (a ^ 2) (n ^ 2) =
      harm (n - 1) / (4 * n) + (twistedSmoothRow τ n - 3 / 8) / (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ a ∈ Ico 1 n,
      Real.cos (τ * Real.log ((a : ℝ) / n)) * jetKernel (a ^ 2) (n ^ 2) =
        1 / (4 * (n : ℝ)) * (1 / ((n : ℝ) - a)) +
          ((n : ℝ) ^ 2)⁻¹ * twistedProfile τ ((a : ℝ) / n) := by
    intro a ha
    have ha1 := (mem_Ico.mp ha).1
    have han := (mem_Ico.mp ha).2
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha1
    have h' : (a : ℝ) < n := by exact_mod_cast han
    have hsplit := twisted_profile_split τ (div_pos ha' hn') ((div_lt_one hn').mpr h')
    have h1 : (n : ℝ) - a ≠ 0 := (sub_pos.mpr h').ne'
    have h2 : (1 : ℝ) - (a : ℝ) / n = ((n : ℝ) - a) / n := by field_simp
    rw [jetKernel_sq_sq ha1 han]
    calc Real.cos (τ * Real.log ((a : ℝ) / n)) *
          (((n : ℝ) ^ 2)⁻¹ * (1 / (1 - ((a : ℝ) / n) ^ 4)))
        = ((n : ℝ) ^ 2)⁻¹ *
          (Real.cos (τ * Real.log ((a : ℝ) / n)) / (1 - ((a : ℝ) / n) ^ 4)) := by ring
      _ = ((n : ℝ) ^ 2)⁻¹ *
          (1 / (4 * (1 - (a : ℝ) / n)) + twistedProfile τ ((a : ℝ) / n)) := by rw [hsplit]
      _ = 1 / (4 * (n : ℝ)) * (1 / ((n : ℝ) - a)) +
          ((n : ℝ) ^ 2)⁻¹ * twistedProfile τ ((a : ℝ) / n) := by
          rw [h2]
          field_simp
  have hend : twistedProfile τ 1 = 3 / 8 := by
    rw [twistedProfile, twistDefect_one]
    norm_num [regularProfile]
  have hsmooth : ∑ a ∈ Ico 1 n, twistedProfile τ ((a : ℝ) / n) = twistedSmoothRow τ n - 3 / 8 := by
    have hI : Icc 1 n = insert n (Ico 1 n) := by
      ext k
      simp only [mem_Icc, mem_insert, mem_Ico]
      omega
    rw [twistedSmoothRow, hI, Finset.sum_insert (by simp), div_self hn'.ne', hend]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_Ico_inv_sub, hsmooth]
  ring

/-! ### The packet functional of the carrier -/

/-- The symbol of the carrier at the frequency `ρ` of a packet: the density of the orbit twisted
by the character of frequency `2ρ`, with the harmonic constant of the collision row and the mesh
constant of the comb of squares. -/
def carrierSymbol (ρ : ℝ) : ℝ :=
  4 * twistedMean (2 * ρ) + Real.eulerMascheroniConstant + Real.log (4 * Real.pi)

/-- **The symbol of the carrier is Weil's archimedean symbol.** -/
theorem carrierSymbol_eq (ρ : ℝ) : carrierSymbol ρ = -EF.gammaBracket ρ := by
  rw [carrierSymbol, four_mul_twistedMean_add, mul_div_cancel_left₀ ρ two_ne_zero]

/-- **The packet functional of the carrier is Weil's archimedean form**: the archimedean part of
Weil's functional without the pole is minus the integral of the spectral density of the packet
against the symbol of the carrier. -/
theorem weilArchRe_sub_pole_eq_carrier (f : _root_.RHTower.WeilOneSided.WeilTestFn) :
    _root_.RHTower.WeilOneSided.weilArchRe (EF.weilTest f.1 f.1) -
        (_root_.RHTower.weilPoleTerm (EF.weilTest f.1 f.1)).re =
      -(1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * carrierSymbol r) := by
  rw [_root_.RHTower.BlindPrimePowerSlack.weilArchRe_sub_pole_eq f, ← mul_neg, ← integral_neg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [carrierSymbol_eq]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
