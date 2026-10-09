import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lacunary theta sums near the real axis: Parseval over periods

For `S_k(x + iy) = Σ_n n^k e^{iπn²(x+iy)}` (`thetaMoment k y x`):

* **Parseval over a period** (`integral_norm_sq_tsum_thetaWave`,
  `integral_norm_sq_thetaMoment`): the frequencies `πn²` are distinct and `e^{iπn²x}` has period
  `2`, so `∫_X^{X+2}|S_k(x+iy)|²dx = 2Σ_n n^{2k}e^{-2πn²y}`.
* **Moment sums** (`tsum_pow_mul_exp_neg_two_sq_le`, `tsum_pow_mul_exp_neg_two_sq_ge`):
  `Σ_n n^{2k}e^{-2πn²y} ≍ y^{-k-1/2}`, the upper bound for every `y > 0` and `k ≥ 1` (comparison
  with the Gaussian integral), the lower bound for `y ≤ 1/4` (the terms `1/√y ≤ n ≤ 2/√y`).
* **Vertical variation** (`integral_norm_sq_thetaMoment_sub_le`): `∂_y S_k = −π S_{k+2}`, so when
  the height `y(x)` varies in `[y₀, y₀ + δ]` along a period,
  `∫|S_k(x+iy(x)) − S_k(x+iy₀)|² ≤ 2δ²π²Σ_n n^{2k+4}e^{-2πn²y₀}`.
* **Rays** (`integral_norm_sq_thetaMoment_ray_le`): along `τ = x − itx`, `x ∈ [x₂, x₁] ⊂ (−∞, 0)`,
  covering by periods bounds the `L²` mass by the number of periods times the Parseval mass at
  the lowest height.
-/

open Complex MeasureTheory
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem integral_cexp_pi_int_mul_period {k : ℤ} (hk : k ≠ 0) (X : ℝ) :
    ∫ x in X..X + 2, cexp (π * I * k * x) = 0 := by
  have hc : (π * I * k : ℂ) ≠ 0 := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    simp [Real.pi_ne_zero, I_ne_zero, this]
  rw [integral_exp_mul_complex hc]
  have : cexp (π * I * k * ((X + 2 : ℝ) : ℂ)) = cexp (π * I * k * (X : ℂ)) := by
    have h2 : (π * I * k * ((X + 2 : ℝ) : ℂ)) = π * I * k * X + k * (2 * π * I) := by
      push_cast; ring
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [this, sub_self, zero_div]

/-- The frequency `e^{iπn²x}`. -/
def thetaWave (n : ℕ) (x : ℝ) : ℂ := cexp (π * I * ((n : ℂ) ^ 2) * x)

theorem norm_thetaWave (n : ℕ) (x : ℝ) : ‖thetaWave n x‖ = 1 := by
  unfold thetaWave
  have : (π * I * ((n : ℂ) ^ 2) * x : ℂ) = ((π * n ^ 2 * x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, norm_exp_ofReal_mul_I]

theorem thetaWave_mul_conj (n m : ℕ) (x : ℝ) :
    thetaWave n x * starRingEnd ℂ (thetaWave m x) =
      cexp (π * I * (((n : ℤ) ^ 2 - (m : ℤ) ^ 2 : ℤ) : ℂ) * x) := by
  unfold thetaWave
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_pow, map_natCast, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem integral_thetaWave_mul_conj (n m : ℕ) (X : ℝ) :
    ∫ x in X..X + 2, thetaWave n x * starRingEnd ℂ (thetaWave m x) = if n = m then 2 else 0 := by
  simp_rw [thetaWave_mul_conj]
  split_ifs with h
  · subst h; simp
  · have hk : ((n : ℤ) ^ 2 - (m : ℤ) ^ 2) ≠ 0 := by
      intro h0
      have h1 : (n : ℤ) ^ 2 = (m : ℤ) ^ 2 := by linarith
      have h2 : (n : ℤ) = m := (sq_eq_sq₀ (by positivity) (by positivity)).1 h1
      exact h (by exact_mod_cast h2)
    exact integral_cexp_pi_int_mul_period hk X

/-- **Parseval over one period.** For absolutely summable `b`,
`∫_X^{X+2} |Σ_n b_n e^{iπn²x}|² dx = 2 Σ_n |b_n|²`. -/
theorem integral_norm_sq_tsum_thetaWave {b : ℕ → ℂ} (hb : Summable fun n => ‖b n‖) (X : ℝ) :
    ∫ x in X..X + 2, ‖∑' n, b n * thetaWave n x‖ ^ 2 = 2 * ∑' n, ‖b n‖ ^ 2 := by
  have hsx : ∀ x, Summable fun n => ‖b n * thetaWave n x‖ := fun x => by
    simpa [norm_mul, norm_thetaWave] using hb
  have hsx' : ∀ x, Summable fun n => ‖starRingEnd ℂ (b n * thetaWave n x)‖ := fun x => by
    simpa [Complex.norm_conj] using hsx x
  let F : ℕ × ℕ → C(ℝ, ℂ) := fun p =>
    ⟨fun x => b p.1 * starRingEnd ℂ (b p.2) *
        cexp (π * I * (((p.1 : ℤ) ^ 2 - (p.2 : ℤ) ^ 2 : ℤ) : ℂ) * x),
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))⟩
  have hpt : ∀ x, ((‖∑' n, b n * thetaWave n x‖ ^ 2 : ℝ) : ℂ) = ∑' p : ℕ × ℕ, F p x := by
    intro x
    have h1 : ((‖∑' n, b n * thetaWave n x‖ ^ 2 : ℝ) : ℂ) =
        (∑' n, b n * thetaWave n x) * starRingEnd ℂ (∑' n, b n * thetaWave n x) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1]
    rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm (hsx x) (hsx' x)]
    congr 1
    funext p
    simp only [F, ContinuousMap.coe_mk]
    rw [← thetaWave_mul_conj, map_mul]
    ring
  have hFsum : Summable fun p : ℕ × ℕ =>
      ‖(F p).restrict (⟨Set.uIcc X (X + 2), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (Summable.mul_of_nonneg hb hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    simp only [ContinuousMap.restrict_apply, F, ContinuousMap.coe_mk, norm_mul,
      Complex.norm_conj]
    have : ‖cexp (π * I * (((p.1 : ℤ) ^ 2 - (p.2 : ℤ) ^ 2 : ℤ) : ℂ) * ((x : ℝ) : ℂ))‖ = 1 := by
      have : (π * I * (((p.1 : ℤ) ^ 2 - (p.2 : ℤ) ^ 2 : ℤ) : ℂ) * ((x : ℝ) : ℂ)) =
          ((π * (((p.1 : ℤ) ^ 2 - (p.2 : ℤ) ^ 2 : ℤ) : ℝ) * x : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, norm_exp_ofReal_mul_I]
    rw [this, mul_one]
  have hint : ∀ p : ℕ × ℕ, ∫ x in X..X + 2, F p x =
      if p.1 = p.2 then 2 * (b p.1 * starRingEnd ℂ (b p.1)) else 0 := by
    intro p
    simp only [F, ContinuousMap.coe_mk]
    rw [intervalIntegral.integral_const_mul]
    have := integral_thetaWave_mul_conj p.1 p.2 X
    simp_rw [thetaWave_mul_conj] at this
    rw [this]
    split_ifs with h
    · rw [h]; ring
    · simp
  have hG : Summable fun p : ℕ × ℕ =>
      (if p.1 = p.2 then 2 * (b p.1 * starRingEnd ℂ (b p.1)) else 0 : ℂ) := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => 2 * (‖b p.1‖ * ‖b p.2‖))
      ((Summable.mul_of_nonneg hb hb (fun _ => norm_nonneg _)
        (fun _ => norm_nonneg _)).mul_left 2) (fun p => ?_)
    split_ifs with h
    · rw [h]; simp
    · simp; positivity
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hpt]
  rw [← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hFsum]
  simp_rw [hint]
  rw [hG.tsum_prod' (fun n => ?_)]
  · have hrow : ∀ n : ℕ, (∑' m : ℕ, (if n = m then 2 * (b n * starRingEnd ℂ (b n)) else 0 : ℂ)) =
        2 * (b n * starRingEnd ℂ (b n)) := by
      intro n
      simp_rw [eq_comm (a := n)]
      exact tsum_ite_eq n (fun _ => 2 * (b n * starRingEnd ℂ (b n)))
    simp only at hrow ⊢
    simp_rw [hrow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [tsum_mul_left]
  · exact (summable_of_ne_finset_zero (s := {n}) (fun m hm => by
      simp only [Finset.mem_singleton] at hm
      simp [Ne.symm hm]))


/-! ## Moment sums -/

theorem summable_pow_mul_exp_neg_sq (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => (n : ℝ) ^ k * Real.exp (-π * n ^ 2 * y) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_mul_exp_neg_nat_mul k (r := π * y) (by positivity))
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
  have : -π * (n : ℝ) ^ 2 * y ≤ -(π * y) * n := by
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hy.le) (sub_nonneg.mpr hn)]
  gcongr

/-- `Σ_{n ≥ 1} e^{-πn²y} ≤ 1/(2√y)`. -/
theorem tsum_exp_neg_sq_succ_le {y : ℝ} (hy : 0 < y) :
    ∑' n : ℕ, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y) ≤ 1 / (2 * Real.sqrt y) := by
  have hint : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(π * y) * x ^ 2) = 1 / (2 * Real.sqrt y) := by
    rw [integral_gaussian_Ioi]
    rw [show π / (π * y) = y⁻¹ by field_simp, Real.sqrt_inv]
    field_simp
  have hint' : IntegrableOn (fun x : ℝ => Real.exp (-(π * y) * x ^ 2)) (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (by positivity)).integrableOn
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun N => ?_)
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-(π * y) * x ^ 2)) (Set.Icc ((0 : ℕ) : ℝ) N) := by
    intro a ha b hb hab
    simp only [Set.mem_Icc, Nat.cast_zero] at ha hb
    apply Real.exp_le_exp.mpr
    have : a ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt (mul_pos Real.pi_pos hy))]
  have h1 := hanti.sum_le_integral_Ico (Nat.zero_le N)
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at h1
  calc ∑ i ∈ Finset.range N, Real.exp (-π * ((i : ℝ) + 1) ^ 2 * y)
      = ∑ i ∈ Finset.Ico 0 N, Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2) := by
        rw [Finset.range_eq_Ico]; refine Finset.sum_congr rfl fun i _ => by ring_nf
    _ ≤ ∫ x in (0 : ℝ)..N, Real.exp (-(π * y) * x ^ 2) := h1
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(π * y) * x ^ 2) := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
        exact setIntegral_mono_set hint' (Filter.Eventually.of_forall fun _ => by positivity)
          (Set.Ioc_subset_Ioi_self.eventuallyLE)
    _ = 1 / (2 * Real.sqrt y) := hint

/-- **Upper moment bound.** For `k ≥ 1` and `y > 0`,
`Σ_n n^{2k} e^{-2πn²y} ≤ (k!/π^k) y^{-k}/(2√y)`. -/
theorem tsum_pow_mul_exp_neg_two_sq_le {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy : 0 < y) :
    ∑' n : ℕ, (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) ≤
      (k.factorial / π ^ k) * y⁻¹ ^ k * (1 / (2 * Real.sqrt y)) := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) := by
    have := summable_pow_mul_exp_neg_sq (2 * k) (y := 2 * y) (by positivity)
    refine this.congr fun n => ?_
    ring_nf
  rw [hs.tsum_eq_zero_add]
  have h0 : (((0 : ℕ) : ℝ)) ^ (2 * k) * Real.exp (-2 * π * ((0 : ℕ) : ℝ) ^ 2 * y) = 0 := by
    simp; omega
  rw [h0, zero_add]
  have hterm : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (2 * k) * Real.exp (-2 * π * ((n + 1 : ℕ) : ℝ) ^ 2 * y) ≤
      (k.factorial / π ^ k) * y⁻¹ ^ k * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y) := by
    intro n
    set s : ℝ := π * ((n : ℝ) + 1) ^ 2 * y with hs_def
    have hs0 : 0 ≤ s := by positivity
    have hpow : s ^ k / k.factorial ≤ Real.exp s := by
      exact Real.pow_div_factorial_le_exp s hs0 k
    have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hsk : s ^ k ≤ k.factorial * Real.exp s := by
      rw [div_le_iff₀ hfac] at hpow; linarith
    have hexp : Real.exp (-2 * π * ((n + 1 : ℕ) : ℝ) ^ 2 * y) =
        Real.exp (-s) * Real.exp (-s) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    have hsk' : ((n + 1 : ℕ) : ℝ) ^ (2 * k) = s ^ k * (π ^ k)⁻¹ * y⁻¹ ^ k := by
      rw [hs_def, mul_pow, mul_pow, ← pow_mul]
      push_cast
      field_simp
      rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hy.ne')]
    rw [hsk']
    have hpk : (0 : ℝ) < π ^ k := by positivity
    have hyk : (0 : ℝ) < y⁻¹ ^ k := by positivity
    have : s ^ k * Real.exp (-s) ≤ k.factorial := by
      have h1 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-s), Real.exp_pos s]
    have hr : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y) = Real.exp (-s) := by
      congr 1; rw [hs_def]; ring
    rw [hr]
    calc s ^ k * (π ^ k)⁻¹ * y⁻¹ ^ k * (Real.exp (-s) * Real.exp (-s))
        = (s ^ k * Real.exp (-s)) * ((π ^ k)⁻¹ * y⁻¹ ^ k * Real.exp (-s)) := by ring
      _ ≤ k.factorial * ((π ^ k)⁻¹ * y⁻¹ ^ k * Real.exp (-s)) := by
          gcongr
      _ = (k.factorial / π ^ k) * y⁻¹ ^ k * Real.exp (-s) := by ring
  have hs2 : Summable fun n : ℕ => Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y) := by
    have := (summable_pow_mul_exp_neg_sq 0 hy).comp_injective (add_left_injective 1)
    refine this.congr fun n => ?_
    simp
  calc ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (2 * k) * Real.exp (-2 * π * ((n + 1 : ℕ) : ℝ) ^ 2 * y)
      ≤ ∑' n : ℕ, (k.factorial / π ^ k) * y⁻¹ ^ k * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y) :=
        Summable.tsum_le_tsum hterm (hs.comp_injective (add_left_injective 1)) (hs2.mul_left _)
    _ = (k.factorial / π ^ k) * y⁻¹ ^ k * ∑' n : ℕ, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y) :=
        tsum_mul_left
    _ ≤ (k.factorial / π ^ k) * y⁻¹ ^ k * (1 / (2 * Real.sqrt y)) := by
        gcongr
        exact tsum_exp_neg_sq_succ_le hy


/-- **Lower moment bound.** For `0 < y ≤ 1/4`,
`Σ_n n^{2k} e^{-2πn²y} ≥ (e^{-8π}/2) y^{-k}/√y`: the terms `1/√y ≤ n ≤ 2/√y` suffice. -/
theorem tsum_pow_mul_exp_neg_two_sq_ge (k : ℕ) {y : ℝ} (hy : 0 < y) (hy4 : y ≤ 1 / 4) :
    Real.exp (-8 * π) / 2 * y⁻¹ ^ k * (1 / Real.sqrt y) ≤
      ∑' n : ℕ, (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) := by
  set s : ℝ := 1 / Real.sqrt y with hs_def
  have hsq : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hs0 : 0 < s := by positivity
  have hs2 : 2 ≤ s := by
    rw [hs_def, le_div_iff₀ hsq]
    have : Real.sqrt y ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hy4
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    linarith
  have hsy : s ^ 2 * y = 1 := by
    rw [hs_def, div_pow, Real.sq_sqrt hy.le]; field_simp
  set N₁ : ℕ := ⌈s⌉₊
  set N₂ : ℕ := ⌊2 * s⌋₊
  have hN₁ : (N₁ : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0.le
  have hN₁' : s ≤ N₁ := Nat.le_ceil s
  have hN₂ : 2 * s - 1 < N₂ := Nat.sub_one_lt_floor (2 * s)
  have hN₂' : (N₂ : ℝ) ≤ 2 * s := Nat.floor_le (by positivity)
  have hle : N₁ ≤ N₂ + 1 := by
    have : (N₁ : ℝ) ≤ N₂ + 1 := by linarith
    exact_mod_cast this
  have hcard : s / 2 ≤ ((Finset.Icc N₁ N₂).card : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub hle]
    push_cast
    linarith
  have hterm : ∀ n ∈ Finset.Icc N₁ N₂,
      y⁻¹ ^ k * Real.exp (-8 * π) ≤ (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : s ≤ (n : ℝ) := le_trans hN₁' (by exact_mod_cast hn.1)
    have h2 : (n : ℝ) ≤ 2 * s := le_trans (by exact_mod_cast hn.2) hN₂'
    have hpow : y⁻¹ ^ k ≤ (n : ℝ) ^ (2 * k) := by
      rw [pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      have : y⁻¹ = s ^ 2 := by
        rw [eq_comm, ← mul_inv_eq_one₀ (inv_ne_zero hy.ne'), inv_inv]; exact hsy
      rw [this]; exact pow_le_pow_left₀ hs0.le h1 2
    have hexp : Real.exp (-8 * π) ≤ Real.exp (-2 * π * n ^ 2 * y) := by
      apply Real.exp_le_exp.mpr
      have : (n : ℝ) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this hy.le, Real.pi_pos]
    exact mul_le_mul hpow hexp (by positivity) (by positivity)
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) := by
    have := summable_pow_mul_exp_neg_sq (2 * k) (y := 2 * y) (by positivity)
    refine this.congr fun n => ?_
    ring_nf
  calc Real.exp (-8 * π) / 2 * y⁻¹ ^ k * (1 / Real.sqrt y)
      = (s / 2) * (y⁻¹ ^ k * Real.exp (-8 * π)) := by rw [hs_def]; ring
    _ ≤ ((Finset.Icc N₁ N₂).card : ℝ) * (y⁻¹ ^ k * Real.exp (-8 * π)) := by gcongr
    _ = ∑ n ∈ Finset.Icc N₁ N₂, y⁻¹ ^ k * Real.exp (-8 * π) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Finset.Icc N₁ N₂, (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) :=
        hsum.sum_le_tsum _ (fun _ _ => by positivity)

/-! ## Theta moments `S_k(x+iy) = Σ n^k e^{iπn²(x+iy)}` -/

/-- `S_k(x + iy) = Σ_n n^k e^{-πn²y} e^{iπn²x}`. -/
def thetaMoment (k : ℕ) (y x : ℝ) : ℂ :=
  ∑' n : ℕ, (((n : ℝ) ^ k * Real.exp (-π * n ^ 2 * y) : ℝ) : ℂ) * thetaWave n x

theorem summable_norm_thetaMoment_coeff (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => ‖(((n : ℝ) ^ k * Real.exp (-π * n ^ 2 * y) : ℝ) : ℂ)‖ := by
  refine (summable_pow_mul_exp_neg_sq k hy).congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Parseval for `S_k` on a horizontal period. -/
theorem integral_norm_sq_thetaMoment (k : ℕ) {y : ℝ} (hy : 0 < y) (X : ℝ) :
    ∫ x in X..X + 2, ‖thetaMoment k y x‖ ^ 2 =
      2 * ∑' n : ℕ, (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y) := by
  unfold thetaMoment
  rw [integral_norm_sq_tsum_thetaWave (summable_norm_thetaMoment_coeff k hy)]
  congr 1
  refine tsum_congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
  ring_nf


/-! ## Vertical variation -/

theorem hasDerivAt_thetaMoment (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun s => thetaMoment k s x) (-π * thetaMoment (k + 2) y x) y := by
  unfold thetaMoment
  have hy2 : 0 < y / 2 := by positivity
  have hu : Summable fun n : ℕ => π * ((n : ℝ) ^ (k + 2) * Real.exp (-π * n ^ 2 * (y / 2))) :=
    (summable_pow_mul_exp_neg_sq (k + 2) hy2).mul_left π
  have hderiv : ∀ (n : ℕ), ∀ s ∈ Set.Ioi (y / 2),
      HasDerivAt (fun s : ℝ => (((n : ℝ) ^ k * Real.exp (-π * n ^ 2 * s) : ℝ) : ℂ) * thetaWave n x)
        ((((n : ℝ) ^ k * (Real.exp (-π * n ^ 2 * s) * (-π * n ^ 2)) : ℝ) : ℂ) * thetaWave n x) s := by
    intro n s _
    have h1 : HasDerivAt (fun s : ℝ => -π * (n : ℝ) ^ 2 * s) (-π * n ^ 2) s :=
      ((hasDerivAt_id s).const_mul (-π * (n : ℝ) ^ 2)).congr_deriv (mul_one _)
    have h2 := ((Real.hasDerivAt_exp _).comp s h1).const_mul ((n : ℝ) ^ k)
    exact h2.ofReal_comp.mul_const _
  have hbound : ∀ (n : ℕ), ∀ s ∈ Set.Ioi (y / 2),
      ‖(((n : ℝ) ^ k * (Real.exp (-π * n ^ 2 * s) * (-π * n ^ 2)) : ℝ) : ℂ) * thetaWave n x‖ ≤
        π * ((n : ℝ) ^ (k + 2) * Real.exp (-π * n ^ 2 * (y / 2))) := by
    intro n s hs
    rw [norm_mul, norm_thetaWave, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have e : (n : ℝ) ^ k * (Real.exp (-π * n ^ 2 * s) * (-π * n ^ 2)) =
        -(π * ((n : ℝ) ^ (k + 2) * Real.exp (-π * n ^ 2 * s))) := by ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)]
    have : y / 2 < s := hs
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))) (sub_nonneg.mpr this.le)]
  have hy0 : y ∈ Set.Ioi (y / 2) := by simp only [Set.mem_Ioi]; linarith
  have hsum0 : Summable fun n : ℕ =>
      (((n : ℝ) ^ k * Real.exp (-π * n ^ 2 * y) : ℝ) : ℂ) * thetaWave n x :=
    Summable.of_norm (by simpa [norm_mul, norm_thetaWave] using
      summable_norm_thetaMoment_coeff k hy)
  have := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hderiv hbound hy0
    hsum0 hy0
  refine this.congr_deriv ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  push_cast
  ring

theorem continuousOn_thetaMoment (k : ℕ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    ContinuousOn (fun p : ℝ × ℝ => thetaMoment k p.2 p.1) (Set.univ ×ˢ Set.Ici y₀) := by
  unfold thetaMoment
  refine continuousOn_tsum (u := fun n : ℕ => (n : ℝ) ^ k * Real.exp (-π * n ^ 2 * y₀))
    (fun n => ?_) (summable_pow_mul_exp_neg_sq k hy₀) (fun n p hp => ?_)
  · apply Continuous.continuousOn
    unfold thetaWave
    fun_prop
  · rw [norm_mul, norm_thetaWave, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have : y₀ ≤ p.2 := hp.2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))) (sub_nonneg.mpr this)]

/-- `S_k(x+iy₁) − S_k(x+iy₀) = −π∫_{y₀}^{y₁} S_{k+2}(x+is) ds`. -/
theorem thetaMoment_sub_eq_integral (k : ℕ) {y₀ y₁ : ℝ} (hy₀ : 0 < y₀) (h : y₀ ≤ y₁) (x : ℝ) :
    thetaMoment k y₁ x - thetaMoment k y₀ x = ∫ s in y₀..y₁, -π * thetaMoment (k + 2) s x := by
  have hc : ContinuousOn (fun s => -π * thetaMoment (k + 2) s x) (Set.Icc y₀ y₁) := by
    refine continuousOn_const.mul ?_
    have := (continuousOn_thetaMoment (k + 2) hy₀).comp
      (Continuous.continuousOn (continuous_const.prodMk continuous_id) : ContinuousOn
        (fun s : ℝ => (x, s)) (Set.Icc y₀ y₁)) (fun s hs => ⟨Set.mem_univ _, hs.1⟩)
    exact this
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => thetaMoment k s x)
    (fun s hs => ?_)
    (hc.intervalIntegrable_of_Icc h)).symm
  rw [Set.uIcc_of_le h] at hs
  exact hasDerivAt_thetaMoment k (lt_of_lt_of_le hy₀ hs.1) x

/-- Cauchy–Schwarz on an interval: `(∫_a^b g)² ≤ (b − a)∫_a^b g²`. -/
theorem sq_integral_le_mul_integral_sq {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  have hℓ : 0 < b - a := sub_pos.mpr h
  set J := ∫ x in a..b, g x
  set μ := J / (b - a)
  have hint1 : IntervalIntegrable g MeasureTheory.volume a b := hg.intervalIntegrable_of_Icc hab
  have hint2 : IntervalIntegrable (fun x => g x ^ 2) MeasureTheory.volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab
  have hnn : 0 ≤ ∫ x in a..b, (g x - μ) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
  have hexp : ∫ x in a..b, (g x - μ) ^ 2 = (∫ x in a..b, g x ^ 2) - 2 * μ * J + μ ^ 2 * (b - a) := by
    have hpt : (fun x => (g x - μ) ^ 2) = fun x => g x ^ 2 - 2 * μ * g x + μ ^ 2 := by
      funext x; ring
    rw [hpt, intervalIntegral.integral_add (hint2.sub (hint1.const_mul _))
        intervalIntegrable_const, intervalIntegral.integral_sub hint2 (hint1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at hnn
  have hμ : μ * (b - a) = J := div_mul_cancel₀ J hℓ.ne'
  nlinarith [hμ]


theorem continuousOn_thetaMoment_comp (k : ℕ) {y₀ : ℝ} (hy₀ : 0 < y₀) {s : Set ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g s) (hgs : ∀ x ∈ s, y₀ ≤ g x) :
    ContinuousOn (fun x => thetaMoment k (g x) x) s := by
  have h := (continuousOn_thetaMoment k hy₀).comp (continuousOn_id.prodMk hg)
    (fun x hx => ⟨Set.mem_univ _, hgs x hx⟩)
  refine h.congr fun x _ => ?_
  simp only [Function.comp_apply, id_eq]

/-- Pointwise vertical variation: `|S_k(x+iy) − S_k(x+iy₀)|² ≤ δπ²∫_{y₀}^{y₀+δ}|S_{k+2}(x+is)|²ds`
for `y₀ ≤ y ≤ y₀ + δ`. -/
theorem norm_sq_thetaMoment_sub_le (k : ℕ) {y₀ y δ : ℝ} (hy₀ : 0 < y₀) (h₀ : y₀ ≤ y)
    (h₁ : y ≤ y₀ + δ) (x : ℝ) :
    ‖thetaMoment k y x - thetaMoment k y₀ x‖ ^ 2 ≤
      δ * π ^ 2 * ∫ s in y₀..y₀ + δ, ‖thetaMoment (k + 2) s x‖ ^ 2 := by
  have hcont : ContinuousOn (fun s => thetaMoment (k + 2) s x) (Set.Ici y₀) := by
    have := (continuousOn_thetaMoment (k + 2) hy₀).comp
      (Continuous.continuousOn (continuous_const.prodMk continuous_id) : ContinuousOn
        (fun s : ℝ => (x, s)) (Set.Ici y₀)) (fun s hs => ⟨Set.mem_univ _, hs⟩)
    exact this
  have hnc : ContinuousOn (fun s => ‖thetaMoment (k + 2) s x‖) (Set.Ici y₀) :=
    continuous_norm.comp_continuousOn hcont
  rw [thetaMoment_sub_eq_integral k hy₀ h₀ x]
  have hA : ‖∫ s in y₀..y, -π * thetaMoment (k + 2) s x‖ ≤
      ∫ s in y₀..y, π * ‖thetaMoment (k + 2) s x‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm h₀).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hB : (∫ s in y₀..y, π * ‖thetaMoment (k + 2) s x‖) ^ 2 ≤
      (y - y₀) * ∫ s in y₀..y, (π * ‖thetaMoment (k + 2) s x‖) ^ 2 :=
    sq_integral_le_mul_integral_sq h₀ (continuousOn_const.mul (hnc.mono Set.Icc_subset_Ici_self))
  have hnn : 0 ≤ ∫ s in y₀..y, π * ‖thetaMoment (k + 2) s x‖ :=
    intervalIntegral.integral_nonneg h₀ (fun s _ => by positivity)
  have hδ : 0 ≤ δ := by linarith
  have hC : ∫ s in y₀..y, (π * ‖thetaMoment (k + 2) s x‖) ^ 2 ≤
      π ^ 2 * ∫ s in y₀..y₀ + δ, ‖thetaMoment (k + 2) s x‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_interval le_rfl h₀ h₁
      (Filter.Eventually.of_forall fun s => by positivity) ?_ |>.trans (le_of_eq ?_)
    · exact (((continuousOn_const.mul hnc).pow 2).mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc
        (by linarith)
    · refine intervalIntegral.integral_congr fun s _ => ?_
      ring
  calc ‖∫ s in y₀..y, -π * thetaMoment (k + 2) s x‖ ^ 2
      ≤ (∫ s in y₀..y, π * ‖thetaMoment (k + 2) s x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hA 2
    _ ≤ (y - y₀) * ∫ s in y₀..y, (π * ‖thetaMoment (k + 2) s x‖) ^ 2 := hB
    _ ≤ δ * (π ^ 2 * ∫ s in y₀..y₀ + δ, ‖thetaMoment (k + 2) s x‖ ^ 2) := by
        gcongr
        · exact intervalIntegral.integral_nonneg h₀ (fun s _ => by positivity)
        · linarith
    _ = δ * π ^ 2 * ∫ s in y₀..y₀ + δ, ‖thetaMoment (k + 2) s x‖ ^ 2 := by ring

/-- **Vertical variation over a period.** If `y₀ ≤ y(x) ≤ y₀ + δ` on `[X, X+2]`, then
`∫_X^{X+2}|S_k(x+iy(x)) − S_k(x+iy₀)|²dx ≤ 2δ²π² Σ_n n^{2k+4}e^{-2πn²y₀}`. -/
theorem integral_norm_sq_thetaMoment_sub_le (k : ℕ) {y₀ δ : ℝ} (hy₀ : 0 < y₀) (hδ : 0 ≤ δ)
    {X : ℝ} {yf : ℝ → ℝ} (hyc : ContinuousOn yf (Set.Icc X (X + 2)))
    (hyl : ∀ x ∈ Set.Icc X (X + 2), y₀ ≤ yf x) (hyu : ∀ x ∈ Set.Icc X (X + 2), yf x ≤ y₀ + δ) :
    ∫ x in X..X + 2, ‖thetaMoment k (yf x) x - thetaMoment k y₀ x‖ ^ 2 ≤
      δ ^ 2 * π ^ 2 * (2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) * Real.exp (-2 * π * n ^ 2 * y₀)) := by
  have hX : X ≤ X + 2 := by linarith
  set f : ℝ → ℝ → ℝ := fun x s => ‖thetaMoment (k + 2) s x‖ ^ 2 with hf
  have hfc : ContinuousOn (Function.uncurry f) (Set.Icc X (X + 2) ×ˢ Set.Icc y₀ (y₀ + δ)) := by
    have := (continuous_norm.comp_continuousOn (continuousOn_thetaMoment (k + 2) hy₀)).pow 2
    refine this.mono fun p hp => ⟨Set.mem_univ _, hp.2.1⟩
  have hfint : MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc X (X + 2))).prod
        (MeasureTheory.volume.restrict (Set.Ioc y₀ (y₀ + δ)))) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    refine (hfc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
    rw [Set.uIoc_of_le hX]
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hG : MeasureTheory.Integrable (fun x => ∫ s, f x s ∂(MeasureTheory.volume.restrict
      (Set.Ioc y₀ (y₀ + δ)))) (MeasureTheory.volume.restrict (Set.uIoc X (X + 2))) :=
    hfint.integral_prod_left
  have hswap := intervalIntegral_integral_swap hfint
  have hpt : ∀ x ∈ Set.Icc X (X + 2), ‖thetaMoment k (yf x) x - thetaMoment k y₀ x‖ ^ 2 ≤
      δ * π ^ 2 * ∫ s, f x s ∂(MeasureTheory.volume.restrict (Set.Ioc y₀ (y₀ + δ))) := by
    intro x hx
    rw [← intervalIntegral.integral_of_le (by linarith)]
    exact norm_sq_thetaMoment_sub_le k hy₀ (hyl x hx) (hyu x hx) x
  have hLc : ContinuousOn (fun x => ‖thetaMoment k (yf x) x - thetaMoment k y₀ x‖ ^ 2)
      (Set.Icc X (X + 2)) := by
    have h1 : ContinuousOn (fun x => thetaMoment k (yf x) x) (Set.Icc X (X + 2)) :=
      continuousOn_thetaMoment_comp k hy₀ hyc hyl
    have h2 : ContinuousOn (fun x => thetaMoment k y₀ x) (Set.Icc X (X + 2)) :=
      continuousOn_thetaMoment_comp k hy₀ (g := fun _ => y₀) continuousOn_const
        (fun _ _ => le_rfl)
    exact (continuous_norm.comp_continuousOn (h1.sub h2)).pow 2
  have hstep1 : ∫ x in X..X + 2, ‖thetaMoment k (yf x) x - thetaMoment k y₀ x‖ ^ 2 ≤
      ∫ x in X..X + 2, δ * π ^ 2 *
        ∫ s, f x s ∂(MeasureTheory.volume.restrict (Set.Ioc y₀ (y₀ + δ))) := by
    refine intervalIntegral.integral_mono_on hX (hLc.intervalIntegrable_of_Icc hX) ?_ hpt
    refine (IntervalIntegrable.const_mul ?_ _)
    rw [intervalIntegrable_iff, Set.uIoc_of_le hX]
    rw [Set.uIoc_of_le hX] at hG
    exact hG
  have hstep2 : ∫ x in X..X + 2, ∫ s, f x s ∂(MeasureTheory.volume.restrict (Set.Ioc y₀ (y₀ + δ))) ≤
      δ * (2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) * Real.exp (-2 * π * n ^ 2 * y₀)) := by
    rw [hswap]
    rw [← intervalIntegral.integral_of_le (by linarith)]
    have hpar : ∀ s ∈ Set.Icc y₀ (y₀ + δ), ∫ x in X..X + 2, f x s ≤
        2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) * Real.exp (-2 * π * n ^ 2 * y₀) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hy₀ hs.1
      simp only [hf]
      rw [integral_norm_sq_thetaMoment (k + 2) hs0 X]
      have hsum : ∀ z : ℝ, 0 < z → Summable fun n : ℕ =>
          (n : ℝ) ^ (2 * (k + 2)) * Real.exp (-2 * π * n ^ 2 * z) := fun z hz =>
        (summable_pow_mul_exp_neg_sq (2 * (k + 2)) (by positivity : 0 < 2 * z)).congr
          fun n => by ring_nf
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine Summable.tsum_le_tsum (fun n => ?_) (hsum s hs0) (hsum y₀ hy₀)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))) (sub_nonneg.mpr hs.1)]
    calc ∫ s in y₀..y₀ + δ, ∫ x in X..X + 2, f x s
        ≤ ∫ s in y₀..y₀ + δ, 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) *
            Real.exp (-2 * π * n ^ 2 * y₀) := by
          refine intervalIntegral.integral_mono_on (by linarith) ?_ intervalIntegrable_const hpar
          have := hfint.integral_prod_right
          rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith : y₀ ≤ y₀ + δ)]
          refine this.congr (Filter.Eventually.of_forall fun s => ?_)
          simp only
          rw [intervalIntegral.integral_of_le hX, Set.uIoc_of_le hX]
          rfl
      _ = δ * (2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) * Real.exp (-2 * π * n ^ 2 * y₀)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc ∫ x in X..X + 2, ‖thetaMoment k (yf x) x - thetaMoment k y₀ x‖ ^ 2
      ≤ ∫ x in X..X + 2, δ * π ^ 2 *
          ∫ s, f x s ∂(MeasureTheory.volume.restrict (Set.Ioc y₀ (y₀ + δ))) := hstep1
    _ = δ * π ^ 2 * ∫ x in X..X + 2,
          ∫ s, f x s ∂(MeasureTheory.volume.restrict (Set.Ioc y₀ (y₀ + δ))) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ δ * π ^ 2 * (δ * (2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) *
          Real.exp (-2 * π * n ^ 2 * y₀))) := by gcongr
    _ = δ ^ 2 * π ^ 2 * (2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) *
          Real.exp (-2 * π * n ^ 2 * y₀)) := by ring


/-! ## Rays approaching the real axis -/

/-- `Σ_n n^{2k} e^{-2πn²y}`, the Parseval mass of `S_k` at height `y`. -/
def thetaMomentMass (k : ℕ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y)

theorem thetaMomentMass_nonneg (k : ℕ) (y : ℝ) : 0 ≤ thetaMomentMass k y :=
  tsum_nonneg fun _ => by positivity

/-- **Ray bound.** Along the ray `τ = x − itx` (`x ∈ [x₂, x₁]`, `x₁ < 0`), the `L²` mass of `S_k` is
at most `K(4Σ_k(y₀) + 4δ²π²Σ_{k+2}(y₀))`, where `y₀ = −tx₁`, `δ = t(x₁ − x₂ + 2)` and
`K = ⌈(x₁ − x₂)/2⌉` periods cover the segment. -/
theorem integral_norm_sq_thetaMoment_ray_le (k : ℕ) {t x₁ x₂ : ℝ} (ht : 0 < t) (hx : x₂ ≤ x₁)
    (hx₁ : x₁ < 0) :
    ∫ x in x₂..x₁, ‖thetaMoment k (t * -x) x‖ ^ 2 ≤
      (⌈(x₁ - x₂) / 2⌉₊ : ℝ) * (4 * thetaMomentMass k (t * -x₁) +
        4 * (t * (x₁ - x₂ + 2)) ^ 2 * π ^ 2 * thetaMomentMass (k + 2) (t * -x₁)) := by
  set K : ℕ := ⌈(x₁ - x₂) / 2⌉₊ with hK_def
  set y₀ : ℝ := t * -x₁ with hy₀_def
  set δ : ℝ := t * (x₁ - x₂ + 2) with hδ_def
  have hy₀ : 0 < y₀ := by rw [hy₀_def]; nlinarith
  have hδ : 0 ≤ δ := by rw [hδ_def]; nlinarith
  have hK1 : (x₁ - x₂) / 2 ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) < (x₁ - x₂) / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  set a : ℕ → ℝ := fun i => x₁ - 2 * K + 2 * i with ha_def
  set g : ℝ → ℝ := fun x => ‖thetaMoment k (t * -x) x‖ ^ 2 with hg_def
  have hgc : ContinuousOn g (Set.Icc (a 0) x₁) := by
    have h := continuousOn_thetaMoment_comp k hy₀ (s := Set.Icc (a 0) x₁)
      (g := fun x => t * -x) (by fun_prop) (fun x hx => by
        simp only [hy₀_def]; nlinarith [hx.2])
    exact (continuous_norm.comp_continuousOn h).pow 2
  have ha0 : a 0 ≤ x₂ := by simp only [ha_def]; push_cast; linarith
  have haK : a K = x₁ := by simp only [ha_def]; ring
  have hstep1 : ∫ x in x₂..x₁, g x ≤ ∫ x in a 0..x₁, g x :=
    intervalIntegral.integral_mono_interval ha0 hx le_rfl
      (Filter.Eventually.of_forall fun x => by positivity)
      (hgc.intervalIntegrable_of_Icc (by linarith))
  have hper : ∀ i < K, ∫ x in a i..a (i + 1), g x ≤
      4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 * thetaMomentMass (k + 2) y₀ := by
    intro i hi
    have hai : a (i + 1) = a i + 2 := by simp only [ha_def]; push_cast; ring
    rw [hai]
    have hsub : Set.Icc (a i) (a i + 2) ⊆ Set.Icc (a 0) x₁ := by
      intro x hx
      have hi' : (i : ℝ) + 1 ≤ K := by exact_mod_cast hi
      constructor
      · have : a 0 ≤ a i := by simp only [ha_def]; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
        linarith [hx.1]
      · have : a i + 2 ≤ x₁ := by simp only [ha_def]; linarith
        linarith [hx.2]
    have hyl : ∀ x ∈ Set.Icc (a i) (a i + 2), y₀ ≤ t * -x := by
      intro x hx; have := (hsub hx).2; simp only [hy₀_def]; nlinarith
    have hyu : ∀ x ∈ Set.Icc (a i) (a i + 2), t * -x ≤ y₀ + δ := by
      intro x hx
      have h1 := (hsub hx).1
      have : a 0 = x₁ - 2 * K := by simp only [ha_def]; push_cast; ring
      simp only [hy₀_def, hδ_def]
      nlinarith
    have hyc : ContinuousOn (fun x : ℝ => t * -x) (Set.Icc (a i) (a i + 2)) := by fun_prop
    have hV := integral_norm_sq_thetaMoment_sub_le k hy₀ hδ hyc hyl hyu
    have hP := integral_norm_sq_thetaMoment k hy₀ (a i)
    have hc1 : ContinuousOn (fun x => thetaMoment k (t * -x) x) (Set.Icc (a i) (a i + 2)) :=
      continuousOn_thetaMoment_comp k hy₀ hyc hyl
    have hc0 : ContinuousOn (fun x => thetaMoment k y₀ x) (Set.Icc (a i) (a i + 2)) :=
      continuousOn_thetaMoment_comp k hy₀ (g := fun _ => y₀) continuousOn_const
        (fun _ _ => le_rfl)
    have hI0 : IntervalIntegrable (fun x => ‖thetaMoment k y₀ x‖ ^ 2) MeasureTheory.volume
        (a i) (a i + 2) :=
      ((continuous_norm.comp_continuousOn hc0).pow 2).intervalIntegrable_of_Icc (by linarith)
    have hId : IntervalIntegrable (fun x => ‖thetaMoment k (t * -x) x - thetaMoment k y₀ x‖ ^ 2)
        MeasureTheory.volume (a i) (a i + 2) :=
      ((continuous_norm.comp_continuousOn (hc1.sub hc0)).pow 2).intervalIntegrable_of_Icc
        (by linarith)
    calc ∫ x in a i..a i + 2, g x
        ≤ ∫ x in a i..a i + 2, (2 * ‖thetaMoment k y₀ x‖ ^ 2 +
            2 * ‖thetaMoment k (t * -x) x - thetaMoment k y₀ x‖ ^ 2) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            ((hgc.mono hsub).intervalIntegrable_of_Icc (by linarith))
            ((hI0.const_mul 2).add (hId.const_mul 2)) fun x _ => ?_
          simp only [hg_def]
          have h := norm_add_le (thetaMoment k y₀ x)
            (thetaMoment k (t * -x) x - thetaMoment k y₀ x)
          rw [add_sub_cancel] at h
          nlinarith [mul_self_le_mul_self (norm_nonneg _) h,
            sq_nonneg (‖thetaMoment k y₀ x‖ -
              ‖thetaMoment k (t * -x) x - thetaMoment k y₀ x‖)]
      _ = 2 * (∫ x in a i..a i + 2, ‖thetaMoment k y₀ x‖ ^ 2) +
            2 * (∫ x in a i..a i + 2, ‖thetaMoment k (t * -x) x - thetaMoment k y₀ x‖ ^ 2) := by
          rw [intervalIntegral.integral_add (hI0.const_mul 2) (hId.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ 2 * (2 * thetaMomentMass k y₀) +
            2 * (δ ^ 2 * π ^ 2 * (2 * thetaMomentMass (k + 2) y₀)) := by
          rw [hP]
          unfold thetaMomentMass
          linarith [hV]
      _ = 4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 * thetaMomentMass (k + 2) y₀ := by ring
  have hsum : ∑ i ∈ Finset.range K, ∫ x in a i..a (i + 1), g x = ∫ x in a 0..a K, g x := by
    refine intervalIntegral.sum_integral_adjacent_intervals fun i hi => ?_
    have hai : a (i + 1) = a i + 2 := by simp only [ha_def]; push_cast; ring
    rw [hai]
    refine (hgc.mono fun x hx => ?_).intervalIntegrable_of_Icc (by linarith)
    have hi' : (i : ℝ) + 1 ≤ K := by exact_mod_cast hi
    constructor
    · have : a 0 ≤ a i := by simp only [ha_def]; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      linarith [hx.1]
    · have : a i + 2 ≤ x₁ := by simp only [ha_def]; linarith
      linarith [hx.2]
  calc ∫ x in x₂..x₁, ‖thetaMoment k (t * -x) x‖ ^ 2 = ∫ x in x₂..x₁, g x := rfl
    _ ≤ ∫ x in a 0..x₁, g x := hstep1
    _ = ∑ i ∈ Finset.range K, ∫ x in a i..a (i + 1), g x := by rw [hsum, haK]
    _ ≤ ∑ _i ∈ Finset.range K,
          (4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 * thetaMomentMass (k + 2) y₀) :=
        Finset.sum_le_sum fun i hi => hper i (Finset.mem_range.mp hi)
    _ = (K : ℝ) * (4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 * thetaMomentMass (k + 2) y₀) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end GaloisForLFunctions.HTGeometry
