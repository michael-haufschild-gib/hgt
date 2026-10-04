import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries

/-!
# Dirichlet series with bounded partial sums

Let `c : ℕ → ℂ` and `s₀ ∈ ℂ` be such that the partial sums `Σ_{n<N} c(n) n^{−s₀}` are bounded by
`M`.  Then for `Re s > Re s₀` the partial sums `Σ_{n<N} c(n) n^{−s}` converge
(`tendsto_sum_term_contLSeries`), their limit `contLSeries c s₀` is holomorphic on
`Re s > Re s₀` (`differentiableOn_contLSeries`), agrees with `LSeries c` wherever the series
converges absolutely (`contLSeries_eq_LSeries`), and stays bounded on the horizontal ray
`s₀ + b`, `b > 0`: `‖contLSeries c s₀ (s₀ + b)‖ ≤ 3M` (`norm_contLSeries_add_ofReal_le`).

**Proof.**  With `a(n) = c(n) n^{−s₀}`, `A(N) = Σ_{n<N} a(n)` and `z = s − s₀`, summation by parts
gives `Σ_{n<N} a(n) n^{−z} = (N−1)^{−z} A(N) − Σ_{i<N−1} ((i+1)^{−z} − i^{−z}) A(i+1)`.  By the mean
value theorem `|(i+1)^{−z} − i^{−z}| ≤ |z| i^{−Re z − 1}`, which is summable locally uniformly on
`Re z > 0`; for real `z = b` the increments telescope to at most `2`.
-/

open Complex Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry.BoundedPartialSums

/-- `n^{−z}`. -/
def powNeg (z : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-z)

/-- Partial sums `A(N) = Σ_{n<N} a(n)`. -/
def partialSum (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ range N, a n

/-- The increment `Δ_i(z) = (i+1)^{−z} − i^{−z}`. -/
def incr (z : ℂ) (i : ℕ) : ℂ := powNeg z (i + 1) - powNeg z i

/-- The summation-by-parts continuation `F(z) = −Σ_i Δ_i(z) A(i+1)`. -/
def continuation (a : ℕ → ℂ) (z : ℂ) : ℂ := -∑' i, incr z i * partialSum a (i + 1)

theorem powNeg_zero {z : ℂ} (hz : 0 < z.re) : powNeg z 0 = 0 := by
  have : -z ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  simp [powNeg, Complex.zero_cpow this]

theorem norm_powNeg {z : ℂ} {n : ℕ} (hn : 1 ≤ n) : ‖powNeg z n‖ = (n : ℝ) ^ (-z.re) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [powNeg, show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]

theorem incr_zero {z : ℂ} (hz : 0 < z.re) : incr z 0 = 1 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  simp [incr, powNeg, hz0]

/-- **Mean value bound.** `‖(i+1)^{−z} − i^{−z}‖ ≤ ‖z‖ i^{−Re z − 1}` for `i ≥ 1`, `Re z > 0`. -/
theorem norm_incr_le {z : ℂ} (hz : 0 < z.re) {i : ℕ} (hi : 1 ≤ i) :
    ‖incr z i‖ ≤ ‖z‖ * (i : ℝ) ^ (-z.re - 1) := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hz0 : -z ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ (-z) with hf
  have hderiv : ∀ x ∈ Set.Icc (i : ℝ) (i + 1),
      HasDerivWithinAt f (-z * (x : ℂ) ^ (-z - 1)) (Set.Icc (i : ℝ) (i + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact (hasDerivAt_ofReal_cpow_const hx0 hz0).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (i : ℝ) (i + 1),
      ‖-z * (x : ℂ) ^ (-z - 1)‖ ≤ ‖z‖ * (i : ℝ) ^ (-z.re - 1) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hi0 hx.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hi0 hx.1 (by linarith)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (i + 1)
    ⟨by linarith, le_rfl⟩
  rw [show (i : ℝ) + 1 - i = 1 by ring, mul_one] at h
  have e1 : powNeg z (i + 1) = f ((i : ℝ) + 1) := by simp [powNeg, hf]
  have e2 : powNeg z i = f (i : ℝ) := by simp [powNeg, hf]
  rw [incr, e1, e2]
  exact h

/-- The summable majorant `u_i = 1_{i=0} + R i^{−δ−1}`. -/
def majorant (δ R : ℝ) (i : ℕ) : ℝ := (if i = 0 then 1 else 0) + R * (i : ℝ) ^ (-δ - 1)

theorem summable_majorant {δ : ℝ} (hδ : 0 < δ) (R : ℝ) : Summable (majorant δ R) := by
  have h1 : Summable fun i : ℕ => if i = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun i hi => by
      rw [Finset.mem_singleton] at hi; simp [hi]
  have h2 : Summable fun i : ℕ => (i : ℝ) ^ (-δ - 1) := by
    refine (Real.summable_nat_rpow_inv.mpr (show 1 < δ + 1 by linarith)).congr fun i => ?_
    rw [show -δ - 1 = -(δ + 1) by ring, Real.rpow_neg (Nat.cast_nonneg i)]
  exact h1.add (h2.mul_left R)

theorem norm_incr_le_majorant {δ R : ℝ} {z : ℂ} (hδ : 0 < δ) (hδz : δ ≤ z.re) (hR : ‖z‖ ≤ R)
    (i : ℕ) : ‖incr z i‖ ≤ majorant δ R i := by
  have hz : 0 < z.re := lt_of_lt_of_le hδ hδz
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [incr_zero hz, norm_one, majorant, if_pos rfl, Nat.cast_zero,
      Real.zero_rpow (by linarith), mul_zero, add_zero]
  · rw [majorant, if_neg hi.ne', zero_add]
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
    calc ‖incr z i‖ ≤ ‖z‖ * (i : ℝ) ^ (-z.re - 1) := norm_incr_le hz hi
      _ ≤ R * (i : ℝ) ^ (-δ - 1) := mul_le_mul hR
          (Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)) (by positivity)
          ((norm_nonneg z).trans hR)

/-- **Summation by parts.** -/
theorem sum_mul_powNeg_eq (a : ℕ → ℂ) (z : ℂ) (N : ℕ) :
    ∑ n ∈ range N, a n * powNeg z n =
      powNeg z (N - 1) * partialSum a N - ∑ i ∈ range (N - 1), incr z i * partialSum a (i + 1) := by
  have h := Finset.sum_range_by_parts (f := powNeg z) (g := a) (n := N)
  simp only [smul_eq_mul] at h
  rw [show (∑ n ∈ range N, a n * powNeg z n) = ∑ n ∈ range N, powNeg z n * a n from
    Finset.sum_congr rfl fun n _ => mul_comm _ _, h]
  rfl

/-- **Bounded twisted sums from polynomial growth.**  If `‖Σ_{m ≤ n} a(m)‖ ≤ K n^θ` and
`Re z > θ ≥ 0`, then every partial sum of `Σ a(n) n^{−z}` is at most
`K (1 + ‖z‖ Σ_i i^{θ − Re z − 1})`. -/
theorem norm_sum_mul_powNeg_le_of_growth {a : ℕ → ℂ} {θ K : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (ha0 : a 0 = 0) (hA : ∀ n : ℕ, 1 ≤ n → ‖partialSum a (n + 1)‖ ≤ K * (n : ℝ) ^ θ)
    {z : ℂ} (hz : θ < z.re) (N : ℕ) :
    ‖∑ n ∈ range N, a n * powNeg z n‖ ≤
      K * (1 + ‖z‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - z.re - 1)) := by
  have hz0 : 0 < z.re := lt_of_le_of_lt hθ hz
  have hsumm : Summable fun i : ℕ => (i : ℝ) ^ (θ - z.re - 1) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hA1 : partialSum a 1 = 0 := by simp [partialSum, ha0]
  rw [sum_mul_powNeg_eq]
  have h1 : ‖powNeg z (N - 1) * partialSum a N‖ ≤ K := by
    rcases Nat.lt_or_ge N 2 with hN | hN
    · interval_cases N
      · simp [partialSum]; exact hK
      · simp [hA1]; exact hK
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      have hm : 1 ≤ m := by omega
      rw [show m + 1 - 1 = m by omega, norm_mul, norm_powNeg hm]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      calc (m : ℝ) ^ (-z.re) * ‖partialSum a (m + 1)‖ ≤ (m : ℝ) ^ (-z.re) * (K * (m : ℝ) ^ θ) :=
            mul_le_mul_of_nonneg_left (hA m hm) (by positivity)
        _ = K * (m : ℝ) ^ (θ - z.re) := by
            rw [mul_comm, mul_assoc, ← Real.rpow_add (by linarith)]; ring_nf
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)) hK
        _ = K := mul_one K
  have h2 : ‖∑ i ∈ range (N - 1), incr z i * partialSum a (i + 1)‖ ≤
      K * ‖z‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - z.re - 1) := by
    have hterm : ∀ i, ‖incr z i * partialSum a (i + 1)‖ ≤
        K * ‖z‖ * (i : ℝ) ^ (θ - z.re - 1) := by
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp only [zero_add, hA1, mul_zero, norm_zero, Nat.cast_zero]
        exact mul_nonneg (mul_nonneg hK (norm_nonneg _)) (Real.rpow_nonneg le_rfl _)
      · have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
        rw [norm_mul]
        calc ‖incr z i‖ * ‖partialSum a (i + 1)‖ ≤ (‖z‖ * (i : ℝ) ^ (-z.re - 1)) *
              (K * (i : ℝ) ^ θ) := mul_le_mul (norm_incr_le hz0 hi) (hA i hi)
                (norm_nonneg _) (by positivity)
          _ = K * ‖z‖ * (i : ℝ) ^ (θ - z.re - 1) := by
              rw [show θ - z.re - 1 = (-z.re - 1) + θ by ring,
                Real.rpow_add (by linarith)]; ring
    calc ‖∑ i ∈ range (N - 1), incr z i * partialSum a (i + 1)‖
        ≤ ∑ i ∈ range (N - 1), K * ‖z‖ * (i : ℝ) ^ (θ - z.re - 1) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
      _ = K * ‖z‖ * ∑ i ∈ range (N - 1), (i : ℝ) ^ (θ - z.re - 1) := by rw [Finset.mul_sum]
      _ ≤ K * ‖z‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - z.re - 1) :=
          mul_le_mul_of_nonneg_left (hsumm.sum_le_tsum _ fun i _ => by positivity)
            (by positivity)
  calc ‖powNeg z (N - 1) * partialSum a N - ∑ i ∈ range (N - 1), incr z i * partialSum a (i + 1)‖
      ≤ ‖powNeg z (N - 1) * partialSum a N‖ +
          ‖∑ i ∈ range (N - 1), incr z i * partialSum a (i + 1)‖ := norm_sub_le _ _
    _ ≤ K + K * ‖z‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - z.re - 1) := add_le_add h1 h2
    _ = K * (1 + ‖z‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - z.re - 1)) := by ring

theorem summable_incr_mul {a : ℕ → ℂ} {M : ℝ} (hM : ∀ N, ‖partialSum a N‖ ≤ M) {z : ℂ}
    (hz : 0 < z.re) : Summable fun i => incr z i * partialSum a (i + 1) := by
  refine Summable.of_norm_bounded ((summable_majorant (half_pos hz) ‖z‖).mul_right M) fun i => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_incr_le_majorant (half_pos hz) (by linarith) le_rfl i) (hM _)
    (norm_nonneg _) ((norm_nonneg _).trans (norm_incr_le_majorant (half_pos hz) (by linarith) le_rfl i))

/-- **Convergence.** -/
theorem tendsto_sum_mul_powNeg {a : ℕ → ℂ} {M : ℝ} (hM : ∀ N, ‖partialSum a N‖ ≤ M) {z : ℂ}
    (hz : 0 < z.re) :
    Tendsto (fun N => ∑ n ∈ range N, a n * powNeg z n) atTop (𝓝 (continuation a z)) := by
  simp_rw [sum_mul_powNeg_eq]
  rw [continuation, ← zero_sub]
  refine Tendsto.sub ?_ (((summable_incr_mul hM hz).hasSum.tendsto_sum_nat).comp
    (tendsto_sub_atTop_nat 1))
  have hpow : Tendsto (fun N : ℕ => ‖powNeg z (N - 1)‖) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hz).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [norm_powNeg (by omega)]
    rfl
  refine squeeze_zero_norm (fun N => ?_) (by simpa using hpow.mul_const M)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM N) (norm_nonneg _)

/-- **Holomorphy** on `Re z > 0`. -/
theorem differentiableOn_continuation {a : ℕ → ℂ} {M : ℝ} (hM : ∀ N, ‖partialSum a N‖ ≤ M) :
    DifferentiableOn ℂ (continuation a) {z | 0 < z.re} := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.re := hz₀
  set δ := z₀.re / 2
  set R := ‖z₀‖ + 1
  set U : Set ℂ := {z | δ < z.re ∧ ‖z‖ < R}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hz₀U : z₀ ∈ U := ⟨by simp only [δ]; linarith, by simp only [R]; linarith⟩
  have hdiff : DifferentiableOn ℂ (fun z => ∑' i, incr z i * partialSum a (i + 1)) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_majorant (half_pos hz₀') R).mul_right M) (fun i => ?_) hU fun i z hz => ?_
    · intro z hz
      have hδ : 0 < δ := half_pos hz₀'
      have hz0 : -z ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp at this
        linarith [hz.1]
      refine (((differentiableAt_id.neg.const_cpow (Or.inr hz0)).sub
        (differentiableAt_id.neg.const_cpow (Or.inr hz0))).mul_const _).differentiableWithinAt
    · rw [norm_mul]
      have hb := norm_incr_le_majorant (half_pos hz₀') hz.1.le hz.2.le i
      exact mul_le_mul hb (hM _) (norm_nonneg _) ((norm_nonneg _).trans hb)
  exact ((hdiff.neg.differentiableAt (hU.mem_nhds hz₀U))).differentiableWithinAt

/-- **Horizontal bound.** For real `b > 0`, every partial sum, hence the continuation, has norm at
most `3M`. -/
theorem norm_continuation_ofReal_le {a : ℕ → ℂ} {M : ℝ} (hM : ∀ N, ‖partialSum a N‖ ≤ M)
    {b : ℝ} (hb : 0 < b) : ‖continuation a b‖ ≤ 3 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hbre : 0 < (b : ℂ).re := by simpa using hb
  set r : ℕ → ℝ := fun i => if i = 0 then 0 else (i : ℝ) ^ (-b) with hr
  have hpowr : ∀ i, powNeg b i = (r i : ℂ) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hr, powNeg_zero hbre]
    · simp only [hr, if_neg hi.ne', powNeg]
      rw [Complex.ofReal_cpow (Nat.cast_nonneg i), Complex.ofReal_neg, Complex.ofReal_natCast]
  set h : ℕ → ℝ := fun i => if i = 0 then 2 else (i : ℝ) ^ (-b) with hh
  have hstep : ∀ i, |r (i + 1) - r i| ≤ h i - h (i + 1) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hr, hh]; norm_num
    · have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have hle : ((i + 1 : ℕ) : ℝ) ^ (-b) ≤ (i : ℝ) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
      simp only [hr, hh, if_neg hi.ne', if_neg (Nat.succ_ne_zero i)]
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hpowle : ∀ i, ‖powNeg b i‖ ≤ 1 := by
    intro i
    rw [hpowr, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hr]
    · have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
      simp only [hr, if_neg hi.ne']
      rw [abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hi1 (by linarith)
  have hpart : ∀ N, ‖∑ n ∈ range N, a n * powNeg b n‖ ≤ 3 * M := by
    intro N
    rw [sum_mul_powNeg_eq]
    have hsum : ∑ i ∈ range (N - 1), ‖incr b i * partialSum a (i + 1)‖ ≤ 2 * M := by
      calc ∑ i ∈ range (N - 1), ‖incr b i * partialSum a (i + 1)‖ ≤
            ∑ i ∈ range (N - 1), (h i - h (i + 1)) * M := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, incr, hpowr, hpowr, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            exact mul_le_mul (hstep i) (hM _) (norm_nonneg _)
              ((abs_nonneg _).trans (hstep i))
        _ = (h 0 - h (N - 1)) * M := by rw [← Finset.sum_mul, Finset.sum_range_sub']
        _ ≤ 2 * M := by
            refine mul_le_mul_of_nonneg_right ?_ hM0
            have : 0 ≤ h (N - 1) := by
              simp only [hh]; split_ifs <;> positivity
            simp only [hh, if_pos rfl]
            linarith
    calc ‖powNeg (↑b) (N - 1) * partialSum a N -
          ∑ i ∈ range (N - 1), incr (↑b) i * partialSum a (i + 1)‖ ≤
          ‖powNeg (↑b) (N - 1) * partialSum a N‖ +
            ‖∑ i ∈ range (N - 1), incr (↑b) i * partialSum a (i + 1)‖ := norm_sub_le _ _
      _ ≤ 1 * M + 2 * M := by
          refine add_le_add ?_ ((norm_sum_le _ _).trans hsum)
          rw [norm_mul]
          exact mul_le_mul (hpowle _) (hM N) (norm_nonneg _) zero_le_one
      _ = 3 * M := by ring
  exact le_of_tendsto' (tendsto_sum_mul_powNeg hM hbre).norm hpart

/-! ## Dirichlet series -/

/-- The continuation of `Σ c(n) n^{−s}` from a base point `s₀` with bounded partial sums. -/
def contLSeries (c : ℕ → ℂ) (s₀ s : ℂ) : ℂ := continuation (LSeries.term c s₀) (s - s₀)

theorem term_eq_mul_powNeg (c : ℕ → ℂ) (s₀ s : ℂ) (n : ℕ) :
    LSeries.term c s n = LSeries.term c s₀ n * powNeg (s - s₀) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', powNeg,
      show s = s₀ + (s - s₀) by ring, Complex.cpow_add _ _ hn0, Complex.cpow_neg]
    simp only [add_sub_cancel_left]
    field_simp

/-- **The partial sums converge** right of a base point with bounded partial sums. -/
theorem tendsto_sum_term_contLSeries {c : ℕ → ℂ} {s₀ : ℂ} {M : ℝ}
    (hM : ∀ N, ‖∑ n ∈ range N, LSeries.term c s₀ n‖ ≤ M) {s : ℂ} (hs : s₀.re < s.re) :
    Tendsto (fun N => ∑ n ∈ range N, LSeries.term c s n) atTop (𝓝 (contLSeries c s₀ s)) := by
  simp_rw [term_eq_mul_powNeg c s₀ s]
  exact tendsto_sum_mul_powNeg hM (by simpa using hs)

theorem differentiableOn_contLSeries {c : ℕ → ℂ} {s₀ : ℂ} {M : ℝ}
    (hM : ∀ N, ‖∑ n ∈ range N, LSeries.term c s₀ n‖ ≤ M) :
    DifferentiableOn ℂ (contLSeries c s₀) {s | s₀.re < s.re} := by
  have h := differentiableOn_continuation (a := LSeries.term c s₀) hM
  refine h.comp (differentiableOn_id.sub_const s₀) fun s hs => ?_
  show 0 < (s - s₀).re
  simpa using hs

/-- Agreement with the absolutely convergent series. -/
theorem contLSeries_eq_LSeries {c : ℕ → ℂ} {s₀ : ℂ} {M : ℝ}
    (hM : ∀ N, ‖∑ n ∈ range N, LSeries.term c s₀ n‖ ≤ M) {s : ℂ} (hs : s₀.re < s.re)
    (hsum : LSeriesSummable c s) : contLSeries c s₀ s = LSeries c s :=
  tendsto_nhds_unique (tendsto_sum_term_contLSeries hM hs) hsum.hasSum.tendsto_sum_nat

/-- The continuation does not depend on the base point. -/
theorem contLSeries_eq_of_base {c : ℕ → ℂ} {s₀ s₁ : ℂ} {M₀ M₁ : ℝ}
    (hM₀ : ∀ N, ‖∑ n ∈ range N, LSeries.term c s₀ n‖ ≤ M₀)
    (hM₁ : ∀ N, ‖∑ n ∈ range N, LSeries.term c s₁ n‖ ≤ M₁) {s : ℂ} (hs₀ : s₀.re < s.re)
    (hs₁ : s₁.re < s.re) : contLSeries c s₀ s = contLSeries c s₁ s :=
  tendsto_nhds_unique (tendsto_sum_term_contLSeries hM₀ hs₀) (tendsto_sum_term_contLSeries hM₁ hs₁)

/-- **Horizontal boundedness** at a base point. -/
theorem norm_contLSeries_add_ofReal_le {c : ℕ → ℂ} {s₀ : ℂ} {M : ℝ}
    (hM : ∀ N, ‖∑ n ∈ range N, LSeries.term c s₀ n‖ ≤ M) {b : ℝ} (hb : 0 < b) :
    ‖contLSeries c s₀ (s₀ + b)‖ ≤ 3 * M := by
  unfold contLSeries
  rw [add_sub_cancel_left]
  exact norm_continuation_ofReal_le (a := LSeries.term c s₀) hM hb

/-- Convergent partial sums are bounded. -/
theorem exists_partialSum_bound_of_tendsto {c : ℕ → ℂ} {s₀ L : ℂ}
    (h : Tendsto (fun N => ∑ n ∈ range N, LSeries.term c s₀ n) atTop (𝓝 L)) :
    ∃ M : ℝ, ∀ N, ‖∑ n ∈ range N, LSeries.term c s₀ n‖ ≤ M := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ h).exists_norm_le
  exact ⟨M, fun N => hM _ ⟨N, rfl⟩⟩

end GaloisForLFunctions.HTGeometry.BoundedPartialSums
