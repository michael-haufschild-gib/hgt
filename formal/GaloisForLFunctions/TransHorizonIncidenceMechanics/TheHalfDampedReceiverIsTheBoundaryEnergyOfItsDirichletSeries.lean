import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverReadsTheDirichletSeriesAtTheCriticalPoint
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel

/-!
# The half-damped receiver is the boundary energy of its Dirichlet series

For a half-damped weight `|c(d)| ≤ K d^{-1/2}` with mean `m = Σ c(d)/d`, centred prefix `A(n)` and
Dirichlet series `C(s) = Σ c(d) d^{-s}`, put `G(s) = ζ(s)(C(s) − m)`. For every `1/2 < σ < 1`,

`Σ_n A(n)² (n^{-2σ} − (n+1)^{-2σ}) = (σ/π) ∫ |G(σ + it)/(σ + it)|² dt`

(`sum_sq_mul_mellinCell_eq_lineEnergy`). Two inputs:

* the complex Mellin pairing `Σ_n A(n)(n^{-s} − (n+1)^{-s}) = G(s)` on `1/2 < Re s < 1`
  (`cmellinPairing_eq_zeta_mul`), the complex form of the real identity of
  `TheHalfDampedReceiverReadsTheDirichletSeriesAtTheCriticalPoint`, with Fubini paid by
  `|n^{-s} − (n+1)^{-s}| ≤ (|s|/σ)(n^{-σ} − (n+1)^{-σ})`;
* Mellin–Plancherel for the step function `y ↦ A(⌊y⌋)` on `(1, ∞)`, whose Mellin transform at `−s`
  is `G(s)/s` and whose weighted energy is the left side divided by `2σ`.

As `σ ↓ 1/2` the cells `n^{-2σ} − (n+1)^{-2σ}` tend to the pronic weights, so
**the receiver is bounded iff the line energies of `G(s)/s` stay bounded as `σ ↓ 1/2`**
(`receiverBounded_of_lineEnergy_le`): the half-damped receiver is the `H²` boundary energy of
`ζ(s)(C(s) − C(1))/s` on the critical line. The receiver reads `ζ` on the strip `1/2 < Re s < 1`
through `|ζ(s)|²` and the weight through its Dirichlet series near `Re s = 1`.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators FourierTransform Interval

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Complex Mellin cells -/

/-- The complex Mellin cell `n^{-s} − (n+1)^{-s}`. -/
def cmellinCell (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)

theorem hasDerivAt_ofReal_cpow_neg {w : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-w)) (-w * (x : ℂ) ^ (-w - 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    (Real.hasDerivAt_log hx.ne').ofReal_comp
  have h3 := (h1.const_mul (-w)).cexp
  have hfun : (fun y : ℝ => (y : ℂ) ^ (-w)) =ᶠ[𝓝 x]
      fun y : ℝ => Complex.exp (-w * ((Real.log y : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hy)),
      ← Complex.ofReal_log hy.le, mul_comm]
  refine (h3.congr_of_eventuallyEq hfun).congr_deriv ?_
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, Complex.cpow_def_of_ne_zero hx0,
    ← Complex.ofReal_log hx.le]
  push_cast
  field_simp

/-- `|n^{-s} − (n+1)^{-s}| ≤ (|s|/σ)(n^{-σ} − (n+1)^{-σ})`, `σ = Re s > 0`, `n ≥ 1`. -/
theorem norm_cmellinCell_le {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖cmellinCell s n‖ ≤ ‖s‖ / s.re * mellinCell s.re n := by
  have hA : (0 : ℝ) < n := by exact_mod_cast hn
  have hAB : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hpos : ∀ y ∈ uIcc (n : ℝ) ((n : ℝ) + 1), 0 < y := by
    intro y hy; rw [uIcc_of_le hAB] at hy; linarith [hy.1]
  have hderiv : ∀ y ∈ uIcc (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (y : ℂ) ^ (-s - 1)) y :=
    fun y hy => hasDerivAt_ofReal_cpow_neg (hpos y hy)
  have hcont : ContinuousOn (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1)) (uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    intro y hy
    have h := hasDerivAt_ofReal_cpow_neg (w := s + 1) (hpos y hy)
    have hfun : (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1)) =
        fun y : ℝ => -s * (y : ℂ) ^ (-(s + 1)) := by
      funext y; congr 2; ring
    rw [hfun]
    exact (continuousAt_const.mul h.continuousAt).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hcell : cmellinCell s n = -(((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - (((n : ℝ) : ℂ)) ^ (-s)) := by
    simp only [cmellinCell]; ring
  rw [hcell, norm_neg, ← hFTC]
  refine (intervalIntegral.norm_integral_le_integral_norm hAB).trans ?_
  have hnorm : EqOn (fun y : ℝ => ‖-s * (y : ℂ) ^ (-s - 1)‖)
      (fun y : ℝ => ‖s‖ * y ^ (-s.re - 1)) (uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    intro y hy
    simp only
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (hpos y hy)]
    congr 2
  rw [intervalIntegral.integral_congr hnorm, intervalIntegral.integral_const_mul]
  have h0 : (0 : ℝ) ∉ uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [uIcc_of_le hAB]; intro h; linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by intro h; linarith, h0⟩)]
  have hexp : -s.re - 1 + 1 = -s.re := by ring
  rw [hexp, mellinCell]
  apply le_of_eq
  field_simp
  ring

/-! ### The complex Mellin pairing -/

/-- Summation by parts for complex cells. -/
theorem sum_range_modulusDefect_mul_cmellinCell {d : ℕ} (hd : 0 < d) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (modulusDefect d n : ℂ) * cmellinCell s n =
      ∑ n ∈ Finset.Icc 1 N, (((if d ∣ n then 1 else 0) - 1 / d : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-s)
        - (modulusDefect d N : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [modulusDefect_zero_right, cmellinCell]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), cmellinCell]
    have hstep : ((modulusDefect d (N + 1) : ℝ) : ℂ) = (modulusDefect d N : ℂ) +
        (((if d ∣ N + 1 then 1 else 0) - 1 / d : ℝ) : ℂ) := by
      rw [modulusDefect_succ hd N, ← Complex.ofReal_add]
      congr 1
      ring
    have hcast : ((((N + 1 : ℕ) : ℝ)) : ℂ) = (((N : ℝ) + 1 : ℝ) : ℂ) := by
      rw [Nat.cast_succ]
    rw [hstep, hcast]
    ring

/-- The divisible terms of `Icc 1 (dM)`, complex form. -/
theorem sum_Icc_dvd_cpow {d : ℕ} (hd : 0 < d) (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 (d * M), (((if d ∣ n then 1 else 0 : ℝ)) : ℂ) * ((n : ℝ) : ℂ) ^ (-s) =
      ((d : ℝ) : ℂ) ^ (-s) * ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) : ℂ) ^ (-s) := by
  have hfilt : (Finset.Icc 1 (d * M)).filter (fun n => d ∣ n) =
      (Finset.Icc 1 M).map ⟨(d * ·), mul_right_injective₀ hd.ne'⟩ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h1
        · exact hk
      · exact Nat.le_of_mul_le_mul_left h2 hd
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd.ne' (by omega)),
        Nat.mul_le_mul_left d hk2⟩, dvd_mul_right d k⟩
  have hcast : ∀ n : ℕ, (((if d ∣ n then 1 else 0 : ℝ)) : ℂ) * ((n : ℝ) : ℂ) ^ (-s) =
      if d ∣ n then ((n : ℝ) : ℂ) ^ (-s) else 0 := fun n => by split_ifs <;> simp
  simp_rw [hcast]
  rw [← Finset.sum_filter, hfilt, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg k)]

/-- The complex strip remainder `Σ_{k≤N} k^{-s} − N^{1-s}/(1-s) → ζ(s)`. -/
def czetaStripRemainder (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-s) - ((N : ℝ) : ℂ) ^ (1 - s) / (1 - s)

/-- **One modulus pairs to `ζ(s)(d^{-s} − 1/d)`, complex form.** -/
theorem hasSum_modulusDefect_mul_cmellinCell {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {d : ℕ}
    (hd : 0 < d) :
    HasSum (fun n => (modulusDefect d n : ℂ) * cmellinCell s n)
      (riemannZeta s * (((d : ℝ) : ℂ) ^ (-s) - 1 / d)) := by
  have hs : Summable (fun n => (modulusDefect d n : ℂ) * cmellinCell s n) := by
    refine ((Real.summable_nat_rpow.mpr (show -s.re - 1 < -1 by linarith)).mul_left ‖s‖)
      |>.of_norm_bounded fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [modulusDefect_zero_right, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hb := (mellinCell_bounds hs0 hn).2
      calc |modulusDefect d n| * ‖cmellinCell s n‖ ≤ 1 * (‖s‖ / s.re * mellinCell s.re n) :=
            mul_le_mul (abs_natDiv_sub_div_le n d hd) (norm_cmellinCell_le hs0 hn)
              (norm_nonneg _) zero_le_one
        _ ≤ ‖s‖ / s.re * (s.re * (n : ℝ) ^ (-s.re - 1)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by field_simp
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR0 : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hpart : ∀ M : ℕ, ∑ n ∈ Finset.range (d * M + 1), (modulusDefect d n : ℂ) * cmellinCell s n =
      ((d : ℝ) : ℂ) ^ (-s) * czetaStripRemainder s M - czetaStripRemainder s (d * M) / d := by
    intro M
    rw [sum_range_modulusDefect_mul_cmellinCell hd s, modulusDefect_mul hd, Complex.ofReal_zero,
      zero_mul, sub_zero]
    have hsplit : ∀ n ∈ Finset.Icc 1 (d * M),
        (((if d ∣ n then 1 else 0) - 1 / d : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-s) =
          (((if d ∣ n then 1 else 0 : ℝ)) : ℂ) * ((n : ℝ) : ℂ) ^ (-s)
            - ((n : ℝ) : ℂ) ^ (-s) / d := fun n _ => by push_cast; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, sum_Icc_dvd_cpow hd s M, ← Finset.sum_div]
    simp only [czetaStripRemainder]
    have hcancel : ((d : ℝ) : ℂ) ^ (-s) * (((M : ℝ) : ℂ) ^ (1 - s) / (1 - s)) =
        (((d * M : ℕ) : ℝ) : ℂ) ^ (1 - s) / (1 - s) / d := by
      have h1s' : -s + 1 ≠ 0 := by rwa [show -s + 1 = 1 - s by ring]
      rw [Nat.cast_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg M),
        show (1 : ℂ) - s = -s + 1 by ring, Complex.cpow_add _ _ hdR0, Complex.cpow_one,
        Complex.ofReal_natCast d]
      field_simp
    rw [mul_sub, hcancel]
    push_cast
    ring
  have hzeta : Tendsto (fun N : ℕ => czetaStripRemainder s N) atTop (𝓝 (riemannZeta s)) :=
    RHTower.tendsto_sum_cpow_sub_pow hs0 hs1
  have hdM : Tendsto (fun M : ℕ => d * M) atTop atTop :=
    tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M hd) tendsto_id
  have hlimit : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (d * M + 1),
      (modulusDefect d n : ℂ) * cmellinCell s n) atTop
      (𝓝 (riemannZeta s * (((d : ℝ) : ℂ) ^ (-s) - 1 / d))) := by
    have h := (hzeta.const_mul (((d : ℝ) : ℂ) ^ (-s))).sub ((hzeta.comp hdM).div_const (d : ℂ))
    have hval : ((d : ℝ) : ℂ) ^ (-s) * riemannZeta s - riemannZeta s / (d : ℂ) =
        riemannZeta s * (((d : ℝ) : ℂ) ^ (-s) - 1 / d) := by ring
    rw [hval] at h
    refine h.congr fun M => ?_
    rw [hpart M]
    rfl
  have hseq : Tendsto (fun M : ℕ => d * M + 1) atTop atTop :=
    tendsto_atTop_mono (fun M => (Nat.le_mul_of_pos_left M hd).trans (Nat.le_succ _)) tendsto_id
  have hfull := (hs.hasSum.tendsto_sum_nat).comp hseq
  have heq := tendsto_nhds_unique hfull hlimit
  rw [← heq]
  exact hs.hasSum

/-- The complex Dirichlet series of a half-damped weight. -/
def weightDirichletSeries (c : ℕ → ℝ) (s : ℂ) : ℂ := ∑' d : ℕ, (c d : ℂ) * ((d : ℝ) : ℂ) ^ (-s)

/-- **The complex Mellin pairing identity.** For a half-damped weight and `1/2 < Re s < 1`,
`Σ_n A(n)(n^{-s} − (n+1)^{-s}) = ζ(s)(C(s) − m)`. -/
theorem cmellinPairing_eq_zeta_mul {K : ℝ} {c : ℕ → ℝ} (hc : DampedClass K (1 / 2) c) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s.re < 1) :
    ∑' n, (weightCenteredPrefix c (∑' d : ℕ, c d / d) n : ℂ) * cmellinCell s n =
      riemannZeta s * (weightDirichletSeries c s - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) := by
  have hsne : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
  set σ := s.re
  have hσ0 : 0 < σ := by linarith
  have hK := nonneg_of_dampedClass hc
  have hsum := summable_div_of_dampedClass (by norm_num) hc
  set θ : ℝ := (σ + 1 / 2) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  set F : ℕ → ℕ → ℂ := fun n d => (c d : ℂ) * (modulusDefect d n : ℂ) * cmellinCell s n with hF
  set g : ℕ → ℝ := fun n => K * ‖s‖ * (n : ℝ) ^ (θ - σ - 1)
  set h : ℕ → ℝ := fun d => (d : ℝ) ^ (-(1 / 2) - θ)
  have hg : Summable g :=
    (Real.summable_nat_rpow.mpr (show θ - σ - 1 < -1 by rw [hθ]; linarith)).mul_left _
  have hh : Summable h := Real.summable_nat_rpow.mpr (show -(1 / 2) - θ < -1 by rw [hθ]; linarith)
  have hg0 : 0 ≤ g := fun n => by positivity
  have hh0 : 0 ≤ h := fun d => by positivity
  have hbound : ∀ n d, ‖F n d‖ ≤ g n * h d := by
    intro n d
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, modulusDefect_zero_right]; exact mul_nonneg (hg0 0) (hh0 d)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [hF, zero_of_dampedClass (by norm_num) hc]; exact mul_nonneg (hg0 n) (hh0 0)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hcell := norm_cmellinCell_le (s := s) hσ0 hn
    have hb := (mellinCell_bounds hσ0 hn).2
    have hα := abs_modulusDefect_le_rpow hθ0 hθ1 d n
    rw [Real.div_rpow hn0.le hd0.le] at hα
    rw [hF, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    calc |c d| * |modulusDefect d n| * ‖cmellinCell s n‖
        ≤ (K * (d : ℝ) ^ (-(1 / 2 : ℝ))) * ((n : ℝ) ^ θ / (d : ℝ) ^ θ) *
            (‖s‖ / σ * (σ * (n : ℝ) ^ (-σ - 1))) :=
          mul_le_mul (mul_le_mul (hc d) hα (abs_nonneg _) (by positivity))
            (hcell.trans (mul_le_mul_of_nonneg_left hb (by positivity))) (norm_nonneg _)
            (by positivity)
      _ = g n * h d := by
          simp only [g, h]
          rw [show θ - σ - 1 = θ + (-σ - 1) by ring, Real.rpow_add hn0,
            show -(1 / 2 : ℝ) - θ = -(1 / 2) + -θ by ring, Real.rpow_add hd0, Real.rpow_neg hd0.le θ]
          field_simp
  have hFsum : Summable (Function.uncurry F) :=
    (Summable.mul_of_nonneg hg hh hg0 hh0).of_norm_bounded fun p => hbound p.1 p.2
  have hrow : ∀ n, Summable (F n) := fun n => (hh.mul_left (g n)).of_norm_bounded fun d => hbound n d
  have hcol : ∀ d, Summable (fun n => F n d) := fun d =>
    (hg.mul_right (h d)).of_norm_bounded fun n => hbound n d
  have hleft : ∑' n, (weightCenteredPrefix c (∑' d : ℕ, c d / d) n : ℂ) * cmellinCell s n =
      ∑' n, ∑' d, F n d := by
    refine tsum_congr fun n => ?_
    rw [weightCenteredPrefix_eq_tsum_modulusDefect c hsum n, Complex.ofReal_tsum,
      ← tsum_mul_right]
    refine tsum_congr fun d => ?_
    simp only [hF]
    push_cast
    ring
  have hcomm : ∑' n, ∑' d, F n d = ∑' d, ∑' n, F n d := (hFsum.tsum_comm' hrow hcol).symm
  have hinner : ∀ d, ∑' n, F n d =
      (c d : ℂ) * (riemannZeta s * (((d : ℝ) : ℂ) ^ (-s) - 1 / d)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [hF, zero_of_dampedClass (by norm_num) hc]
    have hcd : ∀ n, F n d = (c d : ℂ) * ((modulusDefect d n : ℂ) * cmellinCell s n) := fun n => by
      simp only [hF]; ring
    simp_rw [hcd]
    rw [tsum_mul_left, (hasSum_modulusDefect_mul_cmellinCell hσ0 hsne hd).tsum_eq]
  have hS1 : Summable (fun d : ℕ => (c d : ℂ) * ((d : ℝ) : ℂ) ^ (-s)) := by
    refine (summable_mul_rpow_of_dampedClass (σ := σ) (by norm_num) hc
      (by linarith)).abs.of_norm_bounded fun d => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [zero_of_dampedClass (by norm_num) hc]
    · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hd0, abs_of_pos (Real.rpow_pos_of_pos hd0 _)]
      simp [σ]
  have hS2 : Summable (fun d : ℕ => (c d : ℂ) / d) := by
    refine (Complex.summable_ofReal.mpr hsum).congr fun d => ?_
    push_cast; ring
  rw [hleft, hcomm]
  simp_rw [hinner]
  have hsplit : ∀ d : ℕ, (c d : ℂ) * (riemannZeta s * (((d : ℝ) : ℂ) ^ (-s) - 1 / d)) =
      riemannZeta s * ((c d : ℂ) * ((d : ℝ) : ℂ) ^ (-s) - (c d : ℂ) / d) := fun d => by ring
  simp_rw [hsplit]
  rw [tsum_mul_left, hS1.tsum_sub hS2, weightDirichletSeries, Complex.ofReal_tsum]
  congr 2
  refine tsum_congr fun d => ?_
  push_cast; ring

/-! ### Mellin–Plancherel for the step function -/

/-- The step function `y ↦ A(⌊y⌋)` on `(1, ∞)`. -/
def stepSource (A : ℕ → ℝ) (y : ℝ) : ℂ := if 1 < y then ((A ⌊y⌋₊ : ℝ) : ℂ) else 0

theorem floor_eq_of_mem_Ioc {n : ℕ} {y : ℝ} (hy : y ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)) :
    ⌊y⌋₊ = n + 1 := by
  rw [Nat.floor_eq_iff (by linarith [hy.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
  push_cast
  constructor <;> linarith [hy.1, hy.2]

/-- On a unit piece the step function is a.e. the constant `A(n+1)`. -/
theorem stepSource_ae_piece (A : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ y ∂(volume.restrict (Ι ((n : ℝ) + 1) ((n : ℝ) + 2))),
      stepSource A y = ((A (n + 1) : ℝ) : ℂ) := by
  have hpt : ∀ᵐ y ∂(volume : Measure ℝ), y ∉ ({(n : ℝ) + 2} : Set ℝ) :=
    (Set.countable_singleton _).ae_notMem _
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hpt] with y hy hmem
  rw [uIoc_of_le (by linarith)] at hmem
  have hne : y ≠ (n : ℝ) + 2 := fun h => hy (by simp [h])
  have hIoo : y ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2) := ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩
  have h1 : (1 : ℝ) < y := by linarith [hIoo.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  simp only [stepSource, if_pos h1, floor_eq_of_mem_Ioc hIoo]

/-- **Integrals against the step function are series over its pieces.** -/
theorem integral_Ioi_one_stepSource_mul (A : ℕ → ℝ) {k : ℝ → ℂ} (hk : ContinuousOn k (Ici 1))
    (hsum : Summable (fun n : ℕ => |A (n + 1)| * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖)) :
    IntegrableOn (fun y => stepSource A y * k y) (Ioi 1) ∧
      ∫ y in Ioi (1 : ℝ), stepSource A y * k y =
        ∑' n : ℕ, ((A (n + 1) : ℝ) : ℂ) * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), k y := by
  set F : ℝ → ℂ := fun y => stepSource A y * k y
  have hkI : ∀ n : ℕ, IntervalIntegrable k volume ((n : ℝ) + 1) ((n : ℝ) + 2) := fun n =>
    (hk.mono (by
      rw [uIcc_of_le (by linarith)]
      intro y hy; exact le_trans (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hy.1)).intervalIntegrable
  have hFae : ∀ n : ℕ, F =ᵐ[volume.restrict (Ι ((n : ℝ) + 1) ((n : ℝ) + 2))]
      fun y => ((A (n + 1) : ℝ) : ℂ) * k y := fun n => by
    filter_upwards [stepSource_ae_piece A n] with y hy
    simp only [F, hy]
  have hFI : ∀ n : ℕ, IntervalIntegrable F volume ((n : ℝ) + 1) ((n : ℝ) + 2) := fun n =>
    ((hkI n).const_mul _).congr_ae (hFae n).symm
  have hpiece : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), F y =
      ((A (n + 1) : ℝ) : ℂ) * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), k y := fun n => by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_ae_restrict (hFae n)
  have hpieceN : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖F y‖ =
      |A (n + 1)| * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖ := fun n => by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae_restrict ?_
    filter_upwards [hFae n] with y hy
    rw [hy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  set b : ℕ → ℝ := fun N => (N : ℝ) + 1
  have hb : Tendsto b atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hadj : ∀ N : ℕ, ∫ y in (1 : ℝ)..b N, F y =
      ∑ n ∈ Finset.range N, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), F y := fun N => by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := F) (μ := volume)
      (a := fun n : ℕ => (n : ℝ) + 1) (n := N) (fun n _ => by
        have := hFI n; push_cast; convert this using 1; ring)
    simp only [Nat.cast_zero, zero_add] at h
    rw [← h]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring_nf
  have hadjN : ∀ N : ℕ, ∫ y in (1 : ℝ)..b N, ‖F y‖ =
      ∑ n ∈ Finset.range N, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖F y‖ := fun N => by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := fun y => ‖F y‖) (μ := volume)
      (a := fun n : ℕ => (n : ℝ) + 1) (n := N) (fun n _ => by
        have := (hFI n).norm; push_cast; convert this using 1; ring)
    simp only [Nat.cast_zero, zero_add] at h
    rw [← h]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring_nf
  have hint : IntegrableOn F (Ioi 1) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop) (b := b)
      (∑' n : ℕ, |A (n + 1)| * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖) 1 (fun N => ?_) hb
      (Eventually.of_forall fun N => ?_)
    · have hI : IntervalIntegrable F volume 1 (b N) := by
        induction N with
        | zero => simp [b]
        | succ N ih =>
          have h2 := hFI N
          have hb' : b (N + 1) = (N : ℝ) + 2 := by simp only [b]; push_cast; ring
          rw [hb']
          exact ih.trans (by simpa [b] using h2)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp [b])).mp hI
    · rw [hadjN N]
      simp_rw [hpieceN]
      exact Summable.sum_le_tsum _ (fun n _ => mul_nonneg (abs_nonneg _)
        (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _)) hsum
  refine ⟨hint, ?_⟩
  have hser : Summable (fun n : ℕ => ((A (n + 1) : ℝ) : ℂ) *
      ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), k y) := by
    refine hsum.of_norm_bounded fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (abs_nonneg _)
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 1 hint hb
  have hlim2 : Tendsto (fun N : ℕ => ∫ y in (1 : ℝ)..b N, F y) atTop
      (𝓝 (∑' n : ℕ, ((A (n + 1) : ℝ) : ℂ) * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), k y)) := by
    refine hser.hasSum.tendsto_sum_nat.congr fun N => ?_
    rw [hadj N]
    exact Finset.sum_congr rfl fun n _ => (hpiece n).symm
  exact tendsto_nhds_unique hlim1 hlim2

/-- A step source bounded by `B √n` on its pieces. -/
theorem norm_stepSource_le {A : ℕ → ℝ} {B : ℝ} (hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ))
    (y : ℝ) : ‖stepSource A y‖ ≤ if 1 < y then B * y ^ (1 / 2 : ℝ) else 0 := by
  unfold stepSource
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs]
    have hfl : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast h.le)
    refine (hB _ hfl).trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by norm_num)
    · have := (abs_nonneg _).trans (hB _ hfl)
      have hfl0 : (0 : ℝ) < ⌊y⌋₊ := by
        have : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hfl
        linarith
      exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos hfl0 _)
  · simp

theorem measurable_stepSource (A : ℕ → ℝ) : Measurable (stepSource A) := by
  unfold stepSource
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact (measurable_from_nat (f := fun n => ((A n : ℝ) : ℂ))).comp measurable_id.nat_floor

/-- **The Mellin transform of the step source** at `−s` is `Σ_n A(n)(n^{-s} − (n+1)^{-s})/s`. -/
theorem mellin_stepSource_neg {A : ℕ → ℝ} (hA0 : A 0 = 0) {B : ℝ}
    (hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ)) {s : ℂ} (hs : 1 / 2 < s.re) :
    mellin (stepSource A) (-s) = (∑' n, (A n : ℂ) * cmellinCell s n) / s := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
  set k : ℝ → ℂ := fun y => (y : ℂ) ^ (-s - 1)
  have hk : ContinuousOn k (Ici 1) := fun y hy => by
    have hy0 : (0 : ℝ) < y := by linarith [mem_Ici.mp hy]
    exact ((hasDerivAt_ofReal_cpow_neg (w := s + 1) hy0).continuousAt.congr
      (Eventually.of_forall fun z => by simp only [k]; congr 1; ring)).continuousWithinAt
  have hkpiece : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), k y = cmellinCell s (n + 1) / s := by
    intro n
    have h0 : (0 : ℝ) ∉ uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
      rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [integral_cpow (Or.inr ⟨by intro h; apply hsne; linear_combination -h, h0⟩)]
    simp only [cmellinCell, show -s - 1 + 1 = -s by ring]
    push_cast
    field_simp
    ring_nf
  have hknorm : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖ ≤ ((n : ℝ) + 1) ^ (-s.re - 1) := by
    intro n
    have hconst : ∫ _y in ((n : ℝ) + 1)..((n : ℝ) + 2), ((n : ℝ) + 1) ^ (-s.re - 1) =
        ((n : ℝ) + 1) ^ (-s.re - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (by linarith) ?_ (by simp) fun y hy => ?_
    · exact (hk.mono (by
        rw [← uIcc_of_le (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)]
        intro z hz; rw [uIcc_of_le (by linarith)] at hz
        exact le_trans (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hz.1)).norm.intervalIntegrable_of_Icc
          (by linarith)
    · have hy0 : (0 : ℝ) < y := by linarith [hy.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      simp only [k]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      simp only [sub_re, neg_re, one_re]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hy.1 (by linarith)
  have hsumB : Summable (fun n : ℕ => B * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) - s.re - 1)) := by
    have := (Real.summable_nat_rpow.mpr (show (1 / 2 : ℝ) - s.re - 1 < -1 by linarith)).mul_left B
    have h2 := (summable_nat_add_iff 1).mpr this
    refine h2.congr fun n => ?_
    push_cast; ring_nf
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 1 le_rfl); simpa using this
  have hsum : Summable (fun n : ℕ => |A (n + 1)| * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖) := by
    refine hsumB.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _)
      (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _)) fun n => ?_
    have hA := hB (n + 1) (by omega)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc |A (n + 1)| * ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖
        ≤ (B * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) * ((n : ℝ) + 1) ^ (-s.re - 1) := by
          refine mul_le_mul (by exact_mod_cast hA) (hknorm n)
            (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _) (by positivity)
      _ = B * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) - s.re - 1) := by
          rw [mul_assoc, ← Real.rpow_add hn1]; ring_nf
  obtain ⟨hint, heq⟩ := integral_Ioi_one_stepSource_mul A hk hsum
  have hmel : mellin (stepSource A) (-s) = ∫ y in Ioi (1 : ℝ), stepSource A y * k y := by
    rw [mellin]
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one) fun y hy => ?_]
    · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [k, smul_eq_mul]; rw [mul_comm]
    · have hy1 : ¬ 1 < y := hy.2
      simp [stepSource, hy1]
  rw [hmel, heq]
  simp_rw [hkpiece]
  have hser : Summable (fun n : ℕ => (A n : ℂ) * cmellinCell s n) := by
    refine ((Real.summable_nat_rpow.mpr (show (1 / 2 : ℝ) - s.re - 1 < -1 by linarith)).mul_left
      (B * ‖s‖)).of_norm_bounded fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hA0]; positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hb := (mellinCell_bounds hs0 hn).2
      calc |A n| * ‖cmellinCell s n‖ ≤ (B * (n : ℝ) ^ (1 / 2 : ℝ)) *
            (‖s‖ / s.re * (s.re * (n : ℝ) ^ (-s.re - 1))) :=
          mul_le_mul (hB n hn) ((norm_cmellinCell_le hs0 hn).trans
            (mul_le_mul_of_nonneg_left hb (by positivity))) (norm_nonneg _) (by positivity)
        _ = B * ‖s‖ * (n : ℝ) ^ ((1 / 2 : ℝ) - s.re - 1) := by
          rw [show (1 / 2 : ℝ) - s.re - 1 = 1 / 2 + (-s.re - 1) by ring, Real.rpow_add hn0]
          field_simp
  rw [hser.tsum_eq_zero_add, hA0]
  simp only [Complex.ofReal_zero, zero_mul, zero_add]
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  ring

/-- The step source in the logarithmic variable, damped: `u ↦ e^{σu} A(⌊e^{-u}⌋)`. -/
def logStepSource (A : ℕ → ℝ) (σ u : ℝ) : ℂ :=
  (Real.exp (σ * u) : ℂ) * stepSource A (Real.exp (-u))

/-- The Mellin transform of the step source on `Re = −σ` is a Fourier transform. -/
theorem mellin_stepSource_neg_eq_fourier (A : ℕ → ℝ) (σ t : ℝ) :
    mellin (stepSource A) (-((σ : ℂ) + t * I)) = 𝓕 (logStepSource A σ) (t / (-(2 * Real.pi))) := by
  have hf : (fun u : ℝ => Real.exp (-(-((σ : ℂ) + t * I)).re * u) • stepSource A (Real.exp (-u))) =
      logStepSource A σ := by
    funext u
    simp only [logStepSource, neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, neg_neg, Complex.real_smul]
  have hx : (-((σ : ℂ) + t * I)).im / (2 * Real.pi) = t / (-(2 * Real.pi)) := by
    simp only [neg_im, add_im, ofReal_im, mul_im, I_re, mul_zero, ofReal_re, I_im, mul_one,
      zero_add, add_zero]
    rw [div_neg, neg_div]
  rw [mellin_eq_fourier, hf, hx]

/-- `|e^{σu} A(⌊e^{-u}⌋)| ≤ B e^{(σ − 1/2)u}` on `u ≤ 0`, and it vanishes on `u > 0`. -/
theorem norm_logStepSource_le {A : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ)) (σ u : ℝ) :
    ‖logStepSource A σ u‖ ≤ (Iic (0 : ℝ)).indicator (fun u => B * Real.exp ((σ - 1 / 2) * u)) u := by
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 1 le_rfl); simpa using this
  simp only [logStepSource, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hs := norm_stepSource_le hB (Real.exp (-u))
  by_cases hu : u ≤ 0
  · rw [indicator_of_mem (mem_Iic.mpr hu)]
    split_ifs at hs with h1
    · calc Real.exp (σ * u) * ‖stepSource A (Real.exp (-u))‖
          ≤ Real.exp (σ * u) * (B * Real.exp (-u) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
        _ = B * Real.exp ((σ - 1 / 2) * u) := by
            rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]
            congr 2
            ring
    · rw [norm_le_zero_iff.mp hs, norm_zero, mul_zero]
      exact mul_nonneg hB0 (Real.exp_pos _).le
  · rw [indicator_of_notMem (by simpa using hu)]
    have h1 : ¬ 1 < Real.exp (-u) := by
      rw [not_lt, Real.exp_le_one_iff]; linarith
    simp [stepSource, h1]

theorem aestronglyMeasurable_logStepSource (A : ℕ → ℝ) (σ : ℝ) :
    AEStronglyMeasurable (logStepSource A σ) volume :=
  ((Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul σ))).mul
    ((measurable_stepSource A).comp (Real.measurable_exp.comp measurable_neg))).aestronglyMeasurable

theorem integrable_logStepSource {A : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ)) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (logStepSource A σ) :=
  (IntegrableOn.integrable_indicator
    ((integrableOn_exp_mul_Iic (show 0 < σ - 1 / 2 by linarith) 0).const_mul B)
    measurableSet_Iic).mono' (aestronglyMeasurable_logStepSource A σ)
    (Eventually.of_forall (norm_logStepSource_le hB σ))

theorem memLp_logStepSource {A : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ)) {σ : ℝ} (hσ : 1 / 2 < σ) :
    MemLp (logStepSource A σ) 2 := by
  have hgmeas := aestronglyMeasurable_logStepSource A σ
  rw [memLp_two_iff_integrable_sq_norm hgmeas]
  set D2 : ℝ → ℝ := (Iic (0 : ℝ)).indicator fun u => B ^ 2 * Real.exp ((2 * σ - 1) * u)
  have hD2 : Integrable D2 :=
    IntegrableOn.integrable_indicator
      ((integrableOn_exp_mul_Iic (show 0 < 2 * σ - 1 by linarith) 0).const_mul (B ^ 2))
      measurableSet_Iic
  refine hD2.mono' (hgmeas.norm.pow 2) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_logStepSource_le hB σ u
  by_cases hu : u ≤ 0
  · simp only [D2, indicator_of_mem (mem_Iic.mpr hu)] at h ⊢
    calc ‖logStepSource A σ u‖ ^ 2 ≤ (B * Real.exp ((σ - 1 / 2) * u)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = B ^ 2 * Real.exp ((2 * σ - 1) * u) := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  · simp only [D2, indicator_of_notMem (show u ∉ Iic (0 : ℝ) by simpa using hu)] at h ⊢
    rw [le_antisymm h (norm_nonneg _)]; norm_num

/-- The Fourier transform of an integrable `L²` function is square integrable. -/
theorem integrable_norm_sq_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2) :
    Integrable (fun ξ => ‖𝓕 φ ξ‖ ^ 2) := by
  set u : Lp ℂ 2 (volume : Measure ℝ) := hφ2.toLp φ
  have hcoe : (u : ℝ → ℂ) =ᵐ[volume] φ := hφ2.coeFn_toLp
  have hF : ((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ := by
    refine (HTGeometry.coeFn_fourierTransform_eq_fourierIntegral u (hφ.congr hcoe.symm)).trans ?_
    filter_upwards with ξ
    exact Real.fourier_congr_ae hcoe ξ
  have hmem : MemLp (𝓕 φ) 2 := (Lp.memLp (𝓕 u)).ae_eq hF
  exact (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem

/-- The line energy of the step source is finite for `σ > 1/2`. -/
theorem integrable_lineEnergy_stepSource {A : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ)) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun t : ℝ => ‖mellin (stepSource A) (-((σ : ℂ) + t * I))‖ ^ 2) := by
  simp_rw [mellin_stepSource_neg_eq_fourier]
  exact (integrable_norm_sq_fourier (integrable_logStepSource hB hσ)
    (memLp_logStepSource hB hσ)).comp_div (neg_ne_zero.mpr (by positivity))

/-- **Mellin–Plancherel for the step source.** For `σ > 1/2`,
`∫ |𝓜A(−σ − it)|² dt = (π/σ) Σ_n A(n)² (n^{-2σ} − (n+1)^{-2σ})`. -/
theorem lineEnergy_stepSource_eq {A : ℕ → ℝ} (hA0 : A 0 = 0) {B : ℝ}
    (hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ)) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ t : ℝ, ‖mellin (stepSource A) (-((σ : ℂ) + t * I))‖ ^ 2 =
      (Real.pi / σ) * ∑' n, A n ^ 2 * mellinCell (2 * σ) n := by
  have hσ0 : 0 < σ := by linarith
  set g : ℝ → ℂ := logStepSource A σ with hg
  have hmf := mellin_stepSource_neg_eq_fourier A σ
  have hgint : Integrable g := integrable_logStepSource hB hσ
  have hgL2 : MemLp g 2 := memLp_logStepSource hB hσ
  -- Plancherel and rescaling
  have hscale : ∫ t : ℝ, ‖𝓕 g (t / (-(2 * Real.pi)))‖ ^ 2 =
      2 * Real.pi * ∫ ξ : ℝ, ‖𝓕 g ξ‖ ^ 2 := by
    rw [Measure.integral_comp_div (fun ξ => ‖𝓕 g ξ‖ ^ 2) (-(2 * Real.pi)), smul_eq_mul,
      abs_neg, abs_of_pos (by positivity)]
  simp_rw [hmf]
  rw [hscale, HTGeometry.integral_norm_sq_fourier hgint hgL2]
  -- the energy of `g` in the variable `x = e^{-u}`
  set R : ℝ → ℝ := fun x => (if 1 < x then A ⌊x⌋₊ ^ 2 else 0) * x ^ (-2 * σ - 1) with hR
  have hcv := HTGeometry.integral_Ioi_comp_neg_log_div (fun u => ‖g u‖ ^ 2)
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖g (-Real.log x)‖ ^ 2 * x⁻¹ = R x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [hg, logStepSource, neg_neg, Real.exp_log hx0, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hR]
    have he : Real.exp (σ * -Real.log x) = x ^ (-σ) := by
      rw [Real.rpow_def_of_pos hx0]; ring_nf
    rw [he]
    unfold stepSource
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        show (-2 * σ - 1) = (-σ) * 2 + (-1) by ring, Real.rpow_add hx0, Real.rpow_mul hx0.le,
        Real.rpow_neg_one]
      norm_num
      ring
    · simp
  rw [← hcv, setIntegral_congr_fun measurableSet_Ioi hpt]
  have hzero : ∫ x in Ioi (0 : ℝ), R x = ∫ x in Ioi (1 : ℝ), R x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one) fun y hy => ?_
    have hy1 : ¬ 1 < y := hy.2
    simp [hR, hy1]
  rw [hzero]
  -- the series of the pieces
  set k : ℝ → ℂ := fun y => ((y ^ (-2 * σ - 1) : ℝ) : ℂ)
  have hRk : ∀ y, ((R y : ℝ) : ℂ) = stepSource (fun n => A n ^ 2) y * k y := fun y => by
    simp only [hR, k, stepSource]; split_ifs <;> push_cast <;> ring
  have hk : ContinuousOn k (Ici 1) := fun y hy =>
    (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [mem_Ici.mp hy])))).continuousWithinAt
  have hreal : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), y ^ (-2 * σ - 1) =
      mellinCell (2 * σ) (n + 1) / (2 * σ) := by
    intro n
    have h0 : (0 : ℝ) ∉ uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
      rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, h0⟩), mellinCell,
      show -2 * σ - 1 + 1 = -(2 * σ) by ring]
    push_cast
    field_simp
    ring_nf
  have hpiece : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), k y =
      ((mellinCell (2 * σ) (n + 1) / (2 * σ) : ℝ) : ℂ) := fun n => by
    simp only [k]; rw [intervalIntegral.integral_ofReal, hreal n]
  have hnorm : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖ =
      mellinCell (2 * σ) (n + 1) / (2 * σ) := fun n => by
    rw [← hreal n]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le (by linarith)] at hy
    have hy0 : (0 : ℝ) < y := by linarith [hy.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [k, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
  have hB2 : ∀ n, 1 ≤ n → |A n ^ 2| ≤ B ^ 2 * (n : ℝ) ^ (1 : ℝ) := fun n hn => by
    rw [abs_pow, Real.rpow_one]
    have h := hB n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc |A n| ^ 2 ≤ (B * (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = B ^ 2 * n := by
          rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn0]; norm_num
  have hcellsum : Summable (fun n => A n ^ 2 * mellinCell (2 * σ) n) :=
    summable_mul_mellinCell (a := 1) (C := B ^ 2) (show (0 : ℝ) < 2 * σ by linarith)
      (by linarith) (f := fun n => A n ^ 2) (by simp [hA0]) hB2
  have hsumA : Summable (fun n : ℕ => |A (n + 1) ^ 2| *
      ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖) := by
    refine (((summable_nat_add_iff 1).mpr hcellsum).div_const (2 * σ)).congr fun n => ?_
    rw [hnorm n, abs_of_nonneg (sq_nonneg _)]
    ring
  obtain ⟨-, hser⟩ := integral_Ioi_one_stepSource_mul (fun n => A n ^ 2) hk hsumA
  have hRint : ((∫ x in Ioi (1 : ℝ), R x : ℝ) : ℂ) =
      ∑' n : ℕ, ((A (n + 1) ^ 2 : ℝ) : ℂ) * ((mellinCell (2 * σ) (n + 1) / (2 * σ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hRk]
    rw [hser]
    exact tsum_congr fun n => by rw [hpiece n]
  have hRval : ∫ x in Ioi (1 : ℝ), R x =
      ∑' n : ℕ, A (n + 1) ^ 2 * (mellinCell (2 * σ) (n + 1) / (2 * σ)) := by
    have h := hRint
    simp_rw [← Complex.ofReal_mul] at h
    rw [← Complex.ofReal_tsum] at h
    exact_mod_cast h
  have hdiv : ∑' n : ℕ, A (n + 1) ^ 2 * (mellinCell (2 * σ) (n + 1) / (2 * σ)) =
      (∑' n : ℕ, A (n + 1) ^ 2 * mellinCell (2 * σ) (n + 1)) / (2 * σ) := by
    rw [← tsum_div_const]; exact tsum_congr fun n => by ring
  rw [hRval, hdiv, hcellsum.tsum_eq_zero_add, hA0]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add]
  field_simp

/-! ### The receiver as a boundary line energy -/

/-- **The spectral identity of the half-damped receiver.** For `1/2 < σ < 1`,
`Σ_n A(n)² (n^{-2σ} − (n+1)^{-2σ}) = (σ/π) ∫ |ζ(s)(C(s) − m)/s|² dt`, `s = σ + it`. -/
theorem sum_sq_mul_mellinCell_eq_lineEnergy {K : ℝ} {c : ℕ → ℝ} (hc : DampedClass K (1 / 2) c)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∑' n, weightCenteredPrefix c (∑' d : ℕ, c d / d) n ^ 2 * mellinCell (2 * σ) n =
      σ / Real.pi * ∫ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * I) *
        (weightDirichletSeries c ((σ : ℂ) + t * I) - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) /
          ((σ : ℂ) + t * I)‖ ^ 2 := by
  set A := weightCenteredPrefix c (∑' d : ℕ, c d / d)
  have hA0 : A 0 = 0 := weightCenteredPrefix_zero c _
  have hσ0 : 0 < σ := by linarith
  set B := K * (1 + 1 / (1 - 1 / 2) + 1 / (1 / 2))
  have hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ) := fun n hn => by
    have h := abs_weightCenteredPrefix_le_of_dampedClass (K := K) (ε := 1 / 2)
      (by norm_num) (by norm_num) hc hn
    rw [show (n : ℝ) ^ (1 - 1 / 2 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) by norm_num] at h
    exact h
  have hline := lineEnergy_stepSource_eq hA0 hB hσ
  have hpt : ∀ t : ℝ, mellin (stepSource A) (-((σ : ℂ) + t * I)) =
      riemannZeta ((σ : ℂ) + t * I) *
        (weightDirichletSeries c ((σ : ℂ) + t * I) - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) /
          ((σ : ℂ) + t * I) := by
    intro t
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    rw [mellin_stepSource_neg hA0 hB (by rw [hre]; exact hσ),
      cmellinPairing_eq_zeta_mul hc (by rw [hre]; exact hσ) (by rw [hre]; exact hσ1)]
  simp_rw [hpt] at hline
  rw [hline]
  field_simp

/-- The boundary line integrand `|ζ(s)(C(s) − m)/s|²` is integrable on every line `1/2 < σ < 1`. -/
theorem integrable_lineEnergy {K : ℝ} {c : ℕ → ℝ} (hc : DampedClass K (1 / 2) c)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Integrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + t * I) *
      (weightDirichletSeries c ((σ : ℂ) + t * I) - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) /
        ((σ : ℂ) + t * I)‖ ^ 2) := by
  set A := weightCenteredPrefix c (∑' d : ℕ, c d / d)
  have hA0 : A 0 = 0 := weightCenteredPrefix_zero c _
  set B := K * (1 + 1 / (1 - 1 / 2) + 1 / (1 / 2))
  have hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ) := fun n hn => by
    have h := abs_weightCenteredPrefix_le_of_dampedClass (K := K) (ε := 1 / 2)
      (by norm_num) (by norm_num) hc hn
    rw [show (n : ℝ) ^ (1 - 1 / 2 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) by norm_num] at h
    exact h
  refine (integrable_lineEnergy_stepSource hB hσ).congr (Eventually.of_forall fun t => ?_)
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  dsimp only
  rw [mellin_stepSource_neg hA0 hB (by rw [hre]; exact hσ),
    cmellinPairing_eq_zeta_mul hc (by rw [hre]; exact hσ) (by rw [hre]; exact hσ1)]

/-- **A paid receiver caps the cell energies**: `Σ_n A(n)² Δ_n(2σ) ≤ 4σE` for `σ ≥ 1/2`, since
`Δ_n(2σ) ≤ 2σ n^{-2σ-1} ≤ 4σ/(n(n+1))`. -/
theorem tsum_sq_mul_mellinCell_le_of_energy {A : ℕ → ℝ} (hA0 : A 0 = 0) {E σ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hE : ∀ T, ∑ n ∈ Finset.Icc 1 T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) :
    ∑' n, A n ^ 2 * mellinCell (2 * σ) n ≤ 4 * σ * E := by
  have hσ0 : 0 < 2 * σ := by linarith
  have hE0 : 0 ≤ E := by simpa using hE 0
  have hcell : ∀ n, 1 ≤ n → mellinCell (2 * σ) n ≤ 4 * σ / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hpow : (n : ℝ) ^ (-(2 * σ) - 1) ≤ (n : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hsq : (n : ℝ) ^ (-2 : ℝ) ≤ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [Real.rpow_neg hn0.le, Real.rpow_two, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc mellinCell (2 * σ) n ≤ 2 * σ * (n : ℝ) ^ (-(2 * σ) - 1) := (mellinCell_bounds hσ0 hn).2
      _ ≤ 2 * σ * (2 / ((n : ℝ) * ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (hpow.trans hsq) hσ0.le
      _ = 4 * σ / ((n : ℝ) * ((n : ℝ) + 1)) := by ring
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) fun N => ?_
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hA0]
    · exact mul_nonneg (sq_nonneg _) (mellinCell_nonneg hσ0 hn)
  calc ∑ n ∈ Finset.range N, A n ^ 2 * mellinCell (2 * σ) n
      ≤ ∑ n ∈ Finset.range N, 4 * σ * (A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [hA0]
        · calc A n ^ 2 * mellinCell (2 * σ) n
              ≤ A n ^ 2 * (4 * σ / ((n : ℝ) * ((n : ℝ) + 1))) :=
                mul_le_mul_of_nonneg_left (hcell n hn) (sq_nonneg _)
            _ = _ := by ring
    _ = 4 * σ * ∑ n ∈ Finset.Icc 1 (N - 1), A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [← Finset.mul_sum]
        congr 1
        refine (Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_).symm
        · simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
        · have : n = 0 := by simp only [Finset.mem_Icc, Finset.mem_range] at hn hn'; omega
          subst this; simp [hA0]
    _ ≤ 4 * σ * E := mul_le_mul_of_nonneg_left (hE _) (by linarith)

/-- For each horizon the pronic energy is the limit of the cell energies as `σ ↓ 1/2`. -/
theorem tendsto_sum_sq_mul_mellinCell (A : ℕ → ℝ) (T : ℕ) :
    Tendsto (fun σ : ℝ => ∑ n ∈ Finset.Icc 1 T, A n ^ 2 * mellinCell (2 * σ) n) (𝓝[>] (1 / 2))
      (𝓝 (∑ n ∈ Finset.Icc 1 T, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))) := by
  refine tendsto_finsetSum _ fun n hn => ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by linarith
  have hcell : Tendsto (fun σ : ℝ => mellinCell (2 * σ) n) (𝓝[>] (1 / 2))
      (𝓝 (1 / ((n : ℝ) * ((n : ℝ) + 1)))) := by
    have hc : Continuous (fun σ : ℝ => mellinCell (2 * σ) n) := by
      unfold mellinCell
      exact ((continuous_const.rpow (continuous_neg.comp (continuous_const.mul continuous_id))
        fun _ => Or.inl hn0.ne').sub (continuous_const.rpow
          (continuous_neg.comp (continuous_const.mul continuous_id)) fun _ => Or.inl (by positivity)))
    have hval : mellinCell (2 * (1 / 2)) n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      simp only [mellinCell, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_neg_one]
      field_simp
      ring
    rw [← hval]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have := hcell.const_mul (A n ^ 2)
  rwa [mul_one_div] at this

/-- **A bounded boundary line energy pays the receiver.** If the line energies of
`ζ(s)(C(s) − m)/s` are at most `M` on `1/2 < σ < 3/4`, every pronic energy is at most
`3M/(4π)`. -/
theorem weightPronicEnergy_le_of_lineEnergy_le {K M : ℝ} {c : ℕ → ℝ}
    (hc : DampedClass K (1 / 2) c)
    (hM : ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 →
      ∫ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * I) *
        (weightDirichletSeries c ((σ : ℂ) + t * I) - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) /
          ((σ : ℂ) + t * I)‖ ^ 2 ≤ M) (T : ℕ) :
    weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ 3 * M / (4 * Real.pi) := by
  set A := weightCenteredPrefix c (∑' d : ℕ, c d / d)
  have hA0 : A 0 = 0 := weightCenteredPrefix_zero c _
  set B := K * (1 + 1 / (1 - 1 / 2) + 1 / (1 / 2))
  have hB : ∀ n, 1 ≤ n → |A n| ≤ B * (n : ℝ) ^ (1 / 2 : ℝ) := fun n hn => by
    have h := abs_weightCenteredPrefix_le_of_dampedClass (K := K) (ε := 1 / 2)
      (by norm_num) (by norm_num) hc hn
    rw [show (n : ℝ) ^ (1 - 1 / 2 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) by norm_num] at h
    exact h
  have hlim := tendsto_sum_sq_mul_mellinCell A T
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 3 / 4 by norm_num)] with σ hσ
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hsum : Summable (fun n => A n ^ 2 * mellinCell (2 * σ) n) := by
    have hB2 : ∀ n, 1 ≤ n → |A n ^ 2| ≤ B ^ 2 * (n : ℝ) ^ (1 : ℝ) := fun n hn => by
      rw [abs_pow, Real.rpow_one]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc |A n| ^ 2 ≤ (B * (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB n hn) 2
        _ = B ^ 2 * n := by
            rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hn0]; norm_num
    exact summable_mul_mellinCell (a := 1) (C := B ^ 2) (by linarith) (by linarith [hσ.1])
      (f := fun n => A n ^ 2) (by simp [hA0]) hB2
  have hpart : ∑ n ∈ Finset.Icc 1 T, A n ^ 2 * mellinCell (2 * σ) n ≤
      ∑' n, A n ^ 2 * mellinCell (2 * σ) n :=
    Summable.sum_le_tsum _ (fun n hn => by
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · simp [hA0]
      · exact mul_nonneg (sq_nonneg _) (mellinCell_nonneg (by linarith) hn')) hsum
  rw [sum_sq_mul_mellinCell_eq_lineEnergy hc hσ.1 (by linarith [hσ.2])] at hpart
  have hpi : 0 < Real.pi := Real.pi_pos
  calc ∑ n ∈ Finset.Icc 1 T, A n ^ 2 * mellinCell (2 * σ) n
      ≤ σ / Real.pi * M := hpart.trans (mul_le_mul_of_nonneg_left (hM σ hσ.1 hσ.2)
          (div_nonneg hσ0.le hpi.le))
    _ ≤ 3 / 4 / Real.pi * M := by
        have hM0 : 0 ≤ M := (integral_nonneg fun _ => by positivity).trans (hM σ hσ.1 hσ.2)
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hσ.2.le hpi.le) hM0
    _ = 3 * M / (4 * Real.pi) := by field_simp

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
