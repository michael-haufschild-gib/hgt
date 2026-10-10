import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalBound
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip
import GaloisForLFunctions.HTGeometry.GaussianLightConeAmplification

/-!
# One vertical line of the complex-time Gaussian heat trace decides RH

For complex time `τ` with `Re τ > 0` the Gaussian heat trace of the Xi divisor is

`ν(τ) = Σ_q exp(-τ z_q²)`,  `z_q = -i(ρ_q - 1/2)`

(`xiGaussianHeatTraceC`).  Under RH every `z_q²` is a positive real, so `‖ν(τ)‖ ≤ ν(Re τ)`
(`norm_xiGaussianHeatTraceC_le_of_rh`).  This module proves the converse from a single vertical line.

**Theorem** (`riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line`).  For every
`a > 0`, RH holds iff `b ↦ ν(a + ib)` is bounded on `ℝ`.

Possible cancellation between the off-line terms is handled by analytic continuation in the time
variable.

* `ν` converges absolutely and is holomorphic on the whole right half-plane, unconditionally, with
  `‖ν(σ + ib)‖ ≤ (4K/σ) exp(b²/σ)`, where `K = Σ_q ‖z_q‖⁻²`
  (`norm_xiGaussianHeatTraceC_le_growth`, `differentiableAt_xiGaussianHeatTraceC`).
* On the sector `|Im τ| ≤ Re τ`, `Re τ ≥ a` the trace is bounded by `3K/a`, because every zero has
  `‖z_q‖² > 150` (`norm_xiGaussianHeatTraceC_le_of_abs_im_le`).
* Phragmén–Lindelöf on the strip `π/4 < Im s < π/2`, through `τ = a + e^s`, joins the 45° ray to the
  vertical line `Re τ = a`.  This is legitimate because the growth `exp(e^{2 Re s}/a)` has exponent
  `2 < π/(π/4)`.  So a bound on the vertical line propagates to the whole sector
  (`norm_xiGaussianHeatTraceC_le_of_vertical`).
* An off-line zero gives a copy with `Im z_q² > 0`.  Along a ray `a + r e^{iφ}` with `φ` close to
  `π/2`, finitely many exponents `e^{iφ} z_q²` have negative real part, and one of them belongs to
  that copy.  The light-cone lemma `exists_lt_norm_tsum_mul_exp_neg_of_re_neg` then makes the trace
  unbounded on the ray, which contradicts the sector bound.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The imaginary part of the squared spectral coordinate is at most its norm:
`(Im z²)² ≤ ‖z‖²`, since `|Im z| < 1/2`. -/
theorem xiSpectralSq_im_sq_le_norm_sq (q : XiZeroCopy) :
    (xiSpectralPoint q ^ (2 : ℕ)).im ^ 2 ≤ ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hq := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  have hy : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by rw [him, neg_sq]; exact hq
  have hz2 : (xiSpectralPoint q ^ (2 : ℕ)).im =
      2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
    rw [pow_two, Complex.mul_im]; ring
  rw [hz2, Complex.sq_norm, Complex.normSq_apply]
  set x := (xiSpectralPoint q).re
  set y := (xiSpectralPoint q).im
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 4 * y ^ 2), sq_nonneg y]

theorem xiSpectralSq_norm_sq_lt_two_mul_re (q : XiZeroCopy) :
    ‖xiSpectralPoint q‖ ^ (2 : ℕ) < 2 * (xiSpectralPoint q ^ (2 : ℕ)).re := by
  rw [Complex.sq_norm]
  exact xiSpectralPoint_normSq_lt_two_mul_sq_re q

theorem exp_neg_le_inv_of_pos {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp x])

/-- **Termwise growth bound.**  For `Re τ > 0`,
`‖exp(-τ z²)‖ ≤ exp((Im τ)²/Re τ) · (4/Re τ) · ‖z‖⁻²`. -/
theorem norm_xiGaussianHeatTermC_le_growth {τ : ℂ} (hτ : 0 < τ.re) (q : XiZeroCopy) :
    ‖xiGaussianHeatTermC τ q‖ ≤
      Real.exp (τ.im ^ 2 / τ.re) * (4 / τ.re) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  rw [norm_xiGaussianHeatTermC]
  have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
  have hB := xiSpectralSq_im_sq_le_norm_sq q
  have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    have := xiSpectralPoint_ne_zero q
    positivity
  set A := (xiSpectralPoint q ^ (2 : ℕ)).re
  set B := (xiSpectralPoint q ^ (2 : ℕ)).im
  set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  set σ := τ.re
  set b := τ.im
  have h1 : σ * (b * B) ≤ σ ^ 2 * N / 4 + b ^ 2 := by
    nlinarith [sq_nonneg (σ * B / 2 - b), mul_le_mul_of_nonneg_left hB (sq_nonneg σ)]
  have h2 : b * B ≤ σ * N / 4 + b ^ 2 / σ := by
    rw [← sub_nonneg]
    have hid : σ * N / 4 + b ^ 2 / σ - b * B = (σ ^ 2 * N / 4 + b ^ 2 - σ * (b * B)) / σ := by
      field_simp
    rw [hid]
    exact div_nonneg (by linarith) hτ.le
  have h3 : -(σ * A - b * B) ≤ b ^ 2 / σ + -(σ * N / 4) := by nlinarith
  calc Real.exp (-(σ * A - b * B))
      ≤ Real.exp (b ^ 2 / σ + -(σ * N / 4)) := Real.exp_le_exp.2 h3
    _ = Real.exp (b ^ 2 / σ) * Real.exp (-(σ * N / 4)) := Real.exp_add _ _
    _ ≤ Real.exp (b ^ 2 / σ) * (1 / (σ * N / 4)) :=
        mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos (by positivity)) (Real.exp_pos _).le
    _ = Real.exp (b ^ 2 / σ) * (4 / σ) * (1 / N) := by
        field_simp

/-- **Sector bound for one term.**  If `|Im τ| ≤ Re τ`, then `‖exp(-τ z²)‖ ≤ (3/Re τ) ‖z‖⁻²`. -/
theorem norm_xiGaussianHeatTermC_le_of_abs_im_le {τ : ℂ} (hτ : 0 < τ.re) (him : |τ.im| ≤ τ.re)
    (q : XiZeroCopy) :
    ‖xiGaussianHeatTermC τ q‖ ≤ (3 / τ.re) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  rw [norm_xiGaussianHeatTermC]
  have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
  have hB := xiSpectralSq_im_sq_le_norm_sq q
  have h150 := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  set A := (xiSpectralPoint q ^ (2 : ℕ)).re
  set B := (xiSpectralPoint q ^ (2 : ℕ)).im
  set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  set σ := τ.re
  set b := τ.im
  have hBabs : |B| ≤ N / 6 := by
    have hsq : B ^ 2 ≤ (N / 6) ^ 2 := by nlinarith
    have := sq_le_sq.1 hsq
    rwa [abs_of_pos (by linarith : (0 : ℝ) < N / 6)] at this
  have hbB : b * B ≤ σ * (N / 6) := by
    calc b * B ≤ |b * B| := le_abs_self _
      _ = |b| * |B| := abs_mul _ _
      _ ≤ σ * (N / 6) := mul_le_mul him hBabs (abs_nonneg _) hτ.le
  have h3 : -(σ * A - b * B) ≤ -(σ * N / 3) := by nlinarith
  calc Real.exp (-(σ * A - b * B))
      ≤ Real.exp (-(σ * N / 3)) := Real.exp_le_exp.2 h3
    _ ≤ 1 / (σ * N / 3) := exp_neg_le_inv_of_pos (by positivity)
    _ = (3 / σ) * (1 / N) := by field_simp

theorem summable_norm_xiGaussianHeatTermC {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy => ‖xiGaussianHeatTermC τ q‖) :=
  (xiSpectralPoint_inv_sq_summable.mul_left (Real.exp (τ.im ^ 2 / τ.re) * (4 / τ.re))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_xiGaussianHeatTermC_le_growth hτ)

/-- **Global growth.**  `‖ν(σ + ib)‖ ≤ exp(b²/σ) · (4/σ) · Σ_q ‖z_q‖⁻²` for every `σ > 0`. -/
theorem norm_xiGaussianHeatTraceC_le_growth {τ : ℂ} (hτ : 0 < τ.re) :
    ‖xiGaussianHeatTraceC τ‖ ≤ Real.exp (τ.im ^ 2 / τ.re) * (4 / τ.re) *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC hτ)).trans
    (Summable.tsum_le_tsum (norm_xiGaussianHeatTermC_le_growth hτ)
      (summable_norm_xiGaussianHeatTermC hτ) (xiSpectralPoint_inv_sq_summable.mul_left _))

/-- **Sector bound.**  On `Re τ ≥ a`, `|Im τ| ≤ Re τ` the trace is bounded by `(3/a) Σ_q ‖z_q‖⁻²`. -/
theorem norm_xiGaussianHeatTraceC_le_of_abs_im_le {a : ℝ} (ha : 0 < a) {τ : ℂ} (hre : a ≤ τ.re)
    (him : |τ.im| ≤ τ.re) :
    ‖xiGaussianHeatTraceC τ‖ ≤ 3 / a * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hτ : 0 < τ.re := ha.trans_le hre
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC hτ)).trans
    (Summable.tsum_le_tsum (fun q => ?_) (summable_norm_xiGaussianHeatTermC hτ)
      (xiSpectralPoint_inv_sq_summable.mul_left _))
  refine (norm_xiGaussianHeatTermC_le_of_abs_im_le hτ him q).trans ?_
  have : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by positivity
  gcongr

/-- The complex-time heat trace is holomorphic on the open right half-plane. -/
theorem differentiableAt_xiGaussianHeatTraceC {τ₀ : ℂ} (h : 0 < τ₀.re) :
    DifferentiableAt ℂ xiGaussianHeatTraceC τ₀ := by
  set R : ℝ := |τ₀.im| + 1
  set U : Set ℂ := {τ | τ₀.re / 2 < τ.re} ∩ {τ | |τ.im| < R}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
  have hmem : τ₀ ∈ U := ⟨by simp only [mem_setOf_eq]; linarith, by
    simp only [mem_setOf_eq, R]; linarith⟩
  have hbound : ∀ (q : XiZeroCopy) (τ : ℂ), τ ∈ U → ‖xiGaussianHeatTermC τ q‖ ≤
      Real.exp (R ^ 2 / (τ₀.re / 2)) * (4 / (τ₀.re / 2)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q τ hτU
    have hre : τ₀.re / 2 < τ.re := hτU.1
    have him : |τ.im| < R := hτU.2
    have hτ : 0 < τ.re := by linarith
    refine (norm_xiGaussianHeatTermC_le_growth hτ q).trans ?_
    have hN : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by positivity
    have hsq : τ.im ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs τ.im]
      exact pow_le_pow_left₀ (abs_nonneg _) him.le 2
    have he : Real.exp (τ.im ^ 2 / τ.re) ≤ Real.exp (R ^ 2 / (τ₀.re / 2)) :=
      Real.exp_le_exp.2 (div_le_div₀ (by positivity) hsq (by linarith) hre.le)
    have h4 : 4 / τ.re ≤ 4 / (τ₀.re / 2) := div_le_div_of_nonneg_left (by norm_num) (by linarith)
      hre.le
    gcongr
  have hdiff : ∀ q : XiZeroCopy, DifferentiableOn ℂ (fun τ => xiGaussianHeatTermC τ q) U :=
    fun q => by
      unfold xiGaussianHeatTermC
      fun_prop
  have hD := Complex.differentiableOn_tsum_of_summable_norm
    (xiSpectralPoint_inv_sq_summable.mul_left _) hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hmem))

/-- **Phragmén–Lindelöf transfer.**  A bound `C` on the vertical line `Re τ = a` propagates to the
whole sector between the 45° ray from `a` and that line. -/
theorem norm_xiGaussianHeatTraceC_le_of_vertical {a : ℝ} (ha : 0 < a) {C : ℝ}
    (hC : ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C) {s : ℂ}
    (h1 : Real.pi / 4 ≤ s.im) (h2 : s.im ≤ Real.pi / 2) :
    ‖xiGaussianHeatTraceC ((a : ℂ) + Complex.exp s)‖ ≤
      max C (3 / a * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set K := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  have hK : 0 ≤ K := tsum_nonneg fun _ => by positivity
  have hpi := Real.pi_pos
  -- the real part of `a + e^s` is at least `a` on the closed strip
  have hre : ∀ s : ℂ, Real.pi / 4 ≤ s.im → s.im ≤ Real.pi / 2 →
      a ≤ ((a : ℂ) + Complex.exp s).re := by
    intro s h1 h2
    have hcos : 0 ≤ Real.cos s.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩
    simp only [add_re, ofReal_re, Complex.exp_re]
    have := mul_nonneg (Real.exp_pos s.re).le hcos
    linarith
  have hdiffAt : ∀ s : ℂ, Real.pi / 4 ≤ s.im → s.im ≤ Real.pi / 2 →
      DifferentiableAt ℂ (fun s => xiGaussianHeatTraceC ((a : ℂ) + Complex.exp s)) s := by
    intro s h1 h2
    have hτ : 0 < ((a : ℂ) + Complex.exp s).re := ha.trans_le (hre s h1 h2)
    exact (differentiableAt_xiGaussianHeatTraceC hτ).comp s
      ((differentiableAt_const _).add differentiableAt_exp)
  have hd : DiffContOnCl ℂ (fun s => xiGaussianHeatTraceC ((a : ℂ) + Complex.exp s))
      (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine ⟨fun s hs => (hdiffAt s hs.1.le hs.2.le).differentiableWithinAt, ?_⟩
    have hcl : closure (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2)) ⊆
        Complex.im ⁻¹' Icc (Real.pi / 4) (Real.pi / 2) :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_im)
    exact fun s hs => (hdiffAt s (hcl hs).1 (hcl hs).2).continuousAt.continuousWithinAt
  have hgrowth : ∃ c < Real.pi / (Real.pi / 2 - Real.pi / 4), ∃ B,
      (fun s => xiGaussianHeatTraceC ((a : ℂ) + Complex.exp s)) =O[comap (abs ∘ Complex.re) atTop ⊓
        𝓟 (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2))]
        fun s => Real.exp (B * Real.exp (c * |s.re|)) := by
    have h4 : Real.pi / (Real.pi / 2 - Real.pi / 4) = 4 := by field_simp; ring
    refine ⟨2, by rw [h4]; norm_num, 1 / a, Asymptotics.IsBigO.of_bound (4 / a * K) ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun s hs => ?_)
    have hres := hre s hs.1.le hs.2.le
    have hτ : 0 < ((a : ℂ) + Complex.exp s).re := ha.trans_le hres
    refine (norm_xiGaussianHeatTraceC_le_growth hτ).trans ?_
    set σ := ((a : ℂ) + Complex.exp s).re
    set b := ((a : ℂ) + Complex.exp s).im
    have hb : b ^ 2 ≤ Real.exp (2 * |s.re|) := by
      have hbim : b = Real.exp s.re * Real.sin s.im := by
        simp only [b, add_im, ofReal_im, Complex.exp_im, zero_add]
      rw [hbim, mul_pow]
      have hs2 : Real.sin s.im ^ 2 ≤ 1 := Real.sin_sq_le_one _
      have he2 : Real.exp s.re ^ 2 ≤ Real.exp (2 * |s.re|) := by
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.2 (by push_cast; linarith [le_abs_self s.re])
      nlinarith [sq_nonneg (Real.exp s.re), Real.exp_pos (2 * |s.re|)]
    have hexp : Real.exp (b ^ 2 / σ) ≤ Real.exp (1 / a * Real.exp (2 * |s.re|)) := by
      apply Real.exp_le_exp.2
      calc b ^ 2 / σ ≤ b ^ 2 / a := div_le_div_of_nonneg_left (sq_nonneg _) ha hres
        _ ≤ Real.exp (2 * |s.re|) / a := div_le_div_of_nonneg_right hb ha.le
        _ = 1 / a * Real.exp (2 * |s.re|) := by ring
    have h4σ : 4 / σ ≤ 4 / a := div_le_div_of_nonneg_left (by norm_num) ha hres
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (b ^ 2 / σ) * (4 / σ) * K
        ≤ Real.exp (1 / a * Real.exp (2 * |s.re|)) * (4 / a) * K := by gcongr
      _ = 4 / a * K * Real.exp (1 / a * Real.exp (2 * |s.re|)) := by ring
  refine PhragmenLindelof.horizontal_strip
    (f := fun s => xiGaussianHeatTraceC ((a : ℂ) + Complex.exp s)) (z := s) hd hgrowth ?_ ?_ h1 h2
  · -- the 45° ray
    intro z hz
    refine le_max_of_le_right (norm_xiGaussianHeatTraceC_le_of_abs_im_le ha (hre z hz.ge (by
      rw [hz]; linarith)) ?_)
    have hcs : Real.sin z.im = Real.cos z.im := by
      rw [hz, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hcos : 0 ≤ Real.cos z.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    simp only [add_im, add_re, ofReal_im, ofReal_re, Complex.exp_im, Complex.exp_re, zero_add]
    rw [hcs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hcos)]
    linarith
  · -- the vertical line
    intro z hz
    refine le_max_of_le_left ?_
    have hexp : Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [Complex.exp_re, hz, Real.cos_pi_div_two]
      · rw [Complex.exp_im, hz, Real.sin_pi_div_two, mul_one, Complex.mul_I_im, Complex.ofReal_re]
    rw [hexp]
    exact hC _

/-- An off-line zero produces a copy whose squared spectral coordinate has positive imaginary part. -/
theorem exists_xiZeroCopy_sq_im_pos_of_not_riemannHypothesis (h : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 0 < (xiSpectralPoint q ^ (2 : ℕ)).im := by
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero] at h
  push Not at h
  obtain ⟨q, hq⟩ := h
  have hx : (xiSpectralPoint q).re ≠ 0 := by
    have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    have := xiZeroCopy_two_lt_im_sq q
    intro h0
    rw [hre] at h0
    rw [h0] at this
    norm_num at this
  have hB : (xiSpectralPoint q ^ (2 : ℕ)).im ≠ 0 := by
    rw [pow_two, Complex.mul_im]
    intro h0
    have : 2 * ((xiSpectralPoint q).re * (xiSpectralPoint q).im) = 0 := by linarith
    rcases mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left two_ne_zero) with h' | h'
    · exact hx h'
    · exact hq h'
  rcases lt_or_gt_of_ne hB with hneg | hpos
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_⟩
    rw [xiSpectralPoint_lineConj, ← map_pow, Complex.conj_im]
    linarith
  · exact ⟨q, hpos⟩

/-- **Single vertical-line receiver.**  For every `a > 0`, RH holds iff the complex-time Gaussian heat
trace `ν(a + ib) = Σ_q exp(-(a + ib) z_q²)` is bounded in `b ∈ ℝ`. -/
theorem riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C := by
  constructor
  · intro hRH
    refine ⟨xiGaussianHeatTraceReal a, fun b => ?_⟩
    have h := norm_xiGaussianHeatTraceC_le_of_rh hRH (τ := (a : ℂ) + b * I) (by simpa using ha)
    simpa using h
  · rintro ⟨C, hC⟩
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_sq_im_pos_of_not_riemannHypothesis hRH
    set K := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
    set C' := max C (3 / a * K)
    set A₁ := (xiSpectralPoint q₁ ^ (2 : ℕ)).re
    set B₁ := (xiSpectralPoint q₁ ^ (2 : ℕ)).im
    have hpi := Real.pi_pos
    -- a direction close to the vertical in which the copy `q₁` grows
    obtain ⟨φ, hφ1, hφ2, hφneg⟩ : ∃ φ : ℝ, Real.pi / 4 < φ ∧ φ < Real.pi / 2 ∧
        Real.cos φ * A₁ - Real.sin φ * B₁ < 0 := by
      have hcont : ContinuousAt (fun φ : ℝ => Real.cos φ * A₁ - Real.sin φ * B₁) (Real.pi / 2) := by
        fun_prop
      have hval : (fun φ : ℝ => Real.cos φ * A₁ - Real.sin φ * B₁) (Real.pi / 2) < 0 := by
        simp only [Real.cos_pi_div_two, Real.sin_pi_div_two]
        linarith
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hval))
      refine ⟨Real.pi / 2 - min (δ / 2) (Real.pi / 8), ?_, ?_, hball ?_⟩
      · have := min_le_right (δ / 2) (Real.pi / 8)
        linarith
      · have : 0 < min (δ / 2) (Real.pi / 8) := lt_min (by linarith) (by linarith)
        linarith
      · have h0 : 0 < min (δ / 2) (Real.pi / 8) := lt_min (by linarith) (by linarith)
        rw [Real.dist_eq, show Real.pi / 2 - min (δ / 2) (Real.pi / 8) - Real.pi / 2 =
          -min (δ / 2) (Real.pi / 8) by ring, abs_neg, abs_of_pos h0]
        linarith [min_le_left (δ / 2) (Real.pi / 8)]
    have hcosφ : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ2⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsin1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
    set e : ℂ := Complex.exp ((φ : ℂ) * I)
    have he_re : e.re = Real.cos φ := Complex.exp_ofReal_mul_I_re φ
    have he_im : e.im = Real.sin φ := Complex.exp_ofReal_mul_I_im φ
    have hw_re : ∀ q : XiZeroCopy, (e * xiSpectralPoint q ^ (2 : ℕ)).re =
        Real.cos φ * (xiSpectralPoint q ^ (2 : ℕ)).re -
          Real.sin φ * (xiSpectralPoint q ^ (2 : ℕ)).im := fun q => by
      rw [Complex.mul_re, he_re, he_im]
    -- the trace along the ray is bounded by Phragmén–Lindelöf
    have hray : ∀ r : ℝ, 0 ≤ r → ‖xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e)‖ ≤ C' := by
      intro r hr
      rcases hr.eq_or_lt with h0 | hpos
      · rw [← h0, ofReal_zero, zero_mul, add_zero]
        refine le_max_of_le_right (norm_xiGaussianHeatTraceC_le_of_abs_im_le ha (by simp)
          (by simp [ha.le]))
      · have hs : (r : ℂ) * e = Complex.exp ((Real.log r : ℂ) + (φ : ℂ) * I) := by
          rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
        rw [hs]
        exact norm_xiGaussianHeatTraceC_le_of_vertical ha hC (by simp; linarith)
          (by simp; linarith)
    -- the light-cone lemma along the ray
    have hterm : ∀ (q : XiZeroCopy) (r : ℝ),
        Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
            Complex.exp (-(r : ℂ) * (e * xiSpectralPoint q ^ (2 : ℕ))) =
          xiGaussianHeatTermC ((a : ℂ) + (r : ℂ) * e) q := fun q r => by
      rw [xiGaussianHeatTermC, ← Complex.exp_add]
      congr 1
      ring
    have hτre : ∀ r : ℝ, 0 ≤ r → 0 < ((a : ℂ) + (r : ℂ) * e).re := fun r hr => by
      simp only [add_re, ofReal_re, re_ofReal_mul, he_re]
      nlinarith
    have hfin : {q : XiZeroCopy | (e * xiSpectralPoint q ^ (2 : ℕ)).re < 0}.Finite := by
      have hc2 : 0 < Real.cos φ ^ 2 / 4 := by positivity
      have hev := (xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero).eventually
        (gt_mem_nhds hc2)
      refine (Filter.eventually_cofinite.1 hev).subset fun q hq => ?_
      simp only [mem_setOf_eq] at hq ⊢
      rw [hw_re] at hq
      have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
      have hB := xiSpectralSq_im_sq_le_norm_sq q
      have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        have := xiSpectralPoint_ne_zero q
        positivity
      set A := (xiSpectralPoint q ^ (2 : ℕ)).re
      set B := (xiSpectralPoint q ^ (2 : ℕ)).im
      set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
      have hlt : Real.cos φ * N / 2 < |B| := by
        have h1 : Real.sin φ * B ≤ |B| := by
          calc Real.sin φ * B ≤ Real.sin φ * |B| :=
                mul_le_mul_of_nonneg_left (le_abs_self B) hsinφ
            _ ≤ 1 * |B| := mul_le_mul_of_nonneg_right hsin1 (abs_nonneg B)
            _ = |B| := one_mul _
        nlinarith
      have hsq : (Real.cos φ * N / 2) ^ 2 < B ^ 2 := by
        rw [← sq_abs B]
        exact pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
      rw [not_lt, le_div_iff₀ hN]
      nlinarith
    obtain ⟨r, hr0, hr⟩ := GaloisForLFunctions.HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg
      (w := fun q : XiZeroCopy => e * xiSpectralPoint q ^ (2 : ℕ))
      (c := fun q : XiZeroCopy => Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)))
      (ε₀ := 0) le_rfl
      (fun i j hij => by
        have hne : e ≠ 0 := Complex.exp_ne_zero _
        have : xiSpectralPoint i ^ (2 : ℕ) = xiSpectralPoint j ^ (2 : ℕ) :=
          mul_left_cancel₀ hne hij
        simp only [this])
      (fun _ _ => Complex.exp_ne_zero _) hfin
      (m := fun q => (2 / a) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
      (fun q => by positivity) (xiSpectralPoint_inv_sq_summable.mul_left _)
      (fun q hq ε hε => by
        rw [hterm, norm_xiGaussianHeatTermC]
        have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
        have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
          have := xiSpectralPoint_ne_zero q
          positivity
        have hq' : 0 ≤ (e * xiSpectralPoint q ^ (2 : ℕ)).re := hq
        rw [hw_re] at hq'
        have hre' : ((a : ℂ) + (ε : ℂ) * e).re = a + ε * Real.cos φ := by
          simp only [add_re, ofReal_re, re_ofReal_mul, he_re]
        have him' : ((a : ℂ) + (ε : ℂ) * e).im = ε * Real.sin φ := by
          simp only [add_im, ofReal_im, im_ofReal_mul, he_im, zero_add]
        rw [hre', him']
        set A := (xiSpectralPoint q ^ (2 : ℕ)).re
        set B := (xiSpectralPoint q ^ (2 : ℕ)).im
        set N := ‖xiSpectralPoint q‖ ^ (2 : ℕ)
        have hA : 0 < a * A := mul_pos ha (by linarith)
        have hexp : -((a + ε * Real.cos φ) * A - ε * Real.sin φ * B) ≤ -(a * A) := by
          nlinarith [mul_nonneg hε hq']
        calc Real.exp (-((a + ε * Real.cos φ) * A - ε * Real.sin φ * B))
            ≤ Real.exp (-(a * A)) := Real.exp_le_exp.2 hexp
          _ ≤ 1 / (a * A) := exp_neg_le_inv_of_pos hA
          _ ≤ 2 / a * (1 / N) := by
            rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hA (mul_pos ha hN)]
            nlinarith)
      (fun ε hε => by
        simp only [hterm]
        exact summable_norm_xiGaussianHeatTermC (hτre ε hε))
      ⟨q₁, by show (e * xiSpectralPoint q₁ ^ (2 : ℕ)).re < 0; rw [hw_re]; exact hφneg⟩ C'
    have hsum : ∑' q : XiZeroCopy, Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
        Complex.exp (-(r : ℂ) * (e * xiSpectralPoint q ^ (2 : ℕ))) =
          xiGaussianHeatTraceC ((a : ℂ) + (r : ℂ) * e) := by
      rw [xiGaussianHeatTraceC]
      exact tsum_congr fun q => hterm q r
    rw [hsum] at hr
    linarith [hray r hr0]

/-- **Contraction form.**  For every `a > 0`, RH holds iff on the vertical line `Re τ = a` the
complex-time heat trace never exceeds its real-time value: `‖ν(a + ib)‖ ≤ ν(a)` for all `b`. -/
theorem riemannHypothesis_iff_forall_norm_xiGaussianHeatTraceC_le_real {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔
      ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ xiGaussianHeatTraceReal a := by
  constructor
  · intro hRH b
    have h := norm_xiGaussianHeatTraceC_le_of_rh hRH (τ := (a : ℂ) + b * I) (by simpa using ha)
    simpa using h
  · intro h
    exact (riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha).2
      ⟨xiGaussianHeatTraceReal a, h⟩

end

end RHTower
