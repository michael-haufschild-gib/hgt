import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalLineReceiver
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureGaussianAmplifiedReceiver

/-!
# The HCF diagonal at one height, with complex amplification, decides RH

The Gaussian-amplified HCF diagonal at height `t` is `Σ_q F_t(z_q)² exp(-σ(z_q - t)²)`, where
`F_t(z) = 2/(1 + (z - t)²)` (`criticalFeatureGaussianAmplifiedTrace`).  For real amplification `σ`,
RH is equivalent to boundedness at *every* height
(`riemannHypothesis_iff_forall_criticalFeatureGaussianAmplifiedTrace_bounded`).

Here the height is frozen at `t = 0` and the amplification is allowed to be complex:

`H(τ) = Σ_q F_0(z_q)² exp(-τ z_q²)`   (`criticalFeatureComplexAmplifiedTrace`),

with `H(σ) = criticalFeatureGaussianAmplifiedTrace 0 σ` for real `σ`.

**Theorem** (`riemannHypothesis_iff_criticalFeatureComplexAmplifiedTrace_bounded_on_vertical_line`).
For every `a > 0`, RH holds iff `b ↦ H(a + ib)` is bounded.  The HCF height family collapses to a
single height.

The proof is the vertical-line mechanism of `XiGaussianHeatVerticalLineReceiver` with the critical
feature as a coefficient.  The generic Phragmén–Lindelöf step is isolated in
`norm_le_max_of_vertical_of_sector_of_growth`; it applies to any holomorphic function on the right
half-plane with the heat-trace growth `exp(b²/σ)/σ`.  The weight `F_0(z)² = 4/(1 + z²)²` is nonzero,
depends only on `z²`, and is at most `1`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Generic Phragmén–Lindelöf transfer.**  Let `f` be holomorphic on `Re τ > 0` with heat-trace
growth `‖f τ‖ ≤ exp((Im τ)²/Re τ)(4/Re τ) K`.  If `f` is bounded by `S₀` on the sector
`|Im τ| ≤ Re τ`, `Re τ ≥ a`, and by `C` on the vertical line `Re τ = a`, then it is bounded by
`max C S₀` on the sector between the 45° ray from `a` and that line. -/
theorem norm_le_max_of_vertical_of_sector_of_growth {f : ℂ → ℂ} {a C S₀ K : ℝ} (ha : 0 < a)
    (hK : 0 ≤ K)
    (hdiff : ∀ τ : ℂ, 0 < τ.re → DifferentiableAt ℂ f τ)
    (hgrowth : ∀ τ : ℂ, 0 < τ.re → ‖f τ‖ ≤ Real.exp (τ.im ^ 2 / τ.re) * (4 / τ.re) * K)
    (hsector : ∀ τ : ℂ, a ≤ τ.re → |τ.im| ≤ τ.re → ‖f τ‖ ≤ S₀)
    (hC : ∀ b : ℝ, ‖f ((a : ℂ) + b * I)‖ ≤ C) {s : ℂ}
    (h1 : Real.pi / 4 ≤ s.im) (h2 : s.im ≤ Real.pi / 2) :
    ‖f ((a : ℂ) + Complex.exp s)‖ ≤ max C S₀ := by
  have hpi := Real.pi_pos
  have hre : ∀ s : ℂ, Real.pi / 4 ≤ s.im → s.im ≤ Real.pi / 2 →
      a ≤ ((a : ℂ) + Complex.exp s).re := by
    intro s h1 h2
    have hcos : 0 ≤ Real.cos s.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩
    simp only [add_re, ofReal_re, Complex.exp_re]
    have := mul_nonneg (Real.exp_pos s.re).le hcos
    linarith
  have hdiffAt : ∀ s : ℂ, Real.pi / 4 ≤ s.im → s.im ≤ Real.pi / 2 →
      DifferentiableAt ℂ (fun s => f ((a : ℂ) + Complex.exp s)) s := by
    intro s h1 h2
    exact (hdiff _ (ha.trans_le (hre s h1 h2))).comp s
      ((differentiableAt_const _).add differentiableAt_exp)
  have hd : DiffContOnCl ℂ (fun s => f ((a : ℂ) + Complex.exp s))
      (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine ⟨fun s hs => (hdiffAt s hs.1.le hs.2.le).differentiableWithinAt, ?_⟩
    have hcl : closure (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2)) ⊆
        Complex.im ⁻¹' Icc (Real.pi / 4) (Real.pi / 2) :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_im)
    exact fun s hs => (hdiffAt s (hcl hs).1 (hcl hs).2).continuousAt.continuousWithinAt
  have hgr : ∃ c < Real.pi / (Real.pi / 2 - Real.pi / 4), ∃ B,
      (fun s => f ((a : ℂ) + Complex.exp s)) =O[comap (abs ∘ Complex.re) atTop ⊓
        𝓟 (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2))]
        fun s => Real.exp (B * Real.exp (c * |s.re|)) := by
    have h4 : Real.pi / (Real.pi / 2 - Real.pi / 4) = 4 := by field_simp; ring
    refine ⟨2, by rw [h4]; norm_num, 1 / a, Asymptotics.IsBigO.of_bound (4 / a * K) ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun s hs => ?_)
    have hres := hre s hs.1.le hs.2.le
    have hτ : 0 < ((a : ℂ) + Complex.exp s).re := ha.trans_le hres
    refine (hgrowth _ hτ).trans ?_
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
    (f := fun s => f ((a : ℂ) + Complex.exp s)) (z := s) hd hgr ?_ ?_ h1 h2
  · intro z hz
    refine le_max_of_le_right (hsector _ (hre z hz.ge (by rw [hz]; linarith)) ?_)
    have hcs : Real.sin z.im = Real.cos z.im := by
      rw [hz, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hcos : 0 ≤ Real.cos z.im := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    simp only [add_im, add_re, ofReal_im, ofReal_re, Complex.exp_im, Complex.exp_re, zero_add]
    rw [hcs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hcos)]
    linarith
  · intro z hz
    refine le_max_of_le_left ?_
    have hexp : Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [Complex.exp_re, hz, Real.cos_pi_div_two]
      · rw [Complex.exp_im, hz, Real.sin_pi_div_two, mul_one, Complex.mul_I_im, Complex.ofReal_re]
    rw [hexp]
    exact hC _

/-! ## The HCF diagonal at height zero -/

/-- The critical-feature weight at height zero, written in the squared coordinate `w = z²`. -/
def criticalFeatureSquareWeight (w : ℂ) : ℂ := (2 / (1 + w)) ^ 2

theorem criticalFeatureCauchyKernelTest_zero_sq (q : XiZeroCopy) :
    criticalFeatureCauchyKernelTest 0 (xiSpectralPoint q) ^ 2 =
      criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) := by
  have hq := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  have hy : |(xiSpectralPoint q).im| < 1 / 2 := by
    rw [him, abs_neg]
    have h' : ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 2) ^ 2 := by norm_num; linarith
    have := sq_lt_sq.1 h'
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  rw [criticalFeatureCauchyKernelTest_eq_div hy, criticalFeatureSquareWeight]
  simp

theorem one_add_xiSpectralSq_re (q : XiZeroCopy) :
    75 < (1 + xiSpectralPoint q ^ (2 : ℕ)).re := by
  have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
  have h150 := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  rw [add_re, one_re]
  linarith

theorem norm_criticalFeatureSquareWeight_le_one (q : XiZeroCopy) :
    ‖criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ))‖ ≤ 1 := by
  have h75 := one_add_xiSpectralSq_re q
  have hnorm : 75 < ‖1 + xiSpectralPoint q ^ (2 : ℕ)‖ :=
    h75.trans_le ((le_abs_self _).trans (abs_re_le_norm _))
  rw [criticalFeatureSquareWeight, norm_pow, norm_div, Complex.norm_ofNat]
  have h : 2 / ‖1 + xiSpectralPoint q ^ (2 : ℕ)‖ ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ 2 / ‖1 + xiSpectralPoint q ^ (2 : ℕ)‖ := by positivity
  calc (2 / ‖1 + xiSpectralPoint q ^ (2 : ℕ)‖) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 1 := one_pow 2

theorem criticalFeatureSquareWeight_ne_zero (q : XiZeroCopy) :
    criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) ≠ 0 := by
  have h75 := one_add_xiSpectralSq_re q
  have hne : 1 + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := fun h => by rw [h] at h75; simp at h75; linarith
  rw [criticalFeatureSquareWeight]
  exact pow_ne_zero 2 (div_ne_zero two_ne_zero hne)

/-- The HCF diagonal at height zero with complex amplification. -/
def criticalFeatureComplexAmplifiedTrace (τ : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) *
    xiGaussianHeatTermC τ q

/-- At real amplification the complex trace is the corpus HCF diagonal at height zero. -/
theorem criticalFeatureComplexAmplifiedTrace_ofReal (σ : ℝ) :
    criticalFeatureComplexAmplifiedTrace (σ : ℂ) = criticalFeatureGaussianAmplifiedTrace 0 σ := by
  rw [criticalFeatureComplexAmplifiedTrace, criticalFeatureGaussianAmplifiedTrace]
  refine tsum_congr fun q => ?_
  rw [criticalFeatureGaussianAmplifiedTerm, criticalFeatureCauchyKernelTest_zero_sq,
    xiGaussianHeatTermC]
  simp

theorem norm_criticalFeatureComplexTerm_le (τ : ℂ) (q : XiZeroCopy) :
    ‖criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) * xiGaussianHeatTermC τ q‖ ≤
      ‖xiGaussianHeatTermC τ q‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_criticalFeatureSquareWeight_le_one q)

theorem summable_norm_criticalFeatureComplexTerm {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy =>
      ‖criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) * xiGaussianHeatTermC τ q‖) :=
  (summable_norm_xiGaussianHeatTermC hτ).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_criticalFeatureComplexTerm_le τ)

theorem norm_criticalFeatureComplexAmplifiedTrace_le_growth {τ : ℂ} (hτ : 0 < τ.re) :
    ‖criticalFeatureComplexAmplifiedTrace τ‖ ≤ Real.exp (τ.im ^ 2 / τ.re) * (4 / τ.re) *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (summable_norm_criticalFeatureComplexTerm hτ)).trans
    (Summable.tsum_le_tsum (fun q => (norm_criticalFeatureComplexTerm_le τ q).trans
      (norm_xiGaussianHeatTermC_le_growth hτ q)) (summable_norm_criticalFeatureComplexTerm hτ)
      (xiSpectralPoint_inv_sq_summable.mul_left _))

theorem norm_criticalFeatureComplexAmplifiedTrace_le_of_abs_im_le {a : ℝ} (ha : 0 < a) {τ : ℂ}
    (hre : a ≤ τ.re) (him : |τ.im| ≤ τ.re) :
    ‖criticalFeatureComplexAmplifiedTrace τ‖ ≤
      3 / a * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hτ : 0 < τ.re := ha.trans_le hre
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (summable_norm_criticalFeatureComplexTerm hτ)).trans
    (Summable.tsum_le_tsum (fun q => ?_) (summable_norm_criticalFeatureComplexTerm hτ)
      (xiSpectralPoint_inv_sq_summable.mul_left _))
  refine (norm_criticalFeatureComplexTerm_le τ q).trans
    ((norm_xiGaussianHeatTermC_le_of_abs_im_le hτ him q).trans ?_)
  have : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by positivity
  gcongr

theorem differentiableAt_criticalFeatureComplexAmplifiedTrace {τ₀ : ℂ} (h : 0 < τ₀.re) :
    DifferentiableAt ℂ criticalFeatureComplexAmplifiedTrace τ₀ := by
  set R : ℝ := |τ₀.im| + 1
  set U : Set ℂ := {τ | τ₀.re / 2 < τ.re} ∩ {τ | |τ.im| < R}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
  have hmem : τ₀ ∈ U := ⟨by simp only [mem_setOf_eq]; linarith, by
    simp only [mem_setOf_eq, R]; linarith⟩
  have hbound : ∀ (q : XiZeroCopy) (τ : ℂ), τ ∈ U →
      ‖criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) * xiGaussianHeatTermC τ q‖ ≤
        Real.exp (R ^ 2 / (τ₀.re / 2)) * (4 / (τ₀.re / 2)) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q τ hτU
    have hre : τ₀.re / 2 < τ.re := hτU.1
    have him : |τ.im| < R := hτU.2
    have hτ : 0 < τ.re := by linarith
    refine (norm_criticalFeatureComplexTerm_le τ q).trans
      ((norm_xiGaussianHeatTermC_le_growth hτ q).trans ?_)
    have hN : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by positivity
    have hsq : τ.im ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs τ.im]
      exact pow_le_pow_left₀ (abs_nonneg _) him.le 2
    have he : Real.exp (τ.im ^ 2 / τ.re) ≤ Real.exp (R ^ 2 / (τ₀.re / 2)) :=
      Real.exp_le_exp.2 (div_le_div₀ (by positivity) hsq (by linarith) hre.le)
    have h4 : 4 / τ.re ≤ 4 / (τ₀.re / 2) := div_le_div_of_nonneg_left (by norm_num) (by linarith)
      hre.le
    gcongr
  have hdiff : ∀ q : XiZeroCopy, DifferentiableOn ℂ
      (fun τ => criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) *
        xiGaussianHeatTermC τ q) U :=
    fun q => by
      unfold xiGaussianHeatTermC
      fun_prop
  have hD := Complex.differentiableOn_tsum_of_summable_norm
    (xiSpectralPoint_inv_sq_summable.mul_left _) hdiff hU hbound
  exact hD.differentiableAt (hU.mem_nhds hmem)

/-- **Single-height HCF receiver.**  For every `a > 0`, RH holds iff the HCF diagonal at height zero,
amplified by the complex Gaussian `exp(-(a + ib) z²)`, is bounded in `b ∈ ℝ`. -/
theorem riemannHypothesis_iff_criticalFeatureComplexAmplifiedTrace_bounded_on_vertical_line
    {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ b : ℝ, ‖criticalFeatureComplexAmplifiedTrace ((a : ℂ) + b * I)‖ ≤ C := by
  set K := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  have hK : 0 ≤ K := tsum_nonneg fun _ => by positivity
  constructor
  · intro hRH
    refine ⟨2 / a * K, fun b => ?_⟩
    have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
    rw [← tsum_mul_left]
    refine (norm_tsum_le_tsum_norm (summable_norm_criticalFeatureComplexTerm hτ)).trans
      (Summable.tsum_le_tsum (fun q => ?_) (summable_norm_criticalFeatureComplexTerm hτ)
        (xiSpectralPoint_inv_sq_summable.mul_left _))
    refine (norm_criticalFeatureComplexTerm_le _ q).trans ?_
    rw [norm_xiGaussianHeatTermC]
    have him0 : (xiSpectralPoint q ^ (2 : ℕ)).im = 0 := by
      rw [xiSpectralSq_eq_ofReal_re_of_rh hRH q, Complex.ofReal_im]
    have hNA := xiSpectralSq_norm_sq_lt_two_mul_re q
    have hN : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      have := xiSpectralPoint_ne_zero q
      positivity
    have hre' : ((a : ℂ) + b * I).re = a := by simp
    rw [him0, hre', mul_zero, sub_zero]
    set A := (xiSpectralPoint q ^ (2 : ℕ)).re
    have hA : 0 < a * A := mul_pos ha (by linarith)
    calc Real.exp (-(a * A)) ≤ 1 / (a * A) := exp_neg_le_inv_of_pos hA
      _ ≤ 2 / a * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hA (mul_pos ha hN)]
        nlinarith
  · rintro ⟨C, hC⟩
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_sq_im_pos_of_not_riemannHypothesis hRH
    set C' := max C (3 / a * K)
    set A₁ := (xiSpectralPoint q₁ ^ (2 : ℕ)).re
    set B₁ := (xiSpectralPoint q₁ ^ (2 : ℕ)).im
    have hpi := Real.pi_pos
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
    have hray : ∀ r : ℝ, 0 ≤ r →
        ‖criticalFeatureComplexAmplifiedTrace ((a : ℂ) + (r : ℂ) * e)‖ ≤ C' := by
      intro r hr
      rcases hr.eq_or_lt with h0 | hpos
      · rw [← h0, ofReal_zero, zero_mul, add_zero]
        exact le_max_of_le_right (norm_criticalFeatureComplexAmplifiedTrace_le_of_abs_im_le ha
          (by simp) (by simp [ha.le]))
      · have hs : (r : ℂ) * e = Complex.exp ((Real.log r : ℂ) + (φ : ℂ) * I) := by
          rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
        rw [hs]
        exact norm_le_max_of_vertical_of_sector_of_growth ha hK
          (fun τ hτ => differentiableAt_criticalFeatureComplexAmplifiedTrace hτ)
          (fun τ hτ => norm_criticalFeatureComplexAmplifiedTrace_le_growth hτ)
          (fun τ hre him => norm_criticalFeatureComplexAmplifiedTrace_le_of_abs_im_le ha hre him)
          hC (by simp; linarith) (by simp; linarith)
    have hterm : ∀ (q : XiZeroCopy) (r : ℝ),
        criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) *
            Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
            Complex.exp (-(r : ℂ) * (e * xiSpectralPoint q ^ (2 : ℕ))) =
          criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) *
            xiGaussianHeatTermC ((a : ℂ) + (r : ℂ) * e) q := fun q r => by
      rw [xiGaussianHeatTermC, mul_assoc, ← Complex.exp_add]
      congr 2
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
      (c := fun q : XiZeroCopy => criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) *
        Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)))
      (ε₀ := 0) le_rfl
      (fun i j hij => by
        have hne : e ≠ 0 := Complex.exp_ne_zero _
        have : xiSpectralPoint i ^ (2 : ℕ) = xiSpectralPoint j ^ (2 : ℕ) :=
          mul_left_cancel₀ hne hij
        simp only [this])
      (fun q _ => mul_ne_zero (criticalFeatureSquareWeight_ne_zero q) (Complex.exp_ne_zero _)) hfin
      (m := fun q => (2 / a) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
      (fun q => by positivity) (xiSpectralPoint_inv_sq_summable.mul_left _)
      (fun q hq ε hε => by
        rw [hterm]
        refine (norm_criticalFeatureComplexTerm_le _ q).trans ?_
        rw [norm_xiGaussianHeatTermC]
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
        exact summable_norm_criticalFeatureComplexTerm (hτre ε hε))
      ⟨q₁, by show (e * xiSpectralPoint q₁ ^ (2 : ℕ)).re < 0; rw [hw_re]; exact hφneg⟩ C'
    have hsum : ∑' q : XiZeroCopy, criticalFeatureSquareWeight (xiSpectralPoint q ^ (2 : ℕ)) *
        Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
          Complex.exp (-(r : ℂ) * (e * xiSpectralPoint q ^ (2 : ℕ))) =
          criticalFeatureComplexAmplifiedTrace ((a : ℂ) + (r : ℂ) * e) := by
      rw [criticalFeatureComplexAmplifiedTrace]
      exact tsum_congr fun q => hterm q r
    rw [hsum] at hr
    linarith [hray r hr0]

end

end RHTower
