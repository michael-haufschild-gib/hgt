import GaloisForLFunctions.RHTower.WeilMarkovFarOutNonnegativeOddPositivity

/-!
# Thin nonnegative half-line tests have positive odd Markov form at every position

Let `f ≥ 0` be a real `C²` test supported in an interval `[x₀, x₀ + w]` of the positive half-line.
In the odd-sector decomposition
`M(f − f̃) = 2[A(f) − P(f)] + 2 Σ_k f̃(−2k)² + 2 Π(f)`
the trivial-zero squares and the product-prime pairing are nonnegative, and the ratio pairing
`P(f)` vanishes as soon as `w < log 2`, since every lag `log n` with `n ≥ 2` moves the support
off itself. The archimedean form is the Lévy form
`A(f) = 2θ′(0) ‖f‖² + ∫_0^∞ ω(x) ∫ (f(u) − f(u + x))² du dx`,
and for `x > w` the two copies of `f` are disjoint, so the inner integral equals `2‖f‖²`. On
`(w, 1]` the Lévy density satisfies `ω(x) = e^{−x/2}/(1 − e^{−2x}) ≥ e^{−1/2}/(2x)`, which gives
the logarithmic gain `A(f) ≥ (2θ′(0) + e^{−1/2} log(1/w)) ‖f‖²`.

Hence there is an absolute width `w₀ > 0` (`thinWidth`) such that every nonnegative half-line test
of width at most `w₀` satisfies `M(f − f̃) ≥ 2‖f‖²`, at every position `x₀ > 0`. Unlike the
separated-bump positivity of the full Weil form, no restriction on the span `2x₀` is needed: the
interaction between the two bumps `f` and `−f̃` passes entirely through the product pairing and
the trivial-zero squares, which are nonnegative. Together with the far-out fat class, this shows
that a negative direction of the odd Markov form must be a sign-changing test, or a nonnegative
test of intermediate width that is not far out.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ} {x₀ w : ℝ}

/-! ## The ratio pairing vanishes below width `log 2` -/

theorem one_div_two_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- No lag `log n`, `n ≥ 2`, keeps a support of width `w < log 2` on itself. -/
theorem primeSum_eq_zero_of_width_lt (hsupp : ∀ x, x ∉ Icc x₀ (x₀ + w) → f x = 0)
    (hw : w < Real.log 2) : primeSum f = 0 := by
  unfold primeSum
  have hterm : ∀ n : ℕ, vonMangoldtAtom n *
      ((∫ t, f t * f (t - Real.log n)) + ∫ t, f t * f (t + Real.log n)) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · have hlog : w < Real.log n :=
        lt_of_lt_of_le hw (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
      have h1 : ∀ t, f t * f (t - Real.log n) = 0 := by
        intro t
        by_cases ht : t ∈ Icc x₀ (x₀ + w)
        · rw [hsupp (t - Real.log n) (by
            intro hm; rw [mem_Icc] at hm ht; linarith [hm.1, ht.2]), mul_zero]
        · rw [hsupp t ht, zero_mul]
      have h2 : ∀ t, f t * f (t + Real.log n) = 0 := by
        intro t
        by_cases ht : t ∈ Icc x₀ (x₀ + w)
        · rw [hsupp (t + Real.log n) (by
            intro hm; rw [mem_Icc] at hm ht; linarith [hm.2, ht.1]), mul_zero]
        · rw [hsupp t ht, zero_mul]
      simp only [h1, h2, integral_zero, add_zero, mul_zero]
    · unfold vonMangoldtAtom
      rw [if_neg hn, zero_mul]
  simp only [hterm, tsum_zero]

/-! ## The Lévy gain of a thin test -/

/-- Beyond the width, the two copies of the test are disjoint. -/
theorem integral_sq_sub_shift_eq (hf : Continuous f) (hfc : HasCompactSupport f)
    (hsupp : ∀ x, x ∉ Icc x₀ (x₀ + w) → f x = 0) {x : ℝ} (hx : w < x) :
    ∫ u, (f u - f (u + x)) ^ 2 = 2 * ∫ u, f u ^ 2 := by
  have h1 : Integrable fun t => f t ^ 2 := by
    have h0 : Integrable (fun t => f t * f t) :=
      (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
    simpa [pow_two] using h0
  have h2 : Integrable fun u => f (u + x) ^ 2 := h1.comp_add_right x
  have hpt : ∀ u, (f u - f (u + x)) ^ 2 = f u ^ 2 + f (u + x) ^ 2 := by
    intro u
    have h0 : f u * f (u + x) = 0 := by
      by_cases hu : u ∈ Icc x₀ (x₀ + w)
      · rw [hsupp (u + x) (by
          intro hm; rw [mem_Icc] at hm hu; linarith [hm.2, hu.1]), mul_zero]
      · rw [hsupp u hu, zero_mul]
    nlinarith [h0]
  simp_rw [hpt]
  rw [integral_add h1 h2, integral_add_right_eq_self (fun u => f u ^ 2) x]
  ring

/-- `ω(x) ≥ e^{−1/2}/(2x)` on `(0, 1]`. -/
theorem archLevyDensity_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Real.exp (-(1 / 2)) / (2 * x) ≤ archLevyDensity x := by
  unfold archLevyDensity
  have hnum : Real.exp (-(1 / 2)) ≤ Real.exp (-x / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hden_pos : 0 < 1 - Real.exp (-2 * x) := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hden : 1 - Real.exp (-2 * x) ≤ 2 * x := by
    have := Real.add_one_le_exp (-2 * x)
    linarith
  rw [div_le_div_iff₀ (by positivity) hden_pos]
  calc Real.exp (-(1 / 2)) * (1 - Real.exp (-2 * x))
      ≤ Real.exp (-x / 2) * (2 * x) := by gcongr
    _ = Real.exp (-x / 2) * (2 * x) := rfl

/-- **The Lévy gain.** A test of width `w ≤ 1` has Lévy energy at least
`e^{−1/2} log(1/w) ‖f‖²`. -/
theorem levyEnergy_ge_of_width (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ x, x ∉ Icc x₀ (x₀ + w) → f x = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    Real.exp (-(1 / 2)) * Real.log (1 / w) * ∫ u, f u ^ 2 ≤ levyEnergy f := by
  set N : ℝ := ∫ u, f u ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun u => sq_nonneg _
  set L : ℝ → ℝ := fun x => archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2 with hL
  have hLint : IntegrableOn L (Ioi 0) := integrableOn_levyIntegrand hf hfc
  have hsub : Ioc w 1 ⊆ Ioi 0 := fun x hx => lt_trans hw0 hx.1
  -- restrict the Lévy integral to `(w, 1]`
  have hstep1 : ∫ x in Ioc w 1, L x ≤ ∫ x in Ioi 0, L x :=
    setIntegral_mono_set hLint (levyIntegrand_nonneg f) (LE.le.eventuallyLE hsub)
  -- compare with the explicit lower bound on `(w, 1]`
  have hlow : ∀ x ∈ Ioc w 1, Real.exp (-(1 / 2)) * N * x⁻¹ ≤ L x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hw0 hx.1
    have hinner := integral_sq_sub_shift_eq hf.continuous hfc hsupp hx.1
    have hdens := archLevyDensity_ge hx0 hx.2
    simp only [hL]
    rw [hinner]
    calc Real.exp (-(1 / 2)) * N * x⁻¹ = Real.exp (-(1 / 2)) / (2 * x) * (2 * N) := by
          field_simp
      _ ≤ archLevyDensity x * (2 * N) := by gcongr
  have hcont : ContinuousOn (fun x : ℝ => Real.exp (-(1 / 2)) * N * x⁻¹) (Icc w 1) := by
    apply ContinuousOn.mul continuousOn_const
    exact continuousOn_inv₀.mono fun x hx => ne_of_gt (lt_of_lt_of_le hw0 hx.1)
  have hlint : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2)) * N * x⁻¹) (Ioc w 1) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hstep2 : ∫ x in Ioc w 1, Real.exp (-(1 / 2)) * N * x⁻¹ ≤ ∫ x in Ioc w 1, L x :=
    setIntegral_mono_on hlint (hLint.mono_set hsub) measurableSet_Ioc hlow
  -- evaluate the elementary integral
  have hval : ∫ x in Ioc w 1, Real.exp (-(1 / 2)) * N * x⁻¹ =
      Real.exp (-(1 / 2)) * Real.log (1 / w) * N := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hw1, integral_inv_of_pos hw0 one_pos]
    ring
  unfold levyEnergy
  rw [← hval]
  exact hstep2.trans hstep1

/-- The archimedean form of a thin test. -/
theorem archForm_ge_of_width (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ x, x ∉ Icc x₀ (x₀ + w) → f x = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    (2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) * Real.log (1 / w)) * ∫ u, f u ^ 2 ≤
      archForm f := by
  rw [archForm_eq_levyEnergy hf hfc]
  have := levyEnergy_ge_of_width hf hfc hsupp hw0 hw1
  linarith

/-! ## The thin positive cone -/

/-- The absolute width below which the Lévy gain beats the central archimedean constant. -/
def thinWidth : ℝ := Real.exp (-(Real.exp (1 / 2) * (2 + 2 * |gammaHardyPhaseRate 0|)))

theorem thinWidth_pos : 0 < thinWidth := Real.exp_pos _

theorem thinWidth_lt_log_two : thinWidth < Real.log 2 := by
  unfold thinWidth
  have h1 : Real.exp 1 ≤ Real.exp (1 / 2) * (2 + 2 * |gammaHardyPhaseRate 0|) := by
    have hsq : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    rw [hsq]
    have h2 : Real.exp (1 / 2) ≤ 2 + 2 * |gammaHardyPhaseRate 0| := by
      have := Real.exp_one_lt_d9
      nlinarith [abs_nonneg (gammaHardyPhaseRate 0), Real.exp_pos (1 / 2)]
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  calc Real.exp (-(Real.exp (1 / 2) * (2 + 2 * |gammaHardyPhaseRate 0|)))
      ≤ Real.exp (-Real.exp 1) := Real.exp_le_exp.mpr (by linarith)
    _ < 1 / 2 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
        have := Real.exp_one_gt_d9
        have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        have h4 : Real.exp (Real.exp 1) ≥ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
        nlinarith [Real.exp_pos 1]
    _ < Real.log 2 := one_div_two_lt_log_two

theorem thinWidth_le_one : thinWidth ≤ 1 := by
  unfold thinWidth
  rw [Real.exp_le_one_iff]
  have := Real.exp_pos (1 / 2)
  nlinarith [abs_nonneg (gammaHardyPhaseRate 0)]

/-- **Thin nonnegative half-line tests have odd Markov form at least `2‖f‖²`, at every position.**
For a real `C²` test `f ≥ 0` supported in `[x₀, x₀ + w]` with `x₀ > 0` and `w ≤ thinWidth`,
`M(f − f̃) ≥ 2 ∫ f²`. The mechanism is the archimedean Lévy gain `e^{−1/2} log(1/w)` alone: the
ratio pairing vanishes below width `log 2`, and the trivial-zero squares and the product pairing
are nonnegative for `f ≥ 0`. -/
theorem thin_nonneg_oddExt_markovEnergy_ge (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hx₀ : 0 < x₀) (hw0 : 0 < w) (hw : w ≤ thinWidth)
    (hsupp : ∀ x, x ∉ Icc x₀ (x₀ + w) → f x = 0) (hpos : ∀ x, 0 ≤ f x) :
    2 * ∫ u, f u ^ 2 ≤ markovEnergy (fun x => ((f x - f (-x) : ℝ) : ℂ)) := by
  have hsupp' : ∀ x, x < x₀ → f x = 0 := fun x hx =>
    hsupp x (by rw [mem_Icc]; intro hm; linarith [hm.1])
  rw [markovEnergy_oddExtension_eq hf hfc hx₀ hsupp',
    markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc,
    primeSum_eq_zero_of_width_lt hsupp (lt_of_le_of_lt hw thinWidth_lt_log_two), sub_zero]
  have hsq : 0 ≤ ∑' k : ℕ, trivialZeroMoment f k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  have hprod : 0 ≤ productPrimePairing f := productPrimePairing_nonneg hpos
  have hN0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hA := archForm_ge_of_width hf hfc hsupp hw0 (hw.trans thinWidth_le_one)
  -- the Lévy gain beats the central constant
  have hlog : Real.exp (1 / 2) * (2 + 2 * |gammaHardyPhaseRate 0|) ≤ Real.log (1 / w) := by
    have h1 : Real.log (1 / thinWidth) = Real.exp (1 / 2) * (2 + 2 * |gammaHardyPhaseRate 0|) := by
      rw [one_div, Real.log_inv]
      unfold thinWidth
      rw [Real.log_exp]; ring
    rw [← h1]
    exact Real.log_le_log (one_div_pos.mpr thinWidth_pos) (one_div_le_one_div_of_le hw0 hw)
  have hcoef : 1 ≤ 2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) * Real.log (1 / w) := by
    have h2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : Real.exp (-(1 / 2)) * (Real.exp (1 / 2) * (2 + 2 * |gammaHardyPhaseRate 0|)) ≤
        Real.exp (-(1 / 2)) * Real.log (1 / w) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    rw [← mul_assoc, h2, one_mul] at h3
    linarith [neg_abs_le (gammaHardyPhaseRate 0)]
  have hA' : (∫ u, f u ^ 2) ≤ archForm f := by
    calc (∫ u, f u ^ 2) = 1 * ∫ u, f u ^ 2 := (one_mul _).symm
      _ ≤ (2 * gammaHardyPhaseRate 0 + Real.exp (-(1 / 2)) * Real.log (1 / w)) * ∫ u, f u ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hN0
      _ ≤ archForm f := hA
  linarith

/-- A thin nonnegative half-line test that is not identically zero has strictly positive odd
Markov form. -/
theorem thin_nonneg_oddExt_markovEnergy_pos (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hx₀ : 0 < x₀) (hw0 : 0 < w) (hw : w ≤ thinWidth)
    (hsupp : ∀ x, x ∉ Icc x₀ (x₀ + w) → f x = 0) (hpos : ∀ x, 0 ≤ f x)
    (hne : 0 < ∫ u, f u ^ 2) :
    0 < markovEnergy (fun x => ((f x - f (-x) : ℝ) : ℂ)) := by
  have := thin_nonneg_oddExt_markovEnergy_ge hf hfc hx₀ hw0 hw hsupp hpos
  linarith

end

end RHTower
