import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule
import GaloisForLFunctions.RHTower.XiThetaExplicitBounds

/-!
# The critical spectral budget and the unconditional off-line height floor

The difference of the centered relative-resolvent trace at the probe pair
`±(-ci)` — the centered images of `s = 1/2 ± c` — carries a positive spectral
mass per divisor copy,

`P_c(q) = (c−v)/(u²+(c−v)²) + (c+v)/(u²+(c+v)²)`,   `u + iv = pt_q`,

whose total over the complete multiplicity-exact divisor is exactly
`2·Re logDeriv ξ(1/2+c)`.  For `c ≥ 1/2` the strip constraint `|v| < 1/2`
makes every mass positive with the explicit floor `2c/(u² + (c+1/2)²)`, and
the Klein four-group of divisor symmetries embeds four copies of every
strict-right Schwarz pair into that budget.

The sharpest instance is the strip edge `c = 1/2`, where the budget collapses
to a single special value: `ξ(1) = 1/2` gives `logDeriv ξ(1) = Λ₀(1)`, and the
theta representation of `Λ₀` at the critical exponent bounds it by `1/(11π)`
through two exponential integrals — the outer one directly, the inner one by
the inversion `t ↦ t⁻¹`, which carries the reflected kernel back to `(1,∞)`.
The resulting budget `2Λ₀(1) ≤ 3/50` forces every off-critical zero of `ξ`
above height `8`.
-/

open Complex MeasureTheory HurwitzZeta

namespace RHTower

noncomputable section

/-! ## §1 The real probe family -/

/-- The budget probe at real abscissa `c`: the centered image of `s = 1/2 + c`. -/
def xiBudgetProbeAt (c : ℝ) : ℂ := -(c : ℂ) * Complex.I

@[simp] theorem xiBudgetProbeAt_re (c : ℝ) : (xiBudgetProbeAt c).re = 0 := by
  simp [xiBudgetProbeAt]

@[simp] theorem xiBudgetProbeAt_im (c : ℝ) : (xiBudgetProbeAt c).im = -c := by
  simp [xiBudgetProbeAt]

theorem half_add_probeAt_mul_I (c : ℝ) :
    (1 / 2 : ℂ) + xiBudgetProbeAt c * Complex.I = (1 / 2 : ℂ) + (c : ℂ) := by
  rw [xiBudgetProbeAt,
    show ((-(c : ℂ) * Complex.I) * Complex.I) =
      -(c : ℂ) * (Complex.I * Complex.I) from by ring, Complex.I_mul_I]
  ring

theorem XiC_probeAt (c : ℝ) :
    XiC (xiBudgetProbeAt c) = xi ((1 / 2 : ℂ) + (c : ℂ)) := by
  show xi ((1 / 2 : ℂ) + xiBudgetProbeAt c * Complex.I) = _
  rw [half_add_probeAt_mul_I]

/-- Every budget probe at or beyond the strip edge is a regular Xi point. -/
theorem XiC_probeAt_ne_zero_of_half_le {c : ℝ} (hc : 1 / 2 ≤ c) :
    XiC (xiBudgetProbeAt c) ≠ 0 := by
  rw [XiC_probeAt]
  apply xi_ne_zero_of_one_le_re
  norm_num [Complex.div_re]
  linarith

theorem logDeriv_XiC_probeAt (c : ℝ) :
    logDeriv XiC (xiBudgetProbeAt c) =
      logDeriv xi ((1 / 2 : ℂ) + (c : ℂ)) * Complex.I := by
  have hdf : DifferentiableAt ℂ xi
      ((1 / 2 : ℂ) + xiBudgetProbeAt c * Complex.I) := xi_differentiable _
  have hdg : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I)
      (xiBudgetProbeAt c) := by fun_prop
  have hcomp := logDeriv_comp (f := xi)
    (g := fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I)
    (x := xiBudgetProbeAt c) hdf hdg
  have hXiC : XiC = xi ∘ (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I) := by
    funext w
    rfl
  have hd : deriv (fun z : ℂ => (1 / 2 : ℂ) + z * Complex.I)
      (xiBudgetProbeAt c) = Complex.I := by
    simp
  rw [hXiC, hcomp, hd]
  show logDeriv xi ((1 / 2 : ℂ) + xiBudgetProbeAt c * Complex.I) * Complex.I =
    logDeriv xi ((1 / 2 : ℂ) + (c : ℂ)) * Complex.I
  rw [half_add_probeAt_mul_I]

/-- **The difference-trace sum rule at abscissa `c`.**  The per-copy
regularization cancels between the probes `±(-ci)`, leaving an absolutely
convergent resolvent difference. -/
theorem two_logDeriv_XiC_probeAt_eq_tsum {c : ℝ}
    (hne : XiC (xiBudgetProbeAt c) ≠ 0) :
    2 * logDeriv XiC (xiBudgetProbeAt c) =
      ∑' q : XiZeroCopy,
        ((xiSpectralPoint q + xiBudgetProbeAt c)⁻¹ -
          (xiSpectralPoint q - xiBudgetProbeAt c)⁻¹) := by
  have hne' : XiC (-(xiBudgetProbeAt c)) ≠ 0 := by
    rw [XiC_even]
    exact hne
  have h1 := logDeriv_XiC_eq_relativeResolventTrace hne
  have h2 := logDeriv_XiC_eq_relativeResolventTrace hne'
  have hodd := logDeriv_XiC_neg (xiBudgetProbeAt c)
  have hs1 := summable_xiRelativeResolventTerm hne
  have hs2 := summable_xiRelativeResolventTerm hne'
  have key : xiRelativeResolventTrace (xiBudgetProbeAt c) -
      xiRelativeResolventTrace (-(xiBudgetProbeAt c)) =
      2 * logDeriv XiC (xiBudgetProbeAt c) := by
    rw [← h1, ← h2, hodd]
    ring
  rw [← key, xiRelativeResolventTrace, xiRelativeResolventTrace,
    ← hs1.tsum_sub hs2]
  apply tsum_congr
  intro q
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm, sub_neg_eq_add]
  ring

/-! ## §2 The positive spectral mass -/

/-- The per-copy spectral mass at abscissa `c`. -/
def xiBudgetMassAt (c : ℝ) (q : XiZeroCopy) : ℝ :=
  (c - (xiSpectralPoint q).im) /
      ((xiSpectralPoint q).re ^ 2 + (c - (xiSpectralPoint q).im) ^ 2) +
    (c + (xiSpectralPoint q).im) /
      ((xiSpectralPoint q).re ^ 2 + (c + (xiSpectralPoint q).im) ^ 2)

theorem im_budget_summand_at (c : ℝ) (q : XiZeroCopy) :
    ((xiSpectralPoint q + xiBudgetProbeAt c)⁻¹ -
      (xiSpectralPoint q - xiBudgetProbeAt c)⁻¹).im = xiBudgetMassAt c q := by
  have hAre : (xiSpectralPoint q + xiBudgetProbeAt c).re =
      (xiSpectralPoint q).re := by
    rw [Complex.add_re, xiBudgetProbeAt_re, add_zero]
  have hAim : (xiSpectralPoint q + xiBudgetProbeAt c).im =
      (xiSpectralPoint q).im - c := by
    rw [Complex.add_im, xiBudgetProbeAt_im]
    ring
  have hBre : (xiSpectralPoint q - xiBudgetProbeAt c).re =
      (xiSpectralPoint q).re := by
    rw [Complex.sub_re, xiBudgetProbeAt_re, sub_zero]
  have hBim : (xiSpectralPoint q - xiBudgetProbeAt c).im =
      (xiSpectralPoint q).im + c := by
    rw [Complex.sub_im, xiBudgetProbeAt_im]
    ring
  rw [Complex.sub_im, Complex.inv_im, Complex.inv_im,
    Complex.normSq_apply, Complex.normSq_apply, hAre, hAim, hBre, hBim,
    xiBudgetMassAt]
  ring_nf

/-- **Per-copy mass floor** at abscissa `c ≥ 1/2`: the strip constraint makes
both partial fractions positive with a common denominator bound. -/
theorem xiBudgetMassAt_ge {c : ℝ} (hc : 1 / 2 ≤ c) (q : XiZeroCopy) :
    2 * c / ((xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2) ≤
      xiBudgetMassAt c q := by
  obtain ⟨hv1, hv2⟩ := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
  set u := (xiSpectralPoint q).re
  set v := (xiSpectralPoint q).im
  have h1 : 0 < c - v := by linarith
  have h2 : 0 < c + v := by linarith
  have hd1 : (0 : ℝ) < u ^ 2 + (c - v) ^ 2 := by positivity
  have hd2 : (0 : ℝ) < u ^ 2 + (c + v) ^ 2 := by positivity
  have hD : (0 : ℝ) < u ^ 2 + (c + 1 / 2) ^ 2 := by positivity
  have hle1 : u ^ 2 + (c - v) ^ 2 ≤ u ^ 2 + (c + 1 / 2) ^ 2 := by nlinarith
  have hle2 : u ^ 2 + (c + v) ^ 2 ≤ u ^ 2 + (c + 1 / 2) ^ 2 := by nlinarith
  have t1 : (c - v) / (u ^ 2 + (c + 1 / 2) ^ 2) ≤
      (c - v) / (u ^ 2 + (c - v) ^ 2) :=
    div_le_div_of_nonneg_left h1.le hd1 hle1
  have t2 : (c + v) / (u ^ 2 + (c + 1 / 2) ^ 2) ≤
      (c + v) / (u ^ 2 + (c + v) ^ 2) :=
    div_le_div_of_nonneg_left h2.le hd2 hle2
  have hsum : 2 * c / (u ^ 2 + (c + 1 / 2) ^ 2) =
      (c - v) / (u ^ 2 + (c + 1 / 2) ^ 2) +
        (c + v) / (u ^ 2 + (c + 1 / 2) ^ 2) := by
    field_simp
    ring
  rw [xiBudgetMassAt, hsum]
  exact add_le_add t1 t2

theorem xiBudgetMassAt_nonneg {c : ℝ} (hc : 1 / 2 ≤ c) (q : XiZeroCopy) :
    0 ≤ xiBudgetMassAt c q := by
  refine le_trans ?_ (xiBudgetMassAt_ge hc q)
  have : (0 : ℝ) < (xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2 := by
    positivity
  positivity

theorem massAt_lineConj (c : ℝ) (q : XiZeroCopy) :
    xiBudgetMassAt c (xiZeroCopyLineConjEquiv q) = xiBudgetMassAt c q := by
  rw [xiBudgetMassAt, xiBudgetMassAt, xiSpectralPoint_lineConj]
  simp only [Complex.conj_re, Complex.conj_im]
  ring_nf

theorem massAt_reflect (c : ℝ) (q : XiZeroCopy) :
    xiBudgetMassAt c (xiZeroCopyReflectEquiv q) = xiBudgetMassAt c q := by
  rw [xiBudgetMassAt, xiBudgetMassAt, xiSpectralPoint_reflect]
  simp only [Complex.neg_re, Complex.neg_im]
  ring_nf

theorem massAt_copyConj (c : ℝ) (q : XiZeroCopy) :
    xiBudgetMassAt c (xiZeroCopyConjEquiv q) = xiBudgetMassAt c q := by
  rw [xiBudgetMassAt, xiBudgetMassAt, xiSpectralPoint_copyConj]
  simp only [Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im]
  ring_nf

theorem massAt_quadrupleEmbed (c : ℝ)
    (p : (Bool × Bool) × XiRightUpperZeroCopy) :
    xiBudgetMassAt c (xiWardQuadrupleEmbed p) = xiBudgetMassAt c p.2.1.1 := by
  obtain ⟨⟨b, r⟩, q⟩ := p
  cases b <;> cases r <;>
    simp only [xiWardQuadrupleEmbed, xiWardQuadPart, massAt_lineConj,
      massAt_reflect, massAt_copyConj]

theorem summable_budget_summand_at {c : ℝ}
    (hne : XiC (xiBudgetProbeAt c) ≠ 0) :
    Summable (fun q : XiZeroCopy =>
      (xiSpectralPoint q + xiBudgetProbeAt c)⁻¹ -
        (xiSpectralPoint q - xiBudgetProbeAt c)⁻¹) := by
  have hne' : XiC (-(xiBudgetProbeAt c)) ≠ 0 := by
    rw [XiC_even]
    exact hne
  have hs1 := summable_xiRelativeResolventTerm hne
  have hs2 := summable_xiRelativeResolventTerm hne'
  apply (hs1.sub hs2).congr
  intro q
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm, sub_neg_eq_add]
  ring

theorem summable_xiBudgetMassAt {c : ℝ} (hne : XiC (xiBudgetProbeAt c) ≠ 0) :
    Summable (xiBudgetMassAt c) :=
  ((Complex.hasSum_im (summable_budget_summand_at hne).hasSum).summable).congr
    fun q => im_budget_summand_at c q

/-- **The spectral-budget sum rule.**  The complete multiplicity-exact
divisor carries total mass exactly `2·Re logDeriv ξ(1/2+c)`. -/
theorem tsum_xiBudgetMassAt_eq {c : ℝ} (hne : XiC (xiBudgetProbeAt c) ≠ 0) :
    ∑' q : XiZeroCopy, xiBudgetMassAt c q =
      2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re := by
  have him := Complex.im_tsum (summable_budget_summand_at hne)
  have hsum := two_logDeriv_XiC_probeAt_eq_tsum hne
  calc ∑' q : XiZeroCopy, xiBudgetMassAt c q
      = ∑' q : XiZeroCopy,
          ((xiSpectralPoint q + xiBudgetProbeAt c)⁻¹ -
            (xiSpectralPoint q - xiBudgetProbeAt c)⁻¹).im :=
        (tsum_congr fun q => (im_budget_summand_at c q).symm)
    _ = (∑' q : XiZeroCopy,
          ((xiSpectralPoint q + xiBudgetProbeAt c)⁻¹ -
            (xiSpectralPoint q - xiBudgetProbeAt c)⁻¹)).im := him.symm
    _ = (2 * logDeriv XiC (xiBudgetProbeAt c)).im := by rw [hsum]
    _ = 2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re := by
        rw [logDeriv_XiC_probeAt]
        simp [Complex.mul_im]

/-! ## §3 Quadruple counting and the height floor -/

theorem summable_pair_baseAt {c : ℝ} (hne : XiC (xiBudgetProbeAt c) ≠ 0) :
    Summable (fun q : XiRightUpperZeroCopy => xiBudgetMassAt c q.1.1) := by
  have hinj : Function.Injective
      (fun q : XiRightUpperZeroCopy => (q.1.1 : XiZeroCopy)) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  exact (summable_xiBudgetMassAt hne).comp_injective hinj

/-- **Quadruple counting**: four disjoint divisor copies per strict-right
pair inject into the global budget. -/
theorem tsum_pairs_four_mul_massAt_le {c : ℝ} (hc : 1 / 2 ≤ c)
    (hne : XiC (xiBudgetProbeAt c) ≠ 0) :
    ∑' q : XiRightUpperZeroCopy, 4 * xiBudgetMassAt c q.1.1 ≤
      ∑' d : XiZeroCopy, xiBudgetMassAt c d := by
  have hbase := summable_pair_baseAt hne
  have hslice : ∀ i : Bool × Bool,
      (fun q : XiRightUpperZeroCopy =>
        xiBudgetMassAt c (xiWardQuadrupleEmbed (i, q))) =
      fun q : XiRightUpperZeroCopy => xiBudgetMassAt c q.1.1 :=
    fun i => funext fun q => massAt_quadrupleEmbed c (i, q)
  have hFsummable : Summable (fun p : (Bool × Bool) × XiRightUpperZeroCopy =>
      xiBudgetMassAt c (xiWardQuadrupleEmbed p)) := by
    refine (summable_prod_of_nonneg ?_).mpr ⟨?_, ?_⟩
    · intro p
      exact xiBudgetMassAt_nonneg hc _
    · intro i
      rw [hslice i]
      exact hbase
    · apply Summable.of_finite
  have htsumF : ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
      xiBudgetMassAt c (xiWardQuadrupleEmbed p) =
      4 * ∑' q : XiRightUpperZeroCopy, xiBudgetMassAt c q.1.1 := by
    rw [hFsummable.tsum_prod' (fun i => by rw [hslice i]; exact hbase)]
    have hinner : ∀ i : Bool × Bool,
        ∑' q : XiRightUpperZeroCopy,
          xiBudgetMassAt c (xiWardQuadrupleEmbed (i, q)) =
        ∑' q : XiRightUpperZeroCopy, xiBudgetMassAt c q.1.1 :=
      fun i => by rw [hslice i]
    rw [tsum_fintype, Finset.sum_congr rfl (fun i _ => hinner i),
      Finset.sum_const, nsmul_eq_mul]
    norm_num
  have hcomp : ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
      xiBudgetMassAt c (xiWardQuadrupleEmbed p) ≤
      ∑' d : XiZeroCopy, xiBudgetMassAt c d :=
    Summable.tsum_le_tsum_of_inj xiWardQuadrupleEmbed
      xiWardQuadrupleEmbed_injective
      (fun d _ => xiBudgetMassAt_nonneg hc d)
      (fun p => le_rfl)
      hFsummable (summable_xiBudgetMassAt hne)
  calc ∑' q : XiRightUpperZeroCopy, 4 * xiBudgetMassAt c q.1.1
      = 4 * ∑' q : XiRightUpperZeroCopy, xiBudgetMassAt c q.1.1 :=
        tsum_mul_left
    _ = ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
          xiBudgetMassAt c (xiWardQuadrupleEmbed p) := htsumF.symm
    _ ≤ ∑' d : XiZeroCopy, xiBudgetMassAt c d := hcomp

/-- **The height floor from a certified budget.**  If the total spectral mass
at abscissa `c` is at most `B`, every strict-right Schwarz pair has squared
height at least `8c/B − (c+1/2)²`. -/
theorem height_sq_ge_of_budget_le {c B : ℝ} (hc : 1 / 2 ≤ c) (hB : 0 < B)
    (hne : XiC (xiBudgetProbeAt c) ≠ 0)
    (hbud : ∑' d : XiZeroCopy, xiBudgetMassAt c d ≤ B)
    (q : XiRightUpperZeroCopy) :
    8 * c / B - (c + 1 / 2) ^ 2 ≤ ((xiRightCenteredZero q.1).im) ^ 2 := by
  have hbase := summable_pair_baseAt hne
  have hsummand : Summable (fun q : XiRightUpperZeroCopy =>
      4 * xiBudgetMassAt c q.1.1) := hbase.mul_left 4
  have h1 : 4 * xiBudgetMassAt c q.1.1 ≤
      ∑' q' : XiRightUpperZeroCopy, 4 * xiBudgetMassAt c q'.1.1 :=
    hsummand.le_tsum q fun j _ => by
      have := xiBudgetMassAt_nonneg hc j.1.1
      linarith
  have h2 := tsum_pairs_four_mul_massAt_le hc hne
  have h4 := xiBudgetMassAt_ge hc q.1.1
  rw [xiRightCenteredZero_im_eq_spectral_re]
  set u := (xiSpectralPoint q.1.1).re
  have hden : (0 : ℝ) < u ^ 2 + (c + 1 / 2) ^ 2 := by positivity
  have hcpos : (0 : ℝ) < c := by linarith
  have hchain : 8 * c / (u ^ 2 + (c + 1 / 2) ^ 2) ≤ B := by
    have hstep : 4 * (2 * c / (u ^ 2 + (c + 1 / 2) ^ 2)) ≤
        4 * xiBudgetMassAt c q.1.1 := by linarith
    calc 8 * c / (u ^ 2 + (c + 1 / 2) ^ 2)
        = 4 * (2 * c / (u ^ 2 + (c + 1 / 2) ^ 2)) := by ring
      _ ≤ 4 * xiBudgetMassAt c q.1.1 := hstep
      _ ≤ ∑' q' : XiRightUpperZeroCopy,
            4 * xiBudgetMassAt c q'.1.1 := h1
      _ ≤ ∑' d : XiZeroCopy, xiBudgetMassAt c d := h2
      _ ≤ B := hbud
  rw [div_le_iff₀ hden] at hchain
  rw [sub_le_iff_le_add, div_le_iff₀ hB]
  nlinarith [hchain]

/-! ## §4 The critical source constant `Λ₀(1)` -/

theorem twenty_le_exp_three : (20.08 : ℝ) ≤ Real.exp 3 := by
  have he := Real.exp_one_gt_d9
  have hpow : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt : (2.7182818283 : ℝ) ^ (3 : ℕ) < Real.exp 1 ^ (3 : ℕ) :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  rw [hpow]
  nlinarith [hlt]

theorem exp_point_one_four_ge : (1.1498 : ℝ) ≤ Real.exp 0.14 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.14) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- `e^{−π} ≤ 1/23`. -/
theorem exp_neg_pi_le : Real.exp (-Real.pi) ≤ 1 / 23 := by
  have hsplit : Real.exp (3.14 : ℝ) = Real.exp 3 * Real.exp 0.14 := by
    rw [← Real.exp_add]
    norm_num
  have hprod : (20.08 : ℝ) * 1.1498 ≤ Real.exp 3 * Real.exp 0.14 :=
    mul_le_mul twenty_le_exp_three exp_point_one_four_ge (by norm_num)
      (Real.exp_pos 3).le
  have h314 : (23 : ℝ) ≤ Real.exp (3.14 : ℝ) := by
    rw [hsplit]
    nlinarith [hprod]
  have h23 : (23 : ℝ) ≤ Real.exp Real.pi :=
    le_trans h314 (Real.exp_le_exp.mpr (le_of_lt Real.pi_gt_d2))
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h23

theorem exp_neg_pi_mul_le {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-Real.pi * t) ≤ 1 / 23 := by
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_pi_le
  nlinarith [Real.pi_pos]

/-- Sharpened theta decay: `evenKernel 0 t − 1 ≤ (23/11)e^{−πt}` for `t ≥ 1`. -/
theorem evenKernel_zero_sub_one_le_tight {t : ℝ} (ht : 1 ≤ t) :
    evenKernel 0 t - 1 ≤ 23 / 11 * Real.exp (-Real.pi * t) := by
  have h := evenKernel_zero_sub_one_le_of_le ht (exp_neg_pi_mul_le ht)
    (by norm_num)
  calc evenKernel 0 t - 1
      ≤ 2 * Real.exp (-Real.pi * t) / (1 - 1 / 23) := h
    _ = 23 / 11 * Real.exp (-Real.pi * t) := by ring

/-- The outer exponential mass: `∫_1^∞ e^{−πt} dt = e^{−π}/π`. -/
theorem integral_Ioi_one_exp_neg_pi :
    ∫ t in Set.Ioi (1 : ℝ), Real.exp (-Real.pi * t) =
      Real.exp (-Real.pi) / Real.pi := by
  have hπ := Real.pi_pos
  have hderiv : ∀ t ∈ Set.Ioi (1 : ℝ), HasDerivAt
      (fun u : ℝ => -(Real.exp (-Real.pi * u)) / Real.pi)
      (Real.exp (-Real.pi * t)) t := by
    intro t _
    have h0 : HasDerivAt (fun u : ℝ => -Real.pi * u) (-Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (-Real.pi)
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-Real.pi * u))
        (Real.exp (-Real.pi * t) * (-Real.pi)) t :=
      (Real.hasDerivAt_exp (-Real.pi * t)).comp t h0
    have h2 := (h1.neg).div_const Real.pi
    have h2' : HasDerivAt
        (fun u : ℝ => -(Real.exp (-Real.pi * u)) / Real.pi)
        (-(Real.exp (-Real.pi * t) * (-Real.pi)) / Real.pi) t :=
      h2.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    exact h2'.congr_deriv (by field_simp)
  have hcont : ContinuousWithinAt
      (fun u : ℝ => -(Real.exp (-Real.pi * u)) / Real.pi) (Set.Ici 1) 1 := by
    apply Continuous.continuousWithinAt
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).neg).div_const Real.pi
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-Real.pi * t)) (Set.Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 hπ
  have hscale : Filter.Tendsto (fun u : ℝ => Real.pi * u)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hπ Filter.tendsto_id
  have hexp : Filter.Tendsto (fun u : ℝ => Real.exp (-Real.pi * u))
      Filter.atTop (nhds 0) := by
    have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n := 0)
    have hcomp := hbase.comp hscale
    apply hcomp.congr
    intro u
    simp only [Function.comp_apply, pow_zero, one_mul]
    congr 1
    ring
  have hlim : Filter.Tendsto
      (fun u : ℝ => -(Real.exp (-Real.pi * u)) / Real.pi)
      Filter.atTop (nhds 0) := by
    have h := (hexp.neg).div_const Real.pi
    rwa [neg_zero, zero_div] at h
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcont hderiv hint hlim
  rw [hFTC, mul_one]
  ring

/-- The reflected integrand is bounded by its value at the reflection point. -/
theorem inv_mul_exp_neg_pi_div_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t⁻¹ * Real.exp (-Real.pi / t) ≤ Real.exp (-Real.pi) := by
  have hx : 1 ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    linarith
  have hkey : 1 / t ≤ Real.exp (Real.pi * (1 / t - 1)) := by
    have h1 := Real.add_one_le_exp (Real.pi * (1 / t - 1))
    have hπ := Real.pi_gt_three
    nlinarith [hx]
  have hcomb : (1 / t) * Real.exp (-Real.pi / t) ≤
      Real.exp (Real.pi * (1 / t - 1)) * Real.exp (-Real.pi / t) :=
    mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
  have hprod : Real.exp (Real.pi * (1 / t - 1)) *
      Real.exp (-Real.pi / t) = Real.exp (-Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [inv_eq_one_div]
  linarith [hcomb, hprod ▸ hcomb]

theorem integrableOn_inv_mul_exp_neg_pi_div :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t⁻¹ * Real.exp (-Real.pi / t)) (Set.Ioo (0 : ℝ) 1) := by
  apply MeasureTheory.Measure.integrableOn_of_bounded
    (M := Real.exp (-Real.pi))
  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    have h0 : (0 : ℝ) < t := ht.1
    have h1 : t ≤ 1 := le_of_lt ht.2
    have hnn : 0 ≤ t⁻¹ * Real.exp (-Real.pi / t) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact inv_mul_exp_neg_pi_div_le h0 h1

/-- **The reflected exponential mass.**  The inversion `t ↦ t⁻¹` carries the
inner integral to `∫_1^∞ e^{−πx}/x dx`, which the outer mass dominates. -/
theorem integral_Ioo_inv_mul_exp_neg_pi_div_le :
    ∫ t in Set.Ioo (0 : ℝ) 1, t⁻¹ * Real.exp (-Real.pi / t) ≤
      Real.exp (-Real.pi) / Real.pi := by
  have himg : (fun x : ℝ => x⁻¹) '' Set.Ioi (1 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hx⟩
    · rintro ⟨hy0, hy1⟩
      exact ⟨y⁻¹, (one_lt_inv₀ hy0).mpr hy1, inv_inv y⟩
  have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ),
      HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(x ^ 2)⁻¹) (Set.Ioi 1) x := by
    intro x hx
    exact (hasDerivAt_inv (by linarith [Set.mem_Ioi.mp hx] :
      x ≠ 0)).hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ => x⁻¹) (Set.Ioi 1) := by
    intro a _ b _ hab
    dsimp only at hab
    have h2 : (a⁻¹)⁻¹ = (b⁻¹)⁻¹ := by rw [hab]
    rwa [inv_inv, inv_inv] at h2
  have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj
    (fun t : ℝ => t⁻¹ * Real.exp (-Real.pi / t))
  rw [himg] at hsub
  rw [hsub]
  have hcongr : ∀ x ∈ Set.Ioi (1 : ℝ),
      |(-(x ^ 2)⁻¹)| • ((x⁻¹)⁻¹ * Real.exp (-Real.pi / x⁻¹)) =
        x⁻¹ * Real.exp (-Real.pi * x) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹),
      smul_eq_mul, inv_inv]
    have harg : -Real.pi / x⁻¹ = -Real.pi * x := by
      field_simp
    rw [harg]
    field_simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
  have hmono : ∫ x in Set.Ioi (1 : ℝ), x⁻¹ * Real.exp (-Real.pi * x) ≤
      ∫ x in Set.Ioi (1 : ℝ), Real.exp (-Real.pi * x) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro x hx
      have hx0 : (0 : ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
      positivity
    · exact exp_neg_integrableOn_Ioi 1 Real.pi_pos
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro x hx
      have hx1 : (1 : ℝ) < x := hx
      have hinv : x⁻¹ ≤ 1 := le_of_lt (inv_lt_one_of_one_lt₀ hx1)
      have hexp : (0 : ℝ) < Real.exp (-Real.pi * x) := Real.exp_pos _
      nlinarith [hexp, hinv]
  rw [integral_Ioi_one_exp_neg_pi] at hmono
  exact hmono

/-! ### The two Mellin pieces at the critical exponent -/

theorem outer_piece_half_le :
    ∫ t in Set.Ioi (1 : ℝ),
      t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      23 / 11 * (Real.exp (-Real.pi) / Real.pi) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => 23 / 11 * Real.exp (-Real.pi * t)) (Set.Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul _
  have hmono : ∫ t in Set.Ioi (1 : ℝ),
      t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      ∫ t in Set.Ioi (1 : ℝ), 23 / 11 * Real.exp (-Real.pi * t) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro t ht
      have ht0 : (0 : ℝ) < t := by linarith [Set.mem_Ioi.mp ht]
      positivity
    · exact hmaj
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro t ht
      have ht1 : (1 : ℝ) < t := ht
      have hpow : t ^ ((1 / 2 : ℝ) - 1) ≤ 1 := by
        rw [show ((1 / 2 : ℝ) - 1) = -(1 / 2 : ℝ) from by ring]
        calc t ^ (-(1 / 2) : ℝ) ≤ t ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (le_of_lt ht1) (by norm_num)
          _ = 1 := Real.rpow_zero t
      have hnorm : ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
          23 / 11 * Real.exp (-Real.pi * t) := by
        rw [norm_f_modif_eq_of_one_lt ht1]
        exact evenKernel_zero_sub_one_le_tight (le_of_lt ht1)
      have hnn : (0 : ℝ) ≤ ‖(hurwitzEvenFEPair 0).f_modif t‖ := norm_nonneg _
      have hppos : (0 : ℝ) < t ^ ((1 / 2 : ℝ) - 1) :=
        Real.rpow_pos_of_pos (by linarith) _
      nlinarith [hpow, hnorm, hnn, hppos]
  refine le_trans hmono (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_one_exp_neg_pi]

theorem inner_piece_half_le :
    ∫ t in Set.Ioo (0 : ℝ) 1,
      t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      23 / 11 * (Real.exp (-Real.pi) / Real.pi) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => 23 / 11 * (t⁻¹ * Real.exp (-Real.pi / t)))
      (Set.Ioo (0 : ℝ) 1) :=
    integrableOn_inv_mul_exp_neg_pi_div.const_mul _
  have hmono : ∫ t in Set.Ioo (0 : ℝ) 1,
      t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤
      ∫ t in Set.Ioo (0 : ℝ) 1,
        23 / 11 * (t⁻¹ * Real.exp (-Real.pi / t)) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      intro t ht
      have ht0 : (0 : ℝ) < t := ht.1
      positivity
    · exact hmaj
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      intro t ht
      have ht0 : (0 : ℝ) < t := ht.1
      have ht1 : t < 1 := ht.2
      have hx1 : (1 : ℝ) ≤ 1 / t := by
        rw [le_div_iff₀ ht0]
        linarith
      dsimp only
      rw [norm_f_modif_eq_of_lt_one ht0 ht1,
        show ((1 / 2 : ℝ) - 1) = -(1 / 2 : ℝ) from by ring,
        ← mul_assoc, ← Real.rpow_add ht0]
      have hexp : t ^ (-(1 / 2) + -(1 / 2) : ℝ) = t⁻¹ := by
        rw [show (-(1 / 2) + -(1 / 2) : ℝ) = (-1 : ℝ) from by ring,
          Real.rpow_neg_one]
      rw [hexp]
      have hker : evenKernel 0 (1 / t) - 1 ≤
          23 / 11 * Real.exp (-Real.pi * (1 / t)) :=
        evenKernel_zero_sub_one_le_tight hx1
      have harg : Real.exp (-Real.pi * (1 / t)) = Real.exp (-Real.pi / t) := by
        congr 1
        ring
      rw [harg] at hker
      have hinv : (0 : ℝ) < t⁻¹ := by positivity
      nlinarith [hker, hinv]
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left integral_Ioo_inv_mul_exp_neg_pi_div_le
    (by norm_num)

/-- **Certified critical Mellin bound** for the modified theta kernel. -/
theorem norm_mellin_f_modif_half_le :
    ‖mellin (hurwitzEvenFEPair 0).f_modif ((1 : ℂ) / 2)‖ ≤
      2 * (23 / 11 * (Real.exp (-Real.pi) / Real.pi)) := by
  rw [mellin]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hre : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hcongr : (∫ t in Set.Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (((1 : ℂ) / 2) - 1) • (hurwitzEvenFEPair 0).f_modif t‖) =
      ∫ t in Set.Ioi (0 : ℝ),
        t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.sub_re, Complex.one_re, hre]
  rw [hcongr]
  have hsplit : Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (⟨h0, _⟩ | h1)
      · exact h0
      · linarith
    · intro h0
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr h
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_le.mpr hx.2)
  have hIci : MeasureTheory.IntegrableOn (fun t : ℝ =>
      t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      (Set.Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact outer_integrand_integrableOn (by norm_num)
  rw [← hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ici
    (inner_integrand_integrableOn (by norm_num)) hIci]
  have hIci_eq : (∫ t in Set.Ici (1 : ℝ),
      t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) =
      ∫ t in Set.Ioi (1 : ℝ),
        t ^ ((1 / 2 : ℝ) - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ :=
    MeasureTheory.integral_Ici_eq_integral_Ioi
  rw [hIci_eq]
  linarith [inner_piece_half_le, outer_piece_half_le]

/-! ## §5 The certified budget at the strip edge -/

/-- The derivative of `ξ` at the strip edge is half the entire source value. -/
theorem hasDerivAt_xi_one :
    HasDerivAt xi (completedRiemannZeta₀ 1 / 2) 1 := by
  have hp : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) ((1 : ℂ) / 2) 1 := by
    have h : HasDerivAt (fun s : ℂ => s * (s - 1))
        ((1 : ℂ) * ((1 : ℂ) - 1) + 1 * 1) 1 :=
      (hasDerivAt_id (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)
    have h2 := h.div_const 2
    have h2' : HasDerivAt (fun s : ℂ => s * (s - 1) / 2)
        (((1 : ℂ) * ((1 : ℂ) - 1) + 1 * 1) / 2) 1 :=
      h2.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    exact h2'.congr_deriv (by norm_num)
  have hz : HasDerivAt completedRiemannZeta₀
      (deriv completedRiemannZeta₀ 1) 1 :=
    (differentiable_completedZeta₀ 1).hasDerivAt
  have hadd := (hp.mul hz).add_const ((1 : ℂ) / 2)
  have hadd' : HasDerivAt
      (fun s : ℂ =>
        s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2)
      ((1 : ℂ) / 2 * completedRiemannZeta₀ 1 +
        1 * (1 - 1) / 2 * deriv completedRiemannZeta₀ 1) 1 :=
    hadd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hxi : xi = fun s : ℂ =>
      s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2 := rfl
  rw [hxi]
  exact hadd'.congr_deriv (by ring)

/-- **The strip-edge budget identity**: `logDeriv ξ(1) = Λ₀(1)`. -/
theorem logDeriv_xi_one : logDeriv xi 1 = completedRiemannZeta₀ 1 := by
  rw [logDeriv, Pi.div_apply, hasDerivAt_xi_one.deriv, xi_one]
  field_simp

/-- **Certified strip-edge source bound**: `‖Λ₀(1)‖ ≤ 3/100`. -/
theorem norm_completedRiemannZeta₀_one_le :
    ‖completedRiemannZeta₀ (1 : ℂ)‖ ≤ 3 / 100 := by
  have hdef : completedRiemannZeta₀ (1 : ℂ) =
      mellin (hurwitzEvenFEPair 0).f_modif ((1 : ℂ) / 2) / 2 := by
    rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
  have hnum : 23 / 11 * (Real.exp (-Real.pi) / Real.pi) ≤ 3 / 100 := by
    have hd : Real.exp (-Real.pi) / Real.pi ≤ (1 / 23 : ℝ) / 3.14 :=
      div_le_div₀ (by norm_num) exp_neg_pi_le (by norm_num)
        (le_of_lt Real.pi_gt_d2)
    linarith
  rw [hdef, norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2n]
  linarith [norm_mellin_f_modif_half_le]

theorem xi_probe_half_ne_zero : XiC (xiBudgetProbeAt (1 / 2)) ≠ 0 := by
  exact XiC_probeAt_ne_zero_of_half_le (by norm_num)

/-- **The certified critical budget**: the complete divisor carries total
strip-edge spectral mass at most `3/50`. -/
theorem tsum_massAt_half_le :
    ∑' d : XiZeroCopy, xiBudgetMassAt (1 / 2) d ≤ 3 / 50 := by
  rw [tsum_xiBudgetMassAt_eq xi_probe_half_ne_zero]
  have harg : ((1 : ℂ) / 2 + (((1 / 2 : ℝ)) : ℂ)) = 1 := by
    norm_num
  rw [harg, logDeriv_xi_one]
  have hre : (completedRiemannZeta₀ 1).re ≤ ‖completedRiemannZeta₀ 1‖ :=
    Complex.re_le_norm _
  linarith [norm_completedRiemannZeta₀_one_le]

/-- **THE UNCONDITIONAL HEIGHT FLOOR.**  Every strict-right Schwarz pair of
the `ξ`-divisor has squared height above `65`: no off-critical zero of the
Riemann `ξ` lies below height `8`. -/
theorem xiWard_offlinePair_height_sq_gt_sixtyfive (q : XiRightUpperZeroCopy) :
    (65 : ℝ) < ((xiRightCenteredZero q.1).im) ^ 2 := by
  have h := height_sq_ge_of_budget_le (c := 1 / 2) (B := 3 / 50)
    (by norm_num) (by norm_num) xi_probe_half_ne_zero tsum_massAt_half_le q
  have hnum : (65 : ℝ) < 8 * (1 / 2) / (3 / 50) - ((1 / 2) + 1 / 2) ^ 2 := by
    norm_num
  linarith

/-- The height floor in ordinate form: every off-critical zero lies above
height `8`. -/
theorem xiWard_offlinePair_abs_im_gt_eight (q : XiRightUpperZeroCopy) :
    (8 : ℝ) < |(xiRightCenteredZero q.1).im| := by
  have h := xiWard_offlinePair_height_sq_gt_sixtyfive q
  have habs := sq_abs ((xiRightCenteredZero q.1).im)
  nlinarith [abs_nonneg ((xiRightCenteredZero q.1).im), habs]

/-! ## §6 The discrimination window -/

/-- **Exact discrimination identity.**  The difference between the spectral
mass of an off-line copy at height `u` with transverse displacement `v` and the
mass of an on-line copy at the same height is a single rational expression
whose sign is carried entirely by `c² − 3u² − v²`. -/
theorem offline_sub_online_mass (c u v : ℝ)
    (h1 : 0 < u ^ 2 + (c - v) ^ 2) (h2 : 0 < u ^ 2 + (c + v) ^ 2)
    (h3 : 0 < u ^ 2 + c ^ 2) :
    ((c - v) / (u ^ 2 + (c - v) ^ 2) + (c + v) / (u ^ 2 + (c + v) ^ 2)) -
        2 * c / (u ^ 2 + c ^ 2) =
      2 * c * v ^ 2 * (c ^ 2 - 3 * u ^ 2 - v ^ 2) /
        ((u ^ 2 + c ^ 2) *
          ((u ^ 2 + (c - v) ^ 2) * (u ^ 2 + (c + v) ^ 2))) := by
  field_simp
  ring

/-- **Above the discrimination threshold an off-line copy is cheaper.**  For
`3u² + v² > c²` a transversely displaced copy deposits strictly less spectral
mass than an on-line copy at the same height: past height `c/√3` the sum rule
penalises off-line zeros only through their fourfold multiplicity, never
through their displacement. -/
theorem offline_mass_lt_online (c u v : ℝ) (hc : 0 < c) (hv : v ≠ 0)
    (hvc : |v| < c) (hthr : c ^ 2 < 3 * u ^ 2 + v ^ 2) :
    (c - v) / (u ^ 2 + (c - v) ^ 2) + (c + v) / (u ^ 2 + (c + v) ^ 2) <
      2 * c / (u ^ 2 + c ^ 2) := by
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hvc
  have hcv1 : 0 < c - v := by linarith
  have hcv2 : 0 < c + v := by linarith
  have h1 : 0 < u ^ 2 + (c - v) ^ 2 := by positivity
  have h2 : 0 < u ^ 2 + (c + v) ^ 2 := by positivity
  have h3 : 0 < u ^ 2 + c ^ 2 := by positivity
  have hid := offline_sub_online_mass c u v h1 h2 h3
  have hvsq : 0 < v ^ 2 := by positivity
  have hnum : 2 * c * v ^ 2 * (c ^ 2 - 3 * u ^ 2 - v ^ 2) < 0 := by
    have hfac : c ^ 2 - 3 * u ^ 2 - v ^ 2 < 0 := by linarith
    have hpos : 0 < 2 * c * v ^ 2 := by positivity
    exact mul_neg_of_pos_of_neg hpos hfac
  have hden : 0 < (u ^ 2 + c ^ 2) *
      ((u ^ 2 + (c - v) ^ 2) * (u ^ 2 + (c + v) ^ 2)) := by positivity
  have hquot : 2 * c * v ^ 2 * (c ^ 2 - 3 * u ^ 2 - v ^ 2) /
      ((u ^ 2 + c ^ 2) *
        ((u ^ 2 + (c - v) ^ 2) * (u ^ 2 + (c + v) ^ 2))) < 0 :=
    div_neg_of_neg_of_pos hnum hden
  linarith [hid, hquot]

/-- **Below the threshold the displacement itself is penalised.**  For
`3u² + v² < c²` an off-line copy deposits strictly more mass than an on-line
copy at the same height. -/
theorem online_mass_lt_offline (c u v : ℝ) (hc : 0 < c) (hv : v ≠ 0)
    (hvc : |v| < c) (hthr : 3 * u ^ 2 + v ^ 2 < c ^ 2) :
    2 * c / (u ^ 2 + c ^ 2) <
      (c - v) / (u ^ 2 + (c - v) ^ 2) + (c + v) / (u ^ 2 + (c + v) ^ 2) := by
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hvc
  have hcv1 : 0 < c - v := by linarith
  have hcv2 : 0 < c + v := by linarith
  have h1 : 0 < u ^ 2 + (c - v) ^ 2 := by positivity
  have h2 : 0 < u ^ 2 + (c + v) ^ 2 := by positivity
  have h3 : 0 < u ^ 2 + c ^ 2 := by positivity
  have hid := offline_sub_online_mass c u v h1 h2 h3
  have hvsq : 0 < v ^ 2 := by positivity
  have hnum : 0 < 2 * c * v ^ 2 * (c ^ 2 - 3 * u ^ 2 - v ^ 2) := by
    have hfac : 0 < c ^ 2 - 3 * u ^ 2 - v ^ 2 := by linarith
    have hpos : 0 < 2 * c * v ^ 2 := by positivity
    exact mul_pos hpos hfac
  have hden : 0 < (u ^ 2 + c ^ 2) *
      ((u ^ 2 + (c - v) ^ 2) * (u ^ 2 + (c + v) ^ 2)) := by positivity
  have hquot : 0 < 2 * c * v ^ 2 * (c ^ 2 - 3 * u ^ 2 - v ^ 2) /
      ((u ^ 2 + c ^ 2) *
        ((u ^ 2 + (c - v) ^ 2) * (u ^ 2 + (c + v) ^ 2))) :=
    div_pos hnum hden
  linarith [hid, hquot]

/-- **The discrimination window of the ξ-divisor.**  Every off-critical copy
sits above the threshold at the strip-edge probe: the certified height floor
makes `3u² + v² > c²` automatic at `c = 1/2`, so the strip-edge sum rule
charges an off-line copy strictly less than an on-line copy at the same
height.  The entire force of the floor is the fourfold multiplicity. -/
theorem offline_mass_lt_online_at_edge (q : XiRightUpperZeroCopy)
    (hv : (xiSpectralPoint q.1.1).im ≠ 0) :
    xiBudgetMassAt (1 / 2) q.1.1 <
      2 * (1 / 2) / ((xiSpectralPoint q.1.1).re ^ 2 + (1 / 2) ^ 2) := by
  have hfloor := xiWard_offlinePair_height_sq_gt_sixtyfive q
  rw [xiRightCenteredZero_im_eq_spectral_re] at hfloor
  have hvlt := abs_im_xiSpectralPoint_lt_half q.1.1
  have hthr : (1 / 2 : ℝ) ^ 2 <
      3 * (xiSpectralPoint q.1.1).re ^ 2 + (xiSpectralPoint q.1.1).im ^ 2 := by
    nlinarith [sq_nonneg ((xiSpectralPoint q.1.1).im), hfloor]
  exact offline_mass_lt_online (1 / 2) _ _ (by norm_num) hv hvlt hthr

/-! ## §7 The universal height floor -/

/-- No divisor copy is its own functional-equation reflection: that would force
the centered spectral coordinate to vanish. -/
theorem xiZeroCopy_ne_reflect (q : XiZeroCopy) :
    q ≠ xiZeroCopyReflectEquiv q := by
  intro h
  have hs := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_reflect] at hs
  have hzero : xiSpectralPoint q = 0 := by linear_combination hs / 2
  exact xiSpectralPoint_ne_zero q hzero

/-- **Every zero is charged twice.**  Reflection pairs each divisor copy with a
distinct copy of equal mass, so twice any single mass fits inside the budget. -/
theorem two_mul_massAt_le_tsum {c : ℝ} (hc : 1 / 2 ≤ c)
    (hne : XiC (xiBudgetProbeAt c) ≠ 0) (q : XiZeroCopy) :
    2 * xiBudgetMassAt c q ≤ ∑' d : XiZeroCopy, xiBudgetMassAt c d := by
  classical
  have hsum := summable_xiBudgetMassAt hne
  have hpair : ∑ d ∈ ({q, xiZeroCopyReflectEquiv q} : Finset XiZeroCopy),
      xiBudgetMassAt c d = 2 * xiBudgetMassAt c q := by
    rw [Finset.sum_pair (xiZeroCopy_ne_reflect q), massAt_reflect]
    ring
  have hle := hsum.sum_le_tsum
    ({q, xiZeroCopyReflectEquiv q} : Finset XiZeroCopy)
    (fun d _ => xiBudgetMassAt_nonneg hc d)
  linarith [hpair ▸ hle]

/-- **The universal floor.**  Every copy of the `ξ`-divisor — on the critical
line or not — has squared height at least `4c/B − (c+1/2)²`. -/
theorem xiSpectral_re_sq_ge_of_budget {c B : ℝ} (hc : 1 / 2 ≤ c) (hB : 0 < B)
    (hne : XiC (xiBudgetProbeAt c) ≠ 0)
    (hbud : ∑' d : XiZeroCopy, xiBudgetMassAt c d ≤ B) (q : XiZeroCopy) :
    4 * c / B - (c + 1 / 2) ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by
  have h1 := two_mul_massAt_le_tsum hc hne q
  have h4 := xiBudgetMassAt_ge hc q
  set u := (xiSpectralPoint q).re
  have hden : (0 : ℝ) < u ^ 2 + (c + 1 / 2) ^ 2 := by positivity
  have hcpos : (0 : ℝ) < c := by linarith
  have hchain : 4 * c / (u ^ 2 + (c + 1 / 2) ^ 2) ≤ B := by
    have hstep : 2 * (2 * c / (u ^ 2 + (c + 1 / 2) ^ 2)) ≤
        2 * xiBudgetMassAt c q := by linarith
    calc 4 * c / (u ^ 2 + (c + 1 / 2) ^ 2)
        = 2 * (2 * c / (u ^ 2 + (c + 1 / 2) ^ 2)) := by ring
      _ ≤ 2 * xiBudgetMassAt c q := hstep
      _ ≤ ∑' d : XiZeroCopy, xiBudgetMassAt c d := h1
      _ ≤ B := hbud
  rw [div_le_iff₀ hden] at hchain
  rw [sub_le_iff_le_add, div_le_iff₀ hB]
  nlinarith [hchain]

/-- **Certified universal floor**: every zero of `ξ` has squared ordinate
above `32`. -/
theorem xiSpectral_re_sq_gt_thirtytwo (q : XiZeroCopy) :
    (32 : ℝ) < (xiSpectralPoint q).re ^ 2 := by
  have h := xiSpectral_re_sq_ge_of_budget (c := 1 / 2) (B := 3 / 50)
    (by norm_num) (by norm_num) xi_probe_half_ne_zero tsum_massAt_half_le q
  have hnum : (32 : ℝ) < 4 * (1 / 2) / (3 / 50) - ((1 / 2) + 1 / 2) ^ 2 := by
    norm_num
  linarith

/-- **A zero-free horizontal strip for `ξ`**, unconditional and free of any
numerical zero search: `ξ` has no zero of ordinate at most `√32 > 5.6`. -/
theorem xi_ne_zero_of_im_sq_le {s : ℂ} (him : s.im ^ 2 ≤ 32) : xi s ≠ 0 := by
  intro hzero
  have hXiC : XiC (-Complex.I * (s - 1 / 2)) = 0 := by
    show xi ((1 / 2 : ℂ) + (-Complex.I * (s - 1 / 2)) * Complex.I) = 0
    have harg : (1 / 2 : ℂ) + -Complex.I * (s - 1 / 2) * Complex.I = s := by
      rw [show (-Complex.I * (s - 1 / 2) * Complex.I) =
        -(Complex.I * Complex.I) * (s - 1 / 2) from by ring, Complex.I_mul_I]
      ring
    rw [harg]
    exact hzero
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hXiC
  have hre : (-Complex.I * (s - 1 / 2)).re = s.im := by
    simp [Complex.mul_re, Complex.sub_im]
  have hfloor := xiSpectral_re_sq_gt_thirtytwo q
  rw [hq, hre] at hfloor
  linarith

/-- **A zero-free horizontal strip for `ζ`.**  In the right half plane the
Riemann zeta function has no zero of ordinate at most `√32 > 5.6`.  The bound
is certified from the theta representation alone: no zero of `ζ` is located
numerically anywhere in the argument. -/
theorem riemannZeta_ne_zero_of_im_sq_le {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hre : 0 < s.re) (him : s.im ^ 2 ≤ 32) : riemannZeta s ≠ 0 := by
  intro hzero
  have hΛ : completedRiemannZeta s = 0 := by
    have hζ := riemannZeta_def_of_ne_zero hs0
    rw [hzero] at hζ
    have hG : Complex.Gammaℝ s ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos hre
    have h := hζ.symm
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h hG
  have hxi : xi s = 0 := by
    rw [xi_eq_half_mul hs0 hs1, hΛ, mul_zero]
  exact xi_ne_zero_of_im_sq_le him hxi

/-! ## §8 The low-lying counting bound -/

/-- **Spectral capacity of a height window.**  Any finite family of divisor
copies of height at most `T` is bounded in size by the budget divided by the
mass a single copy at height `T` deposits. -/
theorem card_mul_mass_le_of_height_le {c B T : ℝ} (hc : 1 / 2 ≤ c)
    (hne : XiC (xiBudgetProbeAt c) ≠ 0)
    (hbud : ∑' d : XiZeroCopy, xiBudgetMassAt c d ≤ B)
    (S : Finset XiZeroCopy)
    (hS : ∀ q ∈ S, (xiSpectralPoint q).re ^ 2 ≤ T ^ 2) :
    (S.card : ℝ) * (2 * c / (T ^ 2 + (c + 1 / 2) ^ 2)) ≤ B := by
  have hsum := summable_xiBudgetMassAt hne
  have hlow : ∀ q ∈ S, 2 * c / (T ^ 2 + (c + 1 / 2) ^ 2) ≤
      xiBudgetMassAt c q := by
    intro q hq
    refine le_trans ?_ (xiBudgetMassAt_ge hc q)
    have hden : (0 : ℝ) < (xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2 := by
      positivity
    have hT : (0 : ℝ) < T ^ 2 + (c + 1 / 2) ^ 2 := by
      have := hS q hq
      have hsq : (0 : ℝ) ≤ (xiSpectralPoint q).re ^ 2 := sq_nonneg _
      nlinarith
    exact div_le_div_of_nonneg_left (by linarith) hden
      (by linarith [hS q hq])
  have hcard := Finset.card_nsmul_le_sum S (xiBudgetMassAt c)
    (2 * c / (T ^ 2 + (c + 1 / 2) ^ 2)) hlow
  rw [nsmul_eq_mul] at hcard
  have hpart : ∑ q ∈ S, xiBudgetMassAt c q ≤
      ∑' d : XiZeroCopy, xiBudgetMassAt c d :=
    hsum.sum_le_tsum S (fun d _ => xiBudgetMassAt_nonneg hc d)
  linarith

/-- **Unconditional low-lying zero count.**  At most `3(T²+1)/50` divisor
copies of `ξ` have height at most `T`; no numerical zero search enters the
bound. -/
theorem card_le_of_height_le_certified {T : ℝ} (S : Finset XiZeroCopy)
    (hS : ∀ q ∈ S, (xiSpectralPoint q).re ^ 2 ≤ T ^ 2) :
    (S.card : ℝ) ≤ 3 * (T ^ 2 + 1) / 50 := by
  have h := card_mul_mass_le_of_height_le (c := 1 / 2) (B := 3 / 50)
    (by norm_num) xi_probe_half_ne_zero tsum_massAt_half_le S hS
  have hT : (0 : ℝ) < T ^ 2 + ((1 : ℝ) / 2 + 1 / 2) ^ 2 := by positivity
  have hval : 2 * (1 / 2 : ℝ) / (T ^ 2 + ((1 : ℝ) / 2 + 1 / 2) ^ 2) =
      1 / (T ^ 2 + 1) := by
    norm_num
  rw [hval] at h
  have hT1 : (0 : ℝ) < T ^ 2 + 1 := by positivity
  rw [mul_one_div, div_le_iff₀ hT1] at h
  linarith

/-! ## §9 Hypothesis-free budget laws on the exterior probe ray -/

/-- The difference-trace sum rule at every budget probe at or beyond the strip edge. -/
theorem two_logDeriv_XiC_probeAt_eq_tsum_of_half_le {c : ℝ} (hc : 1 / 2 ≤ c) :
    2 * logDeriv XiC (xiBudgetProbeAt c) =
      ∑' q : XiZeroCopy,
        ((xiSpectralPoint q + xiBudgetProbeAt c)⁻¹ -
          (xiSpectralPoint q - xiBudgetProbeAt c)⁻¹) :=
  two_logDeriv_XiC_probeAt_eq_tsum (XiC_probeAt_ne_zero_of_half_le hc)

/-- Spectral budget mass is summable at every probe at or beyond the strip edge. -/
theorem summable_xiBudgetMassAt_of_half_le {c : ℝ} (hc : 1 / 2 ≤ c) :
    Summable (xiBudgetMassAt c) :=
  summable_xiBudgetMassAt (XiC_probeAt_ne_zero_of_half_le hc)

/-- Exact total spectral-budget identity on the complete exterior probe ray. -/
theorem tsum_xiBudgetMassAt_eq_of_half_le {c : ℝ} (hc : 1 / 2 ≤ c) :
    ∑' q : XiZeroCopy, xiBudgetMassAt c q =
      2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re :=
  tsum_xiBudgetMassAt_eq (XiC_probeAt_ne_zero_of_half_le hc)

/-- Fourfold off-line orbit mass fits in the total budget without a caller-supplied regularity
premise. -/
theorem tsum_pairs_four_mul_massAt_le_of_half_le {c : ℝ} (hc : 1 / 2 ≤ c) :
    ∑' q : XiRightUpperZeroCopy, 4 * xiBudgetMassAt c q.1.1 ≤
      ∑' d : XiZeroCopy, xiBudgetMassAt c d :=
  tsum_pairs_four_mul_massAt_le hc (XiC_probeAt_ne_zero_of_half_le hc)

/-- Certified budget control gives the off-line height floor on every exterior probe. -/
theorem height_sq_ge_of_budget_le_of_half_le {c B : ℝ}
    (hc : 1 / 2 ≤ c) (hB : 0 < B)
    (hbud : ∑' d : XiZeroCopy, xiBudgetMassAt c d ≤ B)
    (q : XiRightUpperZeroCopy) :
    8 * c / B - (c + 1 / 2) ^ 2 ≤ ((xiRightCenteredZero q.1).im) ^ 2 :=
  height_sq_ge_of_budget_le hc hB (XiC_probeAt_ne_zero_of_half_le hc) hbud q

/-- Reflection-paired mass fits in the total budget on every exterior probe. -/
theorem two_mul_massAt_le_tsum_of_half_le {c : ℝ} (hc : 1 / 2 ≤ c)
    (q : XiZeroCopy) :
    2 * xiBudgetMassAt c q ≤ ∑' d : XiZeroCopy, xiBudgetMassAt c d :=
  two_mul_massAt_le_tsum hc (XiC_probeAt_ne_zero_of_half_le hc) q

/-- Certified budget control gives the universal divisor height floor on every exterior probe. -/
theorem xiSpectral_re_sq_ge_of_budget_of_half_le {c B : ℝ}
    (hc : 1 / 2 ≤ c) (hB : 0 < B)
    (hbud : ∑' d : XiZeroCopy, xiBudgetMassAt c d ≤ B) (q : XiZeroCopy) :
    4 * c / B - (c + 1 / 2) ^ 2 ≤ (xiSpectralPoint q).re ^ 2 :=
  xiSpectral_re_sq_ge_of_budget hc hB (XiC_probeAt_ne_zero_of_half_le hc) hbud q

/-- Finite-window divisor capacity bound on every exterior probe, with regularity discharged. -/
theorem card_mul_mass_le_of_height_le_of_half_le {c B T : ℝ}
    (hc : 1 / 2 ≤ c)
    (hbud : ∑' d : XiZeroCopy, xiBudgetMassAt c d ≤ B)
    (S : Finset XiZeroCopy)
    (hS : ∀ q ∈ S, (xiSpectralPoint q).re ^ 2 ≤ T ^ 2) :
    (S.card : ℝ) * (2 * c / (T ^ 2 + (c + 1 / 2) ^ 2)) ≤ B :=
  card_mul_mass_le_of_height_le hc (XiC_probeAt_ne_zero_of_half_le hc) hbud S hS

end

end RHTower
