import GaloisForLFunctions.RHTower.ConstrainedWeilPolarDerivativeTest

/-!
# Uniform bounds for the `(z_q² + ¼)²`-weighted ray terms of the plateau family

With the second-order coefficient bounds `‖κ(c)‖, ‖ρ(c)‖ ≤ M₂ e^{|Re c|/4}/‖c‖²`, the twisted moment of
the plateau profile at aperture `a ≥ ½` and complex frequency `c = b + iμ` with `|b| ≤ Θ` satisfies
`‖A(b, μ)‖ ≤ 4 M₂ e^{Θ/4} e^{aΘ} / ‖c‖²` (and `A = 0` when `c = 0`).  Hence the normalised ray term
`e^{−2Θa} · ray_q(a)` weighted by `w_q = (z_q² + ¼)²` is bounded, uniformly in the aperture, by

`rayMajorant_q = 4 M₂² e^{Θ/2} ‖w_q‖ κ_q² / ‖z_q‖²`,  `κ_q = 1/‖c₁‖² + 1/‖c₂‖²`,

which is summable over the copies: for copies with `|Re z_q| ≥ 2|γ|` it is at most
`4096 M₂² e^{Θ/2}/‖z_q‖²`, and the remaining copies are finitely many.  The same majorant, divided
by the exponent gap, bounds the decay norms of the weighted exponential polynomials.
-/

open MeasureTheory Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The weight and the frequency constant -/

/-- The pole-vanishing weight `(z_q² + ¼)²`. -/
def dWeight (q : XiZeroCopy) : ℂ := (xiSpectralPoint q ^ (2 : ℕ) + 1 / 4) ^ (2 : ℕ)

theorem norm_dWeight_le (q : XiZeroCopy) :
    ‖dWeight q‖ ≤ (‖xiSpectralPoint q‖ ^ (2 : ℕ) + 1 / 4) ^ (2 : ℕ) := by
  unfold dWeight
  rw [norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_add_le _ _).trans ?_
  rw [norm_pow, norm_div, norm_one, Complex.norm_ofNat]

theorem quarter_le_norm_sq_xiSpectralPoint (q : XiZeroCopy) :
    (1 / 4 : ℝ) ≤ ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have h := nine_halves_le_abs_re_xiSpectralPoint q
  have h2 : (9 / 2 : ℝ) ≤ ‖xiSpectralPoint q‖ := h.trans (Complex.abs_re_le_norm _)
  nlinarith

theorem norm_dWeight_le' (q : XiZeroCopy) : ‖dWeight q‖ ≤ 4 * ‖xiSpectralPoint q‖ ^ (4 : ℕ) := by
  have h := norm_dWeight_le q
  have h2 := quarter_le_norm_sq_xiSpectralPoint q
  have h3 : (‖xiSpectralPoint q‖ ^ (2 : ℕ) + 1 / 4) ^ (2 : ℕ) ≤ (2 * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc ‖dWeight q‖ ≤ (‖xiSpectralPoint q‖ ^ (2 : ℕ) + 1 / 4) ^ (2 : ℕ) := h
    _ ≤ (2 * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) ^ (2 : ℕ) := h3
    _ = 4 * ‖xiSpectralPoint q‖ ^ (4 : ℕ) := by ring

/-- `κ_q = 1/‖c₁‖² + 1/‖c₂‖²`, with vanishing frequencies contributing `0`. -/
def freqConst (γ : ℝ) (q : XiZeroCopy) : ℝ :=
  (if rayFreq₁ γ q = 0 then 0 else 1 / ‖rayFreq₁ γ q‖ ^ (2 : ℕ))
    + (if rayFreq₂ γ q = 0 then 0 else 1 / ‖rayFreq₂ γ q‖ ^ (2 : ℕ))

theorem freqConst_nonneg (γ : ℝ) (q : XiZeroCopy) : 0 ≤ freqConst γ q := by
  unfold freqConst
  split_ifs <;> positivity

/-! ## Second-order moment bounds -/

/-- Second-order bound on the twisted moments of the plateau profile. -/
theorem norm_twistedMoment_plateau_le₂ {M Θ : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ))
    (hΘ : 0 ≤ Θ) {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) {b μ : ℝ} (hb : |b| ≤ Θ) :
    ‖twistedMoment (plateauProfile a ha0) b μ‖
      ≤ 4 * M * Real.exp (Θ / 4) * Real.exp (a * Θ)
          * (if (b : ℂ) + I * (μ : ℂ) = 0 then 0 else 1 / ‖(b : ℂ) + I * (μ : ℂ)‖ ^ (2 : ℕ)) := by
  by_cases hc : (b : ℂ) + I * (μ : ℂ) = 0
  · have hb0 : b = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    have hμ0 : μ = 0 := by
      have := congrArg Complex.im hc
      simpa using this
    rw [if_pos hc, hb0, hμ0, twistedMoment_zero_zero, norm_zero]
    simp
  · rw [if_neg hc, twistedMoment_plateauProfile ha ha0 hc]
    set c : ℂ := (b : ℂ) + I * (μ : ℂ) with hcdef
    have hcre : c.re = b := by simp [hcdef]
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hE : Real.exp (|b| / 4) ≤ Real.exp (Θ / 4) := Real.exp_le_exp.mpr (by linarith)
    have hE1 : 1 ≤ Real.exp (a * Θ) := Real.one_le_exp (by positivity)
    have hexp : ∀ s : ℝ, |s| ≤ Θ → Real.exp (s * a) ≤ Real.exp (a * Θ) := by
      intro s hs
      apply Real.exp_le_exp.mpr
      have := (abs_le.mp hs).2
      nlinarith
    have hnormexp : ‖Complex.exp (c * (a : ℂ))‖ = Real.exp (b * a) := by
      rw [Complex.norm_exp]
      congr 1
      simp [hcdef, Complex.mul_re]
    have hnormexp' : ‖Complex.exp (-c * (a : ℂ))‖ = Real.exp (-b * a) := by
      rw [Complex.norm_exp]
      congr 1
      simp [hcdef, Complex.mul_re]
    have hκ := (hMb c hc).1
    have hρ := (hMb c hc).2
    have hκ' := (hMb (-c) (neg_ne_zero.mpr hc)).1
    have hρ' := (hMb (-c) (neg_ne_zero.mpr hc)).2
    rw [Complex.neg_re, abs_neg, norm_neg] at hκ' hρ'
    rw [hcre] at hκ hρ hκ' hρ'
    have hK : ∀ x : ℂ, ‖x‖ ≤ M * Real.exp (|b| / 4) / ‖c‖ ^ (2 : ℕ) →
        ‖x‖ ≤ M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ) := by
      intro x hx
      refine hx.trans ?_
      gcongr
    have hb1 := hexp b hb
    have hb2 := hexp (-b) (by rw [abs_neg]; exact hb)
    have hbase : 0 ≤ M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ) := by positivity
    calc ‖Complex.exp (c * (a : ℂ)) * plateauKappa c + plateauRho c
          - (Complex.exp (-c * (a : ℂ)) * plateauKappa (-c) + plateauRho (-c))‖
        ≤ ‖Complex.exp (c * (a : ℂ)) * plateauKappa c + plateauRho c‖
          + ‖Complex.exp (-c * (a : ℂ)) * plateauKappa (-c) + plateauRho (-c)‖ := norm_sub_le _ _
      _ ≤ (‖Complex.exp (c * (a : ℂ))‖ * ‖plateauKappa c‖ + ‖plateauRho c‖)
          + (‖Complex.exp (-c * (a : ℂ))‖ * ‖plateauKappa (-c)‖ + ‖plateauRho (-c)‖) := by
          gcongr <;> exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ (Real.exp (a * Θ) * (M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ))
            + Real.exp (a * Θ) * (M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ)))
          + (Real.exp (a * Θ) * (M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ))
            + Real.exp (a * Θ) * (M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ))) := by
          rw [hnormexp, hnormexp']
          have k1 := hK _ hκ
          have k2 := hK _ hρ
          have k3 := hK _ hκ'
          have k4 := hK _ hρ'
          have := mul_le_mul hb1 k1 (norm_nonneg _) (Real.exp_pos _).le
          have := mul_le_mul hb2 k3 (norm_nonneg _) (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_right hE1 hbase]
      _ = 4 * M * Real.exp (Θ / 4) * Real.exp (a * Θ) * (1 / ‖c‖ ^ (2 : ℕ)) := by ring

/-- Second-order bound on the pair moment. -/
theorem norm_twistedPairMoment_plateau_le₂ {M Θ : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ))
    (hΘ : 0 ≤ Θ) {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ‖twistedPairMoment (plateauProfile a ha0) γ q‖
      ≤ 4 * M * Real.exp (Θ / 4) * Real.exp (a * Θ) * freqConst γ q := by
  unfold twistedPairMoment
  have hb : |-(xiSpectralPoint q).im| ≤ Θ := by rw [abs_neg]; exact hq
  have h1 := norm_twistedMoment_plateau_le₂ hM hMb hΘ ha ha0 (μ := (xiSpectralPoint q).re - γ) hb
  have h2 := norm_twistedMoment_plateau_le₂ hM hMb hΘ ha ha0 (μ := (xiSpectralPoint q).re + γ) hb
  refine (norm_add_le _ _).trans ?_
  unfold freqConst rayFreq₁ rayFreq₂
  linarith

/-- **Uniform bound on the weighted normalised ray term.** -/
def rayMajorant (M Θ γ : ℝ) (q : XiZeroCopy) : ℝ :=
  4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * ‖dWeight q‖ * freqConst γ q ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))

theorem rayMajorant_nonneg (M Θ γ : ℝ) (q : XiZeroCopy) :
    0 ≤ rayMajorant M Θ γ q := by
  unfold rayMajorant
  have := freqConst_nonneg γ q
  positivity

theorem norm_twistedRayTerm_plateau_le₂ {M Θ : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ))
    (hΘ : 0 ≤ Θ) {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ‖twistedRayTerm (plateauProfile a ha0) γ q‖
      ≤ 4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * Real.exp (2 * a * Θ) * freqConst γ q ^ (2 : ℕ)
          * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  unfold twistedRayTerm
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  have hz : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hP := norm_twistedPairMoment_plateau_le₂ hM hMb hΘ ha ha0 γ hq
  have hP0 : 0 ≤ ‖twistedPairMoment (plateauProfile a ha0) γ q‖ := norm_nonneg _
  have hsq := pow_le_pow_left₀ hP0 hP 2
  have hexp : (4 * M * Real.exp (Θ / 4) * Real.exp (a * Θ) * freqConst γ q) ^ (2 : ℕ)
      = 16 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * Real.exp (2 * a * Θ) * freqConst γ q ^ (2 : ℕ) := by
    have e1 : Real.exp (Θ / 4) ^ (2 : ℕ) = Real.exp (Θ / 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.exp (a * Θ) ^ (2 : ℕ) = Real.exp (2 * a * Θ) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, mul_pow, mul_pow, mul_pow, e1, e2]
    norm_num
  rw [div_le_iff₀ (by positivity)]
  calc 1 / 4 * ‖twistedPairMoment (plateauProfile a ha0) γ q‖ ^ (2 : ℕ)
      ≤ 1 / 4 * (16 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * Real.exp (2 * a * Θ) * freqConst γ q ^ (2 : ℕ)) := by
        rw [← hexp]; exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * Real.exp (2 * a * Θ) * freqConst γ q ^ (2 : ℕ)
          * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        field_simp
        ring

/-! ## The weighted exponential polynomial -/

/-- The weighted normalised ray-term polynomial `w_q · P_q`. -/
def weightedRayPoly (Θ γ : ℝ) (q : XiZeroCopy) : ExpPoly :=
  ExpPoly.smul (dWeight q) (normalizedRayTermPoly Θ γ q)

theorem eval_weightedRayPoly {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (Θ γ : ℝ) (q : XiZeroCopy) :
    ExpPoly.eval (weightedRayPoly Θ γ q) a
      = dWeight q * (Complex.exp (-(2 * Θ : ℝ) * (a : ℂ))
          * twistedRayTerm (plateauProfile a ha0) γ q) := by
  unfold weightedRayPoly
  rw [ExpPoly.eval_smul, eval_normalizedRayTermPoly ha ha0]

theorem decaying_weightedRayPoly {Θ : ℝ} (hΘ : 0 ≤ Θ) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) : ExpPoly.Decaying (weightedRayPoly Θ γ q) :=
  ExpPoly.decaying_smul _ (decaying_normalizedRayTermPoly hΘ γ hq)

theorem constTerm_weightedRayPoly (Θ γ : ℝ) (q : XiZeroCopy) :
    ExpPoly.constTerm (weightedRayPoly Θ γ q)
      = dWeight q * ExpPoly.constTerm (normalizedRayTermPoly Θ γ q) :=
  ExpPoly.constTerm_smul _ _

theorem decayNorm_weightedRayPoly (Θ γ : ℝ) (q : XiZeroCopy) :
    ExpPoly.decayNorm (weightedRayPoly Θ γ q)
      = ‖dWeight q‖ * ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q) :=
  ExpPoly.decayNorm_smul _ _

/-- **Uniform bound.** -/
theorem norm_re_eval_weightedRayPoly_le {M Θ : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ))
    (hΘ : 0 ≤ Θ) {a : ℝ} (ha : 1 / 2 ≤ a) (γ : ℝ) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ‖(ExpPoly.eval (weightedRayPoly Θ γ q) a).re‖ ≤ rayMajorant M Θ γ q := by
  have ha0 : 0 ≤ a := by linarith
  rw [eval_weightedRayPoly ha ha0, cexp_neg_two_theta]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := norm_twistedRayTerm_plateau_le₂ hM hMb hΘ ha ha0 γ hq
  have hw : 0 ≤ ‖dWeight q‖ := norm_nonneg _
  have hprod : Real.exp (-(2 * Θ) * a) * Real.exp (2 * a * Θ) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  unfold rayMajorant
  calc ‖dWeight q‖ * (Real.exp (-(2 * Θ) * a) * ‖twistedRayTerm (plateauProfile a ha0) γ q‖)
      ≤ ‖dWeight q‖ * (Real.exp (-(2 * Θ) * a)
          * (4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * Real.exp (2 * a * Θ) * freqConst γ q ^ (2 : ℕ)
            * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))) := by
        gcongr
    _ = (Real.exp (-(2 * Θ) * a) * Real.exp (2 * a * Θ))
          * (4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * ‖dWeight q‖ * freqConst γ q ^ (2 : ℕ)
            * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) := by ring
    _ = 4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * ‖dWeight q‖ * freqConst γ q ^ (2 : ℕ)
          * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by rw [hprod, one_mul]

/-! ## Summability of the majorant -/

/-- Copies far above the centre in ordinate: `|Re z_q| ≥ 2|γ|`. -/
def FarBig (γ : ℝ) (q : XiZeroCopy) : Prop := 2 * |γ| ≤ |(xiSpectralPoint q).re|

theorem finite_not_farBig (γ : ℝ) : {q : XiZeroCopy | ¬ FarBig γ q}.Finite := by
  have h := finite_xiZeroCopy_band 0 (by positivity : (0 : ℝ) ≤ 2 * |γ|)
  refine h.subset ?_
  intro q hq
  simp only [FarBig, mem_setOf_eq, not_le] at hq
  simp only [mem_setOf_eq, sub_zero, ← xiSpectralPoint_re_eq_im]
  exact hq.le

theorem norm_rayFreq_ge_of_farBig (γ : ℝ) {q : XiZeroCopy} (hfar : FarBig γ q) :
    |(xiSpectralPoint q).re| / 2 ≤ ‖rayFreq₁ γ q‖ ∧ |(xiSpectralPoint q).re| / 2 ≤ ‖rayFreq₂ γ q‖ := by
  have hγ : |γ| ≤ |(xiSpectralPoint q).re| / 2 := by unfold FarBig at hfar; linarith
  constructor
  · refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [rayFreq₁_im]
    have := abs_sub_abs_le_abs_sub (xiSpectralPoint q).re γ
    linarith
  · refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [rayFreq₂_im]
    have h1 := abs_sub_abs_le_abs_sub (xiSpectralPoint q).re (-γ)
    rw [abs_neg, sub_neg_eq_add] at h1
    linarith

theorem freqConst_le_of_farBig (γ : ℝ) {q : XiZeroCopy} (hfar : FarBig γ q) :
    freqConst γ q ≤ 16 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  obtain ⟨h1, h2⟩ := norm_rayFreq_ge_of_farBig γ hfar
  have hre := nine_halves_le_abs_re_xiSpectralPoint q
  have hre2 : ‖xiSpectralPoint q‖ ^ (2 : ℕ) / 2 ≤ (xiSpectralPoint q).re ^ (2 : ℕ) := by
    have hh := abs_im_xiSpectralPoint_lt_half q
    have hsq : ‖xiSpectralPoint q‖ ^ (2 : ℕ) = (xiSpectralPoint q).re ^ (2 : ℕ) + (xiSpectralPoint q).im ^ (2 : ℕ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have him : (xiSpectralPoint q).im ^ (2 : ℕ) < 1 / 4 := by
      have := abs_lt.mp hh
      nlinarith [abs_nonneg (xiSpectralPoint q).im, sq_abs (xiSpectralPoint q).im]
    have hre' : (81 / 4 : ℝ) ≤ (xiSpectralPoint q).re ^ (2 : ℕ) := by
      have := pow_le_pow_left₀ (by norm_num) hre 2
      rw [sq_abs] at this
      linarith
    nlinarith
  have hpos1 : 0 < ‖rayFreq₁ γ q‖ := lt_of_lt_of_le (by linarith) h1
  have hpos2 : 0 < ‖rayFreq₂ γ q‖ := lt_of_lt_of_le (by linarith) h2
  have hne1 : rayFreq₁ γ q ≠ 0 := norm_pos_iff.mp hpos1
  have hne2 : rayFreq₂ γ q ≠ 0 := norm_pos_iff.mp hpos2
  unfold freqConst
  rw [if_neg hne1, if_neg hne2]
  have hz : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    have := quarter_le_norm_sq_xiSpectralPoint q; linarith
  have hb1 : 1 / ‖rayFreq₁ γ q‖ ^ (2 : ℕ) ≤ 8 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    rw [div_le_div_iff₀ (by positivity) hz]
    have := pow_le_pow_left₀ (by positivity) h1 2
    rw [div_pow, sq_abs] at this
    nlinarith
  have hb2 : 1 / ‖rayFreq₂ γ q‖ ^ (2 : ℕ) ≤ 8 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    rw [div_le_div_iff₀ (by positivity) hz]
    have := pow_le_pow_left₀ (by positivity) h2 2
    rw [div_pow, sq_abs] at this
    nlinarith
  calc 1 / ‖rayFreq₁ γ q‖ ^ (2 : ℕ) + 1 / ‖rayFreq₂ γ q‖ ^ (2 : ℕ)
      ≤ 8 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) + 8 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := add_le_add hb1 hb2
    _ = 16 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by ring

theorem rayMajorant_le_of_farBig (M Θ γ : ℝ) {q : XiZeroCopy}
    (hfar : FarBig γ q) :
    rayMajorant M Θ γ q ≤ 4096 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  unfold rayMajorant
  have hw := norm_dWeight_le' q
  have hk := freqConst_le_of_farBig γ hfar
  have hk0 := freqConst_nonneg γ q
  have hz : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hk2 : freqConst γ q ^ (2 : ℕ) ≤ (16 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ hk0 hk 2
  have hE : 0 ≤ 4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) := by positivity
  calc 4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * ‖dWeight q‖ * freqConst γ q ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))
      ≤ 4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * (4 * ‖xiSpectralPoint q‖ ^ (4 : ℕ))
          * (16 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
        gcongr
    _ = 4096 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
        field_simp
        ring

/-- **Summability of the majorant.** -/
theorem summable_rayMajorant (M Θ γ : ℝ) :
    Summable (rayMajorant M Θ γ) := by
  classical
  set F : Finset XiZeroCopy := (finite_not_farBig γ).toFinset with hF
  have hsum1 : Summable (fun q : XiZeroCopy =>
      4096 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hsum2 : Summable (fun q : XiZeroCopy => if q ∈ F then rayMajorant M Θ γ q else 0) := by
    refine summable_of_ne_finset_zero (s := F) fun q hq => ?_
    simp [hq]
  refine Summable.of_nonneg_of_le (fun q => rayMajorant_nonneg M Θ γ q) (fun q => ?_)
    (hsum1.add hsum2)
  by_cases hfar : FarBig γ q
  · have hqF : q ∉ F := by
      simp only [hF, Set.Finite.mem_toFinset, mem_setOf_eq, not_not]
      exact hfar
    rw [if_neg hqF, add_zero]
    exact rayMajorant_le_of_farBig M Θ γ hfar
  · have hqF : q ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, mem_setOf_eq]
      exact hfar
    rw [if_pos hqF]
    have : 0 ≤ 4096 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by positivity
    linarith

/-! ## Decay norms of the weighted polynomials -/

/-- Second-order coefficient sum for a far copy: `≤ 4 M₂ e^{Θ/4} κ_q`. -/
theorem coeffSum_shiftedPairPoly_le₂ {Θ M : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ))
    (γ : ℝ) {q : XiZeroCopy} (hq : |(xiSpectralPoint q).im| ≤ Θ) (hfar : FarFromCentre γ q) :
    ExpPoly.coeffSum (shiftedPairPoly Θ γ q) ≤ 4 * (M * Real.exp (Θ / 4)) * freqConst γ q := by
  have h1 := norm_rayFreq₁_ge_one γ hfar
  have h2 := norm_rayFreq₂_ge_one γ hfar
  have hc₁ : rayFreq₁ γ q ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have hc₂ : rayFreq₂ γ q ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; linarith
  have hre₁ : |(rayFreq₁ γ q).re| ≤ Θ := by rw [rayFreq₁_re, abs_neg]; exact hq
  have hre₂ : |(rayFreq₂ γ q).re| ≤ Θ := by rw [rayFreq₂_re, abs_neg]; exact hq
  have hE : ∀ c : ℂ, |c.re| ≤ Θ → Real.exp (|c.re| / 4) ≤ Real.exp (Θ / 4) :=
    fun c hc => Real.exp_le_exp.mpr (by linarith)
  have key : ∀ c : ℂ, c ≠ 0 → |c.re| ≤ Θ →
      ‖plateauKappa c‖ ≤ M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (Θ / 4) / ‖c‖ ^ (2 : ℕ) := by
    intro c hc hcre
    have hE' := hE c hcre
    obtain ⟨k1, k2⟩ := hMb c hc
    constructor
    · exact k1.trans (by gcongr)
    · exact k2.trans (by gcongr)
  have b1 := key _ hc₁ hre₁
  have b2 := key (-rayFreq₁ γ q) (neg_ne_zero.mpr hc₁) (by rw [Complex.neg_re, abs_neg]; exact hre₁)
  have b3 := key _ hc₂ hre₂
  have b4 := key (-rayFreq₂ γ q) (neg_ne_zero.mpr hc₂) (by rw [Complex.neg_re, abs_neg]; exact hre₂)
  rw [norm_neg] at b2 b4
  rw [shiftedPairPoly_explicit Θ γ hc₁ hc₂]
  simp only [ExpPoly.coeffSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, norm_neg]
  unfold freqConst
  rw [if_neg hc₁, if_neg hc₂]
  have e1 : M * Real.exp (Θ / 4) / ‖rayFreq₁ γ q‖ ^ (2 : ℕ)
      = M * Real.exp (Θ / 4) * (1 / ‖rayFreq₁ γ q‖ ^ (2 : ℕ)) := by ring
  have e2 : M * Real.exp (Θ / 4) / ‖rayFreq₂ γ q‖ ^ (2 : ℕ)
      = M * Real.exp (Θ / 4) * (1 / ‖rayFreq₂ γ q‖ ^ (2 : ℕ)) := by ring
  rw [e1] at b1 b2
  rw [e2] at b3 b4
  linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]

/-- Decay norm of a weighted far copy: `≤ rayMajorant_q / m₀`. -/
theorem decayNorm_weightedRayPoly_le_far {Θ g γ M : ℝ} (hΘ : 0 < Θ) (hg : 0 < g) (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ))
    {q : XiZeroCopy} (hq : |(xiSpectralPoint q).im| ≤ Θ) (hz : g ≤ |(xiSpectralPoint q).re|)
    (hγ : g ≤ |γ|) (hfar : FarFromCentre γ q) :
    ExpPoly.decayNorm (weightedRayPoly Θ γ q) ≤ rayMajorant M Θ γ q / min 1 (min Θ g) := by
  have hm0 : 0 < min 1 (min Θ g) := lt_min one_pos (lt_min hΘ hg)
  rw [decayNorm_weightedRayPoly, normalizedRayTermPoly_eq, ExpPoly.decayNorm_smul]
  have hpair := shiftedPairPoly_pairSum_norm_ge hΘ hg hq hz hγ hfar
  have hmul := ExpPoly.decayNorm_mul_le (shiftedPairPoly Θ γ q) (shiftedPairPoly Θ γ q) hm0 hpair
  have hcs := coeffSum_shiftedPairPoly_le₂ hM hMb γ hq hfar
  have hcs0 := ExpPoly.coeffSum_nonneg (shiftedPairPoly Θ γ q)
  have hw : ‖-(1 / 4 : ℂ) / xiSpectralPoint q ^ (2 : ℕ)‖ = 1 / (4 * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    rw [norm_div, norm_neg, norm_div, norm_one, norm_pow, Complex.norm_ofNat]
    ring
  rw [hw]
  have hsq : ExpPoly.coeffSum (shiftedPairPoly Θ γ q) * ExpPoly.coeffSum (shiftedPairPoly Θ γ q)
      ≤ (4 * (M * Real.exp (Θ / 4)) * freqConst γ q) ^ (2 : ℕ) := by
    rw [← sq]
    exact pow_le_pow_left₀ hcs0 hcs 2
  have hexp : (4 * (M * Real.exp (Θ / 4)) * freqConst γ q) ^ (2 : ℕ)
      = 16 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * freqConst γ q ^ (2 : ℕ) := by
    have e1 : Real.exp (Θ / 4) ^ (2 : ℕ) = Real.exp (Θ / 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, mul_pow, mul_pow, e1]
    ring
  have hz0 : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hwn : 0 ≤ ‖dWeight q‖ := norm_nonneg _
  unfold rayMajorant
  calc ‖dWeight q‖ * (1 / (4 * ‖xiSpectralPoint q‖ ^ (2 : ℕ))
        * ExpPoly.decayNorm (ExpPoly.mul (shiftedPairPoly Θ γ q) (shiftedPairPoly Θ γ q)))
      ≤ ‖dWeight q‖ * (1 / (4 * ‖xiSpectralPoint q‖ ^ (2 : ℕ))
        * (ExpPoly.coeffSum (shiftedPairPoly Θ γ q) * ExpPoly.coeffSum (shiftedPairPoly Θ γ q)
          / min 1 (min Θ g))) := by gcongr
    _ ≤ ‖dWeight q‖ * (1 / (4 * ‖xiSpectralPoint q‖ ^ (2 : ℕ))
        * ((16 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * freqConst γ q ^ (2 : ℕ)) / min 1 (min Θ g))) := by
        rw [← hexp]; gcongr
    _ = 4 * M ^ (2 : ℕ) * Real.exp (Θ / 2) * ‖dWeight q‖ * freqConst γ q ^ (2 : ℕ)
          * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) / min 1 (min Θ g) := by
        field_simp
        ring

/-- **Summability of the weighted decay norms.** -/
theorem summable_decayNorm_weightedRayPoly {Θ γ M : ℝ} (hΘ : 0 < Θ) (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ)
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ (2 : ℕ))
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) (hγ : 9 / 2 ≤ |γ|) :
    Summable (fun q : XiZeroCopy => ExpPoly.decayNorm (weightedRayPoly Θ γ q)) := by
  classical
  have hg : (0 : ℝ) < 9 / 2 := by norm_num
  have hm0 : 0 < min 1 (min Θ (9 / 2 : ℝ)) := lt_min one_pos (lt_min hΘ hg)
  set F : Finset XiZeroCopy := (finite_not_farFromCentre γ).toFinset with hF
  have hsum1 : Summable (fun q : XiZeroCopy => rayMajorant M Θ γ q / min 1 (min Θ (9 / 2 : ℝ))) :=
    (summable_rayMajorant M Θ γ).div_const _
  have hsum2 : Summable (fun q : XiZeroCopy =>
      if q ∈ F then ExpPoly.decayNorm (weightedRayPoly Θ γ q) else 0) := by
    refine summable_of_ne_finset_zero (s := F) fun q hq => ?_
    simp [hq]
  refine Summable.of_nonneg_of_le (fun q => ExpPoly.decayNorm_nonneg _) (fun q => ?_)
    (hsum1.add hsum2)
  by_cases hfar : FarFromCentre γ q
  · have hqF : q ∉ F := by
      simp only [hF, Set.Finite.mem_toFinset, mem_setOf_eq, not_not]
      exact hfar
    rw [if_neg hqF, add_zero]
    exact decayNorm_weightedRayPoly_le_far hΘ hg hM hMb (hall q)
      (nine_halves_le_abs_re_xiSpectralPoint q) hγ hfar
  · have hqF : q ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, mem_setOf_eq]
      exact hfar
    rw [if_pos hqF]
    have : 0 ≤ rayMajorant M Θ γ q / min 1 (min Θ (9 / 2 : ℝ)) := by
      have := rayMajorant_nonneg M Θ γ q
      positivity
    linarith

end

end RHTower
