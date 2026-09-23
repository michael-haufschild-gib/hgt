import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelope
import GaloisForLFunctions.RHTower.DirichletLStripBounds

/-!
# The multiplier decays faster than every power on vertical strips

On a closed vertical strip the centered Gaussian contributes

```text
‖exp((s-1/2)^(2 : ℕ))‖ = exp((Re s - 1/2)^(2 : ℕ) - (Im s)^(2 : ℕ)),
```

while the reciprocal Gamma factor grows at most like `exp(π|Im s|)` — the reflection-formula bound.
The Gaussian therefore dominates, and `A(s)(1+|Im s|)^N` is bounded on every closed vertical strip
for every `N`.

Consequently multiplication by `A` sends a datum of polynomial vertical growth to a bounded one, and
in particular preserves polynomial vertical growth: `A` is a multiplier of the moderate class, which
is what makes the enveloped datum and its reflection simultaneously moderate.

The bound used here is `exp(π|Im s|)` rather than Stirling's `exp(π|Im s|/4)`; the Gaussian absorbs
either.
-/

open Complex Set

namespace GaloisForLFunctions

noncomputable section

/-! ## The two factors -/

/-- **The Gaussian contribution.** -/
theorem norm_exp_sq_sub_half (s : ℂ) :
    ‖Complex.exp ((s - 1 / 2) ^ 2)‖ = Real.exp ((s.re - 1 / 2) ^ 2 - s.im ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  norm_num

/-- **The reciprocal Gamma contribution** on a strip away from the real axis. -/
theorem exists_bound_norm_inv_Gamma_strip (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ B * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨B, hB, hbound⟩ := RHTower.exists_lower_bound_norm_Gamma_strip a b
  refine ⟨B / Real.pi, by positivity, fun z hz1 hz2 hzim => ?_⟩
  have h := hbound z hz1 hz2 hzim
  have hexp : 0 < Real.exp (Real.pi * |z.im|) := Real.exp_pos _
  have hGpos : 0 < ‖Complex.Gamma z‖ := by
    rcases lt_or_ge 0 ‖Complex.Gamma z‖ with h' | h'
    · exact h'
    · have hzero : ‖Complex.Gamma z‖ = 0 := le_antisymm h' (norm_nonneg _)
      rw [hzero, mul_zero] at h
      exact absurd h (not_le.mpr Real.pi_pos)
  rw [norm_inv]
  rw [inv_le_iff_one_le_mul₀ hGpos]
  have hkey : Real.pi ≤ B * Real.exp (Real.pi * |z.im|) * ‖Complex.Gamma z‖ := h
  have : B / Real.pi * Real.exp (Real.pi * |z.im|) * ‖Complex.Gamma z‖
      = (B * Real.exp (Real.pi * |z.im|) * ‖Complex.Gamma z‖) / Real.pi := by
    field_simp
  rw [this, le_div_iff₀ Real.pi_pos, one_mul]
  exact hkey

/-! ## Two elementary majorants -/

/-- A downward parabola is bounded by its vertex value. -/
theorem neg_sq_add_mul_le (t b : ℝ) : -t ^ 2 + b * t ≤ b ^ 2 / 4 := by
  nlinarith [sq_nonneg (t - b / 2)]

/-- A power of `1 + t` is dominated by an exponential. -/
theorem one_add_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ Real.exp ((N : ℝ) * t) := by
  have h1 : (1 : ℝ) + t ≤ Real.exp t := by
    have := Real.add_one_le_exp t
    linarith
  calc (1 + t) ^ N ≤ (Real.exp t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
    _ = Real.exp ((N : ℝ) * t) := by rw [← Real.exp_nat_mul]

/-- On a closed real interval a squared shift is bounded by its endpoint values. -/
theorem sq_sub_half_le_max {a b σ : ℝ} (h1 : a ≤ σ) (h2 : σ ≤ b) :
    (σ - 1 / 2) ^ 2 ≤ max ((a - 1 / 2) ^ 2) ((b - 1 / 2) ^ 2) := by
  rcases le_total σ (1 / 2) with h | h
  · refine le_trans ?_ (le_max_left _ _)
    nlinarith
  · refine le_trans ?_ (le_max_right _ _)
    nlinarith

/-! ## Rapid decay on a strip -/

/-- **The multiplier decays faster than every power on every closed vertical strip.** -/
theorem exists_bound_envelope_strip_decay (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
      ‖gammaGaussianEnvelope s‖ * (1 + |s.im|) ^ N ≤ C := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_norm_inv_Gamma_strip (a / 2) (b / 2)
  have hpi1 : (1 : ℝ) < Real.pi := by
    have := Real.pi_gt_three
    linarith
  set K : ℝ := max ((a - 1 / 2) ^ 2) ((b - 1 / 2) ^ 2) with hK
  refine ⟨Real.pi ^ (b / 2) * B * Real.exp K * Real.exp ((Real.pi / 2 + (N : ℝ)) ^ 2 / 4), by
    have : (0:ℝ) < Real.pi ^ (b / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    positivity, fun s hs1 hs2 hsim => ?_⟩
  set t : ℝ := |s.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht2 : t ^ 2 = s.im ^ 2 := sq_abs _
  -- the reciprocal archimedean factor
  have hhalf1 : a / 2 ≤ (s / 2).re := by
    rw [Complex.div_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply]
    norm_num
    linarith
  have hhalf2 : (s / 2).re ≤ b / 2 := by
    rw [Complex.div_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply]
    norm_num
    linarith
  have hhalfim : (s / 2).im = s.im / 2 := by
    rw [Complex.div_im]
    simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply]
    norm_num
    ring
  have hhalfabs : 1 ≤ |(s / 2).im| := by
    rw [hhalfim, abs_div]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  have hGam := hbound (s / 2) hhalf1 hhalf2 hhalfabs
  have hcpow : ‖(Real.pi : ℂ) ^ (s / 2)‖ = Real.pi ^ (s / 2).re :=
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos _
  have hcpowle : Real.pi ^ (s / 2).re ≤ Real.pi ^ (b / 2) :=
    (Real.rpow_le_rpow_left_iff hpi1).mpr hhalf2
  have hinvΓℝ : ‖(Complex.Gammaℝ s)⁻¹‖
      ≤ Real.pi ^ (b / 2) * (B * Real.exp (Real.pi * (t / 2))) := by
    rw [inv_Gammaℝ_eq, norm_mul, hcpow]
    refine mul_le_mul hcpowle ?_ (norm_nonneg _) (Real.rpow_pos_of_pos Real.pi_pos _).le
    have : |(s / 2).im| = t / 2 := by
      rw [hhalfim, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), ht]
    rw [← this]
    exact hGam
  -- the Gaussian
  have hGauss : ‖Complex.exp ((s - 1 / 2) ^ 2)‖ ≤ Real.exp K * Real.exp (-t ^ 2) := by
    rw [norm_exp_sq_sub_half, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := sq_sub_half_le_max hs1 hs2
    rw [ht2]
    linarith
  -- assemble
  have hnorm : ‖gammaGaussianEnvelope s‖
      = ‖Complex.exp ((s - 1 / 2) ^ 2)‖ * ‖(Complex.Gammaℝ s)⁻¹‖ := by
    rw [gammaGaussianEnvelope, norm_mul]
  have hpow : (1 + t) ^ N ≤ Real.exp ((N : ℝ) * t) := one_add_pow_le_exp ht0 N
  have hstep : ‖gammaGaussianEnvelope s‖ * (1 + t) ^ N
      ≤ (Real.exp K * Real.exp (-t ^ 2)) *
        (Real.pi ^ (b / 2) * (B * Real.exp (Real.pi * (t / 2)))) * Real.exp ((N : ℝ) * t) := by
    rw [hnorm]
    refine mul_le_mul (mul_le_mul hGauss hinvΓℝ (norm_nonneg _) (by positivity)) hpow
      (by positivity) (by positivity)
  have hcollect : (Real.exp K * Real.exp (-t ^ 2)) *
        (Real.pi ^ (b / 2) * (B * Real.exp (Real.pi * (t / 2)))) * Real.exp ((N : ℝ) * t)
      = Real.pi ^ (b / 2) * B * Real.exp K *
          Real.exp (-t ^ 2 + (Real.pi / 2 + (N : ℝ)) * t) := by
    have h1 : Real.exp (Real.pi * (t / 2)) * Real.exp ((N : ℝ) * t)
        = Real.exp ((Real.pi / 2 + (N : ℝ)) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-t ^ 2) * Real.exp ((Real.pi / 2 + (N : ℝ)) * t)
        = Real.exp (-t ^ 2 + (Real.pi / 2 + (N : ℝ)) * t) := by rw [← Real.exp_add]
    calc (Real.exp K * Real.exp (-t ^ 2)) *
          (Real.pi ^ (b / 2) * (B * Real.exp (Real.pi * (t / 2)))) * Real.exp ((N : ℝ) * t)
        = Real.pi ^ (b / 2) * B * Real.exp K *
            (Real.exp (-t ^ 2) * (Real.exp (Real.pi * (t / 2)) * Real.exp ((N : ℝ) * t))) := by
          ring
      _ = Real.pi ^ (b / 2) * B * Real.exp K *
            (Real.exp (-t ^ 2) * Real.exp ((Real.pi / 2 + (N : ℝ)) * t)) := by rw [h1]
      _ = Real.pi ^ (b / 2) * B * Real.exp K *
            Real.exp (-t ^ 2 + (Real.pi / 2 + (N : ℝ)) * t) := by rw [h2]
  have hvertex : Real.exp (-t ^ 2 + (Real.pi / 2 + (N : ℝ)) * t)
      ≤ Real.exp ((Real.pi / 2 + (N : ℝ)) ^ 2 / 4) :=
    Real.exp_le_exp.mpr (neg_sq_add_mul_le t (Real.pi / 2 + (N : ℝ)))
  calc ‖gammaGaussianEnvelope s‖ * (1 + |s.im|) ^ N
      ≤ (Real.exp K * Real.exp (-t ^ 2)) *
          (Real.pi ^ (b / 2) * (B * Real.exp (Real.pi * (t / 2)))) * Real.exp ((N : ℝ) * t) :=
        hstep
    _ = Real.pi ^ (b / 2) * B * Real.exp K *
          Real.exp (-t ^ 2 + (Real.pi / 2 + (N : ℝ)) * t) := hcollect
    _ ≤ Real.pi ^ (b / 2) * B * Real.exp K *
          Real.exp ((Real.pi / 2 + (N : ℝ)) ^ 2 / 4) := by
        refine mul_le_mul_of_nonneg_left hvertex ?_
        have : (0:ℝ) < Real.pi ^ (b / 2) := Real.rpow_pos_of_pos Real.pi_pos _
        positivity

/-! ## The horizontal band -/

/-- The multiplier is bounded on every compact horizontal band of a strip. -/
theorem exists_bound_envelope_band (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ 2 →
      ‖gammaGaussianEnvelope s‖ ≤ C := by
  have hcompact : IsCompact (Icc a b ×ℂ Icc (-2 : ℝ) 2) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    differentiable_gammaGaussianEnvelope.continuous.continuousOn
  refine ⟨|C| + 1, by positivity, fun s hs1 hs2 hsim => ?_⟩
  have hmem : s ∈ Icc a b ×ℂ Icc (-2 : ℝ) 2 := by
    refine Complex.mem_reProdIm.mpr ⟨⟨hs1, hs2⟩, ?_⟩
    have h1 : -2 ≤ s.im := neg_le_of_abs_le hsim
    have h2 : s.im ≤ 2 := le_of_abs_le hsim
    exact ⟨h1, h2⟩
  have := hC s hmem
  have hle : C ≤ |C| := le_abs_self C
  linarith

/-! ## Moderation is preserved -/

/-- A datum has polynomial vertical growth when on every closed vertical strip its modulus is
dominated by a power of the height. -/
def HasStripPolyGrowth (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ C * (1 + |s.im|) ^ N

/-- **Multiplying by the multiplier turns polynomial vertical growth into boundedness.** -/
theorem exists_bound_envelope_mul (F : ℂ → ℂ) (hF : HasStripPolyGrowth F) (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖gammaGaussianEnvelope s * F s‖ ≤ C := by
  obtain ⟨N, D, hD, hFb⟩ := hF a b
  obtain ⟨C₁, hC₁, hdecay⟩ := exists_bound_envelope_strip_decay a b N
  obtain ⟨C₂, hC₂, hband⟩ := exists_bound_envelope_band a b
  refine ⟨D * C₁ + D * C₂ * 3 ^ N + 1, by positivity, fun s hs1 hs2 => ?_⟩
  have hFs := hFb s hs1 hs2
  have habs : (0:ℝ) ≤ (1 + |s.im|) ^ N := by positivity
  rw [norm_mul]
  rcases le_total 2 |s.im| with hcase | hcase
  · -- the decaying region
    have h1 := hdecay s hs1 hs2 hcase
    have hmul : ‖gammaGaussianEnvelope s‖ * ‖F s‖
        ≤ ‖gammaGaussianEnvelope s‖ * (D * (1 + |s.im|) ^ N) :=
      mul_le_mul_of_nonneg_left hFs (norm_nonneg _)
    have hre : ‖gammaGaussianEnvelope s‖ * (D * (1 + |s.im|) ^ N)
        = D * (‖gammaGaussianEnvelope s‖ * (1 + |s.im|) ^ N) := by ring
    have h2 : D * (‖gammaGaussianEnvelope s‖ * (1 + |s.im|) ^ N) ≤ D * C₁ :=
      mul_le_mul_of_nonneg_left h1 hD
    have hpos : (0:ℝ) ≤ D * C₂ * 3 ^ N := by positivity
    calc ‖gammaGaussianEnvelope s‖ * ‖F s‖ ≤ D * (1 + |s.im|) ^ N *
          ‖gammaGaussianEnvelope s‖ := by
            rw [mul_comm (D * (1 + |s.im|) ^ N)]
            exact hmul
      _ = D * (‖gammaGaussianEnvelope s‖ * (1 + |s.im|) ^ N) := by ring
      _ ≤ D * C₁ := h2
      _ ≤ D * C₁ + D * C₂ * 3 ^ N + 1 := by linarith
  · -- the band
    have h1 := hband s hs1 hs2 hcase
    have hgrow : (1 + |s.im|) ^ N ≤ 3 ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have hFle : ‖F s‖ ≤ D * 3 ^ N := by
      refine hFs.trans ?_
      exact mul_le_mul_of_nonneg_left hgrow hD
    have hFnn : (0:ℝ) ≤ ‖F s‖ := norm_nonneg _
    have hprod : ‖gammaGaussianEnvelope s‖ * ‖F s‖ ≤ C₂ * (D * 3 ^ N) :=
      mul_le_mul h1 hFle hFnn hC₂.le
    have hrw : C₂ * (D * 3 ^ N) = D * C₂ * 3 ^ N := by ring
    have hpos : (0:ℝ) ≤ D * C₁ := by positivity
    rw [hrw] at hprod
    linarith

/-- **The multiplier preserves polynomial vertical growth.** -/
theorem hasStripPolyGrowth_envelope_mul {F : ℂ → ℂ} (hF : HasStripPolyGrowth F) :
    HasStripPolyGrowth (fun s => gammaGaussianEnvelope s * F s) := by
  intro a b
  obtain ⟨C, hC, hbound⟩ := exists_bound_envelope_mul F hF a b
  refine ⟨0, C, hC.le, fun s hs1 hs2 => ?_⟩
  simpa using hbound s hs1 hs2

/-- Reflection preserves polynomial vertical growth. -/
theorem hasStripPolyGrowth_one_sub {F : ℂ → ℂ} (hF : HasStripPolyGrowth F) :
    HasStripPolyGrowth (fun s => F (1 - s)) := by
  intro a b
  obtain ⟨N, C, hC, hbound⟩ := hF (1 - b) (1 - a)
  refine ⟨N, C, hC, fun s hs1 hs2 => ?_⟩
  have hre1 : 1 - b ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hre2 : (1 - s).re ≤ 1 - a := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have him : |(1 - s).im| = |s.im| := by
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  rw [← him]
  exact hbound (1 - s) hre1 hre2

/-- **The enveloped datum and its reflection are simultaneously moderate**, which is the growth half
of the universal envelope theorem: the reflected transform equals `A(s)F(1-s)` wherever the
reflection identity applies. -/
theorem hasStripPolyGrowth_envelope_mul_one_sub {F : ℂ → ℂ} (hF : HasStripPolyGrowth F) :
    HasStripPolyGrowth (fun s => gammaGaussianEnvelope s * F (1 - s)) :=
  hasStripPolyGrowth_envelope_mul (hasStripPolyGrowth_one_sub hF)

/-- The reflected enveloped datum is the enveloped reflected datum, pointwise on the left of the
line `Re s = 1`. -/
theorem evenChiFactor_mul_envelope_mul_one_sub {F : ℂ → ℂ} {s : ℂ} (hs : s.re < 1) :
    evenChiFactor s * (gammaGaussianEnvelope (1 - s) * F (1 - s))
      = gammaGaussianEnvelope s * F (1 - s) := by
  rw [← mul_assoc, evenChiFactor_mul_envelope_one_sub_of_re_lt_one hs]

/-! ## The growth class is an algebra -/

/-- A product of data of polynomial vertical growth has polynomial vertical growth. -/
theorem HasStripPolyGrowth.mul {F G : ℂ → ℂ} (hF : HasStripPolyGrowth F)
    (hG : HasStripPolyGrowth G) : HasStripPolyGrowth (fun s => F s * G s) := by
  intro a b
  obtain ⟨N, C, hC, hFb⟩ := hF a b
  obtain ⟨M, D, hD, hGb⟩ := hG a b
  refine ⟨N + M, C * D, by positivity, fun s hs1 hs2 => ?_⟩
  rw [norm_mul]
  calc ‖F s‖ * ‖G s‖ ≤ (C * (1 + |s.im|) ^ N) * (D * (1 + |s.im|) ^ M) :=
        mul_le_mul (hFb s hs1 hs2) (hGb s hs1 hs2) (norm_nonneg _) (by positivity)
    _ = C * D * (1 + |s.im|) ^ (N + M) := by rw [pow_add]; ring

/-- An affine coordinate has polynomial vertical growth. -/
theorem hasStripPolyGrowth_sub_const (c : ℂ) : HasStripPolyGrowth (fun s => s - c) := by
  intro a b
  refine ⟨1, |a| + |b| + ‖c‖ + 1, by positivity, fun s hs1 hs2 => ?_⟩
  have h1 : ‖s - c‖ ≤ ‖s‖ + ‖c‖ := norm_sub_le s c
  have h2 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have h3 : |s.re| ≤ |a| + |b| := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have : -|a| ≤ a := neg_abs_le a
      have hb : (0:ℝ) ≤ |b| := abs_nonneg b
      linarith
    · have : b ≤ |b| := le_abs_self b
      have ha : (0:ℝ) ≤ |a| := abs_nonneg a
      linarith
  have h4 : (0:ℝ) ≤ |s.im| := abs_nonneg _
  have h5 : (0:ℝ) ≤ ‖c‖ := norm_nonneg _
  have h6 : (0:ℝ) ≤ |a| + |b| := by positivity
  calc ‖s - c‖ ≤ (|a| + |b|) + |s.im| + ‖c‖ := by linarith
    _ ≤ (|a| + |b| + ‖c‖ + 1) * (1 + |s.im|) ^ 1 := by
        rw [pow_one]
        nlinarith

end

end GaloisForLFunctions
