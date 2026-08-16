import GaloisForLFunctions.RHTower.ProlateEndpointLowerBound
import GaloisForLFunctions.RHTower.ProlateWKBSubsolution
import GaloisForLFunctions.HTGeometry.RiccatiNoDip
import GaloisForLFunctions.HTGeometry.EnvelopeFromLogDerivative

/-!
# The sharp endpoint bound in the decaying direction

The corpus owns the Riccati *sub*solution side of the prolate barrier: the logarithmic derivative
of a positive mode is at most the WKB profile, so the mode decays *no faster* than
`exp(−∫ √q)`.  The opposite inequality — that it decays at least that fast — is what an upper bound
for the leakage needs, and it does not follow from a supersolution: the WKB profile is not one.

It follows instead from positivity alone.  Beyond the turning point the flux has one sign, so the
Riccati derivative `v = −Φ′/Φ` is *nonnegative* on the whole remaining band; and a nonnegative
solution of `v′ = v² + b v − q` cannot have been far below `√q` at the left end of any window on
which it stays nonnegative — that is `sub_sub_div_le_of_riccati_nonneg`.  Applying it on the window
`[t, t+ℓ]` at every `t` gives

```text
v(t) ≥ √q(t) − b(t+ℓ) − 2/ℓ ,
```

and integrating that turns the sharp exponential rate into an endpoint bound whose only loss is the
integral of the drift `b` plus the length divided by `ℓ` — both polynomial in the bandwidth.
-/

noncomputable section

open Set MeasureTheory
open _root_.RHTower
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

variable {c χ : ℝ} {Φ : ℝ → ℝ}

/-! ## Monotonicity of the two coefficients -/

/-- The Riccati potential is nondecreasing on the nonnegative part of the band. -/
theorem prolatePotential_mono (hcχ : 0 ≤ c ^ 2 + χ) {y z : ℝ}
    (hy0 : 0 ≤ y) (hyz : y ≤ z) (hz1 : z < 1) :
    (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2) ≤ (χ + c ^ 2 * z ^ 2) / (1 - z ^ 2) := by
  have hy1 : y < 1 := lt_of_le_of_lt hyz hz1
  have hz0 : 0 ≤ z := le_trans hy0 hyz
  have hpy : 0 < 1 - y ^ 2 := by nlinarith
  have hpz : 0 < 1 - z ^ 2 := by nlinarith
  have hsq : y ^ 2 ≤ z ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hpy hpz]
  nlinarith [hcχ, hsq]

/-- The drift coefficient is nondecreasing on the nonnegative part of the band. -/
theorem prolateDrift_mono {y z : ℝ} (hy0 : 0 ≤ y) (hyz : y ≤ z) (hz1 : z < 1) :
    2 * y / (1 - y ^ 2) ≤ 2 * z / (1 - z ^ 2) := by
  have hy1 : y < 1 := lt_of_le_of_lt hyz hz1
  have hz0 : 0 ≤ z := le_trans hy0 hyz
  have hpy : 0 < 1 - y ^ 2 := by nlinarith
  have hpz : 0 < 1 - z ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hpy hpz]
  nlinarith [mul_nonneg (sub_nonneg.2 hyz) (by positivity : (0 : ℝ) ≤ 1 + y * z)]

/-- The drift coefficient is nonnegative on the nonnegative part of the band. -/
theorem prolateDrift_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ 2 * y / (1 - y ^ 2) := by
  have hpy : 0 < 1 - y ^ 2 := by nlinarith
  positivity

/-! ## The Riccati derivative is nonnegative beyond the turning point -/

/-- Beyond the turning point a positive mode has nonnegative Riccati derivative. -/
theorem prolateLogDeriv_nonneg
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    {y₀ : ℝ} (hy₀ : -1 < y₀)
    (hpos : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hturn : ∀ t ∈ Icc y₀ 1, 0 ≤ χ + c ^ 2 * t ^ 2)
    {y : ℝ} (hy : y ∈ Ico y₀ 1) :
    0 ≤ prolateLogDeriv Φ y := by
  have hd := deriv_nonpos_of_turning hsm heig hy₀ (fun t ht => (hpos t ht).le) hturn hy
  have hΦ : 0 < Φ y := hpos y ⟨hy.1, hy.2.le⟩
  rw [prolateLogDeriv, neg_nonneg]
  exact div_nonpos_of_nonpos_of_nonneg hd hΦ.le

/-! ## The pointwise lower bound for the Riccati derivative -/

set_option maxHeartbeats 1600000 in
/-- **The Riccati derivative is close to the WKB profile from below.**  On any window inside the
band on which the mode stays positive, the logarithmic derivative at the left end is at least the
WKB profile there, less the drift at the right end and the reciprocal window length. -/
theorem prolateWKB_sub_le_prolateLogDeriv
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hcχ : 0 ≤ c ^ 2 + χ)
    {y₀ y₁ : ℝ} (hy0 : 0 ≤ y₀) (hlt : y₀ < y₁) (hy1 : y₁ < 1)
    (hpos : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hturn : ∀ t ∈ Icc y₀ 1, 0 ≤ χ + c ^ 2 * t ^ 2)
    (hQ0 : 0 < χ + c ^ 2 * y₀ ^ 2) :
    prolateWKB c χ y₀ - 2 * y₁ / (1 - y₁ ^ 2) - 2 / (y₁ - y₀)
      ≤ prolateLogDeriv Φ y₀ := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hsm).2)).1
  have hy₀neg : (-1 : ℝ) < y₀ := by linarith
  have hsubIcc : Icc y₀ y₁ ⊆ Icc y₀ 1 := Icc_subset_Icc le_rfl hy1.le
  have hpow : ∀ y ∈ Icc y₀ y₁, (0 : ℝ) < 1 - y ^ 2 := by
    intro y hy
    have h1 : 0 ≤ y := le_trans hy0 hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 hy1
    nlinarith
  -- the Riccati datum
  set v : ℝ → ℝ := prolateLogDeriv Φ with hv
  set B : ℝ → ℝ := fun y => 2 * y / (1 - y ^ 2) with hB
  set Q : ℝ → ℝ := fun y => (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2) with hQ
  set v' : ℝ → ℝ := fun y => v y ^ 2 + B y * v y - Q y with hv'
  have hvcont : ContinuousOn v (Icc y₀ y₁) := by
    refine ContinuousOn.neg (ContinuousOn.div hd2.continuous.continuousOn
      hd1.continuous.continuousOn ?_)
    intro y hy
    exact (hpos y (hsubIcc hy)).ne'
  have hvderiv : ∀ y ∈ Ioo y₀ y₁, HasDerivAt v (v' y) y := by
    intro y hy
    have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨lt_of_le_of_lt hy₀neg.le hy.1, lt_trans hy.2 hy1⟩
    have hΦ : Φ y ≠ 0 := (hpos y (hsubIcc ⟨hy.1.le, hy.2.le⟩)).ne'
    exact hasDerivAt_prolateLogDeriv hsm heig hmem hΦ
  have hBcont : ContinuousOn B (Icc y₀ y₁) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro y hy
    exact (hpow y hy).ne'
  have hvnn : ∀ y ∈ Icc y₀ y₁, 0 ≤ v y := by
    intro y hy
    exact prolateLogDeriv_nonneg hsm heig hy₀neg hpos hturn ⟨hy.1, lt_of_le_of_lt hy.2 hy1⟩
  have hpow0 : (0 : ℝ) < 1 - y₀ ^ 2 := hpow y₀ (left_mem_Icc.2 hlt.le)
  have hSsq : prolateWKB c χ y₀ ^ 2 = Q y₀ := by
    rw [prolateWKB, hQ]
    exact Real.sq_sqrt (by positivity)
  have hSpos : 0 < prolateWKB c χ y₀ := by
    rw [prolateWKB]
    exact Real.sqrt_pos.2 (by positivity)
  refine sub_sub_div_le_of_riccati_nonneg (v' := v') (B := B) (Q := Q) hlt hvcont hvderiv
    (fun y _ => rfl) hBcont hvnn hSpos ?_ ?_ ?_
  · intro y hy
    rw [hSsq]
    exact prolatePotential_mono hcχ hy0 hy.1 (lt_of_le_of_lt hy.2 hy1)
  · intro y hy
    exact prolateDrift_nonneg (le_trans hy0 hy.1) (lt_of_le_of_lt hy.2 hy1)
  · intro y hy
    exact prolateDrift_mono (le_trans hy0 hy.1) hy.2 hy1

/-! ## The endpoint bound -/

set_option maxHeartbeats 1600000 in
/-- **The sharp endpoint upper bound.**  A positive mode beyond the turning point decays at least
like the exponential of the WKB integral, up to the drift and the window loss. -/
theorem prolate_endpoint_le
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hcχ : 0 ≤ c ^ 2 + χ)
    {a b l : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hl : 0 < l) (hbl : b + l < 1)
    (hpos : ∀ t ∈ Icc a 1, 0 < Φ t)
    (hturn : ∀ t ∈ Icc a 1, 0 ≤ χ + c ^ 2 * t ^ 2)
    (hQ0 : 0 < χ + c ^ 2 * a ^ 2) :
    Φ b ≤ Φ a * Real.exp (-∫ t in a..b,
      (prolateWKB c χ t - 2 * (b + l) / (1 - (b + l) ^ 2) - 2 / l)) := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hb1 : b < 1 := by linarith
  have hsubIcc : Icc a b ⊆ Icc a 1 := Icc_subset_Icc le_rfl hb1.le
  set W : ℝ → ℝ := fun t =>
    prolateWKB c χ t - 2 * (b + l) / (1 - (b + l) ^ 2) - 2 / l with hW
  have hWcont : ContinuousOn W (Icc a b) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_const) continuousOn_const
    refine continuousOn_prolateWKB fun y hy => ?_
    have h1 : 0 ≤ y := le_trans ha0 hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 hb1
    nlinarith
  have hUcont : ContinuousOn (fun t => -W t) (Icc a b) := hWcont.neg
  have hkey : ∀ t ∈ Icc a b, W t ≤ prolateLogDeriv Φ t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have htl : t < t + l := by linarith
    have htl1 : t + l < 1 := by linarith [ht.2]
    have hposT : ∀ u ∈ Icc t 1, 0 < Φ u := fun u hu =>
      hpos u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hturnT : ∀ u ∈ Icc t 1, 0 ≤ χ + c ^ 2 * u ^ 2 := fun u hu =>
      hturn u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hQT : 0 < χ + c ^ 2 * t ^ 2 := by
      have hsq : a ^ 2 ≤ t ^ 2 := by nlinarith [ht.1, ha0]
      nlinarith [hQ0, hsq, sq_nonneg c]
    have hbound := prolateWKB_sub_le_prolateLogDeriv hsm heig hcχ ht0 htl htl1
      hposT hturnT hQT
    have hdrift : 2 * (t + l) / (1 - (t + l) ^ 2) ≤ 2 * (b + l) / (1 - (b + l) ^ 2) :=
      prolateDrift_mono (by linarith) (by linarith [ht.2]) hbl
    have hlen : t + l - t = l := by ring
    rw [hlen] at hbound
    show prolateWKB c χ t - 2 * (b + l) / (1 - (b + l) ^ 2) - 2 / l ≤ prolateLogDeriv Φ t
    linarith [hbound, hdrift]
  have hlogderiv : ∀ t ∈ Icc a b, deriv Φ t ≤ (-W t) * Φ t := by
    intro t ht
    have hΦ : 0 < Φ t := hpos t (hsubIcc ht)
    have h := hkey t ht
    rw [prolateLogDeriv] at h
    have hdiv : deriv Φ t / Φ t ≤ -W t := by linarith
    rwa [div_le_iff₀ hΦ] at hdiv
  have hres := le_mul_exp_integral_of_logDeriv_le' (f := Φ) (f' := deriv Φ) (U := fun t => -W t)
    hab (fun t _ => (hd1 t).hasDerivAt) (fun t ht => hpos t (hsubIcc ht)) hUcont hlogderiv
  have hint : (∫ t in a..b, -W t) = -∫ t in a..b, W t := intervalIntegral.integral_neg
  rwa [hint] at hres

/-! ## The proportional window, and a loss that is only logarithmic -/

set_option maxHeartbeats 1600000 in
/-- **The pointwise bound with a proportional window.**  Taking the comparison window to be half the
distance to the singular endpoint makes both the drift and the reciprocal length `O(1/(1−t))`, with
the absolute constant `6`. -/
theorem prolateWKB_sub_six_div_le_prolateLogDeriv
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hcχ : 0 ≤ c ^ 2 + χ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hpos : ∀ u ∈ Icc t 1, 0 < Φ u)
    (hturn : ∀ u ∈ Icc t 1, 0 ≤ χ + c ^ 2 * u ^ 2)
    (hQ0 : 0 < χ + c ^ 2 * t ^ 2) :
    prolateWKB c χ t - 6 / (1 - t) ≤ prolateLogDeriv Φ t := by
  have hmid : t < (1 + t) / 2 := by linarith
  have hmid1 : (1 + t) / 2 < 1 := by linarith
  have hbound := prolateWKB_sub_le_prolateLogDeriv hsm heig hcχ ht0 hmid hmid1 hpos hturn hQ0
  have h1t : 0 < 1 - t := by linarith
  have hgap : (1 + t) / 2 - t = (1 - t) / 2 := by ring
  have hlen : 2 / ((1 + t) / 2 - t) = 4 / (1 - t) := by
    rw [hgap]
    field_simp
    norm_num
  have hden : 1 - ((1 + t) / 2) ^ 2 = (1 - t) * (3 + t) / 4 := by ring
  have hdrift : 2 * ((1 + t) / 2) / (1 - ((1 + t) / 2) ^ 2) = 4 * (1 + t) / ((1 - t) * (3 + t)) := by
    rw [hden]
    field_simp
  have h3t : (0 : ℝ) < 3 + t := by linarith
  have hcomb : 4 * (1 + t) / ((1 - t) * (3 + t)) + 4 / (1 - t) ≤ 6 / (1 - t) := by
    have hhalf : 4 * (1 + t) / ((1 - t) * (3 + t)) ≤ 2 / (1 - t) := by
      rw [div_le_div_iff₀ (by positivity) h1t]
      nlinarith [sq_nonneg (1 - t)]
    have hsplit : (6 : ℝ) / (1 - t) = 2 / (1 - t) + 4 / (1 - t) := by
      field_simp
      ring
    linarith [hhalf, hsplit]
  rw [hlen, hdrift] at hbound
  linarith [hbound, hcomb]

set_option maxHeartbeats 1600000 in
/-- **The endpoint upper bound with a logarithmic loss.**  The exponent differs from the WKB
integral by `6·log((1−a)/(1−b))`, a polynomial factor in the bandwidth once `1 − b` is a negative
power of it. -/
theorem prolate_endpoint_le_log
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hcχ : 0 ≤ c ^ 2 + χ)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1)
    (hpos : ∀ t ∈ Icc a 1, 0 < Φ t)
    (hturn : ∀ t ∈ Icc a 1, 0 ≤ χ + c ^ 2 * t ^ 2)
    (hQ0 : 0 < χ + c ^ 2 * a ^ 2) :
    Φ b ≤ Φ a * Real.exp (-∫ t in a..b, (prolateWKB c χ t - 6 / (1 - t))) := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hsubIcc : Icc a b ⊆ Icc a 1 := Icc_subset_Icc le_rfl hb1.le
  set W : ℝ → ℝ := fun t => prolateWKB c χ t - 6 / (1 - t) with hW
  have hWcont : ContinuousOn W (Icc a b) := by
    refine ContinuousOn.sub ?_ (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    · refine continuousOn_prolateWKB fun y hy => ?_
      have h1 : 0 ≤ y := le_trans ha0 hy.1
      have h2 : y < 1 := lt_of_le_of_lt hy.2 hb1
      nlinarith
    · intro y hy
      have h2 : y < 1 := lt_of_le_of_lt hy.2 hb1
      linarith
  have hkey : ∀ t ∈ Icc a b, W t ≤ prolateLogDeriv Φ t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
    have hposT : ∀ u ∈ Icc t 1, 0 < Φ u := fun u hu => hpos u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hturnT : ∀ u ∈ Icc t 1, 0 ≤ χ + c ^ 2 * u ^ 2 := fun u hu =>
      hturn u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hQT : 0 < χ + c ^ 2 * t ^ 2 := by
      have hsq : a ^ 2 ≤ t ^ 2 := by nlinarith [ht.1, ha0]
      nlinarith [hQ0, hsq, sq_nonneg c]
    exact prolateWKB_sub_six_div_le_prolateLogDeriv hsm heig hcχ ht0 ht1 hposT hturnT hQT
  have hlogderiv : ∀ t ∈ Icc a b, deriv Φ t ≤ (-W t) * Φ t := by
    intro t ht
    have hΦ : 0 < Φ t := hpos t (hsubIcc ht)
    have h := hkey t ht
    rw [prolateLogDeriv] at h
    have hdiv : deriv Φ t / Φ t ≤ -W t := by linarith
    rwa [div_le_iff₀ hΦ] at hdiv
  have hres := le_mul_exp_integral_of_logDeriv_le' (f := Φ) (f' := deriv Φ) (U := fun t => -W t)
    hab (fun t _ => (hd1 t).hasDerivAt) (fun t ht => hpos t (hsubIcc ht)) hWcont.neg hlogderiv
  have hint : (∫ t in a..b, -W t) = -∫ t in a..b, W t := intervalIntegral.integral_neg
  rwa [hint] at hres

/-- The logarithmic loss, in closed form. -/
theorem integral_six_div_one_sub {a b : ℝ} (hab : a ≤ b) (hb1 : b < 1) :
    (∫ t in a..b, 6 / (1 - t)) = 6 * (Real.log (1 - a) - Real.log (1 - b)) := by
  have hb : 0 < 1 - b := by linarith
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun u : ℝ => -(6 * Real.log (1 - u))) (6 / (1 - t)) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have h1t : (0 : ℝ) < 1 - t := by
      have := ht.2
      linarith
    have hinner : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - t)) t :=
      hinner.log h1t.ne'
    have hmul : HasDerivAt (fun u : ℝ => -(6 * Real.log (1 - u))) (-(6 * (-1 / (1 - t)))) t :=
      (hlog.const_mul (6 : ℝ)).neg
    refine hmul.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => 6 / (1 - t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    have := ht.2
    have : (0 : ℝ) < 1 - t := by linarith
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

end GaloisForLFunctions.RHTower
