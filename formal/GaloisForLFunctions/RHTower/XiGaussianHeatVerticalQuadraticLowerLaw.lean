import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalQuadraticCoefficient
import GaloisForLFunctions.RHTower.XiGaussianHeatSectorBoundednessLaw
import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.HTGeometry.PowerSumTuranLowerBound
import GaloisForLFunctions.RHTower.XiMassLogRetreatTail

/-!
# The vertical quadratic growth of the zero heat trace measures the asymptotic deviation

For `ν(τ) = Σ_q e^{-τ z_q²}` on the vertical line `Re τ = a`, every zero with `|β − ½| ≤ Δ` above some
height gives `ν(a + ib) = O(e^{(Δ² + ε) b²/a})`
(`exists_norm_xiGaussianHeatTraceC_le_quadratic_coefficient`).

**Theorem** (`xiSpectralPoint_im_sq_le_of_vertical_quadratic`).  Conversely, if
`‖ν(a + ib)‖ ≤ C e^{c b²}` for all real `b`, then for every `λ > 0` all zeros above some height
satisfy `(β − ½)² ≤ a c (1 + λ)`.

**Theorem** (`vertical_quadratic_rate_le_iff`).  For `c ≥ 0`: `ν(a + ib) = O(e^{c' b²})` for every
`c' > c` iff `limsup_{|γ|→∞} (β − ½)² ≤ ac`.  So `inf {c : ν(a + ib) = O(e^{c b²})} = Δ∞²/a` with
`Δ∞ = limsup_{|γ|→∞} |β − ½|`: the vertical quadratic growth of the zero heat trace (equivalently of
the Gaussian prime chirp) is exactly the asymptotic deviation of the zeros from the critical line.

**Corollary** (`asymptoticQuasiRH_iff_vertical_quadratic_rate_lt`).  The zeros lie asymptotically in
a strip `|β − ½| ≤ δ < ½` iff `ν(a + ib) = O(e^{c b²})` for some `c < 1/(4a)`; the unconditional
rate is `1/(4a)`.

Mechanism.
* **Phragmén–Lindelöf** (`norm_le_max_of_vertical_of_ray`).  `ν(τ) e^{c(τ−a)²}` is bounded on the
  vertical line by hypothesis and on the 45° ray from `a` by the unconditional sector bound, so
  `‖ν(τ)‖ ≤ C₁ e^{c (Im τ)²}` between them.
* **Truncation.**  At heights `|Im τ| ≤ aΓ/4` the copies with `|γ| > Γ` contribute a bounded tail;
  there are at most `20(Γ+1)(A + log(Γ+6))` copies with `|γ| ≤ Γ`.
* **Power sums on a ray from the origin.**  Along `τ = ν τ₁` the truncated trace is the power sum
  `Σ_q (e^{-τ₁ w_q})^ν`.  The separation-free lower bound `exists_norm_powerSum_ge_scaled` gives a
  sample `ν ∈ [M+1, M+N]` where the truncated trace is at least `e^{-Re(ν τ₁ w₀)} / (2B(M,N))`,
  `log B = O(N log(NM))`, for any chosen copy `w₀`.  No separation of the zeros is needed.
* **Optimization.**  For a copy `z₀ = γ₀ + iη₀` with `γ₀η₀ > 0` and `η₀² > ac(1+λ)`, sample near
  `P = a(1 + μ) + i γ₀η₀/c`.  The copy contributes `exp(γ₀²(2η₀²/c − a(1+μ)) + O(1))` while the
  bound allows only `exp(γ₀²η₀²/c)`; the gap `≍ γ₀²` beats the loss `O(γ₀ log² γ₀)`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Phragmén–Lindelöf between the 45° ray and the vertical line -/

/-- **Phragmén–Lindelöf on the sector between the 45° ray from `a` and the vertical line.**  In the
logarithmic coordinate `τ = a + e^s` the sector is the strip `π/4 ≤ Im s ≤ π/2`, and the growth
`exp(B |τ − a|²) = exp(B e^{2 Re s})` is below the strip threshold `e^{4|Re s|}`. -/
theorem norm_le_max_of_vertical_of_ray {f : ℂ → ℂ} {a C S₀ K B : ℝ} (ha : 0 < a)
    (hdiff : ∀ τ : ℂ, 0 < τ.re → DifferentiableAt ℂ f τ)
    (hgrowth : ∀ τ : ℂ, a ≤ τ.re → ‖f τ‖ ≤ K * Real.exp (B * ‖τ - a‖ ^ 2))
    (hray : ∀ r : ℝ, 0 ≤ r → ‖f ((a : ℂ) + r * Complex.exp (Real.pi / 4 * I))‖ ≤ S₀)
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
  have hgr : ∃ c < Real.pi / (Real.pi / 2 - Real.pi / 4), ∃ B',
      (fun s => f ((a : ℂ) + Complex.exp s)) =O[comap (abs ∘ Complex.re) atTop ⊓
        𝓟 (Complex.im ⁻¹' Ioo (Real.pi / 4) (Real.pi / 2))]
        fun s => Real.exp (B' * Real.exp (c * |s.re|)) := by
    have h4 : Real.pi / (Real.pi / 2 - Real.pi / 4) = 4 := by field_simp; ring
    refine ⟨2, by rw [h4]; norm_num, |B|, Asymptotics.IsBigO.of_bound |K| ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun s hs => ?_)
    have hres := hre s hs.1.le hs.2.le
    refine (hgrowth _ hres).trans ?_
    have hnorm : ‖(a : ℂ) + Complex.exp s - a‖ ^ 2 = Real.exp (2 * s.re) := by
      rw [add_sub_cancel_left, Complex.norm_exp, ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [hnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hBle : B * Real.exp (2 * s.re) ≤ |B| * Real.exp (2 * |s.re|) :=
      mul_le_mul (le_abs_self B) (Real.exp_le_exp.2 (by linarith [le_abs_self s.re]))
        (Real.exp_pos _).le (abs_nonneg B)
    calc K * Real.exp (B * Real.exp (2 * s.re)) ≤ |K| * Real.exp (B * Real.exp (2 * s.re)) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
      _ ≤ |K| * Real.exp (|B| * Real.exp (2 * |s.re|)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hBle) (abs_nonneg K)
  refine PhragmenLindelof.horizontal_strip
    (f := fun s => f ((a : ℂ) + Complex.exp s)) (z := s) hd hgr ?_ ?_ h1 h2
  · intro z hz
    refine le_max_of_le_right ?_
    have hexp : Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) * Complex.exp (Real.pi / 4 * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;> simp [hz]
    rw [hexp]
    exact hray _ (Real.exp_pos _).le
  · intro z hz
    refine le_max_of_le_left ?_
    have hexp : Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [Complex.exp_re, hz, Real.cos_pi_div_two]
      · rw [Complex.exp_im, hz, Real.sin_pi_div_two, mul_one, Complex.mul_I_im, Complex.ofReal_re]
    rw [hexp]
    exact hC _

/-- A point between the 45° ray and the vertical axis has argument in `[π/4, π/2]`. -/
theorem pi_div_four_le_arg_of_re_le_im {z : ℂ} (hz : z ≠ 0) (hre : 0 ≤ z.re) (him : z.re ≤ z.im) :
    Real.pi / 4 ≤ z.arg := by
  rw [Complex.arg_of_re_nonneg hre]
  have hnorm : 0 < ‖z‖ := norm_pos_iff.2 hz
  have him0 : 0 ≤ z.im := hre.trans him
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hkey : Real.sqrt 2 / 2 ≤ z.im / ‖z‖ := by
    rw [le_div_iff₀ hnorm]
    have h2 : (Real.sqrt 2 / 2 * ‖z‖) ^ 2 ≤ z.im ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), hsq]
      nlinarith
    have hl : 0 ≤ Real.sqrt 2 / 2 * ‖z‖ := by positivity
    exact (sq_le_sq₀ hl him0).1 h2
  calc Real.pi / 4 = Real.arcsin (Real.sin (Real.pi / 4)) := by
        rw [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    _ = Real.arcsin (Real.sqrt 2 / 2) := by rw [Real.sin_pi_div_four]
    _ ≤ Real.arcsin (z.im / ‖z‖) := Real.arcsin_le_arcsin hkey

/-- **Phragmén–Lindelöf in rectangular form.**  Under the hypotheses of
`norm_le_max_of_vertical_of_ray`, every `τ` with `0 ≤ Re τ − a ≤ Im τ` has `‖f τ‖ ≤ max C S₀`. -/
theorem norm_le_max_of_vertical_of_ray_rect {f : ℂ → ℂ} {a C S₀ K B : ℝ} (ha : 0 < a)
    (hdiff : ∀ τ : ℂ, 0 < τ.re → DifferentiableAt ℂ f τ)
    (hgrowth : ∀ τ : ℂ, a ≤ τ.re → ‖f τ‖ ≤ K * Real.exp (B * ‖τ - a‖ ^ 2))
    (hray : ∀ r : ℝ, 0 ≤ r → ‖f ((a : ℂ) + r * Complex.exp (Real.pi / 4 * I))‖ ≤ S₀)
    (hC : ∀ b : ℝ, ‖f ((a : ℂ) + b * I)‖ ≤ C) {τ : ℂ} (hX : a ≤ τ.re) (hXY : τ.re - a ≤ τ.im) :
    ‖f τ‖ ≤ max C S₀ := by
  by_cases h0 : τ = a
  · refine le_max_of_le_left ?_
    have := hC 0
    rwa [Complex.ofReal_zero, zero_mul, add_zero, ← h0] at this
  · have hz0 : τ - a ≠ 0 := sub_ne_zero.2 h0
    have hzre : 0 ≤ (τ - a).re := by rw [sub_re, ofReal_re]; linarith
    have hzim : (τ - a).re ≤ (τ - a).im := by rw [sub_re, sub_im, ofReal_re, ofReal_im]; linarith
    have h1 : Real.pi / 4 ≤ (Complex.log (τ - a)).im := by
      rw [Complex.log_im]; exact pi_div_four_le_arg_of_re_le_im hz0 hzre hzim
    have h2 : (Complex.log (τ - a)).im ≤ Real.pi / 2 := by
      rw [Complex.log_im]; exact Complex.arg_le_pi_div_two_iff.2 (Or.inl hzre)
    have := norm_le_max_of_vertical_of_ray ha hdiff hgrowth hray hC h1 h2
    rwa [Complex.exp_log hz0, add_sub_cancel] at this

/-! ## The heat trace between the 45° ray and the vertical line -/

theorem norm_exp_mul_sub_sq (c : ℝ) (a : ℝ) (τ : ℂ) :
    ‖Complex.exp (c * (τ - a) ^ 2)‖ = Real.exp (c * ((τ.re - a) ^ 2 - τ.im ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im]
  ring

/-- **Quadratic vertical growth spreads to the sector.**  If `‖ν(a + ib)‖ ≤ C e^{c b²}` for every
`b`, then `‖ν(τ)‖ ≤ C₁ e^{c (Im τ)²}` whenever `0 ≤ Re τ − a ≤ Im τ`. -/
theorem exists_norm_xiGaussianHeatTraceC_le_sector_of_vertical {a c C : ℝ} (ha : 0 < a)
    (hc : 0 ≤ c)
    (hC : ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (c * b ^ 2)) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ τ : ℂ, a ≤ τ.re → τ.re - a ≤ τ.im →
      ‖xiGaussianHeatTraceC τ‖ ≤ C₁ * Real.exp (c * τ.im ^ 2) := by
  obtain ⟨S, hS⟩ := xiGaussianHeatTraceC_sector_bounded_six ha
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS (a : ℂ) (by simp) (by simp))
  set K₀ : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hK₀
  have hK₀0 : 0 ≤ K₀ := tsum_nonneg fun _ => by positivity
  set f : ℂ → ℂ := fun τ => xiGaussianHeatTraceC τ * Complex.exp (c * (τ - a) ^ 2) with hf
  have hdiff : ∀ τ : ℂ, 0 < τ.re → DifferentiableAt ℂ f τ := fun τ hτ =>
    (differentiableAt_xiGaussianHeatTraceC hτ).mul (by fun_prop)
  have hgrowth : ∀ τ : ℂ, a ≤ τ.re →
      ‖f τ‖ ≤ (4 / a * K₀) * Real.exp ((1 / a + c) * ‖τ - a‖ ^ 2) := by
    intro τ hτ
    have hτ0 : 0 < τ.re := ha.trans_le hτ
    have h1 := norm_xiGaussianHeatTraceC_le_growth hτ0
    rw [← hK₀] at h1
    have him : τ.im ^ 2 ≤ ‖τ - a‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
      nlinarith [sq_nonneg (τ.re - a)]
    have hre : (τ.re - a) ^ 2 ≤ ‖τ - a‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
      nlinarith [sq_nonneg τ.im]
    have he1 : Real.exp (τ.im ^ 2 / τ.re) ≤ Real.exp (‖τ - a‖ ^ 2 / a) :=
      Real.exp_le_exp.2 ((div_le_div_of_nonneg_left (sq_nonneg _) ha hτ).trans
        (div_le_div_of_nonneg_right him ha.le))
    have he2 : 4 / τ.re ≤ 4 / a := div_le_div_of_nonneg_left (by norm_num) ha hτ
    have he3 : Real.exp (c * ((τ.re - a) ^ 2 - τ.im ^ 2)) ≤ Real.exp (c * ‖τ - a‖ ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg τ.im]) hc)
    rw [hf]
    simp only
    rw [norm_mul, norm_exp_mul_sub_sq]
    calc ‖xiGaussianHeatTraceC τ‖ * Real.exp (c * ((τ.re - a) ^ 2 - τ.im ^ 2))
        ≤ (Real.exp (‖τ - a‖ ^ 2 / a) * (4 / a) * K₀) * Real.exp (c * ‖τ - a‖ ^ 2) := by
          refine mul_le_mul (h1.trans ?_) he3 (Real.exp_pos _).le (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul he1 he2 (by positivity) (Real.exp_pos _).le)
            hK₀0
      _ = (4 / a * K₀) * Real.exp ((1 / a + c) * ‖τ - a‖ ^ 2) := by
          rw [show (1 / a + c) * ‖τ - a‖ ^ 2 = ‖τ - a‖ ^ 2 / a + c * ‖τ - a‖ ^ 2 by ring,
            Real.exp_add]
          ring
  have hray : ∀ r : ℝ, 0 ≤ r → ‖f ((a : ℂ) + r * Complex.exp (Real.pi / 4 * I))‖ ≤ S := by
    intro r hr
    have he : Complex.exp (Real.pi / 4 * I) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) +
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * I := by
      rw [show (Real.pi / 4 * I : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
        Real.sin_pi_div_four]
    set τ : ℂ := (a : ℂ) + r * Complex.exp (Real.pi / 4 * I) with hτ
    have hτre : τ.re = a + r * (Real.sqrt 2 / 2) := by
      rw [hτ, he]; simp
    have hτim : τ.im = r * (Real.sqrt 2 / 2) := by
      rw [hτ, he]; simp
    have hs2 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    have hsec := hS τ (by rw [hτre]; nlinarith) (by
      rw [hτre, hτim, abs_of_nonneg (mul_nonneg hr hs2)]; nlinarith)
    rw [hf]
    simp only
    rw [norm_mul, norm_exp_mul_sub_sq, hτre, hτim]
    have : c * ((a + r * (Real.sqrt 2 / 2) - a) ^ 2 - (r * (Real.sqrt 2 / 2)) ^ 2) = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
    exact hsec
  have hvert : ∀ b : ℝ, ‖f ((a : ℂ) + b * I)‖ ≤ C := by
    intro b
    rw [hf]
    simp only
    rw [norm_mul, norm_exp_mul_sub_sq]
    have h1 := hC b
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at h1 ⊢
    rw [show c * ((0 : ℝ) ^ 2 - b ^ 2) = -(c * b ^ 2) by ring, Real.exp_neg, ← div_eq_mul_inv,
      div_le_iff₀ (Real.exp_pos _)]
    exact h1
  refine ⟨max C S, le_max_of_le_right hS0, fun τ hX hXY => ?_⟩
  have hfτ := norm_le_max_of_vertical_of_ray_rect ha hdiff hgrowth hray hvert hX hXY
  rw [hf] at hfτ
  simp only at hfτ
  rw [norm_mul, norm_exp_mul_sub_sq] at hfτ
  have hpos : 0 < Real.exp (c * ((τ.re - a) ^ 2 - τ.im ^ 2)) := Real.exp_pos _
  have hν : ‖xiGaussianHeatTraceC τ‖ ≤
      max C S * Real.exp (-(c * ((τ.re - a) ^ 2 - τ.im ^ 2))) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hfτ
  refine hν.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (le_max_of_le_right hS0))
  nlinarith [sq_nonneg (τ.re - a)]

/-! ## Truncation of the trace -/

/-- Beyond height `Γ ≥ 4|Im τ|/a` the heat terms are dominated by the real-time terms at `3a/4`. -/
theorem norm_xiGaussianHeatTermC_le_tail {a Γ : ℝ} (ha : 0 < a) {τ : ℂ} (h1 : a ≤ τ.re)
    (h2 : τ.re ≤ 2 * a) (h3 : 4 * |τ.im| ≤ a * Γ) {q : XiZeroCopy}
    (hq : Γ < |(xiSpectralPoint q).re|) :
    ‖xiGaussianHeatTermC τ q‖ ≤
      Real.exp (a / 2) * ‖xiGaussianHeatTermC ((3 * a / 4 : ℝ) : ℂ) q‖ := by
  rw [norm_xiGaussianHeatTermC, norm_xiGaussianHeatTermC, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hq4 := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  set γ := (xiSpectralPoint q).re with hγ
  set η := (xiSpectralPoint q).im with hη'
  have hwre : (xiSpectralPoint q ^ (2 : ℕ)).re = γ ^ 2 - η ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hwim : (xiSpectralPoint q ^ (2 : ℕ)).im = 2 * γ * η := by
    rw [pow_two, Complex.mul_im]; ring
  rw [hwre, hwim, Complex.ofReal_re, Complex.ofReal_im]
  have hη2 : η ^ 2 ≤ 1 / 4 := by
    rw [him, neg_sq]; exact hq4.le
  have h2η : 2 * |η| ≤ 1 := by
    nlinarith [sq_abs η, abs_nonneg η, sq_nonneg (2 * |η| - 1)]
  have hy : |τ.im| ≤ a * |γ| / 4 := by
    nlinarith [mul_lt_mul_of_pos_left hq ha]
  have hcross : τ.im * (2 * γ * η) ≤ τ.re * γ ^ 2 / 4 := by
    have h4 : |τ.im * (2 * γ * η)| ≤ |τ.im| * |γ| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have h8 := mul_le_mul_of_nonneg_left h2η (mul_nonneg (abs_nonneg τ.im) (abs_nonneg γ))
      linarith
    have h5 : |τ.im| * |γ| ≤ τ.re * γ ^ 2 / 4 := by
      have h6 : |τ.im| * |γ| ≤ a * |γ| / 4 * |γ| := mul_le_mul_of_nonneg_right hy (abs_nonneg _)
      have h7 : a * |γ| / 4 * |γ| = a * γ ^ 2 / 4 := by rw [← sq_abs γ]; ring
      nlinarith [sq_nonneg γ]
    exact (le_abs_self _).trans (h4.trans h5)
  have hA : 0 ≤ (τ.re - a) * γ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hB : 0 ≤ (τ.re - 3 * a / 4) * (1 / 4 - η ^ 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **Tail bound.**  For `a ≤ Re τ ≤ 2a` and `4 |Im τ| ≤ aΓ`, the copies with `|γ| > Γ` contribute at
most `e^{a/2} Σ_q |e^{-(3a/4) w_q}|`. -/
theorem norm_xiGaussianHeatTraceC_sub_sum_le {a Γ : ℝ} (ha : 0 < a) {τ : ℂ} (h1 : a ≤ τ.re)
    (h2 : τ.re ≤ 2 * a) (h3 : 4 * |τ.im| ≤ a * Γ) :
    ‖xiGaussianHeatTraceC τ - ∑ q ∈ xiCopiesBelow Γ, xiGaussianHeatTermC τ q‖ ≤
      Real.exp (a / 2) * ∑' q : XiZeroCopy, ‖xiGaussianHeatTermC ((3 * a / 4 : ℝ) : ℂ) q‖ := by
  have hτ0 : 0 < τ.re := ha.trans_le h1
  have hs := summable_norm_xiGaussianHeatTermC hτ0
  have hsum := hs.of_norm.sum_add_tsum_compl (s := xiCopiesBelow Γ)
  rw [xiGaussianHeatTraceC, ← hsum, add_sub_cancel_left]
  have hg : Summable (fun q : XiZeroCopy => ‖xiGaussianHeatTermC ((3 * a / 4 : ℝ) : ℂ) q‖) :=
    summable_norm_xiGaussianHeatTermC (by rw [ofReal_re]; positivity)
  refine (norm_tsum_le_tsum_norm (hs.subtype _)).trans ?_
  refine (Summable.tsum_le_tsum (fun x => ?_) (hs.subtype _)
    ((hg.mul_left (Real.exp (a / 2))).subtype _)).trans ?_
  · have hx2 := x.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, mem_xiCopiesBelow, not_le] at hx2
    have hx : Γ < |(xiSpectralPoint x.1).re| := by
      rwa [zeroOrdinate, ← xiSpectralPoint_re_eq] at hx2
    exact norm_xiGaussianHeatTermC_le_tail ha h1 h2 h3 hx
  · rw [← tsum_mul_left]
    exact Summable.tsum_subtype_le
      (fun q => Real.exp (a / 2) * ‖xiGaussianHeatTermC ((3 * a / 4 : ℝ) : ℂ) q‖) _
      (fun _ => by positivity) (hg.mul_left _)

/-! ## Power sums along a ray from the origin -/

/-- The Turán denominator `e N (6(N+1)(M+2N+2))^N`. -/
def turanDenominator (M N : ℕ) : ℝ :=
  Real.exp 1 * N * (6 * (N + 1) * ((M : ℝ) + 2 * N + 2)) ^ N

/-- **The truncated trace on a ray is a power sum.**  For a finite set `K` of copies containing `q₀`
and every `M`, some `ν ∈ [M+1, M+#K]` has
`‖Σ_{q∈K} e^{-ν τ₁ w_q}‖ ≥ ‖e^{-ν τ₁ w_{q₀}}‖ / (2 · turanDenominator M #K)`. -/
theorem exists_norm_finsum_xiGaussianHeatTermC_ge (K : Finset XiZeroCopy) {q₀ : XiZeroCopy}
    (hq₀ : q₀ ∈ K) (τ₁ : ℂ) (M : ℕ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + K.card ∧
      ‖xiGaussianHeatTermC ((ν : ℂ) * τ₁) q₀‖ / (2 * turanDenominator M K.card) ≤
        ‖∑ q ∈ K, xiGaussianHeatTermC ((ν : ℂ) * τ₁) q‖ := by
  have hpow : ∀ (ν : ℕ) (q : XiZeroCopy),
      xiGaussianHeatTermC τ₁ q ^ ν = xiGaussianHeatTermC ((ν : ℂ) * τ₁) q := by
    intro ν q
    rw [xiGaussianHeatTermC, xiGaussianHeatTermC, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hZ : 0 < ‖xiGaussianHeatTermC τ₁ q₀‖ := by
    rw [xiGaussianHeatTermC, Complex.norm_exp]; exact Real.exp_pos _
  obtain ⟨ν, h1, h2, h3⟩ := GaloisForLFunctions.HTGeometry.exists_norm_powerSum_ge_scaled K
    (fun q => xiGaussianHeatTermC τ₁ q) hZ ⟨q₀, hq₀, le_rfl⟩ M
  refine ⟨ν, h1, h2, ?_⟩
  rw [← norm_pow, hpow] at h3
  simp only [hpow] at h3
  exact h3

theorem turanDenominator_pos {M N : ℕ} (hN : 1 ≤ N) : 0 < turanDenominator M N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold turanDenominator
  positivity

/-! ## Explicit growth of the Turán loss -/

theorem rpow_five_fourths_eq {x : ℝ} (hx : 0 < x) :
    x ^ (5 / 4 : ℝ) = x * x ^ (1 / 4 : ℝ) := by
  rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hx, Real.rpow_one]

/-- `log(2 · turanDenominator (N m₀) N) ≤ (log(6(m₀+4)) + 14)(N+1)^{5/4}`. -/
theorem log_two_mul_turanDenominator_le {N m₀ : ℕ} (hN : 1 ≤ N) :
    Real.log (2 * turanDenominator (N * m₀) N) ≤
      (Real.log (6 * ((m₀ : ℝ) + 4)) + 14) * ((N : ℝ) + 1) ^ (5 / 4 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
  set X : ℝ := 6 * ((N : ℝ) + 1) * (((N * m₀ : ℕ) : ℝ) + 2 * N + 2) with hX
  have hX0 : 0 < X := by rw [hX]; positivity
  have hXle : X ≤ 6 * ((m₀ : ℝ) + 4) * ((N : ℝ) + 1) ^ 2 := by
    rw [hX]; push_cast; nlinarith [mul_nonneg hN0.le hm0]
  have hlog : Real.log (2 * turanDenominator (N * m₀) N) =
      Real.log 2 + 1 + Real.log N + N * Real.log X := by
    unfold turanDenominator
    rw [← hX, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]
    ring
  set R : ℝ := ((N : ℝ) + 1) ^ (1 / 4 : ℝ) with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow (by linarith) (by norm_num)
  have hL0 : 0 ≤ Real.log (6 * ((m₀ : ℝ) + 4)) := Real.log_nonneg (by linarith)
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ 4 * R := log_le_four_mul_rpow (by positivity)
  have hlogN : Real.log N ≤ 4 * R :=
    (Real.log_le_log hN0 (by linarith)).trans hlogN1
  have hlogX : Real.log X ≤ Real.log (6 * ((m₀ : ℝ) + 4)) + 2 * Real.log ((N : ℝ) + 1) := by
    refine (Real.log_le_log hX0 hXle).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  rw [hlog, rpow_five_fourths_eq (by positivity), ← hR]
  have hNX : (N : ℝ) * Real.log X ≤
      (N : ℝ) * (Real.log (6 * ((m₀ : ℝ) + 4)) + 8 * R) :=
    mul_le_mul_of_nonneg_left (by linarith) hN0.le
  nlinarith [mul_le_mul_of_nonneg_left hR1 hL0, mul_nonneg hN0.le hL0,
    mul_le_mul_of_nonneg_right (show (N : ℝ) ≤ N + 1 by linarith) (by linarith : (0 : ℝ) ≤ R)]

/-- The zero copies with `|γ| ≤ Γ` number at most `(20(|A| + 4) + 1)(Γ + 6)^{5/4} − 1`. -/
theorem card_xiCopiesBelow_add_one_le {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    ((xiCopiesBelow Γ).card : ℝ) + 1 ≤
      (20 * (|xiLineTwoLogDerivConstant| + 4) + 1) * (Γ + 6) ^ (5 / 4 : ℝ) := by
  have h := card_xiCopiesBelow_le_log hΓ
  set A := xiLineTwoLogDerivConstant
  set R : ℝ := (Γ + 6) ^ (1 / 4 : ℝ) with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog : Real.log (Γ + 6) ≤ 4 * R := log_le_four_mul_rpow (by linarith)
  have hA : A ≤ |A| * R := (le_abs_self A).trans (le_mul_of_one_le_right (abs_nonneg A) hR1)
  have h1 : 20 * (Γ + 1) * (A + Real.log (Γ + 6)) ≤ 20 * (Γ + 6) * ((|A| + 4) * R) := by
    have h2 : A + Real.log (Γ + 6) ≤ (|A| + 4) * R := by nlinarith
    have h3 : 0 ≤ (|A| + 4) * R := by positivity
    nlinarith
  rw [rpow_five_fourths_eq (by linarith), ← hR]
  nlinarith [abs_nonneg A]

/-- A quadratic beats `D (G + 1)^{25/16} + L` from some threshold on. -/
theorem exists_threshold_quadratic_dominates {κ D L : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ G : ℝ, H ≤ G → D * (G + 1) ^ (25 / 16 : ℝ) + L < κ * G ^ 2 := by
  set X : ℝ := (4 * D + L + 1) / κ with hX
  have hX0 : 0 < X := by rw [hX]; positivity
  refine ⟨max 1 (X ^ (16 / 7 : ℝ)), le_max_left _ _, fun G hG => ?_⟩
  have hG1 : 1 ≤ G := (le_max_left _ _).trans hG
  have hG0 : 0 < G := by linarith
  have hGX : X ≤ G ^ (7 / 16 : ℝ) := by
    have h1 : X ^ (16 / 7 : ℝ) ≤ G := (le_max_right _ _).trans hG
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 7 / 16)
    rwa [← Real.rpow_mul hX0.le, show (16 / 7 : ℝ) * (7 / 16) = 1 by norm_num,
      Real.rpow_one] at h2
  have hsplit : G ^ 2 = G ^ (7 / 16 : ℝ) * G ^ (25 / 16 : ℝ) := by
    rw [← Real.rpow_add hG0, show (7 / 16 : ℝ) + 25 / 16 = 2 by norm_num, Real.rpow_two]
  have hG25 : 1 ≤ G ^ (25 / 16 : ℝ) := Real.one_le_rpow hG1 (by norm_num)
  have hG1' : (G + 1) ^ (25 / 16 : ℝ) ≤ 4 * G ^ (25 / 16 : ℝ) := by
    calc (G + 1) ^ (25 / 16 : ℝ) ≤ (2 * G) ^ (25 / 16 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 ^ (25 / 16 : ℝ) * G ^ (25 / 16 : ℝ) := Real.mul_rpow (by norm_num) hG0.le
      _ ≤ 4 * G ^ (25 / 16 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (2 : ℝ) ^ (25 / 16 : ℝ) ≤ 2 ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := by rw [Real.rpow_two]; norm_num
  have hκX : κ * X = 4 * D + L + 1 := by rw [hX]; field_simp
  rw [hsplit]
  have h1 : (4 * D + L + 1) * G ^ (25 / 16 : ℝ) ≤ κ * (G ^ (7 / 16 : ℝ) * G ^ (25 / 16 : ℝ)) := by
    rw [← mul_assoc, ← hκX]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGX hκ.le) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hG1' hD]

/-! ## The lower half of the quadratic law -/

/-- Every zero copy has a symmetric copy with the same `|γ|`, `|β − ½|` and `γ (β − ½)`-orientation
making `Im w ≥ 0`. -/
theorem exists_xiZeroCopy_oriented (q : XiZeroCopy) :
    ∃ q' : XiZeroCopy, |(xiSpectralPoint q').re| = |(xiSpectralPoint q).re| ∧
      (xiSpectralPoint q').im ^ 2 = (xiSpectralPoint q).im ^ 2 ∧
      0 ≤ (xiSpectralPoint q').re * (xiSpectralPoint q').im := by
  by_cases h : 0 ≤ (xiSpectralPoint q).re * (xiSpectralPoint q).im
  · exact ⟨q, rfl, rfl, h⟩
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_, ?_, ?_⟩
    · rw [xiSpectralPoint_lineConj, Complex.conj_re]
    · rw [xiSpectralPoint_lineConj, Complex.conj_im, neg_sq]
    · rw [xiSpectralPoint_lineConj, Complex.conj_re, Complex.conj_im]
      push Not at h
      linarith

theorem natCast_mul_div_re_im (x Y : ℝ) {n : ℕ} (hn : 0 < n) (ν : ℕ) :
    ((ν : ℂ) * ((((x : ℝ) : ℂ) + (Y : ℂ) * I) / (n : ℂ))).re = (ν : ℝ) / n * x ∧
      ((ν : ℂ) * ((((x : ℝ) : ℂ) + (Y : ℂ) * I) / (n : ℂ))).im = (ν : ℝ) / n * Y := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : (ν : ℂ) * ((((x : ℝ) : ℂ) + (Y : ℂ) * I) / (n : ℂ)) =
      (((ν : ℝ) / n : ℝ) : ℂ) * (((x : ℝ) : ℂ) + (Y : ℂ) * I) := by
    push_cast; field_simp
  rw [h, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  simp

/-- The sampling parameter `t = ν/(M+N)` lies in `[1/(1+μ), 1]` once `μ M ≥ N`. -/
theorem sample_parameter_bounds {M N ν : ℕ} {μ : ℝ} (hμ : 0 < μ) (hMN : (N : ℝ) ≤ μ * M)
    (hN : 1 ≤ N) (h1 : M + 1 ≤ ν) (h2 : ν ≤ M + N) :
    (ν : ℝ) / ((M + N : ℕ) : ℝ) ≤ 1 ∧ 1 ≤ (ν : ℝ) / ((M + N : ℕ) : ℝ) * (1 + μ) := by
  have hpos : (0 : ℝ) < ((M + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + N)
  have h1' : (M : ℝ) + 1 ≤ ν := by exact_mod_cast h1
  have h2' : (ν : ℝ) ≤ M + N := by exact_mod_cast h2
  constructor
  · rw [div_le_one hpos]; push_cast; exact h2'
  · rw [div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
    push_cast
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith

/-- The exponent algebra: with `μ = ε/(4+3ε)` and `E²/c > a(1+ε)`,
`E₀/(1+μ) − c Y² ≥ a ε G²/2` where `E₀ = −a(1+μ)(G² − E²) + 2 G E Y` and `Y = G E / c`. -/
theorem vertical_exponent_gap {a c ε G E : ℝ} (ha : 0 < a) (hc : 0 < c) (hε : 0 < ε)
    (hbad : a * (1 + ε) < E ^ 2 / c) :
    a * ε * G ^ 2 / 2 ≤
      (-(a * (1 + ε / (4 + 3 * ε))) * (G ^ 2 - E ^ 2) + G * E / c * (2 * (G * E))) /
          (1 + ε / (4 + 3 * ε)) - c * (G * E / c) ^ 2 := by
  set μ : ℝ := ε / (4 + 3 * ε) with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hμ3 : μ ≤ 1 / 3 := by rw [hμ, div_le_iff₀ (by positivity)]; linarith
  have h1μ : 0 < 1 + μ := by linarith
  have hratio : (1 - μ) / (1 + μ) = (1 + ε / 2) / (1 + ε) := by
    rw [div_eq_div_iff h1μ.ne' (by linarith), hμ]; field_simp; ring
  have hcY : c * (G * E / c) ^ 2 = G ^ 2 * (E ^ 2 / c) := by field_simp
  have hE0' : (-(a * (1 + μ)) * (G ^ 2 - E ^ 2) + G * E / c * (2 * (G * E))) / (1 + μ) =
      -(a * (G ^ 2 - E ^ 2)) + 2 * (G ^ 2 * (E ^ 2 / c)) / (1 + μ) := by
    field_simp
  rw [hcY, hE0']
  have h3 : 2 * (G ^ 2 * (E ^ 2 / c)) / (1 + μ) - G ^ 2 * (E ^ 2 / c) =
      G ^ 2 * (E ^ 2 / c) * ((1 - μ) / (1 + μ)) := by field_simp; ring
  have h4 : G ^ 2 * (a * (1 + ε)) * ((1 - μ) / (1 + μ)) = G ^ 2 * a * (1 + ε / 2) := by
    rw [hratio]; field_simp
  have h5 : G ^ 2 * (a * (1 + ε)) * ((1 - μ) / (1 + μ)) ≤
      G ^ 2 * (E ^ 2 / c) * ((1 - μ) / (1 + μ)) := by
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (by linarith) h1μ.le)
    exact mul_le_mul_of_nonneg_left hbad.le (sq_nonneg G)
  nlinarith [sq_nonneg E, sq_nonneg G]

/-- **The single-copy inequality.**  Under the sector and tail bounds, a copy `z₀` with
`Re z₀ Im z₀ ≥ 0`, `(Im z₀)² > ac(1+ε)` and `|Re z₀| ≥ 2√(ac)` satisfies
`a ε (Re z₀)²/2 ≤ log(2 · turanDenominator (N m₀) N) + log(C₁ + T₀ + 1)`, `N = #{|γ| ≤ Γ}`. -/
theorem vertical_quadratic_copy_bound {a c C₁ T₀ ε : ℝ} (ha : 0 < a) (hc : 0 < c) (hε : 0 < ε)
    (hC₁ : 0 ≤ C₁) (hT₀ : 0 ≤ T₀)
    (hsector : ∀ τ : ℂ, a ≤ τ.re → τ.re - a ≤ τ.im →
      ‖xiGaussianHeatTraceC τ‖ ≤ C₁ * Real.exp (c * τ.im ^ 2))
    (htail : ∀ Γ : ℝ, ∀ τ : ℂ, a ≤ τ.re → τ.re ≤ 2 * a → 4 * |τ.im| ≤ a * Γ →
      ‖xiGaussianHeatTraceC τ - ∑ q ∈ xiCopiesBelow Γ, xiGaussianHeatTermC τ q‖ ≤ T₀)
    {m₀ : ℕ} (hm₀ : (4 + 3 * ε) / ε ≤ m₀)
    {q₀ : XiZeroCopy} (horient : 0 ≤ (xiSpectralPoint q₀).re * (xiSpectralPoint q₀).im)
    (hbad : a * c * (1 + ε) < (xiSpectralPoint q₀).im ^ 2)
    (hG : 2 * Real.sqrt (a * c) ≤ |(xiSpectralPoint q₀).re|) {Γ : ℝ}
    (hΓ : Γ = |(xiSpectralPoint q₀).re| * (1 + 4 * |(xiSpectralPoint q₀).im| / (a * c)) + 1) :
    a * ε * (xiSpectralPoint q₀).re ^ 2 / 2 ≤
      Real.log (2 * turanDenominator ((xiCopiesBelow Γ).card * m₀) (xiCopiesBelow Γ).card) +
        Real.log (C₁ + T₀ + 1) := by
  set z := xiSpectralPoint q₀ with hz
  set G := |z.re| with hGdef
  set E := |z.im| with hEdef
  have hGE : z.re * z.im = G * E := by rw [hGdef, hEdef, ← abs_mul, abs_of_nonneg horient]
  have hE2 : E ^ 2 = z.im ^ 2 := sq_abs _
  have hG2 : G ^ 2 = z.re ^ 2 := sq_abs _
  have hac : 0 < a * c := mul_pos ha hc
  have hsac : 0 < Real.sqrt (a * c) := Real.sqrt_pos.2 hac
  have hsac2 : Real.sqrt (a * c) * Real.sqrt (a * c) = a * c := Real.mul_self_sqrt hac.le
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hG
  have hEsq : a * c * (1 + ε) < E ^ 2 := by rw [hE2]; exact hbad
  have hbad' : a * (1 + ε) < E ^ 2 / c := by rw [lt_div_iff₀ hc]; linarith
  have hE0 : 0 < E := by
    rcases (abs_nonneg z.im).eq_or_lt with h | h
    · rw [← hEdef] at h; rw [← h] at hEsq; norm_num at hEsq
      linarith [mul_pos hac (show (0 : ℝ) < 1 + ε by linarith)]
    · exact h
  have hEge : Real.sqrt (a * c) ≤ E := by
    rw [show E = Real.sqrt (E ^ 2) by rw [Real.sqrt_sq hE0.le]]
    exact Real.sqrt_le_sqrt (by linarith [mul_pos hac hε])
  set μ : ℝ := ε / (4 + 3 * ε) with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hμ3 : μ ≤ 1 / 3 := by rw [hμ, div_le_iff₀ (by positivity)]; linarith
  have hμm : 1 ≤ μ * m₀ := by
    have h1 : μ * ((4 + 3 * ε) / ε) = 1 := by rw [hμ]; field_simp
    rw [← h1]; exact mul_le_mul_of_nonneg_left hm₀ hμ0.le
  set Y : ℝ := G * E / c with hY
  have hY0 : 0 ≤ Y := by positivity
  have hY2a : 2 * a ≤ Y := by
    rw [hY, le_div_iff₀ hc]
    have h1 : 2 * Real.sqrt (a * c) * Real.sqrt (a * c) ≤ G * E :=
      mul_le_mul hG hEge hsac.le hG0.le
    linarith
  have hΓY : 4 * Y ≤ a * Γ := by
    have h1 : a * Γ = a * G + 4 * Y + a := by rw [hΓ, hY]; field_simp
    rw [h1]; linarith [mul_pos ha hG0]
  set K := xiCopiesBelow Γ with hK
  have hq₀K : q₀ ∈ K := by
    rw [hK, mem_xiCopiesBelow, zeroOrdinate, ← xiSpectralPoint_re_eq, ← hz, ← hGdef, hΓ]
    have : 0 ≤ G * (4 * E / (a * c)) := by positivity
    linarith
  set N := K.card with hN
  have hN1 : 1 ≤ N := Finset.card_pos.2 ⟨q₀, hq₀K⟩
  set M := N * m₀ with hM
  have hμM : (N : ℝ) ≤ μ * M := by
    rw [hM]; push_cast
    linarith [mul_le_mul_of_nonneg_left hμm (Nat.cast_nonneg (α := ℝ) N)]
  obtain ⟨ν, hν1, hν2, hν⟩ := exists_norm_finsum_xiGaussianHeatTermC_ge K hq₀K
    ((((a * (1 + μ) : ℝ) : ℂ) + (Y : ℂ) * I) / ((M + N : ℕ) : ℂ)) M
  set t : ℝ := (ν : ℝ) / ((M + N : ℕ) : ℝ) with ht
  obtain ⟨hτre, hτim⟩ := natCast_mul_div_re_im (a * (1 + μ)) Y (n := M + N) (by omega) ν
  obtain ⟨ht1, ht0⟩ := sample_parameter_bounds hμ0 hμM hN1 hν1 hν2
  rw [← ht] at hτre hτim ht1 ht0
  set τ : ℂ := (ν : ℂ) * ((((a * (1 + μ) : ℝ) : ℂ) + (Y : ℂ) * I) / ((M + N : ℕ) : ℂ))
    with hτdef
  have htpos : 0 < t :=
    (pos_iff_pos_of_mul_pos (lt_of_lt_of_le one_pos ht0)).2 (by linarith)
  have ht34 : 3 / 4 ≤ t := by linarith [mul_le_mul_of_nonneg_left hμ3 htpos.le]
  have hta : t * (a * (1 + μ)) ≤ a * (1 + μ) := by
    have := mul_le_mul_of_nonneg_right ht1 (show 0 ≤ a * (1 + μ) by positivity)
    linarith
  have hre1 : a ≤ τ.re := by
    rw [hτre]; linarith [mul_le_mul_of_nonneg_left ht0 ha.le]
  have hre2 : τ.re ≤ 2 * a := by rw [hτre]; linarith [mul_le_mul_of_nonneg_left hμ3 ha.le]
  have hsec : τ.re - a ≤ τ.im := by
    rw [hτre, hτim]
    linarith [mul_le_mul_of_nonneg_right ht34 hY0, mul_le_mul_of_nonneg_left hμ3 ha.le]
  have htl : 4 * |τ.im| ≤ a * Γ := by
    rw [hτim, abs_of_nonneg (by positivity)]
    linarith [mul_le_mul_of_nonneg_right ht1 hY0]
  -- upper bound for the truncated sum
  have hup : ‖∑ q ∈ K, xiGaussianHeatTermC τ q‖ ≤ (C₁ + T₀ + 1) * Real.exp (c * Y ^ 2) := by
    have h1 := hsector τ hre1 hsec
    have h2 := htail Γ τ hre1 hre2 htl
    have h3 : ‖∑ q ∈ K, xiGaussianHeatTermC τ q‖ ≤
        ‖xiGaussianHeatTraceC τ‖ + ‖xiGaussianHeatTraceC τ - ∑ q ∈ K, xiGaussianHeatTermC τ q‖ := by
      have := norm_sub_le (xiGaussianHeatTraceC τ)
        (xiGaussianHeatTraceC τ - ∑ q ∈ K, xiGaussianHeatTermC τ q)
      rwa [sub_sub_cancel] at this
    have h4 : Real.exp (c * τ.im ^ 2) ≤ Real.exp (c * Y ^ 2) := by
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hc.le)
      rw [hτim]
      exact pow_le_pow_left₀ (by positivity) (by linarith [mul_le_mul_of_nonneg_right ht1 hY0]) 2
    have h5 : 1 ≤ Real.exp (c * Y ^ 2) := Real.one_le_exp (by positivity)
    calc ‖∑ q ∈ K, xiGaussianHeatTermC τ q‖ ≤ C₁ * Real.exp (c * Y ^ 2) + T₀ :=
          h3.trans (add_le_add (h1.trans (mul_le_mul_of_nonneg_left h4 hC₁)) h2)
      _ ≤ (C₁ + T₀ + 1) * Real.exp (c * Y ^ 2) := by
          linarith [mul_le_mul_of_nonneg_left h5 hT₀, (Real.exp_pos (c * Y ^ 2)).le]
  -- lower bound for the chosen copy
  set E0 : ℝ := -(a * (1 + μ)) * (G ^ 2 - E ^ 2) + Y * (2 * (G * E)) with hE0def
  have hterm : ‖xiGaussianHeatTermC τ q₀‖ = Real.exp (t * E0) := by
    rw [norm_xiGaussianHeatTermC, hτre, hτim]
    congr 1
    have hwre : (z ^ (2 : ℕ)).re = G ^ 2 - E ^ 2 := by
      rw [pow_two, Complex.mul_re, hG2, hE2]; ring
    have hwim : (z ^ (2 : ℕ)).im = 2 * (G * E) := by
      rw [pow_two, Complex.mul_im, ← hGE]; ring
    rw [← hz, hwre, hwim, hE0def]
    ring
  have hE0pos : 0 ≤ E0 := by
    rw [hE0def, hY]
    have h2 : a * (1 + μ) ≤ 2 * (E ^ 2 / c) := by
      linarith [mul_le_mul_of_nonneg_left hμ3 ha.le, mul_pos ha hε]
    have h1 : a * (1 + μ) * G ^ 2 ≤ 2 * (E ^ 2 / c) * G ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg G)
    have h3 : G * E / c * (2 * (G * E)) = 2 * (E ^ 2 / c) * G ^ 2 := by ring
    have h4 : 0 ≤ a * (1 + μ) * E ^ 2 := by positivity
    linarith
  have hexp_low : Real.exp (E0 / (1 + μ)) ≤ ‖xiGaussianHeatTermC τ q₀‖ := by
    rw [hterm]
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_le_mul_of_nonneg_left ht0 hE0pos]
  have hB := turanDenominator_pos (M := M) hN1
  have hmain : Real.exp (E0 / (1 + μ)) ≤
      2 * turanDenominator M N * ((C₁ + T₀ + 1) * Real.exp (c * Y ^ 2)) := by
    refine hexp_low.trans ?_
    have h1 := hν
    rw [div_le_iff₀ (by positivity)] at h1
    calc ‖xiGaussianHeatTermC τ q₀‖
        ≤ ‖∑ q ∈ K, xiGaussianHeatTermC τ q‖ * (2 * turanDenominator M N) := h1
      _ ≤ (C₁ + T₀ + 1) * Real.exp (c * Y ^ 2) * (2 * turanDenominator M N) :=
          mul_le_mul_of_nonneg_right hup (by positivity)
      _ = _ := by ring
  have hlog := Real.log_le_log (Real.exp_pos _) hmain
  rw [Real.log_exp, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  have halg := vertical_exponent_gap (G := G) ha hc hε hbad'
  rw [← hμ, ← hY, ← hE0def] at halg
  rw [← hG2]
  linarith

/-- The Turán loss for a copy at height `G` is `O((G + 1)^{25/16})`. -/
theorem log_turanDenominator_copy_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (m₀ : ℕ)
    (q₀ : XiZeroCopy) {Γ : ℝ}
    (hΓ : Γ = |(xiSpectralPoint q₀).re| * (1 + 4 * |(xiSpectralPoint q₀).im| / (a * c)) + 1) :
    Real.log (2 * turanDenominator ((xiCopiesBelow Γ).card * m₀) (xiCopiesBelow Γ).card) ≤
      (Real.log (6 * ((m₀ : ℝ) + 4)) + 14) *
        ((20 * (|xiLineTwoLogDerivConstant| + 4) + 1) * (7 + 2 / (a * c)) ^ (5 / 4 : ℝ)) ^
          (5 / 4 : ℝ) * (|(xiSpectralPoint q₀).re| + 1) ^ (25 / 16 : ℝ) := by
  set G := |(xiSpectralPoint q₀).re| with hG
  have hG0 : 0 ≤ G := abs_nonneg _
  have hac : 0 < a * c := mul_pos ha hc
  set D₁ : ℝ := 20 * (|xiLineTwoLogDerivConstant| + 4) + 1 with hD₁
  have hD₁0 : 1 ≤ D₁ := by rw [hD₁]; have := abs_nonneg xiLineTwoLogDerivConstant; linarith
  set D₂ : ℝ := 7 + 2 / (a * c) with hD₂
  have h2ac : 0 ≤ 2 / (a * c) := by positivity
  have hD₂0 : 1 ≤ D₂ := by rw [hD₂]; linarith
  have hN1 : 1 ≤ (xiCopiesBelow Γ).card := by
    refine Finset.card_pos.2 ⟨q₀, ?_⟩
    rw [mem_xiCopiesBelow, zeroOrdinate, ← xiSpectralPoint_re_eq, ← hG, hΓ]
    have : 0 ≤ G * (4 * |(xiSpectralPoint q₀).im| / (a * c)) := by positivity
    nlinarith
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hE : |(xiSpectralPoint q₀).im| ≤ 1 / 2 := by
    have h4 := xi_divisor_support_centered_re_sq_lt_quarter q₀.1
    have him' : (xiSpectralPoint q₀).im = -((q₀.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    have h5 : (xiSpectralPoint q₀).im ^ 2 ≤ 1 / 4 := by rw [him', neg_sq]; exact h4.le
    nlinarith [sq_abs (xiSpectralPoint q₀).im, abs_nonneg (xiSpectralPoint q₀).im]
  have hΓ6 : Γ + 6 ≤ D₂ * (G + 1) := by
    have h1 : 4 * |(xiSpectralPoint q₀).im| / (a * c) ≤ 2 / (a * c) :=
      div_le_div_of_nonneg_right (by linarith) hac.le
    rw [hΓ, hD₂]
    nlinarith [mul_le_mul_of_nonneg_left h1 hG0]
  have hcount := card_xiCopiesBelow_add_one_le hΓ0
  rw [← hD₁] at hcount
  have h1 : ((xiCopiesBelow Γ).card : ℝ) + 1 ≤ D₁ * D₂ ^ (5 / 4 : ℝ) * (G + 1) ^ (5 / 4 : ℝ) := by
    refine hcount.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hΓ6 (by norm_num)
  have hNG : (((xiCopiesBelow Γ).card : ℝ) + 1) ^ (5 / 4 : ℝ) ≤
      (D₁ * D₂ ^ (5 / 4 : ℝ)) ^ (5 / 4 : ℝ) * (G + 1) ^ (25 / 16 : ℝ) := by
    calc (((xiCopiesBelow Γ).card : ℝ) + 1) ^ (5 / 4 : ℝ)
        ≤ (D₁ * D₂ ^ (5 / 4 : ℝ) * (G + 1) ^ (5 / 4 : ℝ)) ^ (5 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      _ = (D₁ * D₂ ^ (5 / 4 : ℝ)) ^ (5 / 4 : ℝ) * (G + 1) ^ (25 / 16 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith)]
          norm_num
  have hlogB := log_two_mul_turanDenominator_le (m₀ := m₀) hN1
  have hD₀0 : 0 ≤ Real.log (6 * ((m₀ : ℝ) + 4)) + 14 := by
    have : 0 ≤ Real.log (6 * ((m₀ : ℝ) + 4)) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m₀; linarith)
    linarith
  refine hlogB.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hNG hD₀0

/-- **The lower half of the vertical quadratic law.**  If `‖ν(a + ib)‖ ≤ C e^{c b²}` for every real
`b`, then for every `ε > 0` all zero copies above some height satisfy `(β − ½)² ≤ a c (1 + ε)`. -/
theorem xiSpectralPoint_im_sq_le_of_vertical_quadratic {a c C : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hC : ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (c * b ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ, ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| →
      (xiSpectralPoint q).im ^ 2 ≤ a * c * (1 + ε) := by
  obtain ⟨C₁, hC₁, hsector⟩ := exists_norm_xiGaussianHeatTraceC_le_sector_of_vertical ha hc.le hC
  set T₀ : ℝ := Real.exp (a / 2) *
    ∑' q : XiZeroCopy, ‖xiGaussianHeatTermC ((3 * a / 4 : ℝ) : ℂ) q‖ with hT₀
  have hT₀0 : 0 ≤ T₀ :=
    mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => norm_nonneg _)
  have htail : ∀ Γ : ℝ, ∀ τ : ℂ, a ≤ τ.re → τ.re ≤ 2 * a → 4 * |τ.im| ≤ a * Γ →
      ‖xiGaussianHeatTraceC τ - ∑ q ∈ xiCopiesBelow Γ, xiGaussianHeatTermC τ q‖ ≤ T₀ :=
    fun Γ τ h1 h2 h3 => norm_xiGaussianHeatTraceC_sub_sum_le ha h1 h2 h3
  set m₀ : ℕ := ⌈(4 + 3 * ε) / ε⌉₊ with hm₀
  have hm₀' : (4 + 3 * ε) / ε ≤ m₀ := Nat.le_ceil _
  set D : ℝ := (Real.log (6 * ((m₀ : ℝ) + 4)) + 14) *
    ((20 * (|xiLineTwoLogDerivConstant| + 4) + 1) * (7 + 2 / (a * c)) ^ (5 / 4 : ℝ)) ^
      (5 / 4 : ℝ) with hD
  have hD0 : 0 ≤ D := by
    have h1 : 0 ≤ Real.log (6 * ((m₀ : ℝ) + 4)) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m₀; linarith)
    have h2 : 0 ≤ 2 / (a * c) := by positivity
    have h3 := abs_nonneg xiLineTwoLogDerivConstant
    rw [hD]; positivity
  set L₁ : ℝ := Real.log (C₁ + T₀ + 1) with hL₁
  have hL₁0 : 0 ≤ L₁ := Real.log_nonneg (by linarith)
  obtain ⟨H₀, -, hH₀⟩ := exists_threshold_quadratic_dominates (κ := a * ε / 2)
    (by positivity) hD0 hL₁0
  refine ⟨max H₀ (2 * Real.sqrt (a * c)), fun q hq => ?_⟩
  by_contra hbad
  push Not at hbad
  obtain ⟨q₀, hre, him, horient⟩ := exists_xiZeroCopy_oriented q
  rw [← him] at hbad
  rw [← hre] at hq
  have hGH : H₀ ≤ |(xiSpectralPoint q₀).re| := (le_max_left _ _).trans hq
  have hGs : 2 * Real.sqrt (a * c) ≤ |(xiSpectralPoint q₀).re| := (le_max_right _ _).trans hq
  have hcore := vertical_quadratic_copy_bound ha hc hε hC₁ hT₀0 hsector htail hm₀' horient hbad
    hGs rfl
  have hloss := log_turanDenominator_copy_le ha hc m₀ q₀ (Γ := |(xiSpectralPoint q₀).re| *
    (1 + 4 * |(xiSpectralPoint q₀).im| / (a * c)) + 1) rfl
  rw [← hD] at hloss
  have hfinal : a * ε * |(xiSpectralPoint q₀).re| ^ 2 / 2 ≤
      D * (|(xiSpectralPoint q₀).re| + 1) ^ (25 / 16 : ℝ) + L₁ := by
    rw [sq_abs]
    linarith
  have := hH₀ _ hGH
  linarith

/-! ## The exact law -/

/-- **The vertical quadratic law.**  For `a > 0` and `c ≥ 0`, the zero heat trace satisfies
`‖ν(a + ib)‖ = O(e^{c' b²})` for every `c' > c` iff `limsup_{|γ|→∞} (β − ½)² ≤ a c`.  Hence
`inf {c : ν(a + ib) = O(e^{c b²})} = Δ∞²/a`. -/
theorem vertical_quadratic_rate_le_iff {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    (∀ c' : ℝ, c < c' → ∃ C : ℝ, ∀ b : ℝ,
        ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (c' * b ^ 2)) ↔
      ∀ η : ℝ, 0 < η → ∃ H : ℝ, ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| →
        (xiSpectralPoint q).im ^ 2 ≤ a * c + η := by
  constructor
  · intro h η hη
    set c' : ℝ := c + η / (4 * a) with hc'
    have hc'0 : 0 < c' := by rw [hc']; positivity
    have hlt : c < c' := by
      have h0 : 0 < η / (4 * a) := by positivity
      rw [hc']; linarith
    obtain ⟨C, hC⟩ := h c' hlt
    set ε : ℝ := η / (a * c' * 4) with hε
    have hε0 : 0 < ε := by rw [hε]; positivity
    obtain ⟨H, hH⟩ := xiSpectralPoint_im_sq_le_of_vertical_quadratic ha hc'0 hC hε0
    refine ⟨H, fun q hq => (hH q hq).trans ?_⟩
    have h1 : a * c' * (1 + ε) = a * c + η / 4 + η / 4 := by
      rw [hε, hc']; field_simp
    rw [h1]; linarith
  · intro h c' hcc'
    set η : ℝ := a * (c' - c) / 2 with hη
    have hcc : 0 < c' - c := by linarith
    have hη0 : 0 < η := by rw [hη]; positivity
    obtain ⟨H, hH⟩ := h η hη0
    have hzeros : ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| →
        |(xiSpectralPoint q).im| ≤ Real.sqrt (a * c + η) := by
      intro q hq
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hH q hq)
    obtain ⟨C, hC⟩ := exists_norm_xiGaussianHeatTraceC_le_quadratic_coefficient ha hη0 hzeros
    refine ⟨C, fun b => (hC b).trans ?_⟩
    have hC0 : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans_eq (by simp))
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0
    rw [Real.sq_sqrt (by positivity)]
    have h1 : (a * c + η + η) / a = c' := by rw [hη]; field_simp; ring
    rw [show (a * c + η + η) * b ^ 2 / a = (a * c + η + η) / a * b ^ 2 by ring, h1]

/-- **Asymptotic quasi-RH as a vertical quadratic rate.**  The zeros stay asymptotically inside a
strip `|β − ½| ≤ δ` with `δ < ½` iff `‖ν(a + ib)‖ = O(e^{c b²})` for some `c < 1/(4a)`, the
unconditional rate being `1/(4a)`. -/
theorem asymptoticQuasiRH_iff_vertical_quadratic_rate_lt {a : ℝ} (ha : 0 < a) :
    (∃ δ : ℝ, δ < 1 / 2 ∧ ∃ H : ℝ, ∀ q : XiZeroCopy, H ≤ |(xiSpectralPoint q).re| →
        |(xiSpectralPoint q).im| ≤ δ) ↔
      ∃ c : ℝ, c < 1 / (4 * a) ∧ ∃ C : ℝ, ∀ b : ℝ,
        ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C * Real.exp (c * b ^ 2) := by
  constructor
  · rintro ⟨δ, hδ, H, hH⟩
    set δ' : ℝ := max δ 0 with hδ'
    have hδ'0 : 0 ≤ δ' := le_max_right _ _
    have hδ'h : δ' < 1 / 2 := max_lt hδ (by norm_num)
    set ε : ℝ := (1 / 4 - δ' ^ 2) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; nlinarith
    obtain ⟨C, hC⟩ := exists_norm_xiGaussianHeatTraceC_le_quadratic_coefficient (Δ := δ') ha hε0
      fun q hq => (hH q hq).trans (le_max_left _ _)
    refine ⟨(δ' ^ 2 + ε) / a, ?_, C, fun b => (hC b).trans_eq ?_⟩
    · rw [div_lt_div_iff₀ ha (by positivity)]; nlinarith
    · ring_nf
  · rintro ⟨c, hc, C, hC⟩
    by_cases hc0 : c ≤ 0
    · have hC' : ∀ b : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤
          |C| * Real.exp (1 / (16 * a) * b ^ 2) := by
        intro b
        refine (hC b).trans
          (mul_le_mul (le_abs_self C) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _))
        have h1 : 0 ≤ 1 / (16 * a) * b ^ 2 := by positivity
        linarith [mul_nonpos_of_nonpos_of_nonneg hc0 (sq_nonneg b)]
      obtain ⟨H, hH⟩ := xiSpectralPoint_im_sq_le_of_vertical_quadratic ha
        (by positivity : (0 : ℝ) < 1 / (16 * a)) hC' one_pos
      refine ⟨Real.sqrt (1 / 8), ?_, H, fun q hq => ?_⟩
      · rw [Real.sqrt_lt' (by norm_num)]; norm_num
      · have h1 := hH q hq
        have h2 : a * (1 / (16 * a)) * (1 + 1) = 1 / 8 := by field_simp; ring
        rw [h2] at h1
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt h1
    · push Not at hc0
      set ε : ℝ := (1 / (4 * a) - c) / (2 * c) with hε
      have hgap : 0 < 1 / (4 * a) - c := by linarith
      have hε0 : 0 < ε := by rw [hε]; positivity
      obtain ⟨H, hH⟩ := xiSpectralPoint_im_sq_le_of_vertical_quadratic ha hc0 hC hε0
      have hlt : a * c * (1 + ε) < 1 / 4 := by
        have h1 : a * c * (1 + ε) = a * c + a * (1 / (4 * a) - c) / 2 := by
          rw [hε]; field_simp
        rw [h1]
        have : a * (1 / (4 * a)) = 1 / 4 := by field_simp
        nlinarith
      refine ⟨Real.sqrt (a * c * (1 + ε)), ?_, H, fun q hq => ?_⟩
      · rw [Real.sqrt_lt' (by norm_num)]; linarith
      · rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (hH q hq)

end

end RHTower
