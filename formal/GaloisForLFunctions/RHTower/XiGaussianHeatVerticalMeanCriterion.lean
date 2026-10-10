import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalQuadraticLowerLaw
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalSpectralLaw
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalExponentialType
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius

/-!
# RH as the vanishing of one vertical mean of the prime chirp

On the vertical line `τ = a + ib` let `ν(τ) = Σ_q e^{-τ w_q}` be the zero heat trace and
`(π/τ)^{1/2} S(τ)` the Gaussian prime chirp, `S(τ) = Σ_n Λ(n) n^{-1/2} e^{-(log n)²/(4τ)}`.

**Theorem** (`riemannHypothesis_iff_tendsto_vertical_mean`).  For every `a > 0`, RH holds iff the
Cesàro mean `(1/B) ∫₀^B ν(a + ib) db` tends to `0`.

**Theorem** (`riemannHypothesis_iff_tendsto_vertical_mean_primeChirp`).  RH holds iff
`(1/B) ∫₀^B (π/τ_b)^{1/2} S(τ_b) db → 0`, `τ_b = a + ib`: the primes have mean zero along one
vertical line in complex heat time.

So the HCF producer needs no pointwise control at all: one mean value suffices.  Likewise RH holds
iff `∫₀^B ‖(π/τ_b)^{1/2} S(τ_b)‖ db` grows polynomially
(`riemannHypothesis_iff_integral_norm_primeChirp_polynomial`), against the unconditional `e^{B²/(4a)}`.  Under RH the
mean is the Bohr coefficient at frequency `0`, which vanishes because every `γ² > 0`
(`tendsto_bohrCoeff_xiGaussianHeatTraceC_of_rh`).

Mechanism of the converse.  The primitive `P(τ) = Σ_q e^{-τ w_q}/w_q` satisfies `P' = -ν`, so
`∫₀^B ν(a + ib) db = i(P(a + iB) − P(a))` and a bounded mean makes `P` linearly bounded on the line
(`riemannHypothesis_of_primitive_polynomial`).  Phragmén–Lindelöf on the sector between the 45° ray
and the line, applied to `P(τ)/(τ+1)^K`, gives `‖P(τ)‖ ≤ M |τ+1|^K` there; a Cauchy estimate on
circles of radius `a` about `2a + ib` turns this into a polynomial bound for `ν` on `Re τ = 2a`, which
forces RH (`riemannHypothesis_iff_xiGaussianHeatTraceC_subexponential`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## The primitive of the heat trace -/

/-- The primitive `P(τ) = Σ_q e^{-τ w_q}/w_q`, `w_q = z_q²`, with `P' = -ν`. -/
def xiGaussianHeatPrimitiveC (τ : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiGaussianHeatTermC τ q / xiSpectralPoint q ^ (2 : ℕ)

theorem norm_xiGaussianHeatTermC_div_le (τ : ℂ) (q : XiZeroCopy) :
    ‖xiGaussianHeatTermC τ q / xiSpectralPoint q ^ (2 : ℕ)‖ ≤ ‖xiGaussianHeatTermC τ q‖ / 150 := by
  have h := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  rw [norm_div, norm_pow]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) h.le

theorem summable_norm_xiGaussianHeatTermC_div {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy => ‖xiGaussianHeatTermC τ q / xiSpectralPoint q ^ (2 : ℕ)‖) :=
  ((summable_norm_xiGaussianHeatTermC hτ).div_const 150).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_xiGaussianHeatTermC_div_le τ)

theorem norm_xiGaussianHeatPrimitiveC_le {τ : ℂ} (hτ : 0 < τ.re) :
    ‖xiGaussianHeatPrimitiveC τ‖ ≤ (∑' q : XiZeroCopy, ‖xiGaussianHeatTermC τ q‖) / 150 := by
  rw [xiGaussianHeatPrimitiveC, ← tsum_div_const]
  exact (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC_div hτ)).trans
    ((summable_norm_xiGaussianHeatTermC_div hτ).tsum_le_tsum (norm_xiGaussianHeatTermC_div_le τ)
      ((summable_norm_xiGaussianHeatTermC hτ).div_const 150))

/-- **`P' = -ν`** on the open right half-plane. -/
theorem hasDerivAt_xiGaussianHeatPrimitiveC {τ₀ : ℂ} (h : 0 < τ₀.re) :
    HasDerivAt xiGaussianHeatPrimitiveC (-xiGaussianHeatTraceC τ₀) τ₀ := by
  set R : ℝ := |τ₀.im| + 1
  set U : Set ℂ := {τ | τ₀.re / 2 < τ.re} ∩ {τ | |τ.im| < R}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)
  have hmem : τ₀ ∈ U := ⟨by simp only [mem_setOf_eq]; linarith, by
    simp only [mem_setOf_eq, R]; linarith⟩
  set F : XiZeroCopy → ℂ → ℂ := fun q τ => xiGaussianHeatTermC τ q / xiSpectralPoint q ^ (2 : ℕ)
  have hbound : ∀ (q : XiZeroCopy) (τ : ℂ), τ ∈ U → ‖F q τ‖ ≤
      Real.exp (R ^ 2 / (τ₀.re / 2)) * (4 / (τ₀.re / 2)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q τ hτU
    have hre : τ₀.re / 2 < τ.re := hτU.1
    have him : |τ.im| < R := hτU.2
    have hτ : 0 < τ.re := by linarith
    refine (norm_xiGaussianHeatTermC_div_le τ q).trans ?_
    refine (div_le_self (norm_nonneg _) (by norm_num)).trans ?_
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
  have hdiff : ∀ q : XiZeroCopy, DifferentiableOn ℂ (F q) U := fun q => by
    simp only [F, xiGaussianHeatTermC]
    fun_prop
  have hsum := xiSpectralPoint_inv_sq_summable.mul_left
    (Real.exp (R ^ 2 / (τ₀.re / 2)) * (4 / (τ₀.re / 2)))
  have hD := Complex.differentiableOn_tsum_of_summable_norm hsum hdiff hU hbound
  have hDer := Complex.hasSum_deriv_of_summable_norm hsum hdiff hU hbound hmem
  have hderiv : ∀ q : XiZeroCopy, deriv (F q) τ₀ = -xiGaussianHeatTermC τ₀ q := by
    intro q
    have hz : xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := by
      have := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
      intro h0; rw [← norm_pow, h0, norm_zero] at this; linarith
    have hd : HasDerivAt (F q) (Complex.exp (-τ₀ * xiSpectralPoint q ^ (2 : ℕ)) *
        (-(xiSpectralPoint q ^ (2 : ℕ))) / xiSpectralPoint q ^ (2 : ℕ)) τ₀ := by
      simp only [F, xiGaussianHeatTermC]
      refine HasDerivAt.div_const ?_ _
      have h1 : HasDerivAt (fun τ : ℂ => -τ * xiSpectralPoint q ^ (2 : ℕ))
          (-(xiSpectralPoint q ^ (2 : ℕ))) τ₀ := by
        simpa using ((hasDerivAt_id τ₀).neg.mul_const (xiSpectralPoint q ^ (2 : ℕ)))
      exact h1.cexp
    rw [hd.deriv, xiGaussianHeatTermC, mul_neg, neg_div, mul_div_assoc, div_self hz, mul_one]
  have hP : deriv xiGaussianHeatPrimitiveC τ₀ = -xiGaussianHeatTraceC τ₀ := by
    have h1 := hDer.tsum_eq
    rw [show (fun w => ∑' (i : XiZeroCopy), F i w) = xiGaussianHeatPrimitiveC from rfl] at h1
    rw [← h1, tsum_congr hderiv, tsum_neg, xiGaussianHeatTraceC]
  rw [← hP]
  exact (hD.differentiableAt (hU.mem_nhds hmem)).hasDerivAt

theorem differentiableAt_xiGaussianHeatPrimitiveC {τ₀ : ℂ} (h : 0 < τ₀.re) :
    DifferentiableAt ℂ xiGaussianHeatPrimitiveC τ₀ :=
  (hasDerivAt_xiGaussianHeatPrimitiveC h).differentiableAt

theorem xiGaussianHeatTermC_conj_lineConj (τ : ℂ) (q : XiZeroCopy) :
    xiGaussianHeatTermC ((starRingEnd ℂ) τ) (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiGaussianHeatTermC τ q) := by
  rw [xiGaussianHeatTermC, xiGaussianHeatTermC, xiSpectralPoint_lineConj, ← Complex.exp_conj]
  congr 1
  simp [map_mul, map_neg, map_pow]

theorem xiGaussianHeatPrimitiveC_conj (τ : ℂ) :
    xiGaussianHeatPrimitiveC ((starRingEnd ℂ) τ) = (starRingEnd ℂ) (xiGaussianHeatPrimitiveC τ) := by
  rw [xiGaussianHeatPrimitiveC, xiGaussianHeatPrimitiveC, Complex.conj_tsum,
    ← xiZeroCopyLineConjEquiv.tsum_eq]
  refine tsum_congr fun q => ?_
  rw [xiGaussianHeatTermC_conj_lineConj, xiSpectralPoint_lineConj, map_div₀, map_pow]

/-- **The vertical integral of the trace is a difference of the primitive.** -/
theorem integral_xiGaussianHeatTraceC_vertical {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I) =
      I * (xiGaussianHeatPrimitiveC ((a : ℂ) + B * I) - xiGaussianHeatPrimitiveC (a : ℂ)) := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) B, HasDerivAt
      (fun b : ℝ => I * xiGaussianHeatPrimitiveC ((a : ℂ) + b * I))
      (xiGaussianHeatTraceC ((a : ℂ) + x * I)) x := by
    intro x _
    have hre : 0 < ((a : ℂ) + x * I).re := by simpa using ha
    have h1 : HasDerivAt (fun b : ℝ => (a : ℂ) + b * I) I x := by
      simpa using ((hasDerivAt_id (x : ℂ)).mul_const I).const_add (a : ℂ) |>.comp_ofReal
    have h2 := (hasDerivAt_xiGaussianHeatPrimitiveC hre).comp x h1
    refine (h2.const_mul I).congr_deriv ?_
    linear_combination (-xiGaussianHeatTraceC ((a : ℂ) + x * I)) * I_sq
  have hint : IntervalIntegrable (fun b : ℝ => xiGaussianHeatTraceC ((a : ℂ) + b * I)) volume 0 B :=
    (continuous_xiGaussianHeatTraceC_vertical ha).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  ring

/-! ## A polynomially bounded primitive forces RH -/

theorem tsum_norm_xiGaussianHeatTermC_le_growth {τ : ℂ} (hτ : 0 < τ.re) :
    ∑' q : XiZeroCopy, ‖xiGaussianHeatTermC τ q‖ ≤
      Real.exp (τ.im ^ 2 / τ.re) * (4 / τ.re) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  rw [← tsum_mul_left]
  exact (summable_norm_xiGaussianHeatTermC hτ).tsum_le_tsum (norm_xiGaussianHeatTermC_le_growth hτ)
    (xiSpectralPoint_inv_sq_summable.mul_left _)

theorem tsum_norm_xiGaussianHeatTermC_le_of_abs_im_le {τ : ℂ} (hτ : 0 < τ.re)
    (him : |τ.im| ≤ τ.re) :
    ∑' q : XiZeroCopy, ‖xiGaussianHeatTermC τ q‖ ≤
      3 / τ.re * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  rw [← tsum_mul_left]
  exact (summable_norm_xiGaussianHeatTermC hτ).tsum_le_tsum
    (norm_xiGaussianHeatTermC_le_of_abs_im_le hτ him) (xiSpectralPoint_inv_sq_summable.mul_left _)

theorem one_le_norm_add_one {τ : ℂ} (h : 0 ≤ τ.re) : 1 ≤ ‖τ + 1‖ :=
  calc (1 : ℝ) ≤ (τ + 1).re := by rw [add_re, one_re]; linarith
    _ ≤ |(τ + 1).re| := le_abs_self _
    _ ≤ ‖τ + 1‖ := Complex.abs_re_le_norm _

/-- The norm of the primitive on the line is even in `b`. -/
theorem norm_xiGaussianHeatPrimitiveC_neg (a b : ℝ) :
    ‖xiGaussianHeatPrimitiveC ((a : ℂ) + b * I)‖ =
      ‖xiGaussianHeatPrimitiveC ((a : ℂ) + ((-b : ℝ) : ℂ) * I)‖ := by
  have hconj : (a : ℂ) + b * I = (starRingEnd ℂ) ((a : ℂ) + ((-b : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [hconj, xiGaussianHeatPrimitiveC_conj, Complex.norm_conj]

theorem norm_xiGaussianHeatTraceC_neg (a b : ℝ) :
    ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ =
      ‖xiGaussianHeatTraceC ((a : ℂ) + ((-b : ℝ) : ℂ) * I)‖ := by
  have hconj : (a : ℂ) + b * I = (starRingEnd ℂ) ((a : ℂ) + ((-b : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [hconj, xiGaussianHeatTraceC_conj, Complex.norm_conj]

/-- **Phragmén–Lindelöf for the primitive.**  A polynomial bound for `P` on the upper half of the
vertical line `Re τ = a` propagates to the sector between the 45° ray from `a` and the line. -/
theorem exists_norm_xiGaussianHeatPrimitiveC_le_sector {a C : ℝ} {K : ℕ} (ha : 0 < a)
    (hP : ∀ b : ℝ, 0 ≤ b → ‖xiGaussianHeatPrimitiveC ((a : ℂ) + b * I)‖ ≤ C * (1 + b) ^ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℂ, a ≤ τ.re → τ.re - a ≤ τ.im →
      ‖xiGaussianHeatPrimitiveC τ‖ ≤ M * ‖τ + 1‖ ^ K := by
  set K₀ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hK₀
  have hK₀0 : 0 ≤ K₀ := tsum_nonneg fun _ => by positivity
  have hC0 : 0 ≤ C := by
    have h := hP 0 le_rfl
    simp only [add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hPall : ∀ b : ℝ, ‖xiGaussianHeatPrimitiveC ((a : ℂ) + b * I)‖ ≤ C * (1 + |b|) ^ K := by
    intro b
    rcases le_or_gt 0 b with hb | hb
    · rw [abs_of_nonneg hb]; exact hP b hb
    · rw [norm_xiGaussianHeatPrimitiveC_neg, abs_of_neg hb]; exact hP (-b) (by linarith)
  set f : ℂ → ℂ := fun τ => xiGaussianHeatPrimitiveC τ / (τ + 1) ^ K with hf
  have hfle : ∀ τ : ℂ, 0 ≤ τ.re → ‖f τ‖ ≤ ‖xiGaussianHeatPrimitiveC τ‖ := by
    intro τ h
    rw [hf]
    simp only
    rw [norm_div, norm_pow]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (one_le_norm_add_one h))
  have hdiff : ∀ τ : ℂ, 0 < τ.re → DifferentiableAt ℂ f τ := by
    intro τ h
    refine (differentiableAt_xiGaussianHeatPrimitiveC h).div (by fun_prop) ?_
    refine pow_ne_zero _ fun h0 => ?_
    have := one_le_norm_add_one h.le
    rw [h0, norm_zero] at this
    linarith
  have hgrowth : ∀ τ : ℂ, a ≤ τ.re →
      ‖f τ‖ ≤ (4 / a * K₀ / 150) * Real.exp (1 / a * ‖τ - a‖ ^ 2) := by
    intro τ hτ
    have hτ0 : 0 < τ.re := ha.trans_le hτ
    refine (hfle τ hτ0.le).trans ((norm_xiGaussianHeatPrimitiveC_le hτ0).trans ?_)
    have h1 := tsum_norm_xiGaussianHeatTermC_le_growth hτ0
    rw [← hK₀] at h1
    have him : τ.im ^ 2 ≤ ‖τ - a‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
      nlinarith [sq_nonneg (τ.re - a)]
    have he1 : Real.exp (τ.im ^ 2 / τ.re) ≤ Real.exp (1 / a * ‖τ - a‖ ^ 2) := by
      refine Real.exp_le_exp.2 ((div_le_div_of_nonneg_left (sq_nonneg _) ha hτ).trans ?_)
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right him ha.le
    have he2 : 4 / τ.re ≤ 4 / a := div_le_div_of_nonneg_left (by norm_num) ha hτ
    have h2 : Real.exp (τ.im ^ 2 / τ.re) * (4 / τ.re) * K₀ ≤
        Real.exp (1 / a * ‖τ - a‖ ^ 2) * (4 / a) * K₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul he1 he2 (by positivity) (Real.exp_pos _).le) hK₀0
    calc (∑' q : XiZeroCopy, ‖xiGaussianHeatTermC τ q‖) / 150
        ≤ Real.exp (1 / a * ‖τ - a‖ ^ 2) * (4 / a) * K₀ / 150 :=
          div_le_div_of_nonneg_right (h1.trans h2) (by norm_num)
      _ = (4 / a * K₀ / 150) * Real.exp (1 / a * ‖τ - a‖ ^ 2) := by ring
  have hray : ∀ r : ℝ, 0 ≤ r →
      ‖f ((a : ℂ) + r * Complex.exp (Real.pi / 4 * I))‖ ≤ 3 / a * K₀ / 150 := by
    intro r hr
    have he : Complex.exp (Real.pi / 4 * I) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) +
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * I := by
      rw [show (Real.pi / 4 * I : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
        Real.sin_pi_div_four]
    set τ : ℂ := (a : ℂ) + r * Complex.exp (Real.pi / 4 * I) with hτ
    have hτre : τ.re = a + r * (Real.sqrt 2 / 2) := by rw [hτ, he]; simp
    have hτim : τ.im = r * (Real.sqrt 2 / 2) := by rw [hτ, he]; simp
    have hs2 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    have hτ0 : 0 < τ.re := by rw [hτre]; nlinarith
    have hτa : a ≤ τ.re := by rw [hτre]; nlinarith
    have him : |τ.im| ≤ τ.re := by
      rw [hτim, hτre, abs_of_nonneg (mul_nonneg hr hs2)]; linarith
    refine (hfle τ hτ0.le).trans ((norm_xiGaussianHeatPrimitiveC_le hτ0).trans ?_)
    refine div_le_div_of_nonneg_right ((tsum_norm_xiGaussianHeatTermC_le_of_abs_im_le hτ0 him).trans
      ?_) (by norm_num)
    rw [← hK₀]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) ha hτa) hK₀0
  have hvert : ∀ b : ℝ, ‖f ((a : ℂ) + b * I)‖ ≤ C * 2 ^ K := by
    intro b
    rw [hf]
    simp only
    rw [norm_div, norm_pow]
    have hz : (1 + |b|) / 2 ≤ ‖(a : ℂ) + b * I + 1‖ := by
      have h1 : |b| ≤ ‖(a : ℂ) + b * I + 1‖ := by
        have := Complex.abs_im_le_norm ((a : ℂ) + b * I + 1)
        simpa using this
      have h2 := one_le_norm_add_one (τ := (a : ℂ) + b * I) (by simpa using ha.le)
      linarith
    have hpos : 0 < ‖(a : ℂ) + b * I + 1‖ ^ K := pow_pos (by linarith [abs_nonneg b]) K
    rw [div_le_iff₀ hpos]
    calc ‖xiGaussianHeatPrimitiveC ((a : ℂ) + b * I)‖ ≤ C * (1 + |b|) ^ K := hPall b
      _ = C * 2 ^ K * ((1 + |b|) / 2) ^ K := by rw [div_pow]; field_simp
      _ ≤ C * 2 ^ K * ‖(a : ℂ) + b * I + 1‖ ^ K :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz K) (by positivity)
  refine ⟨max (C * 2 ^ K) (3 / a * K₀ / 150), le_max_of_le_left (by positivity),
    fun τ h1 h2 => ?_⟩
  have hfτ := norm_le_max_of_vertical_of_ray_rect ha hdiff hgrowth hray hvert h1 h2
  rw [hf] at hfτ
  simp only at hfτ
  have hτ1 : 1 ≤ ‖τ + 1‖ := one_le_norm_add_one (by linarith)
  have hpos : 0 < ‖τ + 1‖ ^ K := pow_pos (by linarith) K
  rw [norm_div, norm_pow, div_le_iff₀ hpos] at hfτ
  exact hfτ

/-- **A polynomially bounded primitive forces RH.**  If `‖P(a + ib)‖ ≤ C(1 + b)^K` for `b ≥ 0`, then
every zero lies on the critical line. -/
theorem riemannHypothesis_of_primitive_polynomial {a C : ℝ} {K : ℕ} (ha : 0 < a)
    (hP : ∀ b : ℝ, 0 ≤ b → ‖xiGaussianHeatPrimitiveC ((a : ℂ) + b * I)‖ ≤ C * (1 + b) ^ K) :
    RiemannHypothesis := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_xiGaussianHeatPrimitiveC_le_sector ha hP
  set K₀ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hK₀
  have hK₀0 : 0 ≤ K₀ := tsum_nonneg fun _ => by positivity
  -- Cauchy estimate on circles of radius `a` about `2a + ib`, `b ≥ 3a`
  have hfar : ∀ b : ℝ, 3 * a ≤ b →
      ‖xiGaussianHeatTraceC (((2 * a : ℝ) : ℂ) + b * I)‖ ≤ M * (3 * a + b + 1) ^ K / a := by
    intro b hb
    set τ₀ : ℂ := ((2 * a : ℝ) : ℂ) + b * I with hτ₀
    have hτ₀re : τ₀.re = 2 * a := by simp [hτ₀]
    have hτ₀im : τ₀.im = b := by simp [hτ₀]
    have hd : DiffContOnCl ℂ xiGaussianHeatPrimitiveC (Metric.ball τ₀ a) := by
      refine DifferentiableOn.diffContOnCl fun z hz => ?_
      rw [closure_ball τ₀ ha.ne'] at hz
      have hdist : ‖z - τ₀‖ ≤ a := by rw [← dist_eq_norm]; exact hz
      have hre : |z.re - τ₀.re| ≤ a := by
        have h := Complex.abs_re_le_norm (z - τ₀)
        rw [sub_re] at h
        linarith
      have hz0 : 0 < z.re := by rw [hτ₀re] at hre; have := (abs_le.1 hre).1; linarith
      exact (differentiableAt_xiGaussianHeatPrimitiveC hz0).differentiableWithinAt
    have hsph : ∀ z ∈ Metric.sphere τ₀ a,
        ‖xiGaussianHeatPrimitiveC z‖ ≤ M * (3 * a + b + 1) ^ K := by
      intro z hz
      have hdist : ‖z - τ₀‖ = a := by rw [← dist_eq_norm]; exact hz
      have hre : |z.re - 2 * a| ≤ a := by
        rw [← hτ₀re, ← sub_re]; exact (Complex.abs_re_le_norm _).trans hdist.le
      have him : |z.im - b| ≤ a := by
        rw [← hτ₀im, ← sub_im]; exact (Complex.abs_im_le_norm _).trans hdist.le
      obtain ⟨hre1, hre2⟩ := abs_le.1 hre
      obtain ⟨him1, him2⟩ := abs_le.1 him
      have h1 := hM z (by linarith) (by linarith)
      have hnorm : ‖z + 1‖ ≤ 3 * a + b + 1 := by
        calc ‖z + 1‖ = ‖(z - τ₀) + (τ₀ + 1)‖ := by ring_nf
          _ ≤ ‖z - τ₀‖ + ‖τ₀ + 1‖ := norm_add_le _ _
          _ ≤ a + (2 * a + 1 + b) := by
              rw [hdist]
              refine add_le_add le_rfl ?_
              calc ‖τ₀ + 1‖ ≤ |(τ₀ + 1).re| + |(τ₀ + 1).im| := Complex.norm_le_abs_re_add_abs_im _
                _ = 2 * a + 1 + b := by
                    rw [add_re, add_im, one_re, one_im, hτ₀re, hτ₀im, add_zero,
                      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          _ = 3 * a + b + 1 := by ring
      exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm K) hM0)
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ha hd hsph
    rw [(hasDerivAt_xiGaussianHeatPrimitiveC (by rw [hτ₀re]; linarith)).deriv, norm_neg]
      at hcauchy
    exact hcauchy
  -- a polynomial bound on the whole line `Re τ = 2a`
  set D : ℝ := max (M * (3 * a + 1) ^ K / a) (Real.exp (9 * a / 2) * (4 / (2 * a)) * K₀) with hD
  have hline : ∀ b : ℝ, ‖xiGaussianHeatTraceC (((2 * a : ℝ) : ℂ) + b * I)‖ ≤ D * (1 + |b|) ^ K := by
    have hpos : ∀ b : ℝ, 1 ≤ (1 + |b|) ^ K := fun b => one_le_pow₀ (by linarith [abs_nonneg b])
    have hcase : ∀ b : ℝ, 0 ≤ b →
        ‖xiGaussianHeatTraceC (((2 * a : ℝ) : ℂ) + b * I)‖ ≤ D * (1 + b) ^ K := by
      intro b hb
      rcases le_or_gt (3 * a) b with h3 | h3
      · refine (hfar b h3).trans (le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by positivity)))
        have h4 : (3 * a + b + 1) ^ K ≤ (3 * a + 1) ^ K * (1 + b) ^ K := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by nlinarith) K
        calc M * (3 * a + b + 1) ^ K / a ≤ M * ((3 * a + 1) ^ K * (1 + b) ^ K) / a :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hM0) ha.le
          _ = M * (3 * a + 1) ^ K / a * (1 + b) ^ K := by ring
      · have hτ0 : 0 < ((((2 * a : ℝ) : ℂ) + b * I)).re := by simp; linarith
        refine (norm_xiGaussianHeatTraceC_le_growth hτ0).trans ?_
        have hre : ((((2 * a : ℝ) : ℂ) + b * I)).re = 2 * a := by simp
        have him : ((((2 * a : ℝ) : ℂ) + b * I)).im = b := by simp
        rw [hre, him]
        have hexp : Real.exp (b ^ 2 / (2 * a)) ≤ Real.exp (9 * a / 2) := by
          refine Real.exp_le_exp.2 ?_
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        calc Real.exp (b ^ 2 / (2 * a)) * (4 / (2 * a)) * K₀
            ≤ Real.exp (9 * a / 2) * (4 / (2 * a)) * K₀ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp (by positivity)) hK₀0
          _ ≤ D := le_max_right _ _
          _ ≤ D * (1 + b) ^ K := le_mul_of_one_le_right
              ((le_max_right _ _).trans' (by positivity)) (one_le_pow₀ (by linarith))
    intro b
    rcases le_or_gt 0 b with hb | hb
    · rw [abs_of_nonneg hb]; exact hcase b hb
    · rw [norm_xiGaussianHeatTraceC_neg, abs_of_neg hb]; exact hcase (-b) (by linarith)
  -- a polynomial bound is subexponential
  refine (riemannHypothesis_iff_xiGaussianHeatTraceC_subexponential
    (a := 2 * a) (by linarith)).2 fun ε hε => ?_
  have hD0 : 0 ≤ D := le_max_of_le_left (by positivity)
  refine ⟨D * ((K.factorial : ℝ) / ε ^ K * Real.exp ε), fun b => (hline b).trans ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (ε * (1 + |b|)) (by positivity) K
  have hfac : (0 : ℝ) < K.factorial := by exact_mod_cast Nat.factorial_pos K
  have h2 : (1 + |b|) ^ K ≤ (K.factorial : ℝ) / ε ^ K * Real.exp ε * Real.exp (ε * |b|) := by
    have hεK : 0 < ε ^ K := pow_pos hε K
    have he : Real.exp ε * Real.exp (ε * |b|) = Real.exp (ε * (1 + |b|)) := by
      rw [← Real.exp_add]; ring_nf
    rw [mul_assoc, he, div_mul_eq_mul_div, le_div_iff₀ hεK]
    rw [div_le_iff₀ hfac, mul_pow] at h1
    linarith
  calc D * (1 + |b|) ^ K ≤ D * ((K.factorial : ℝ) / ε ^ K * Real.exp ε * Real.exp (ε * |b|)) :=
        mul_le_mul_of_nonneg_left h2 hD0
    _ = D * ((K.factorial : ℝ) / ε ^ K * Real.exp ε) * Real.exp (ε * |b|) := by ring

/-! ## The mean-value criteria -/

/-- **RH as a vanishing vertical mean.**  For every `a > 0`, RH holds iff
`(1/B) ∫₀^B ν(a + ib) db → 0`. -/
theorem riemannHypothesis_iff_tendsto_vertical_mean {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ Tendsto (fun B : ℝ => (1 / (B : ℂ)) *
      ∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I)) atTop (𝓝 0) := by
  constructor
  · intro hRH
    have h := tendsto_bohrCoeff_xiGaussianHeatTraceC_of_rh hRH ha 0
    have hzero : (∑' q : XiZeroCopy, if xiSpectralSqRe q = 0 then
        ((Real.exp (-(a * xiSpectralSqRe q)) : ℝ) : ℂ) else 0) = 0 :=
      (tsum_congr fun q => if_neg (xiSpectralSqRe_pos q).ne').trans tsum_zero
    rw [hzero] at h
    refine h.congr fun B => ?_
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  · intro h
    set K₀ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hK₀
    have hK₀0 : 0 ≤ K₀ := tsum_nonneg fun _ => by positivity
    obtain ⟨B₀, hB₀⟩ := (Metric.tendsto_atTop.1 h) 1 one_pos
    set B₁ : ℝ := max B₀ 1 with hB₁
    have hB₁1 : 1 ≤ B₁ := le_max_right _ _
    set G : ℝ := Real.exp (B₁ ^ 2 / a) * (4 / a) * K₀ with hG
    have hG0 : 0 ≤ G := by positivity
    have hνG : ∀ b : ℝ, |b| ≤ B₁ → ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ G := by
      intro b hb
      have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
      refine (norm_xiGaussianHeatTraceC_le_growth hτ).trans ?_
      have hre : ((a : ℂ) + b * I).re = a := by simp
      have him : ((a : ℂ) + b * I).im = b := by simp
      rw [hre, him, hG, ← hK₀]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
        (by positivity)) hK₀0
      refine div_le_div_of_nonneg_right ?_ ha.le
      rw [← sq_abs b]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hint : ∀ B : ℝ, 0 ≤ B →
        ‖∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ (1 + B₁ * G) * (1 + B) := by
      intro B hB
      rcases le_or_gt B₁ B with h1 | h1
      · have h2 := hB₀ B (le_trans (le_max_left _ _) h1)
        have hBpos : 0 < B := by linarith
        rw [dist_zero_right, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hBpos, one_div, inv_mul_lt_iff₀ hBpos, mul_one] at h2
        nlinarith [mul_nonneg hB (mul_nonneg (by linarith : (0 : ℝ) ≤ B₁) hG0)]
      · have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := B)
          (C := G) (f := fun b : ℝ => xiGaussianHeatTraceC ((a : ℂ) + b * I)) (fun x hx => by
            rw [Set.uIoc_of_le hB] at hx
            exact hνG x (by rw [abs_of_pos hx.1]; linarith [hx.2]))
        rw [sub_zero, abs_of_nonneg hB] at h2
        refine h2.trans ?_
        nlinarith [mul_nonneg hB hG0]
    refine riemannHypothesis_of_primitive_polynomial (K := 1)
      (C := ‖xiGaussianHeatPrimitiveC (a : ℂ)‖ + (1 + B₁ * G)) ha fun b hb => ?_
    have h1 := integral_xiGaussianHeatTraceC_vertical ha b
    have h2 : xiGaussianHeatPrimitiveC ((a : ℂ) + b * I) = xiGaussianHeatPrimitiveC (a : ℂ) -
        I * ∫ b in (0 : ℝ)..b, xiGaussianHeatTraceC ((a : ℂ) + b * I) := by
      rw [h1]
      ring_nf
      rw [I_sq]
      ring
    rw [h2, pow_one]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    have h3 := hint b hb
    have h4 : 0 ≤ ‖xiGaussianHeatPrimitiveC (a : ℂ)‖ := norm_nonneg _
    nlinarith

/-- **RH as a vanishing vertical mean of the prime chirp.**  For every `a > 0`, RH holds iff
`(1/B) ∫₀^B (π/τ_b)^{1/2} S(τ_b) db → 0`, `τ_b = a + ib`. -/
theorem riemannHypothesis_iff_tendsto_vertical_mean_primeChirp {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ Tendsto (fun B : ℝ => (1 / (B : ℂ)) *
      ∫ b in (0 : ℝ)..B, gaussianPrimeChirpC ((a : ℂ) + b * I)) atTop (𝓝 0) := by
  have hA := tendsto_bohrCoeff_gaussianArchCriticalC ha 0
  have hP := tendsto_bohrCoeff_gaussianArchPoleC (a := a) (ω := 0) (by norm_num)
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hA hP
  have hre : ∀ b : ℝ, 0 < ((a : ℂ) + b * I).re := fun b => by simpa using ha
  have hcontA : Continuous fun b : ℝ => gaussianArchCriticalC ((a : ℂ) + b * I) := by
    refine continuous_iff_continuousAt.2 fun b => ?_
    exact ContinuousAt.comp (g := gaussianArchCriticalC) (f := fun b : ℝ => (a : ℂ) + b * I)
      (differentiableAt_gaussianArchCriticalC (hre b)).continuousAt
      ((by fun_prop : Continuous fun b : ℝ => (a : ℂ) + b * I).continuousAt)
  have hcontP : Continuous fun b : ℝ => gaussianArchPoleC ((a : ℂ) + b * I) := by
    unfold gaussianArchPoleC; fun_prop
  have hcontN := continuous_xiGaussianHeatTraceC_vertical ha
  have hsplit : ∀ B : ℝ, (1 / (B : ℂ)) * ∫ b in (0 : ℝ)..B, gaussianPrimeChirpC ((a : ℂ) + b * I) =
      (1 / (B : ℂ)) * (∫ b in (0 : ℝ)..B, gaussianArchCriticalC ((a : ℂ) + b * I)) +
        (1 / (B : ℂ)) * (∫ b in (0 : ℝ)..B, gaussianArchPoleC ((a : ℂ) + b * I)) -
          (Real.pi : ℂ) * ((1 / (B : ℂ)) *
            ∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I)) := by
    intro B
    have hpt : ∀ b : ℝ, gaussianPrimeChirpC ((a : ℂ) + b * I) =
        gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I) -
          (Real.pi : ℂ) * xiGaussianHeatTraceC ((a : ℂ) + b * I) := by
      intro b
      have := pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime (hre b)
      linear_combination this
    simp_rw [hpt]
    have hAP : IntervalIntegrable (fun b : ℝ => gaussianArchCriticalC ((a : ℂ) + b * I) +
        gaussianArchPoleC ((a : ℂ) + b * I)) volume 0 B := (hcontA.add hcontP).intervalIntegrable _ _
    have hN' : IntervalIntegrable (fun b : ℝ => (Real.pi : ℂ) *
        xiGaussianHeatTraceC ((a : ℂ) + b * I)) volume 0 B :=
      (hcontN.const_mul _).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hAP hN',
      intervalIntegral.integral_add (hcontA.intervalIntegrable _ _) (hcontP.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    ring
  rw [riemannHypothesis_iff_tendsto_vertical_mean ha]
  constructor
  · intro hν
    have h := (hA.add hP).sub (hν.const_mul (Real.pi : ℂ))
    rw [add_zero, mul_zero, sub_zero] at h
    exact h.congr fun B => (hsplit B).symm
  · intro hprime
    have h := ((hA.add hP).sub hprime).const_mul (1 / (Real.pi : ℂ))
    rw [add_zero, sub_zero, mul_zero] at h
    refine h.congr fun B => ?_
    rw [hsplit B]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    generalize (1 / (B : ℂ)) * ∫ b in (0 : ℝ)..B, gaussianArchCriticalC ((a : ℂ) + b * I) = A
    generalize (1 / (B : ℂ)) * ∫ b in (0 : ℝ)..B, gaussianArchPoleC ((a : ℂ) + b * I) = P
    generalize (1 / (B : ℂ)) * ∫ b in (0 : ℝ)..B, xiGaussianHeatTraceC ((a : ℂ) + b * I) = N
    field_simp
    ring

/-! ## Polynomial `L¹` growth -/

/-- **RH as polynomial `L¹` growth of the prime chirp.**  Unconditionally `‖S(a+ib)‖` may grow like
`e^{b²/(4a)}`; RH holds iff `∫₀^B ‖(π/τ_b)^{1/2} S(τ_b)‖ db = O((1+B)^K)` for some `K`. -/
theorem riemannHypothesis_iff_integral_norm_primeChirp_polynomial {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∃ C : ℝ, ∃ K : ℕ, ∀ B : ℝ, 0 ≤ B →
      ∫ b in (0 : ℝ)..B, ‖gaussianPrimeChirpC ((a : ℂ) + b * I)‖ ≤ C * (1 + B) ^ K := by
  set A : ℝ := ∫ x : ℝ, ‖xiGaussianCenteredArchIntegrand a 0 x‖ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  set Pc : ℝ := 2 * Real.pi * Real.exp (a / 4) with hPc
  have hPc0 : 0 ≤ Pc := by positivity
  have hre : ∀ b : ℝ, 0 < ((a : ℂ) + b * I).re := fun b => by simpa using ha
  have hpt : ∀ b : ℝ, gaussianPrimeChirpC ((a : ℂ) + b * I) =
      gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I) -
        (Real.pi : ℂ) * xiGaussianHeatTraceC ((a : ℂ) + b * I) := by
    intro b
    have := pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime (hre b)
    linear_combination this
  have hcontA : Continuous fun b : ℝ => gaussianArchCriticalC ((a : ℂ) + b * I) := by
    refine continuous_iff_continuousAt.2 fun b => ?_
    exact ContinuousAt.comp (g := gaussianArchCriticalC) (f := fun b : ℝ => (a : ℂ) + b * I)
      (differentiableAt_gaussianArchCriticalC (hre b)).continuousAt
      ((by fun_prop : Continuous fun b : ℝ => (a : ℂ) + b * I).continuousAt)
  have hcontP : Continuous fun b : ℝ => gaussianArchPoleC ((a : ℂ) + b * I) := by
    unfold gaussianArchPoleC; fun_prop
  have hcontN := continuous_xiGaussianHeatTraceC_vertical ha
  have hcontPr : Continuous fun b : ℝ => gaussianPrimeChirpC ((a : ℂ) + b * I) := by
    have h : (fun b : ℝ => gaussianPrimeChirpC ((a : ℂ) + b * I)) = fun b : ℝ =>
        gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I) -
          (Real.pi : ℂ) * xiGaussianHeatTraceC ((a : ℂ) + b * I) := funext hpt
    rw [h]
    exact (hcontA.add hcontP).sub (hcontN.const_mul _)
  have hπ : 0 < Real.pi := Real.pi_pos
  constructor
  · intro hRH
    obtain ⟨Cν, hCν⟩ :=
      (riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha).1 hRH
    have hCν0 : 0 ≤ Cν := (norm_nonneg _).trans (hCν 0)
    refine ⟨A + Pc + Real.pi * Cν, 1, fun B hB => ?_⟩
    have hbound : ∀ b : ℝ, ‖gaussianPrimeChirpC ((a : ℂ) + b * I)‖ ≤ A + Pc + Real.pi * Cν := by
      intro b
      rw [hpt b]
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        (norm_gaussianArchCriticalC_le a b) (norm_gaussianArchPoleC a b).le)) ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
      exact mul_le_mul_of_nonneg_left (hCν b) hπ.le
    have h1 : ∫ b in (0 : ℝ)..B, ‖gaussianPrimeChirpC ((a : ℂ) + b * I)‖ ≤
        ∫ b in (0 : ℝ)..B, (A + Pc + Real.pi * Cν) :=
      intervalIntegral.integral_mono_on hB (hcontPr.norm.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) fun b _ => hbound b
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    rw [pow_one]
    nlinarith [mul_nonneg hB (by positivity : (0 : ℝ) ≤ A + Pc + Real.pi * Cν)]
  · rintro ⟨C, K, hC⟩
    refine riemannHypothesis_of_primitive_polynomial (K := K + 1)
      (C := ‖xiGaussianHeatPrimitiveC (a : ℂ)‖ + (A + Pc + |C|) / Real.pi) ha fun b hb => ?_
    have h1 := integral_xiGaussianHeatTraceC_vertical ha b
    have h2 : xiGaussianHeatPrimitiveC ((a : ℂ) + b * I) = xiGaussianHeatPrimitiveC (a : ℂ) -
        I * ∫ b in (0 : ℝ)..b, xiGaussianHeatTraceC ((a : ℂ) + b * I) := by
      rw [h1]
      ring_nf
      rw [I_sq]
      ring
    have hνpt : ∀ t : ℝ, ‖xiGaussianHeatTraceC ((a : ℂ) + t * I)‖ ≤
        (A + Pc + ‖gaussianPrimeChirpC ((a : ℂ) + t * I)‖) / Real.pi := by
      intro t
      rw [le_div_iff₀ hπ]
      have := pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime (hre t)
      have h3 : Real.pi * ‖xiGaussianHeatTraceC ((a : ℂ) + t * I)‖ =
          ‖gaussianArchCriticalC ((a : ℂ) + t * I) + gaussianArchPoleC ((a : ℂ) + t * I) -
            gaussianPrimeChirpC ((a : ℂ) + t * I)‖ := by
        rw [← this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
      rw [mul_comm, h3]
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        (norm_gaussianArchCriticalC_le a t) (norm_gaussianArchPoleC a t).le)) le_rfl)
    have hint : ‖∫ t in (0 : ℝ)..b, xiGaussianHeatTraceC ((a : ℂ) + t * I)‖ ≤
        ((A + Pc) * b + C * (1 + b) ^ K) / Real.pi := by
      refine (intervalIntegral.norm_integral_le_integral_norm hb).trans ?_
      have h4 : ∫ t in (0 : ℝ)..b, ‖xiGaussianHeatTraceC ((a : ℂ) + t * I)‖ ≤
          ∫ t in (0 : ℝ)..b, (A + Pc + ‖gaussianPrimeChirpC ((a : ℂ) + t * I)‖) / Real.pi :=
        intervalIntegral.integral_mono_on hb (hcontN.norm.intervalIntegrable _ _)
          (((continuous_const.add hcontPr.norm).div_const _).intervalIntegrable _ _)
          fun t _ => hνpt t
      refine h4.trans ?_
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add
        (continuous_const.intervalIntegrable _ _) (hcontPr.norm.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      exact div_le_div_of_nonneg_right (by linarith [hC b hb]) hπ.le
    rw [h2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    have h1b : (1 : ℝ) ≤ 1 + b := by linarith
    have hpK : (1 + b) ^ K ≤ (1 + b) ^ (K + 1) := pow_le_pow_right₀ h1b (Nat.le_succ K)
    have hpb : b ≤ (1 + b) ^ (K + 1) := by
      calc b ≤ 1 + b := by linarith
        _ = (1 + b) ^ 1 := (pow_one _).symm
        _ ≤ (1 + b) ^ (K + 1) := pow_le_pow_right₀ h1b (by omega)
    have hp1 : 1 ≤ (1 + b) ^ (K + 1) := one_le_pow₀ h1b
    have h5 : ((A + Pc) * b + C * (1 + b) ^ K) / Real.pi ≤
        (A + Pc + |C|) / Real.pi * (1 + b) ^ (K + 1) := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hπ.le
      have h6 : C * (1 + b) ^ K ≤ |C| * (1 + b) ^ (K + 1) :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hpK (abs_nonneg C))
      nlinarith [mul_le_mul_of_nonneg_left hpb (by positivity : (0 : ℝ) ≤ A + Pc)]
    have h7 : 0 ≤ ‖xiGaussianHeatPrimitiveC (a : ℂ)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hp1 h7]

end

end RHTower
