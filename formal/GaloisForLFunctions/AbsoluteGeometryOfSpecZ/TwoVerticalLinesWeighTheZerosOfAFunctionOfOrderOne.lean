import GaloisForLFunctions.RHTower.CompletionLogDerivZeroPairs

/-!
# Two vertical lines weigh the zeros of a function of order one

Let `E` be entire of order one, `E(2) ≠ 0`, with all zeros in the closed strip `0 ≤ Re s ≤ 1`,
and let `H` be entire with `|H(σ + it)| ≤ D (1 + t²)⁻²` on `−1 ≤ σ ≤ 2`. For `1 < c ≤ 2`

`Σ_ρ H(ρ) = (1/2π) (∫ H(c + it) E'/E(c + it) dt − ∫ H(1 − c + it) E'/E(1 − c + it) dt)`,

the sum over the zeros with multiplicity (`hasSum_zeros_two_lines`). No functional equation is
used: this is the zero side of an explicit formula for any completed `L`-function, self-dual
or not.

* **Partial fractions** (`exists_hasSum_logDeriv`). Hadamard's factorization gives
  `E'/E(s) = a + Σ_ρ (1/(s − ρ) + 1/(ρ − 2))` off the zeros, with `Σ_ρ |ρ − 2|⁻² < ∞`.
* **One zero** (`two_line_simple_pole_add_const`). The two lines cut out the residue `H(ρ)` of
  `H(s)/(s − ρ)`; the line integrals of `H` itself agree, so a constant added to the pole term
  drops out of the difference. This removes both `1/(ρ − 2)` and `a`.
* **All zeros** (`hasSum_line_integral_partialFractions`). On a line at distance `δ` from the
  strip, `|1/(s − ρ) + 1/(ρ − 2)| ≤ |s − 2|(1 + |s − 2|/δ)/|ρ − 2|²`, which against the decay of
  `H` is integrable along the line and summable over the zeros.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.EntireZeroDivisor
open Zeta23 Zeta23.WeilEF

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open RHTower.OrderOneHadamard RHTower.CompletionZeroPairs RHTower.WeilLineIntegral

/-! ### Hadamard's partial fractions -/

/-- The zeros of `E` with multiplicity: the copies of the divisor of `z ↦ E(z + 2)`, moved
back by `2`. -/
def zeroOf (E : ℂ → ℂ) (q : ZeroCopy (fun z => E (z + 2))) : ℂ :=
  zeroCopyPoint (fun z => E (z + 2)) q + 2

theorem apply_zeroOf {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (q : ZeroCopy (fun z => E (z + 2))) : E (zeroOf E q) = 0 :=
  apply_zeroCopyPoint (f := fun z => E (z + 2))
    ((hE.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ) q

/-- **Hadamard's partial fractions.** For `E` entire of order one with `E(2) ≠ 0`:
`E'/E(s) − a = Σ_ρ (1/(s − ρ) + 1/(ρ − 2))` at every `s` that is not a zero, and
`Σ_ρ |ρ − 2|⁻² < ∞`. -/
theorem exists_hasSum_logDeriv {E : ℂ → ℂ} (hE : Differentiable ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) (h2 : E 2 ≠ 0) :
    (∀ q, zeroOf E q ≠ 2) ∧
    Summable (fun q : ZeroCopy (fun z => E (z + 2)) => 1 / ‖zeroOf E q - 2‖ ^ (2 : ℕ)) ∧
    ∃ a : ℂ, ∀ s : ℂ, E s ≠ 0 →
      HasSum (fun q : ZeroCopy (fun z => E (z + 2)) =>
        (s - zeroOf E q)⁻¹ + (zeroOf E q - 2)⁻¹) (logDeriv E s - a) := by
  unfold zeroOf
  set f : ℂ → ℂ := fun z => E (z + 2) with hfdef
  have hfd : Differentiable ℂ f := hE.comp (differentiable_id.add_const 2)
  have hf : AnalyticOnNhd ℂ f univ := hfd.differentiableOn.analyticOnNhd isOpen_univ
  have hf0 : f 0 ≠ 0 := by simpa [hfdef] using h2
  have hford : ∀ z, analyticOrderAt f z ≠ ⊤ := fun z =>
    hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ z)
      (by rw [(hf 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]; exact ENat.zero_ne_top)
  have hC6 : 0 ≤ 6 * C := by positivity
  have hbf := bound_shift hC hbound
  obtain ⟨a, b, hab⟩ := exists_expAffine_mul_hadamardProduct hC6 hf hf0 hford hbf
  have hsum := summable_inv_sq_zeroCopyPoint hC6 hf hf0 hbf
  have hane := zeroCopyPoint_ne_zero hf hf0
  refine ⟨fun q h => hane q (by linear_combination h), ?_, a, fun s hs => ?_⟩
  · refine hsum.congr fun q => ?_
    rw [add_sub_cancel_right]
  set P := hadamardProduct f with hP
  have hPd : Differentiable ℂ P := fun z =>
    (hadamardProduct_analytic hf hf0 hsum z (mem_univ z)).differentiableAt
  have hfs : f (s - 2) ≠ 0 := by simpa [hfdef] using hs
  have hwq : ∀ q, s - 2 ≠ zeroCopyPoint f q := fun q h => hfs (h ▸ apply_zeroCopyPoint hf q)
  have hPw : P (s - 2) ≠ 0 := by
    intro h0
    apply hfs
    rw [hab (s - 2), h0, mul_zero]
  have hfeq : f = fun z => Complex.exp (a * z + b) * P z := funext hab
  have hd : HasDerivAt (fun z => Complex.exp (a * z + b))
      (Complex.exp (a * (s - 2) + b) * a) (s - 2) := by
    have := ((hasDerivAt_id (s - 2)).const_mul a).add_const b
    simpa using this.cexp
  -- the expansion of `f'/f` at `s − 2`
  have hlog : logDeriv f (s - 2) =
      a + ∑' q, ((s - 2 - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹) := by
    have hlf : logDeriv f (s - 2) =
        logDeriv (fun z => Complex.exp (a * z + b) * P z) (s - 2) := by
      rw [hfeq]
    rw [hlf, logDeriv_mul (f := fun z => Complex.exp (a * z + b)) (g := P) (s - 2)
      (Complex.exp_ne_zero _) hPw (by fun_prop) (hPd _)]
    rw [hP, hadamardProduct, RHTower.logDeriv_canonicalProductE1Indexed hane hsum hwq]
    congr 1
    rw [logDeriv_apply, hd.deriv]
    field_simp
  have hEf : logDeriv E s = logDeriv f (s - 2) := by
    have hcomp : E = f ∘ fun w => w - 2 := by
      funext w
      simp [hfdef]
    rw [hcomp, logDeriv_comp (hfd _) (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - 2) s)]
    simp
  have hT : Summable fun q => (s - 2 - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹ := by
    refine (RHTower.summable_canonicalProductE1LogDerivTerm hane hsum hwq).neg.congr fun q => ?_
    rw [show zeroCopyPoint f q - (s - 2) = -(s - 2 - zeroCopyPoint f q) by ring, inv_neg]
    ring
  have hval : logDeriv E s - a =
      ∑' q, ((s - 2 - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹) := by
    rw [hEf, hlog]
    ring
  rw [hval]
  refine hT.hasSum.congr_fun fun q => ?_
  rw [show s - (zeroCopyPoint f q + 2) = s - 2 - zeroCopyPoint f q by ring, add_sub_cancel_right]

/-! ### One zero between two lines -/

/-- The line integrals of an entire function with an integrable majorant on a strip agree. -/
theorem integral_line_eq {H : ℂ → ℂ} (hH : Differentiable ℂ H) {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) :
    ∫ t : ℝ, H (b + t * I) = ∫ t : ℝ, H (a + t * I) := by
  have hφ : Integrable (fun t : ℝ => C / (1 + t ^ 2)) := by
    simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
  have htop : Tendsto (fun t : ℝ => C / (1 + t ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num)))
  have hbot : Tendsto (fun t : ℝ => C / (1 + t ^ 2)) atBot (𝓝 0) := by
    refine Tendsto.congr (fun t => ?_) (htop.comp tendsto_neg_atBot_atTop)
    show C / (1 + (-t) ^ 2) = C / (1 + t ^ 2)
    rw [neg_sq]
  exact vertical_line_shift hab (fun s _ _ => hH s) hφ hC htop hbot

/-- An entire function with the majorant `C/(1 + t²)` is integrable on each line of the
strip. -/
theorem integrable_line_of_bound {H : ℂ → ℂ} (hH : Differentiable ℂ H) {σ C : ℝ}
    (hC : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) :
    Integrable (fun t : ℝ => H (σ + t * I)) := by
  have hφ : Integrable (fun t : ℝ => C / (1 + t ^ 2)) := by
    simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
  exact integrable_line (fun t => hH _) hφ hC

/-- **Two lines, one simple pole, and a constant.** For `a < Re p < b`,
`∫ H(b + it)(1/(b + it − p) + w) dt − ∫ H(a + it)(1/(a + it − p) + w) dt = 2π H(p)`: the
constant `w` does not contribute. -/
theorem two_line_simple_pole_add_const {H : ℂ → ℂ} (hH : Differentiable ℂ H) {a b C : ℝ}
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) {p : ℂ}
    (hp1 : a < p.re) (hp2 : p.re < b) (w : ℂ) :
    (∫ t : ℝ, H (b + t * I) * ((b + t * I - p)⁻¹ + w)) -
      (∫ t : ℝ, H (a + t * I) * ((a + t * I - p)⁻¹ + w)) = 2 * Real.pi * H p := by
  have hab : a ≤ b := by linarith
  have hib := integrable_line_div hH hC hab le_rfl hp2.ne'
  have hia := integrable_line_div hH hC le_rfl hab hp1.ne
  have hHb := integrable_line_of_bound hH (fun t => hC b t hab le_rfl)
  have hHa := integrable_line_of_bound hH (fun t => hC a t le_rfl hab)
  have hpole := two_line_simple_pole hH hC hp1 hp2
  have hline := integral_line_eq hH hab hC
  have eb : (∫ t : ℝ, H (b + t * I) * ((b + t * I - p)⁻¹ + w)) =
      (∫ t : ℝ, H (b + t * I) / (b + t * I - p)) + w * ∫ t : ℝ, H (b + t * I) := by
    rw [← integral_const_mul, ← integral_add hib (hHb.const_mul w)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [div_eq_mul_inv]
    ring
  have ea : (∫ t : ℝ, H (a + t * I) * ((a + t * I - p)⁻¹ + w)) =
      (∫ t : ℝ, H (a + t * I) / (a + t * I - p)) + w * ∫ t : ℝ, H (a + t * I) := by
    rw [← integral_const_mul, ← integral_add hia (hHa.const_mul w)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [div_eq_mul_inv]
    ring
  rw [eb, ea, hline]
  linear_combination hpole

/-! ### The partial fractions on a line -/

/-- `|1/(s − ρ) + 1/(ρ − 2)| ≤ |s − 2| (1 + |s − 2|/δ) / |ρ − 2|²` when `|s − ρ| ≥ δ`. -/
theorem norm_inv_add_inv_le {s ρ : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsρ : δ ≤ ‖s - ρ‖) (hρ : ρ ≠ 2) :
    ‖(s - ρ)⁻¹ + (ρ - 2)⁻¹‖ ≤ ‖s - 2‖ * (1 + ‖s - 2‖ / δ) / ‖ρ - 2‖ ^ 2 := by
  have hB : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδ hsρ
  have h1 : s - ρ ≠ 0 := norm_pos_iff.mp hB
  have h2 : ρ - 2 ≠ 0 := sub_ne_zero.mpr hρ
  have hR : 0 < ‖ρ - 2‖ := norm_pos_iff.mpr h2
  have hA : 0 ≤ ‖s - 2‖ := norm_nonneg _
  have heq : (s - ρ)⁻¹ + (ρ - 2)⁻¹ = (s - 2) / ((s - ρ) * (ρ - 2)) := by
    field_simp
    ring
  have htri : ‖ρ - 2‖ ≤ ‖s - ρ‖ + ‖s - 2‖ := by
    have := norm_sub_le (s - 2) (s - ρ)
    rw [show s - 2 - (s - ρ) = ρ - 2 by ring] at this
    linarith
  have hone : 1 ≤ ‖s - ρ‖ / δ := (one_le_div hδ).mpr hsρ
  have hRle : ‖ρ - 2‖ ≤ ‖s - ρ‖ * (1 + ‖s - 2‖ / δ) := by
    have : ‖s - 2‖ ≤ ‖s - 2‖ * (‖s - ρ‖ / δ) := le_mul_of_one_le_right hA hone
    calc ‖ρ - 2‖ ≤ ‖s - ρ‖ + ‖s - 2‖ * (‖s - ρ‖ / δ) := by linarith
      _ = ‖s - ρ‖ * (1 + ‖s - 2‖ / δ) := by ring
  rw [heq, norm_div, norm_mul, div_le_div_iff₀ (mul_pos hB hR) (pow_pos hR 2)]
  calc ‖s - 2‖ * ‖ρ - 2‖ ^ 2 = ‖s - 2‖ * ‖ρ - 2‖ * ‖ρ - 2‖ := by ring
    _ ≤ ‖s - 2‖ * ‖ρ - 2‖ * (‖s - ρ‖ * (1 + ‖s - 2‖ / δ)) :=
        mul_le_mul_of_nonneg_left hRle (mul_nonneg hA hR.le)
    _ = ‖s - 2‖ * (1 + ‖s - 2‖ / δ) * (‖s - ρ‖ * ‖ρ - 2‖) := by ring

/-- On a line of the strip `−1 ≤ σ ≤ 2`: `|s − 2|(1 + |s − 2|/δ) ≤ (6 + 18/δ)(1 + t²)`. -/
theorem norm_line_sub_two_mul_le {σ δ : ℝ} (hσ1 : -1 ≤ σ) (hσ2 : σ ≤ 2) (hδ : 0 < δ) (t : ℝ) :
    ‖(σ : ℂ) + t * I - 2‖ * (1 + ‖(σ : ℂ) + t * I - 2‖ / δ) ≤ (6 + 18 / δ) * (1 + t ^ 2) := by
  have hA0 : 0 ≤ ‖(σ : ℂ) + t * I - 2‖ := norm_nonneg _
  have hA : ‖(σ : ℂ) + t * I - 2‖ ≤ 3 + |t| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : ((σ : ℂ) + t * I - 2).re = σ - 2 := by simp
    have him : ((σ : ℂ) + t * I - 2).im = t := by simp
    rw [hre, him, abs_of_nonpos (by linarith)]
    linarith
  have ht : 2 * |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have h1 : ‖(σ : ℂ) + t * I - 2‖ ≤ 6 * (1 + t ^ 2) := by nlinarith
  have h2 : ‖(σ : ℂ) + t * I - 2‖ ^ 2 ≤ 18 * (1 + t ^ 2) := by
    have : ‖(σ : ℂ) + t * I - 2‖ ^ 2 ≤ (3 + |t|) ^ 2 := pow_le_pow_left₀ hA0 hA 2
    nlinarith [sq_abs t]
  have h3 : ‖(σ : ℂ) + t * I - 2‖ ^ 2 / δ ≤ 18 * (1 + t ^ 2) / δ :=
    div_le_div_of_nonneg_right h2 hδ.le
  calc ‖(σ : ℂ) + t * I - 2‖ * (1 + ‖(σ : ℂ) + t * I - 2‖ / δ)
      = ‖(σ : ℂ) + t * I - 2‖ + ‖(σ : ℂ) + t * I - 2‖ ^ 2 / δ := by ring
    _ ≤ 6 * (1 + t ^ 2) + 18 * (1 + t ^ 2) / δ := add_le_add h1 h3
    _ = (6 + 18 / δ) * (1 + t ^ 2) := by ring

/-- **Termwise integration of the partial fractions on a line.** On a line `Re s = σ` of the
strip `−1 ≤ σ ≤ 2` at distance at least `δ` from the points `ρ_q`, a test of fourth-order decay
integrates the expansion `Σ_q (1/(s − ρ_q) + 1/(ρ_q − 2)) = E'/E(s) − a` term by term. -/
theorem hasSum_line_integral_partialFractions {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    {ι : Type*} [Countable ι] {ρ : ι → ℂ} (hρ2 : ∀ q, ρ q ≠ 2)
    (hsum : Summable fun q => 1 / ‖ρ q - 2‖ ^ (2 : ℕ)) {a : ℂ}
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {D σ δ : ℝ} (hσ1 : -1 ≤ σ) (hσ2 : σ ≤ 2)
    (hδ : 0 < δ) (hdist : ∀ q, δ ≤ |σ - (ρ q).re|)
    (hD : ∀ t : ℝ, ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2)
    (hne : ∀ t : ℝ, E (σ + t * I) ≠ 0)
    (hpf : ∀ t : ℝ, HasSum (fun q => ((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹)
      (logDeriv E (σ + t * I) - a)) :
    Integrable (fun t : ℝ => H (σ + t * I) * (logDeriv E (σ + t * I) - a)) ∧
    HasSum (fun q => ∫ t : ℝ, H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹))
      (∫ t : ℝ, H (σ + t * I) * (logDeriv E (σ + t * I) - a)) := by
  have hD0 : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hD 0)
    simpa using h
  set M : ℝ := D * (6 + 18 / δ) with hM
  have hM0 : 0 ≤ M := by positivity
  have hline : Continuous fun t : ℝ => (σ : ℂ) + t * I := by fun_prop
  have hHc : Continuous fun t : ℝ => H (σ + t * I) := hH.continuous.comp hline
  have hsρ : ∀ q (t : ℝ), δ ≤ ‖(σ : ℂ) + t * I - ρ q‖ := fun q t => by
    refine (hdist q).trans ?_
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I - ρ q)
    simpa using this
  have hne' : ∀ q (t : ℝ), (σ : ℂ) + t * I - ρ q ≠ 0 := fun q t =>
    norm_pos_iff.mp (lt_of_lt_of_le hδ (hsρ q t))
  -- the pointwise majorant of one term
  have hterm : ∀ q (t : ℝ), ‖H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹)‖ ≤
      M * (1 + t ^ 2)⁻¹ * (1 / ‖ρ q - 2‖ ^ (2 : ℕ)) := by
    intro q t
    have hR : 0 < ‖ρ q - 2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hρ2 q))
    have h1 := norm_inv_add_inv_le hδ (hsρ q t) (hρ2 q)
    have h2 := norm_line_sub_two_mul_le hσ1 hσ2 hδ t
    have ht : 0 < 1 + t ^ 2 := by positivity
    rw [norm_mul]
    calc ‖H (σ + t * I)‖ * ‖((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹‖
        ≤ D / (1 + t ^ 2) ^ 2 * ((6 + 18 / δ) * (1 + t ^ 2) / ‖ρ q - 2‖ ^ 2) := by
          refine mul_le_mul (hD t) (h1.trans ?_) (norm_nonneg _) (by positivity)
          exact div_le_div_of_nonneg_right h2 (by positivity)
      _ = M * (1 + t ^ 2)⁻¹ * (1 / ‖ρ q - 2‖ ^ (2 : ℕ)) := by
          rw [hM]
          field_simp
  have hFc : ∀ q, Continuous fun t : ℝ =>
      H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹) := fun q =>
    hHc.mul (((hline.sub continuous_const).inv₀ (hne' q)).add continuous_const)
  have hdom : ∀ q, Integrable fun t : ℝ => M * (1 + t ^ 2)⁻¹ * (1 / ‖ρ q - 2‖ ^ (2 : ℕ)) :=
    fun q => (integrable_inv_one_add_sq.const_mul M).mul_const _
  have hFi : ∀ q, Integrable fun t : ℝ =>
      H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹) := fun q =>
    (hdom q).mono' (hFc q).aestronglyMeasurable (Eventually.of_forall (hterm q))
  have hFn : ∀ q, ∫ t : ℝ, ‖H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹)‖ ≤
      M * Real.pi * (1 / ‖ρ q - 2‖ ^ (2 : ℕ)) := by
    intro q
    refine (integral_mono (hFi q).norm (hdom q) (hterm q)).trans (le_of_eq ?_)
    rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]
  have hFs : Summable fun q =>
      ∫ t : ℝ, ‖H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹)‖ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun t => norm_nonneg _) hFn
      (hsum.mul_left (M * Real.pi))
  have hpt : ∀ t : ℝ, HasSum
      (fun q => H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹))
      (H (σ + t * I) * (logDeriv E (σ + t * I) - a)) := fun t => (hpf t).mul_left _
  refine ⟨?_, ?_⟩
  · -- integrability of the sum, dominated by the summed majorants
    have hcl : Continuous fun t : ℝ => logDeriv E ((σ : ℂ) + t * I) := by
      have hd : Continuous (deriv E) := (hE.contDiff (n := 1)).continuous_deriv le_rfl
      simp only [logDeriv_apply]
      exact (hd.comp hline).div (hE.continuous.comp hline) hne
    have hdom2 : Integrable fun t : ℝ =>
        M * (1 + t ^ 2)⁻¹ * ∑' q, 1 / ‖ρ q - 2‖ ^ (2 : ℕ) :=
      (integrable_inv_one_add_sq.const_mul M).mul_const _
    refine hdom2.mono' (hHc.mul (hcl.sub continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    exact (hpt t).norm_le_of_bounded (hsum.hasSum.mul_left (M * (1 + t ^ 2)⁻¹)) (hterm · t)
  · have h := hasSum_integral_of_summable_integral_norm hFi hFs
    have heq : (∫ t : ℝ, ∑' q, H (σ + t * I) * (((σ : ℂ) + t * I - ρ q)⁻¹ + (ρ q - 2)⁻¹)) =
        ∫ t : ℝ, H (σ + t * I) * (logDeriv E (σ + t * I) - a) :=
      integral_congr_ae (Eventually.of_forall fun t => (hpt t).tsum_eq)
    rw [heq] at h
    exact h

/-! ### The zeros between two lines -/

/-- **Two vertical lines weigh the zeros.** For `E` entire of order one with `E(2) ≠ 0` and
zeros in `0 ≤ Re s ≤ 1`, an entire `H` of fourth-order decay on `−1 ≤ Re s ≤ 2`, and
`1 < c ≤ 2`: `Σ_ρ H(ρ)` over the zeros with multiplicity is `1/2π` times the difference of the
line integrals of `H · E'/E` on `Re s = c` and `Re s = 1 − c`. -/
theorem hasSum_zeros_two_lines {E : ℂ → ℂ} (hE : Differentiable ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℂ, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) (h2 : E 2 ≠ 0)
    (hstrip : ∀ s, E s = 0 → 0 ≤ s.re ∧ s.re ≤ 1)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) {D : ℝ}
    (hD : ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) :
    Integrable (fun t : ℝ => H (c + t * I) * logDeriv E (c + t * I)) ∧
    Integrable (fun t : ℝ => H ((1 - c : ℝ) + t * I) * logDeriv E ((1 - c : ℝ) + t * I)) ∧
    HasSum (fun q : ZeroCopy (fun z => E (z + 2)) => H (zeroOf E q))
      ((1 / (2 * Real.pi) : ℂ) * ((∫ t : ℝ, H (c + t * I) * logDeriv E (c + t * I)) -
        ∫ t : ℝ, H ((1 - c : ℝ) + t * I) * logDeriv E ((1 - c : ℝ) + t * I))) := by
  have hfd : AnalyticOnNhd ℂ (fun z => E (z + 2)) univ :=
    (hE.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  haveI := countable_zeroCopy hfd
  obtain ⟨hρ2, hsum, a, hpf⟩ := exists_hasSum_logDeriv hE hC hbound h2
  have hD0 : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hD 0 0 (by norm_num) (by norm_num))
    simpa using h
  -- second-order decay, for the single poles
  have hD1 : ∀ σ t : ℝ, 1 - c ≤ σ → σ ≤ c → ‖H (σ + t * I)‖ ≤ D / (1 + t ^ 2) := by
    intro σ t h1 h2
    refine (hD σ t (by linarith) (by linarith)).trans ?_
    have ht : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    exact div_le_div_of_nonneg_left hD0 (by positivity) (by nlinarith)
  have hzre : ∀ q, 0 ≤ (zeroOf E q).re ∧ (zeroOf E q).re ≤ 1 := fun q =>
    hstrip _ (apply_zeroOf hE q)
  have hδ : 0 < c - 1 := by linarith
  -- the two lines are off the zeros
  have hneR : ∀ t : ℝ, E ((c : ℂ) + t * I) ≠ 0 := fun t h0 => by
    have := (hstrip _ h0).2
    simp at this
    linarith
  have hneL : ∀ t : ℝ, E (((1 - c : ℝ) : ℂ) + t * I) ≠ 0 := fun t h0 => by
    have := (hstrip _ h0).1
    simp at this
    linarith
  obtain ⟨hiR, hsR⟩ := hasSum_line_integral_partialFractions hE hρ2 hsum (a := a) hH
    (σ := c) (δ := c - 1) (by linarith) hc2 hδ
    (fun q => by rw [abs_of_nonneg (by linarith [(hzre q).2])]; linarith [(hzre q).2])
    (fun t => hD c t (by linarith) hc2) hneR (fun t => hpf _ (hneR t))
  obtain ⟨hiL, hsL⟩ := hasSum_line_integral_partialFractions hE hρ2 hsum (a := a) hH
    (σ := 1 - c) (δ := c - 1) (by linarith) (by linarith) hδ
    (fun q => by rw [abs_of_nonpos (by linarith [(hzre q).1])]; linarith [(hzre q).1])
    (fun t => hD (1 - c) t (by linarith) (by linarith)) hneL (fun t => hpf _ (hneL t))
  have hHR := integrable_line_of_bound hH (fun t => hD1 c t (by linarith) le_rfl)
  have hHL := integrable_line_of_bound hH (fun t => hD1 (1 - c) t le_rfl (by linarith))
  -- remove the constant `a`
  have hRa : (fun t : ℝ => H (c + t * I) * logDeriv E (c + t * I)) =
      fun t : ℝ => H (c + t * I) * (logDeriv E (c + t * I) - a) + a * H (c + t * I) := by
    funext t
    ring
  have hLa : (fun t : ℝ => H ((1 - c : ℝ) + t * I) * logDeriv E ((1 - c : ℝ) + t * I)) =
      fun t : ℝ => H ((1 - c : ℝ) + t * I) * (logDeriv E ((1 - c : ℝ) + t * I) - a) +
        a * H ((1 - c : ℝ) + t * I) := by
    funext t
    ring
  refine ⟨by rw [hRa]; exact hiR.add (hHR.const_mul a),
    by rw [hLa]; exact hiL.add (hHL.const_mul a), ?_⟩
  have hline := integral_line_eq hH (show 1 - c ≤ c by linarith) hD1
  have hval : (∫ t : ℝ, H (c + t * I) * logDeriv E (c + t * I)) -
      (∫ t : ℝ, H ((1 - c : ℝ) + t * I) * logDeriv E ((1 - c : ℝ) + t * I)) =
      (∫ t : ℝ, H (c + t * I) * (logDeriv E (c + t * I) - a)) -
        ∫ t : ℝ, H ((1 - c : ℝ) + t * I) * (logDeriv E ((1 - c : ℝ) + t * I) - a) := by
    rw [hRa, hLa, integral_add hiR (hHR.const_mul a), integral_add hiL (hHL.const_mul a),
      integral_const_mul, integral_const_mul, hline]
    ring
  rw [hval]
  have hdiff := (hsR.sub hsL).mul_left (1 / (2 * Real.pi) : ℂ)
  refine hdiff.congr_fun fun q => ?_
  have hpole := two_line_simple_pole_add_const hH hD1 (p := zeroOf E q)
    (by linarith [(hzre q).1]) (by linarith [(hzre q).2]) ((zeroOf E q - 2)⁻¹)
  rw [hpole]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
